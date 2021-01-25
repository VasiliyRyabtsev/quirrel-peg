#include "sqpcheader.h"
#include <stdarg.h>
#include <ctype.h>
#include <setjmp.h>
#include <algorithm>
#include "sqopcodes.h"
#include "sqstring.h"
#include "sqfuncproto.h"
#include "sqcompiler.h"
#include "sqfuncstate.h"
#include "sqlexer.h"
#include "sqvm.h"
#include "sqtable.h"
#include "peglib.h"

#define MAX_COMPILER_ERROR_LEN 256
#define MAX_FUNCTION_NAME_LEN 128


using namespace peg;

static const char *grammar = R"(
    FunctionBody <- Statement*
    Statement <- ReturnStatement / 'local' LocalDeclStatement / Expression

    ReturnStatement <- 'return' Expression
    LocalDeclStatement <- 'function' LocalFuncDeclStmt / LocalVarDeclStmt
    LocalVarDeclStmt <- IDENTIFIER '=' Expression / IDENTIFIER
    LocalFuncDeclStmt <- IDENTIFIER '(' FuncParams ')' '{' FunctionBody '}'
    FuncParams <- IDENTIFIER? (',' IDENTIFIER)*
    Expression <- BinaryOpExpr / PrefixedExpr
    BinaryOpExpr <- PrefixedExpr (BINARY_OP PrefixedExpr)* {
                            precedence
                            L ??
                            L ||
                            L && in
                            L ^
                            L &
                            L == != <=>
                            L < <= > >= instanceof
                            L << >> >>>
                            L + -
                            L / * %

    }
    PrefixedExpr <- FunctionCall / Factor
    Factor <- FLOAT / INTEGER / BOOLEAN / NULL / STRING_LITERAL / IDENTIFIER / '(' Expression ')'
    FunctionCall <- Factor '(' FuncCallArgs ')'
    FuncCallArgs <- Expression? (','? Expression)*

    INTEGER     <- < ['-+']? [0-9]+ >
    FLOAT       <- < [-+]?[0-9]* '.'? [0-9]+([eE][-+]?[0-9]+)? / ['-+']?[0-9]+ '.' [0-9]* >
    BOOLEAN     <- < 'true' | 'false' >
    NULL        <- 'null'
    STRING_LITERAL <- '"' < ([^"] / '""')* > '"'
    IDENTIFIER  <- < [a-zA-Z_][a-zA-Z_0-9]* >
    BINARY_OP   <- '??' / '||' / '&&' / 'in' / '^' / '&' /
                    '==' / '!=' / '<=>' / '<' / '<=' / '>' / '>=' / 'instanceof' /
                    '<<' / '>>' / '>>>' / '+' / '-' / '/' / '*' / '%'


    %whitespace <- [ \t\r\n]*
    %word       <- IDENTIFIER
)";


class SQPegCompiler
{
public:
    SQPegCompiler(SQVM *v, const SQChar* sourcename, bool raiseerror, bool lineinfo)
        : _vm(v)
        , _fs(nullptr)
        , _lineinfo(lineinfo)
        , _raiseerror(raiseerror)
        , _scopedconsts(_ss(v)->_alloc_ctx)
    {
        _sourcename = SQString::Create(_ss(v), sourcename);
        _sourcename_ptr = v->constStrings.perpetuate(sourcename);
        // _scope.outers = 0;
        // _scope.stacksize = 0;
        _compilererror[0] = _SC('\0');
    }

    static void ThrowError(void *ud, const SQChar *s) {
        SQPegCompiler *c = (SQPegCompiler *)ud;
        c->Error(s);
    }

    void Error(const SQChar *s, ...)
    {
        va_list vl;
        va_start(vl, s);
        scvsprintf(_compilererror, MAX_COMPILER_ERROR_LEN, s, vl);
        va_end(vl);
        //longjmp(_errorjmp,1);
    }

    bool processChildren(const Ast &ast, int depth) {
        for (const auto &node : ast.nodes)
            processNode(*node.get(), depth + 1);
        return true;
    }


    SQObjectPtr makeString(const std::string_view &s) {
        return _fs->CreateString(s.data(), s.length());
    }

    bool IsConstant(const SQObject &name,SQObject &e)
    {
        if (IsLocalConstant(name, e))
            return true;
        if (IsGlobalConstant(name, e))
            return true;
        return false;
    }

    bool IsLocalConstant(const SQObject &name,SQObject &e)
    {
        SQObjectPtr val;
        for (SQInteger i=SQInteger(_scopedconsts.size())-1; i>=0; --i) {
            SQObjectPtr &tbl = _scopedconsts[i];
            if (!sq_isnull(tbl) && _table(tbl)->Get(name,val)) {
                e = val;
                return true;
            }
        }
        return false;
    }

    bool IsGlobalConstant(const SQObject &name,SQObject &e)
    {
        SQObjectPtr val;
        if(_table(_ss(_vm)->_consts)->Get(name,val)) {
            e = val;
            return true;
        }
        return false;
    }

    bool CheckDuplicateLocalIdentifier(const SQObject &name, const SQChar *desc, bool ignore_global_consts)
    {
        if (_fs->GetLocalVariable(name) >= 0) {
            printf(_SC("%s name '%s' conflicts with existing local variable\n"), desc, _string(name)->_val);
            return false;
        }
        if (_stringval(name) == _stringval(_fs->_name)) {
            printf(_SC("%s name '%s' conflicts with function name\n"), desc, _stringval(name));
            return false;
        }

        SQObject constant;
        if (ignore_global_consts ? IsLocalConstant(name, constant) : IsConstant(name, constant)) {
            printf(_SC("%s name '%s' conflicts with existing constant/enum\n"), desc, _stringval(name));
            return false;
        }
        return true;
    }

    void MoveIfCurrentTargetIsLocal() {
        SQInteger trg = _fs->TopTarget();
        if(_fs->IsLocal(trg)) {
            trg = _fs->PopTarget(); //pops the target and moves it
            _fs->AddInstruction(_OP_MOVE, _fs->PushTarget(), trg);
        }
    }


    bool processNode(const Ast &ast, int depth)
    {
        //printf("%*cname = %s | token = %s\n", depth*2, ' ',
        //    ast.name.c_str(), ast.is_token ? std::string(ast.token).c_str() : "N/A");

        if (ast.name == "INTEGER") {
            SQInteger target = _fs->PushTarget();
            SQInteger value = ast.token_to_number<SQInteger>();
            if (value <= INT_MAX && value > INT_MIN) //does it fit in 32 bits?
                _fs->AddInstruction(_OP_LOADINT, target, value);
            else
                _fs->AddInstruction(_OP_LOAD, target, _fs->GetNumericConstant(value));
        }
        else if (ast.name == "FLOAT") {
            SQInteger target = _fs->PushTarget();
            SQFloat value = ast.token_to_number<SQFloat>();
            if (sizeof(SQFloat) == sizeof(SQInt32))
                _fs->AddInstruction(_OP_LOADFLOAT, target,*((SQInt32 *)&value));
            else
                _fs->AddInstruction(_OP_LOAD, target, _fs->GetNumericConstant(value));
        }
        else if (ast.name == "BOOLEAN") {
            _fs->AddInstruction(_OP_LOADBOOL, _fs->PushTarget(), ast.token == "true"?1:0);
        }
        else if (ast.name == "NULL") {
            _fs->AddInstruction(_OP_LOADNULLS, _fs->PushTarget(), 1);
        }
        else if (ast.name == "STRING_LITERAL") {
            _fs->AddInstruction(_OP_LOAD, _fs->PushTarget(), _fs->GetConstant(_fs->CreateString(ast.token.data(), ast.token.length())));
        }
        else if (ast.name == "ReturnStatement") {
            SQInteger retexp = _fs->GetCurrentPos()+1;

            if (!processChildren(ast, depth))
                return false;

            if (_fs->_traps > 0)
                _fs->AddInstruction(_OP_POPTRAP, _fs->_traps, 0);
            _fs->_returnexp = retexp;
            _fs->AddInstruction(_OP_RETURN, 1, _fs->PopTarget(),_fs->GetStackSize());
        }
        else if (ast.name == "BinaryOpExpr") {
            assert(ast.nodes.size() == 3);
            processChildren(ast, depth);
            SQInteger op1 = _fs->PopTarget();
            SQInteger op2 = _fs->PopTarget();
            SQInteger op3 = 0;

            SQOpcode op;
            if (ast.nodes[1]->name != "BINARY_OP") {
                printf("BINARY_OP expected\n");
                return false;
            }

            auto opStr = ast.nodes[1]->token;
            if (opStr == "+")           op = _OP_ADD;
            else if (opStr == "-")      op = _OP_SUB;
            else if (opStr == "*")      op = _OP_MUL;
            else if (opStr == "/")      op = _OP_DIV;
            else if (opStr == "%")      op = _OP_MOD;
            else {
                printf("Unknown operator '%s'\n", std::string(opStr).c_str());
                return false;
            }

            _fs->AddInstruction(op, _fs->PushTarget(), op1, op2, op3);
        }
        else if (ast.name == "LocalVarDeclStmt") {
            SQObjectPtr varname = makeString(ast.nodes[0]->token);
            if (!CheckDuplicateLocalIdentifier(varname, _SC("Local variable"), false))
                return false;

            if (ast.nodes.size() > 1) {
                if (!processChildren(ast, depth))
                    return false;
                SQInteger src = _fs->PopTarget();
                SQInteger dest = _fs->PushTarget();
                if (dest != src)
                    _fs->AddInstruction(_OP_MOVE, dest, src);
            }
            else {
                _fs->AddInstruction(_OP_LOADNULLS, _fs->PushTarget(), 1);
            }
            _fs->PopTarget();
            _fs->PushLocalVariable(varname);
        }
        else if (ast.name == "Factor") {
            const auto& tp = ast.nodes[0]->name;
            if (tp == "IDENTIFIER") {
                SQObjectPtr id = makeString(ast.nodes[0]->token);
                SQInteger pos = _fs->GetLocalVariable(id);
                if(pos != -1) // Handle a local variable (includes 'this')
                    _fs->PushTarget(pos);
                else {
                    printf("Unknown local variable '%s'\n", _stringval(id));
                    return false;
                }

            }
            if (!processChildren(ast, depth))
                return false;
        }
        else if (ast.name == "LocalFuncDeclStmt") {
            assert(ast.nodes[0]->name == "IDENTIFIER");
            assert(ast.nodes[1]->name == "FuncParams");
            assert(ast.nodes[2]->name == "FunctionBody");
            SQObjectPtr varname = makeString(ast.nodes[0]->token);
            if (!CheckDuplicateLocalIdentifier(varname, _SC("Function"), false))
                return false;

            SQFuncState *funcstate = _fs->PushChildState(_ss(_vm));
            funcstate->_name = varname;
            funcstate->AddParameter(_fs->CreateString(_SC("this")));
            funcstate->_sourcename = _sourcename;
            funcstate->_sourcename_ptr = _sourcename_ptr;
            SQInteger defparams = 0;
            for (const auto &paramNode : ast.nodes[1]->nodes) {
                SQObjectPtr paramname = makeString(paramNode->token);
                funcstate->AddParameter(paramname);
            }

            SQFuncState *currchunk = _fs;
            _fs = funcstate;

            // body
            processNode(*ast.nodes[2].get(), depth+1);

            //funcstate->AddLineInfos(_lex._prevtoken == _SC('\n')?_lex._lasttokenline:_lex._currentline, _lineinfo, true);
            funcstate->AddInstruction(_OP_RETURN, -1);
            funcstate->SetStackSize(0);

            SQFunctionProto *func = funcstate->BuildProto();
#ifdef _DEBUG_DUMP
            funcstate->Dump(func);
#endif
            _fs = currchunk;
            _fs->_functions.push_back(func);
            _fs->PopChildState();

            _fs->AddInstruction(_OP_CLOSURE, _fs->PushTarget(), _fs->_functions.size() - 1, 0);
            _fs->PopTarget();
            _fs->PushLocalVariable(varname);
        }
        else if (ast.name == "FunctionCall") {
            assert(ast.nodes.size() == 2);

            // resolve function
            processNode(*ast.nodes[0].get(), depth+1);
            _fs->AddInstruction(_OP_MOVE, _fs->PushTarget(), 0);

            Ast *args = ast.nodes[1].get();
            //printf("%d arg nodes\n", int(args->nodes.size()));

            SQInteger nargs = 1;//this
            for (size_t i=0; i<args->nodes.size(); ++i) {
                processNode(*args->nodes[i].get(), depth+1);
                MoveIfCurrentTargetIsLocal();
                nargs++;
            }
            for(SQInteger i = 0; i < (nargs - 1); i++)
                _fs->PopTarget();
            SQInteger stackbase = _fs->PopTarget();
            SQInteger closure = _fs->PopTarget();
            SQInteger target = _fs->PushTarget();
            assert(target >= -1);
            assert(target < 255);
            _fs->AddInstruction(_OP_CALL, target, closure, stackbase, nargs);
        }
        else {
            if (!processChildren(ast, depth))
                return false;
        }


        return true;
    }

    bool processAst(const Ast &ast, SQObjectPtr &o)
    {
        _scopedconsts.push_back();
        SQFuncState funcstate(_ss(_vm), NULL,ThrowError,this);
        funcstate._name = SQString::Create(_ss(_vm), _SC("__main__"));
        _fs = &funcstate;
        _fs->AddParameter(_fs->CreateString(_SC("this")));
        _fs->AddParameter(_fs->CreateString(_SC("vargv")));
        _fs->_varparams = true;
        _fs->_sourcename = _sourcename;
        _fs->_sourcename_ptr = _sourcename_ptr;
        SQInteger stacksize = _fs->GetStackSize();

        processNode(ast, 0);

        _fs->SetStackSize(stacksize);
        //_fs->AddLineInfos(_lex._currentline, _lineinfo, true);
        _fs->AddInstruction(_OP_RETURN, 0xFF);
        _fs->SetStackSize(0);
        o =_fs->BuildProto();

#ifdef _DEBUG_DUMP
        _fs->Dump(_funcproto(o));
#endif

        assert(_scopedconsts.size()==1);
        return true;
    }

    bool Compile(const SQChar *src, SQInteger /*src_len*/, SQObjectPtr &o)
    {
        printf("===\n%s\n===\n", src);

        parser parser(grammar);


        // //parser["INTEGER"] = [](const SemanticValues& vs, std::any& dt) {
        // //    printf("INTEGER action\n");
        // //};
        // parser["INTEGER"].enter = [](const char* s, size_t n, std::any& dt) {
        //     printf("INTEGER enter\n");
        // };
        // parser["INTEGER"] = [](const SemanticValues& vs) {
        //     printf("INTEGER action\n");
        //     return vs.token_to_number<SQInteger>();
        // };
        // parser["INTEGER"].leave = [](const char* s, size_t n, size_t matchlen, std::any& value, std::any& dt) {
        //     printf("INTEGER leave\n");
        // };

        parser.log = [](size_t line, size_t col, const std::string& msg) {
            printf("Parse error at %d:%d: %s", int(line), int(col), msg.c_str());
        };

        parser.enable_ast();

        auto expr = src;
        std::shared_ptr<Ast> ast;
        if (!parser.parse(expr, ast)) {
            std::cout << "syntax error..." << std::endl;
            return false;
        }

        //std::shared_ptr<Ast> astOpt = AstOptimizer(true).optimize(ast);
        std::shared_ptr<Ast> astOpt = ast;
        std::cout << ast_to_s(astOpt);
        //std::cout << expr << " = " << eval(*ast) << std::endl;

        return processAst(*astOpt.get(), o);
        // o = SQObjectPtr();
        // return false;
    }

private:
    //std::shared_ptr<Ast> ast;

    SQVM *_vm;
    SQFuncState *_fs;
    SQObjectPtr _sourcename;
    const SQChar * _sourcename_ptr;
    bool _lineinfo;
    bool _raiseerror;
    // SQInteger _debugline;
    // SQInteger _debugop;
//    SQScope _scope;
    SQChar _compilererror[MAX_COMPILER_ERROR_LEN];
    SQObjectPtrVec _scopedconsts;
};


bool CompilePeg(SQVM *vm, const SQChar *src, SQInteger src_len, const HSQOBJECT *bindings, const SQChar *sourcename,
                SQObjectPtr &out, bool raiseerror, bool lineinfo)
{
    SQPegCompiler p(vm, sourcename, raiseerror, lineinfo);
    return p.Compile(src, src_len, out);
}
