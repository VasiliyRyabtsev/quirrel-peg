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

#include "grammar.cpp.inc"

struct SQScope {
    SQInteger outers;
    SQInteger stacksize;
};

#define BEGIN_SCOPE() SQScope __oldscope__ = _scope; \
                     _scope.outers = _fs->_outers; \
                     _scope.stacksize = _fs->GetStackSize(); \
                     _scopedconsts.push_back();

#define RESOLVE_OUTERS() if(_fs->GetStackSize() != _fs->_blockstacksizes.top()) { \
                            if(_fs->CountOuters(_fs->_blockstacksizes.top())) { \
                                _fs->AddInstruction(_OP_CLOSE,0,_fs->_blockstacksizes.top()); \
                            } \
                        }

#define END_SCOPE_NO_CLOSE() {  if(_fs->GetStackSize() != _scope.stacksize) { \
                            _fs->SetStackSize(_scope.stacksize); \
                        } \
                        _scope = __oldscope__; \
                        assert(!_scopedconsts.empty()); \
                        _scopedconsts.pop_back(); \
                    }

#define END_SCOPE() {   SQInteger oldouters = _fs->_outers;\
                        if(_fs->GetStackSize() != _scope.stacksize) { \
                            _fs->SetStackSize(_scope.stacksize); \
                            if(oldouters != _fs->_outers) { \
                                _fs->AddInstruction(_OP_CLOSE,0,_scope.stacksize); \
                            } \
                        } \
                        _scope = __oldscope__; \
                        _scopedconsts.pop_back(); \
                    }

#define BEGIN_BREAKBLE_BLOCK()  SQInteger __nbreaks__=_fs->_unresolvedbreaks.size(); \
                            SQInteger __ncontinues__=_fs->_unresolvedcontinues.size(); \
                            _fs->_breaktargets.push_back(0);_fs->_continuetargets.push_back(0); \
                            _fs->_blockstacksizes.push_back(_scope.stacksize);


#define END_BREAKBLE_BLOCK(continue_target) {__nbreaks__=_fs->_unresolvedbreaks.size()-__nbreaks__; \
                    __ncontinues__=_fs->_unresolvedcontinues.size()-__ncontinues__; \
                    if(__ncontinues__>0)ResolveContinues(_fs,__ncontinues__,continue_target); \
                    if(__nbreaks__>0)ResolveBreaks(_fs,__nbreaks__); \
                    _fs->_breaktargets.pop_back();_fs->_continuetargets.pop_back(); \
                    _fs->_blockstacksizes.pop_back(); }


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
        _scope.outers = 0;
        _scope.stacksize = 0;
        _compilererror[0] = _SC('\0');
    }


    static void ThrowError(void *ud, const SQChar *s) {
        SQPegCompiler *c = (SQPegCompiler *)ud;
        c->Error(s);
    }


    void Error(const SQChar *s, ...) {
        va_list vl;
        va_start(vl, s);
        scvsprintf(_compilererror, MAX_COMPILER_ERROR_LEN, s, vl);
        va_end(vl);
        longjmp(_errorjmp,1);
    }


    bool CanBeDefaultDelegate(const SQObjectPtr &key)
    {
        if (sq_type(key) != OT_STRING)
            return false;

        // this can be optimized by keeping joined list/table of used keys
        SQTable *delegTbls[] = {
            _table(_fs->_sharedstate->_table_default_delegate),
            _table(_fs->_sharedstate->_array_default_delegate),
            _table(_fs->_sharedstate->_string_default_delegate),
            _table(_fs->_sharedstate->_number_default_delegate),
            _table(_fs->_sharedstate->_generator_default_delegate),
            _table(_fs->_sharedstate->_closure_default_delegate),
            _table(_fs->_sharedstate->_thread_default_delegate),
            _table(_fs->_sharedstate->_class_default_delegate),
            _table(_fs->_sharedstate->_instance_default_delegate),
            _table(_fs->_sharedstate->_weakref_default_delegate),
            _table(_fs->_sharedstate->_userdata_default_delegate)
        };
        SQObjectPtr tmp;
        for (SQInteger i=0; i<sizeof(delegTbls)/sizeof(delegTbls[0]); ++i) {
            if (delegTbls[i]->Get(key, tmp))
                return true;
        }
        return false;
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

    void CheckDuplicateLocalIdentifier(const SQObject &name, const SQChar *desc, bool ignore_global_consts)
    {
        if (_fs->GetLocalVariable(name) >= 0)
            Error(_SC("%s name '%s' conflicts with existing local variable"), desc, _string(name)->_val);
        if (_stringval(name) == _stringval(_fs->_name))
            Error(_SC("%s name '%s' conflicts with function name"), desc, _stringval(name));

        SQObject constant;
        if (ignore_global_consts ? IsLocalConstant(name, constant) : IsConstant(name, constant))
            Error(_SC("%s name '%s' conflicts with existing constant/enum"), desc, _stringval(name));
    }

    void MoveIfCurrentTargetIsLocal() {
        SQInteger trg = _fs->TopTarget();
        if(_fs->IsLocal(trg)) {
            trg = _fs->PopTarget(); //pops the target and moves it
            _fs->AddInstruction(_OP_MOVE, _fs->PushTarget(), trg);
        }
    }

    void ResolveBreaks(SQFuncState *funcstate, SQInteger ntoresolve)
    {
        while(ntoresolve > 0) {
            SQInteger pos = funcstate->_unresolvedbreaks.back();
            funcstate->_unresolvedbreaks.pop_back();
            //set the jmp instruction
            funcstate->SetInstructionParams(pos, 0, funcstate->GetCurrentPos() - pos, 0);
            ntoresolve--;
        }
    }
    void ResolveContinues(SQFuncState *funcstate, SQInteger ntoresolve, SQInteger targetpos)
    {
        while(ntoresolve > 0) {
            SQInteger pos = funcstate->_unresolvedcontinues.back();
            funcstate->_unresolvedcontinues.pop_back();
            //set the jmp instruction
            funcstate->SetInstructionParams(pos, 0, targetpos - pos, 0);
            ntoresolve--;
        }
    }


    std::string unescapeString(const std::string_view& s) {
        std::string res;
        res.reserve(s.length()+1);

#define APPEND_CHAR(c) res.append(1, c)
        for (size_t i=0, n=s.length(); i<n; ++i) {
            char c = s[i];
            if (c=='\\' && i<n-1) {
                switch (s[i+1]) {
                    case _SC('t'): APPEND_CHAR(_SC('\t')); break;
                    case _SC('a'): APPEND_CHAR(_SC('\a')); break;
                    case _SC('b'): APPEND_CHAR(_SC('\b')); break;
                    case _SC('n'): APPEND_CHAR(_SC('\n')); break;
                    case _SC('r'): APPEND_CHAR(_SC('\r')); break;
                    case _SC('v'): APPEND_CHAR(_SC('\v')); break;
                    case _SC('f'): APPEND_CHAR(_SC('\f')); break;
                    case _SC('0'): APPEND_CHAR(_SC('\0')); break;
                    case _SC('\\'): APPEND_CHAR(_SC('\\')); break;
                    case _SC('"'):  APPEND_CHAR(_SC('"'));  break;
                    case _SC('\''): APPEND_CHAR(_SC('\'')); break;
                    default:
                        res.append(1, '\\');
                        res.append(1, s[i+1]);
                }
                ++i;
                continue;
            }
            res.append(1, c);
        }
#undef APPEND_CHAR
        return res;
    }

    void processChildren(const Ast &ast) {
        for (const auto &node : ast.nodes)
            processNode(*node.get());
    }

    void Statement(const Ast &ast) {
        assert(ast.nodes.size()==1);
        _fs->AddLineInfos(ast.line, _lineinfo);
        processChildren(ast);
        if (ast.nodes[0]->name == "Expression") {
            _fs->DiscardTarget();
            //_fs->PopTarget();
        }

        _fs->SnoozeOpt();
    }


    void FactorPush(const Ast &ast) {
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
            std::string s = unescapeString(ast.token);
            _fs->AddInstruction(_OP_LOAD, _fs->PushTarget(), _fs->GetConstant(_fs->CreateString(s.c_str(), s.length())));
        }
        else if (ast.name == "LOADROOT") {
            _fs->AddInstruction(_OP_LOADROOT, _fs->PushTarget());
        }
        else
            Error(_SC("Unexpected factor primitive '%s' "), ast.name);
    }


    void Factor(const Ast &ast) {
        const auto& tp = ast.nodes[0]->name;
        if (tp == "IDENTIFIER") {
            SQObjectPtr id = makeString(ast.nodes[0]->token);

            SQInteger pos;
            if ((pos = _fs->GetLocalVariable(id)) != -1) // Handle a local variable (includes 'this')
                _fs->PushTarget(pos);
            else if ((pos = _fs->GetOuterVariable(id)) != -1)
                _fs->AddInstruction(_OP_GETOUTER, _fs->PushTarget(), pos);
            else if (sq_isstring(_fs->_name) && scstrcmp(_stringval(_fs->_name), _stringval(id))==0)
                _fs->AddInstruction(_OP_LOADCALLEE, _fs->PushTarget());
            else
                Error(_SC("Unknown local variable '%s'"), _stringval(id));
        }
        processChildren(ast);
    }


    void ReturnStatement(const Ast &ast) {
        SQInteger retexp = _fs->GetCurrentPos()+1;

        processChildren(ast);

        if (_fs->_traps > 0)
            _fs->AddInstruction(_OP_POPTRAP, _fs->_traps, 0);
        _fs->_returnexp = retexp;
        _fs->AddInstruction(_OP_RETURN, 1, _fs->PopTarget(),_fs->GetStackSize());
    }


    void BlockStatement(const Ast &ast) {
        BEGIN_SCOPE();
        processChildren(ast);
        END_SCOPE_NO_CLOSE();
        //END_SCOPE();
        // if(closeframe) {
        //     END_SCOPE();
        // }
        // else {
        //     END_SCOPE_NO_CLOSE();
        // }
    }


    void BinaryOpExpr(const Ast &ast) {
        assert(ast.nodes.size() == 3);

        processChildren(ast);

        SQInteger op1 = _fs->PopTarget();
        SQInteger op2 = _fs->PopTarget();
        SQInteger op3 = 0;

        SQOpcode op;
        if (ast.nodes[1]->name != "BINARY_OP")
            Error(_SC("BINARY_OP expected"));

        auto opStr = ast.nodes[1]->token;
        if (opStr == "+")           op = _OP_ADD;
        else if (opStr == "-")      op = _OP_SUB;
        else if (opStr == "*")      op = _OP_MUL;
        else if (opStr == "/")      op = _OP_DIV;
        else if (opStr == "%")      op = _OP_MOD;
        else if (opStr == "==")     op = _OP_EQ;
        else if (opStr == "!=")     op = _OP_NE;
        else if (opStr == ">")      {op = _OP_CMP; op3 = CMP_G;}
        else if (opStr == "<")      {op = _OP_CMP; op3 = CMP_L;}
        else if (opStr == ">=")     {op = _OP_CMP; op3 = CMP_GE;}
        else if (opStr == "<=")     {op = _OP_CMP; op3 = CMP_LE;}
        else if (opStr == "<=>")    {op = _OP_CMP; op3 = CMP_3W;}
        else
            Error(_SC("Unknown operator '%s'"), std::string(opStr).c_str());

        _fs->AddInstruction(op, _fs->PushTarget(), op1, op2, op3);
    }


    void LocalVarDeclStmt(const Ast &ast) {
        SQObjectPtr varname = makeString(ast.nodes[0]->token);
        CheckDuplicateLocalIdentifier(varname, _SC("Local variable"), false);

        if (ast.nodes.size() > 1) {
            processChildren(ast);
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


    void LocalFuncDeclStmt(const Ast &ast) {
        assert(ast.nodes[0]->name == "IDENTIFIER");
        assert(ast.nodes[1]->name == "FuncParams");
        assert(ast.nodes[2]->name == "Statement");
        SQObjectPtr varname = makeString(ast.nodes[0]->token);
        CheckDuplicateLocalIdentifier(varname, _SC("Function"), false);

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
        processNode(*ast.nodes[2].get());

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


    void PrefixedExpr(const Ast &ast) {
        assert(ast.nodes.size() >= 1);
        assert(ast.nodes[0]->name == "Factor" || ast.nodes[0]->name == "LOADROOT");
        size_t nNodes = ast.nodes.size();

        processNode(*ast.nodes[0].get());

        bool needPrepCall = false;
        for (size_t i=1; i<nNodes; ++i) {
            const auto &node = *ast.nodes[i].get();
            bool nextIsCall = (i<nNodes-1) && ast.nodes[i+1]->name == "FunctionCall";

            if (node.name == "SlotGet") {
                assert(node.nodes.size() == 1);

                processNode(*node.nodes[0].get());

                SQInteger flags = 0;

                if (nextIsCall) {
                    assert(!needPrepCall);
                    needPrepCall = true;
                } else {
                    SQInteger p2 = _fs->PopTarget(); //src in OP_GET
                    SQInteger p1 = _fs->PopTarget(); //key in OP_GET
                    _fs->AddInstruction(_OP_GET, _fs->PushTarget(), p1, p2, flags);
                }
            }
            else if (node.name == "SlotNamedGet" || node.name == "RootSlotGet") {
                assert(node.nodes.size() == 1);

                SQInteger flags = 0;
                SQObjectPtr constant = makeString(node.nodes[0]->token);
                if (CanBeDefaultDelegate(constant))
                    flags |= OP_GET_FLAG_ALLOW_DEF_DELEGATE;

                _fs->AddInstruction(_OP_LOAD, _fs->PushTarget(), _fs->GetConstant(constant));

                if (nextIsCall) {
                    assert(!needPrepCall);
                    needPrepCall = true;
                } else {
                    SQInteger p2 = _fs->PopTarget(); //src in OP_GET
                    SQInteger p1 = _fs->PopTarget(); //key in OP_GET
                    _fs->AddInstruction(_OP_GET, _fs->PushTarget(), p1, p2, flags);
                }
            }
            else if (node.name == "FunctionCall") {
                assert(node.nodes.size() == 1);

                if (needPrepCall) {
                    // member/slot function
                    SQInteger key     = _fs->PopTarget();  /* location of the key */
                    SQInteger table   = _fs->PopTarget();  /* location of the object */
                    SQInteger closure = _fs->PushTarget(); /* location for the closure */
                    SQInteger ttarget = _fs->PushTarget(); /* location for 'this' pointer */
                    _fs->AddInstruction(_OP_PREPCALL, closure, key, table, ttarget);
                    needPrepCall = false;
                }
                else {
                    // local function
                    _fs->AddInstruction(_OP_MOVE, _fs->PushTarget(), 0);
                }

                {
                    Ast *args = node.nodes[0].get();
                    //printf("%d arg nodes\n", int(args->nodes.size()));

                    SQInteger nargs = 1;//this
                    for (size_t i=0; i<args->nodes.size(); ++i) {
                        processNode(*args->nodes[i].get());
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
            }
        }
    }


    void VarModifyStmt(const Ast &ast) {
        assert(ast.nodes.size() == 3);

        SQObjectPtr id = makeString(ast.nodes[0]->token);
        SQInteger pos;
        bool isOuter = false;
        if ((pos = _fs->GetLocalVariable(id)) != -1) {
            _fs->PushTarget(pos);
        } else if ((pos = _fs->GetOuterVariable(id)) != -1) {
            _fs->AddInstruction(_OP_GETOUTER, _fs->PushTarget(), pos);
            isOuter = true;
        } else
            Error(_SC("Unknown local variable '%s'"), _stringval(id));

        if (ast.nodes[1]->token != "=")
            Error(_SC("Only '=' is supported for now"));

        processNode(*ast.nodes[2].get());

        if (!isOuter) {
            SQInteger src = _fs->PopTarget();
            SQInteger dst = pos; //_fs->TopTarget();
            _fs->AddInstruction(_OP_MOVE, dst, src);
        } else {
            SQInteger src = _fs->PopTarget();
            SQInteger dst = _fs->PushTarget();
            _fs->AddInstruction(_OP_SETOUTER, dst, pos, src);
        }
    }


    void SlotModifyStmt(const Ast &ast) {
        assert(ast.nodes.size() == 4);
        assert(ast.nodes[2]->token == "=" || ast.nodes[2]->token == "<-");

        processChildren(ast);

        SQInteger val = _fs->PopTarget();
        SQInteger key = _fs->PopTarget();
        SQInteger src = _fs->PopTarget();
        SQOpcode  op = ast.nodes[2]->token == "=" ? _OP_SET : _OP_NEWSLOT;
        _fs->AddInstruction(op, _fs->PushTarget(), src, key, val);
    }


    void ArrayInit(const Ast &ast) {
        assert(ast.nodes.size() == 1);
        assert(ast.nodes[0]->name == "ArgValues");
        const auto &args = ast.nodes[0];

        SQInteger len = args->nodes.size();
        _fs->AddInstruction(_OP_NEWOBJ, _fs->PushTarget(), len, 0, NOT_ARRAY);
        for (SQInteger key=0; key<len; ++key) {
            processNode(*args->nodes[key].get());

            SQInteger val = _fs->PopTarget();
            SQInteger array = _fs->TopTarget();
            _fs->AddInstruction(_OP_APPENDARRAY, array, val, AAT_STACK);
        }
    }


    void TableInit(const Ast &ast) {
        SQInteger len = ast.nodes.size();
        SQInteger tblPos = _fs->PushTarget();
        _fs->AddInstruction(_OP_NEWOBJ, tblPos, len, 0, NOT_TABLE);
        for (const auto &item : ast.nodes) {
            assert(item->name == "TableInitItem");
            if (item->nodes[0]->name == "IDENTIFIER") {
                SQObjectPtr key = makeString(item->nodes[0]->token);
                _fs->AddInstruction(_OP_LOAD, _fs->PushTarget(), _fs->GetConstant(key));

                if (item->nodes.size()==1) {
                    SQInteger pos;
                    if ((pos = _fs->GetLocalVariable(key)) != -1)
                        _fs->PushTarget(pos);
                    else if ((pos = _fs->GetOuterVariable(key)) != -1)
                        _fs->AddInstruction(_OP_GETOUTER, _fs->PushTarget(), pos);
                    else
                        Error(_SC("Local variable '%s' not found"), _stringval(key));
                }
            }
            processNode(*item.get());

            SQInteger val = _fs->PopTarget();
            SQInteger key = _fs->PopTarget();
            //unsigned char flags = isstatic ? NEW_SLOT_STATIC_FLAG : 0;
            SQInteger table = tblPos ; // _fs->TopTarget(); //<<BECAUSE OF THIS NO COMMON EMIT FUNC IS POSSIBLE
            _fs->AddInstruction(_OP_NEWSLOT, 0xFF, table, key, val);
        }
    }


    void IfStmt(const Ast &ast) {
        assert(ast.nodes.size() == 2 || ast.nodes.size() == 3);
        assert(ast.nodes[0]->name == "Expression");

        processNode(*ast.nodes[0].get());

        _fs->AddInstruction(_OP_JZ, _fs->PopTarget());
        SQInteger jnepos = _fs->GetCurrentPos();
        processNode(*ast.nodes[1].get());
        SQInteger endifblock = _fs->GetCurrentPos();

        bool hasElse = ast.nodes.size() == 3;
        if (hasElse) {
            _fs->AddInstruction(_OP_JMP);
            SQInteger jmppos = _fs->GetCurrentPos();
            processNode(*ast.nodes[2].get());
            _fs->SetInstructionParam(jmppos, 1, _fs->GetCurrentPos() - jmppos);
        }
        _fs->SetInstructionParam(jnepos, 1, endifblock - jnepos + (hasElse?1:0));
    }


    void ForStmt(const Ast &ast) {
        assert(ast.nodes.size()==3 || ast.nodes.size()==4);
        const auto &forInitNode = *ast.nodes[0].get();
        const auto &forCondNode = *ast.nodes[1].get();
        const auto &forActionNode = *ast.nodes[2].get();

        BEGIN_SCOPE();

        processNode(forInitNode);

        _fs->SnoozeOpt();
        SQInteger jmppos = _fs->GetCurrentPos();
        SQInteger jzpos = -1;

        if (!forCondNode.nodes.empty()) {
            processNode(forCondNode);
            _fs->AddInstruction(_OP_JZ, _fs->PopTarget());
            jzpos = _fs->GetCurrentPos();
        }

        _fs->SnoozeOpt();
        SQInteger expstart = _fs->GetCurrentPos() + 1;
        for (const auto &node : forActionNode.nodes) {
            assert(node->name == "Expression");
            processNode(*node.get());
            _fs->PopTarget();
        }


        _fs->SnoozeOpt();
        SQInteger expend = _fs->GetCurrentPos();
        SQInteger expsize = (expend - expstart) + 1;
        SQInstructionVec exp(_fs->_sharedstate->_alloc_ctx);
        if (expsize > 0) {
            for (SQInteger i = 0; i < expsize; i++)
                exp.push_back(_fs->GetInstruction(expstart + i));
            _fs->PopInstructions(expsize);
        }

        BEGIN_BREAKBLE_BLOCK()

        if (ast.nodes.size() == 4) {
            processNode(*ast.nodes[3].get());
        }

        SQInteger continuetrg = _fs->GetCurrentPos();
        if (expsize > 0) {
            for (SQInteger i = 0; i < expsize; i++)
                _fs->AddInstruction(exp[i]);
        }
        _fs->AddInstruction(_OP_JMP, 0, jmppos - _fs->GetCurrentPos() - 1, 0);
        if (jzpos>  0)
            _fs->SetInstructionParam(jzpos, 1, _fs->GetCurrentPos() - jzpos);

        END_BREAKBLE_BLOCK(continuetrg);

        END_SCOPE();
    }


    void ForeachStmt(const Ast &ast) {
        //     ForeachStmt <- 'foreach' '(' IDENTIFIER (',' IDENTIFIER) 'in' Expression ')' Statement
        assert(ast.nodes.size() == 3 || ast.nodes.size() == 4);

        SQObject idxname, valname;
        valname = makeString(ast.nodes[0]->token);
        CheckDuplicateLocalIdentifier(valname, _SC("Iterator"), false);

        int containerIdx = 1, actionStmtIdx = 2;
        if (ast.nodes.size() == 4) {
            idxname = valname;
            valname = makeString(ast.nodes[1]->token);
            CheckDuplicateLocalIdentifier(valname, _SC("Iterator"), false);
            containerIdx = 2;
            actionStmtIdx = 3;
        }
        else {
            idxname = _fs->CreateString(_SC("@INDEX@"));
        }

        //save the stack size
        BEGIN_SCOPE();
        //put the table in the stack(evaluate the table expression)
        processNode(*ast.nodes[containerIdx].get());

        SQInteger container = _fs->TopTarget();
        //push the index local var
        SQInteger indexpos = _fs->PushLocalVariable(idxname);
        _fs->AddInstruction(_OP_LOADNULLS, indexpos,1);
        //push the value local var
        SQInteger valuepos = _fs->PushLocalVariable(valname);
        _fs->AddInstruction(_OP_LOADNULLS, valuepos,1);
        //push reference index
        SQInteger itrpos = _fs->PushLocalVariable(_fs->CreateString(_SC("@ITERATOR@"))); //use invalid id to make it inaccessible
        _fs->AddInstruction(_OP_LOADNULLS, itrpos,1);
        SQInteger jmppos = _fs->GetCurrentPos();
        _fs->AddInstruction(_OP_FOREACH, container, 0, indexpos);
        SQInteger foreachpos = _fs->GetCurrentPos();
        _fs->AddInstruction(_OP_POSTFOREACH, container, 0, indexpos);
        //generate the statement code
        BEGIN_BREAKBLE_BLOCK()

        processNode(*ast.nodes[actionStmtIdx].get());

        _fs->AddInstruction(_OP_JMP, 0, jmppos - _fs->GetCurrentPos() - 1);
        _fs->SetInstructionParam(foreachpos, 1, _fs->GetCurrentPos() - foreachpos);
        _fs->SetInstructionParam(foreachpos + 1, 1, _fs->GetCurrentPos() - foreachpos);
        END_BREAKBLE_BLOCK(foreachpos - 1);
        //restore the local variable stack(remove index,val and ref idx)
        _fs->PopTarget();
        END_SCOPE();
    }


    void BreakStmt(const Ast &ast) {
        if(_fs->_breaktargets.size() <= 0)
            Error(_SC("'break' has to be in a loop block"));
        if(_fs->_breaktargets.top() > 0){
            _fs->AddInstruction(_OP_POPTRAP, _fs->_breaktargets.top(), 0);
        }
        RESOLVE_OUTERS();
        _fs->AddInstruction(_OP_JMP, 0, -1234);
        _fs->_unresolvedbreaks.push_back(_fs->GetCurrentPos());
    }


    void ContinueStmt(const Ast &ast) {
        if(_fs->_continuetargets.size() <= 0)
            Error(_SC("'continue' has to be in a loop block"));
        if(_fs->_continuetargets.top() > 0) {
            _fs->AddInstruction(_OP_POPTRAP, _fs->_continuetargets.top(), 0);
        }
        RESOLVE_OUTERS();
        _fs->AddInstruction(_OP_JMP, 0, -1234);
        _fs->_unresolvedcontinues.push_back(_fs->GetCurrentPos());
    }

    void ThrowStmt(const Ast &ast) {
        processChildren(ast);
        _fs->AddInstruction(_OP_THROW, _fs->PopTarget());
    }

    void TryCatchStmt(const Ast &ast) {
        _fs->AddInstruction(_OP_PUSHTRAP,0,0);
        _fs->_traps++;
        if(_fs->_breaktargets.size()) _fs->_breaktargets.top()++;
        if(_fs->_continuetargets.size()) _fs->_continuetargets.top()++;
        SQInteger trappos = _fs->GetCurrentPos();

        {
            BEGIN_SCOPE();
            processNode(ast.nodes[0]);
            END_SCOPE();
        }

        _fs->_traps--;
        _fs->AddInstruction(_OP_POPTRAP, 1, 0);
        if(_fs->_breaktargets.size()) _fs->_breaktargets.top()--;
        if(_fs->_continuetargets.size()) _fs->_continuetargets.top()--;
        _fs->AddInstruction(_OP_JMP, 0, 0);
        SQInteger jmppos = _fs->GetCurrentPos();
        _fs->SetInstructionParam(trappos, 1, (_fs->GetCurrentPos() - trappos));

        SQObject exid = makeString(ast.nodes[1]->token);

        {
            BEGIN_SCOPE();
            SQInteger ex_target = _fs->PushLocalVariable(exid);
            _fs->SetInstructionParam(trappos, 0, ex_target);
            processNode(ast.nodes[2]);
            _fs->SetInstructionParams(jmppos, 0, (_fs->GetCurrentPos() - jmppos), 0);
            END_SCOPE();
        }
    }

    template <typename T> void processNode(const std::shared_ptr<T> &node)
    {
        processNode(*node.get());
    }

    void processNode(const Ast &ast)
    {
        //printf("%*cname = %s | token = %s\n", depth*2, ' ',
        //    ast.name.c_str(), ast.is_token ? std::string(ast.token).c_str() : "N/A");
        _src_line = int(ast.line);
        _src_col = int(ast.column);

        if (ast.name == "Statement")
            Statement(ast);
        else if (ast.name == "INTEGER" || ast.name == "FLOAT" || ast.name == "BOOLEAN" || ast.name == "NULL" || ast.name == "STRING_LITERAL")
            FactorPush(ast);
        else if (ast.name == "LOADROOT") {
            _fs->AddInstruction(_OP_LOADROOT, _fs->PushTarget());
        }
        else if (ast.name == "ReturnStatement")
            ReturnStatement(ast);
        else if (ast.name == "BlockStmt")
            BlockStatement(ast);
        else if (ast.name == "BinaryOpExpr")
            BinaryOpExpr(ast);
        else if (ast.name == "LocalVarDeclStmt")
            LocalVarDeclStmt(ast);
        else if (ast.name == "Factor")
            Factor(ast);
        else if (ast.name == "LocalFuncDeclStmt")
            LocalFuncDeclStmt(ast);
        else if (ast.name == "PrefixedExpr")
            PrefixedExpr(ast);
        else if (ast.name == "SlotGet" || ast.name == "SlotNamedGet" || ast.name == "FunctionCall")
            Error(_SC("'%s' should be processed from PrefixedExpr node"), ast.name.c_str());
        else if (ast.name == "VarModifyStmt")
            VarModifyStmt(ast);
        else if (ast.name == "SlotModifyStmt")
            SlotModifyStmt(ast);
        else if (ast.name == "ArrayInit")
            ArrayInit(ast);
        else if (ast.name == "TableInit")
            TableInit(ast);
        else if (ast.name == "IfStmt")
            IfStmt(ast);
        else if (ast.name == "ForStmt")
            ForStmt(ast);
        else if (ast.name == "ForeachStmt")
            ForeachStmt(ast);
        else if (ast.name == "BreakStmt")
            BreakStmt(ast);
        else if (ast.name == "ContinueStmt")
            ContinueStmt(ast);
        else if (ast.name == "ThrowStmt")
            ThrowStmt(ast);
        else if (ast.name == "TryCatchStmt")
            TryCatchStmt(ast);
        else
            processChildren(ast);
    }

    void processAst(const Ast &ast, SQObjectPtr &o)
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

        processNode(ast);

        _fs->SetStackSize(stacksize);
        _fs->AddLineInfos(ast.line, _lineinfo, true); //== TODO: check if line is begin or end
        _fs->AddInstruction(_OP_RETURN, 0xFF);
        _fs->SetStackSize(0);
        o =_fs->BuildProto();

#ifdef _DEBUG_DUMP
        _fs->Dump(_funcproto(o));
#endif

        assert(_scopedconsts.size()==1);
    }

    bool Compile(const SQChar *src, SQInteger src_len, SQObjectPtr &o)
    {
        printf("===\n%.*s\n===\n", int(src_len), src);

        parser parser(grammar);

        if(setjmp(_errorjmp) == 0) {

            parser.log = [&](size_t line, size_t col, const std::string& msg) {
                Error(_SC("Parse error at %d:%d: %s"), int(line), int(col), msg.c_str());
            };

            parser.enable_ast();

            auto expr = src;
            std::shared_ptr<Ast> ast;
            if (!parser.parse_n(expr, size_t(src_len), ast)) {
                // std::cout << "syntax error..." << std::endl;
                // return false;
            }

            //std::shared_ptr<Ast> astOpt = AstOptimizer(true).optimize(ast);
            std::shared_ptr<Ast> astOpt = ast;
            std::cout << ast_to_s(astOpt);
            //std::cout << expr << " = " << eval(*ast) << std::endl;

            processAst(*astOpt.get(), o);
        } else {
            if(_raiseerror && _ss(_vm)->_compilererrorhandler) {
                _ss(_vm)->_compilererrorhandler(_vm, _compilererror, sq_type(_sourcename) == OT_STRING?_stringval(_sourcename):_SC("unknown"),
                    _src_line, _src_col);
            }
            _vm->_lasterror = SQString::Create(_ss(_vm), _compilererror, -1);
            return false;
        }
        return true;
    }

private:
    SQVM *_vm;
    SQFuncState *_fs;
    SQObjectPtr _sourcename;
    const SQChar * _sourcename_ptr;
    bool _lineinfo;
    bool _raiseerror;
    SQScope _scope;
    SQChar _compilererror[MAX_COMPILER_ERROR_LEN];
    SQObjectPtrVec _scopedconsts;
    jmp_buf _errorjmp;
    int _src_line = -1, _src_col = -1;
};


bool CompilePeg(SQVM *vm, const SQChar *src, SQInteger src_len, const HSQOBJECT *bindings, const SQChar *sourcename,
                SQObjectPtr &out, bool raiseerror, bool lineinfo)
{
    SQPegCompiler p(vm, sourcename, raiseerror, lineinfo);
    return p.Compile(src, src_len, out);
}
