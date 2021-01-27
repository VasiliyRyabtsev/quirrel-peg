/*  see copyright notice in squirrel.h */

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdarg.h>

//#if !defined(__cplusplus) || __cplusplus < 201703L
//#error "Requires complete C++17 support"
//#endif

#if defined(_MSC_VER) && defined(_DEBUG)
#include <crtdbg.h>
#include <conio.h>
#endif
#include <squirrel.h>
#include <sqstdblob.h>
#include <sqstdsystem.h>
#include <sqstdio.h>
#include <sqstdmath.h>
#include <sqstdstring.h>
#include <sqstdaux.h>
#include <sqmodules.h>

#ifdef SQUNICODE
#define scfprintf fwprintf
#define scvprintf vfwprintf
#else
#define scfprintf fprintf
#define scvprintf vfprintf
#endif


static SqModules *module_mgr = nullptr;


void PrintVersionInfos();

#if defined(_MSC_VER) && defined(_DEBUG)
int MemAllocHook( int allocType, void *userData, size_t size, int blockType,
   long requestNumber, const unsigned char *filename, int lineNumber)
{
    //if(requestNumber==769)_asm int 3;
    return 1;
}
#endif


SQInteger quit(HSQUIRRELVM v)
{
    int *done;
    sq_getuserpointer(v,-1,(SQUserPointer*)&done);
    *done=1;
    return 0;
}

void printfunc(HSQUIRRELVM SQ_UNUSED_ARG(v),const SQChar *s,...)
{
    va_list vl;
    va_start(vl, s);
    scvprintf(stdout, s, vl);
    va_end(vl);
}

void errorfunc(HSQUIRRELVM SQ_UNUSED_ARG(v),const SQChar *s,...)
{
    va_list vl;
    va_start(vl, s);
    scvprintf(stderr, s, vl);
    va_end(vl);
}

void PrintVersionInfos()
{
    scfprintf(stdout,_SC("%s %s (%d bits)\n"),SQUIRREL_VERSION,SQUIRREL_COPYRIGHT,((int)(sizeof(SQInteger)*8)));
}

void PrintUsage()
{
    scfprintf(stderr,_SC("usage: sq <options> <scriptpath [args]>.\n")
        _SC("Available options are:\n")
        _SC("   -m              enable module support and run file as module\n")
        _SC("   -c              compiles the file to bytecode(default output 'out.cnut')\n")
        _SC("   -o              specifies output file for the -c option\n")
        _SC("   -c              compiles only\n")
        _SC("   -d              generates debug infos\n")
        _SC("   -v              displays version infos\n")
        _SC("   -h              prints help\n"));
}

#define _INTERACTIVE 0
#define _DONE 2
#define _ERROR 3
//<<FIXME>> this func is a mess
int getargs(HSQUIRRELVM v,int argc, char* argv[],SQInteger *retval)
{
    int i;
    int compiles_only = 0;
	int run_as_module = 0;
    SQBool use_peg = SQFalse;
#ifdef SQUNICODE
    static SQChar temp[500];
#endif
    char * output = NULL;
    *retval = 0;
    if(argc>1)
    {
        int arg=1,exitloop=0;

        while(arg < argc && !exitloop)
        {

            if(argv[arg][0]=='-')
            {
                switch(argv[arg][1])
                {
                case 'd': //DEBUG(debug infos)
                    sq_enabledebuginfo(v,1);
                    sq_lineinfo_in_expressions(v, 1);
                    break;
                case 'c':
                    compiles_only = 1;
                    break;
                case 'm':
                    run_as_module = 1;
                    break;
                case 'p':
                    use_peg = SQTrue;
                    break;
                case 'o':
                    if(arg < argc) {
                        arg++;
                        output = argv[arg];
                    }
                    break;
                case 'v':
                    PrintVersionInfos();
                    return _DONE;

                case 'h':
                    PrintVersionInfos();
                    PrintUsage();
                    return _DONE;
                default:
                    PrintVersionInfos();
                    scprintf(_SC("unknown prameter '-%c'\n"),argv[arg][1]);
                    PrintUsage();
                    *retval = -1;
                    return _ERROR;
                }
            }else break;
            arg++;
        }

        // src file

        if(arg<argc) {
            const SQChar *filename=NULL;
#ifdef SQUNICODE
            mbstowcs(temp,argv[arg],strlen(argv[arg]));
            filename=temp;
#else
            filename=argv[arg];
#endif

            arg++;

            //sq_pushstring(v,_SC("ARGS"),-1);
            //sq_newarray(v,0);

            //sq_createslot(v,-3);
            //sq_pop(v,1);
            if(compiles_only) {
                if(SQ_SUCCEEDED(sqstd_loadfile(v,filename,SQTrue,false))){
                    const SQChar *outfile = _SC("out.cnut");
                    if(output) {
#ifdef SQUNICODE
                        int len = (int)(strlen(output)+1);
                        mbstowcs(sq_getscratchpad(v,len*sizeof(SQChar)),output,len);
                        outfile = sq_getscratchpad(v,-1);
#else
                        outfile = output;
#endif
                    }
                    if(SQ_SUCCEEDED(sqstd_writeclosuretofile(v,outfile)))
                        return _DONE;
                }
            }
            else if (run_as_module) {
                SqModules::SqObjPtr exports;
                std::string errMsg;
                if (!module_mgr->requireModule(filename, true, "__main__", exports, errMsg)) {
                    scprintf(_SC("Error [%s]\n"), errMsg.c_str());
                    return _ERROR;
                }
                return _DONE;
            }
            else {
                //if(SQ_SUCCEEDED(sqstd_dofile(v,filename,SQFalse,SQTrue))) {
                    //return _DONE;
                //}
                if(SQ_SUCCEEDED(sqstd_loadfile(v,filename,SQTrue,use_peg))) {
                    int callargs = 1;
                    sq_pushroottable(v);
                    for(i=arg;i<argc;i++)
                    {
                        const SQChar *a;
#ifdef SQUNICODE
                        int alen=(int)strlen(argv[i]);
                        a=sq_getscratchpad(v,(int)(alen*sizeof(SQChar)));
                        mbstowcs(sq_getscratchpad(v,-1),argv[i],alen);
                        sq_getscratchpad(v,-1)[alen] = _SC('\0');
#else
                        a=argv[i];
#endif
                        sq_pushstring(v,a,-1);
                        callargs++;
                        //sq_arrayappend(v,-2);
                    }
                    if(SQ_SUCCEEDED(sq_call(v,callargs,SQTrue,SQTrue))) {
                        SQObjectType type = sq_gettype(v,-1);
                        if(type == OT_INTEGER) {
                            *retval = type;
                            sq_getinteger(v,-1,retval);
                        }
                        return _DONE;
                    }
                    else{
                        return _ERROR;
                    }

                }
            }
            //if this point is reached an error occurred
            {
                const SQChar *err;
                sq_getlasterror(v);
                if(SQ_SUCCEEDED(sq_getstring(v,-1,&err))) {
                    scprintf(_SC("Error [%s]\n"),err);
                    *retval = -2;
                    return _ERROR;
                }
            }

        }
    }

    return _INTERACTIVE;
}

void Interactive(HSQUIRRELVM v)
{

#define MAXINPUT 1024
    SQChar buffer[MAXINPUT];
    SQInteger blocks =0;
    SQInteger string=0;
    SQInteger retval=0;
    SQInteger done=0;
    PrintVersionInfos();

    sq_pushroottable(v);
    sq_pushstring(v,_SC("quit"),-1);
    sq_pushuserpointer(v,&done);
    sq_newclosure(v,quit,1);
    sq_setparamscheck(v,1,NULL);
    sq_newslot(v,-3,SQFalse);
    sq_pop(v,1);

    while (!done)
    {
        SQInteger i = 0;
        scprintf(_SC("\nsq>"));
        for(;;) {
            int c;
            if(done)return;
            c = getchar();
            if (c == _SC('\n')) {
                if (i>0 && buffer[i-1] == _SC('\\'))
                {
                    buffer[i-1] = _SC('\n');
                }
                else if(blocks==0)break;
                buffer[i++] = _SC('\n');
            }
            else if (c==_SC('}')) {blocks--; buffer[i++] = (SQChar)c;}
            else if(c==_SC('{') && !string){
                    blocks++;
                    buffer[i++] = (SQChar)c;
            }
            else if(c==_SC('"') || c==_SC('\'')){
                    string=!string;
                    buffer[i++] = (SQChar)c;
            }
            else if (i >= MAXINPUT-1) {
                scfprintf(stderr, _SC("sq : input line too long\n"));
                break;
            }
            else{
                buffer[i++] = (SQChar)c;
            }
        }
        buffer[i] = _SC('\0');

        if(buffer[0]==_SC('=')){
            scsprintf(sq_getscratchpad(v,MAXINPUT),(size_t)MAXINPUT,_SC("return (%s)"),&buffer[1]);
            memcpy(buffer,sq_getscratchpad(v,-1),(scstrlen(sq_getscratchpad(v,-1))+1)*sizeof(SQChar));
            retval=1;
        }
        i=scstrlen(buffer);
        if(i>0){
            SQInteger oldtop=sq_gettop(v);
            if(SQ_SUCCEEDED(sq_compilebuffer(v,buffer,i,_SC("interactive console"),SQTrue))){
            //if(SQ_SUCCEEDED(sq_compilepeg(v,buffer,i,_SC("interactive console"),SQTrue))){
                sq_pushroottable(v);
                if(SQ_SUCCEEDED(sq_call(v,1,retval,SQTrue)) &&  retval){
                    scprintf(_SC("\n"));
                    sq_pushroottable(v);
                    sq_pushstring(v,_SC("print"),-1);
                    sq_get(v,-2);
                    sq_pushroottable(v);
                    sq_push(v,-4);
                    sq_call(v,2,SQFalse,SQTrue);
                    retval=0;
                    scprintf(_SC("\n"));
                }
            }

            sq_settop(v,oldtop);
        }
    }
}


void test_peg(HSQUIRRELVM v)
{
    const char* code1 = R"(
        local a = 444+1
        return a+a-2*2
    )";
    const char* code2 = R"(
        local z = 2000
        local function a(x, y) {
            return x+y+1000
        }
        return a(222, 333)+z
    )";
    const char* code2a = R"(
        local z = 2000
        local function a(x, y) {
            return x+y+1000+z
        }
        return a(222, 333)
    )";
    const char* code2b = R"(
        local z = 2000
        local function a(x, y) {
            z=x+y
        }
        a(222,333)
        return z
    )";
    const char* code3 = R"(
        local function a(x, y) {
            return x+y+1000
        }
        return a
    )";
    const char* code4 = "return 1000.1 + 234. + .0234 + 50000";
    const char* code5 = "return -1.23e-5";
    const char* code6 = "return \"Ab\\nc\"\"deF\"";
    const char* code7 = R"(return "Abc""deF" + 111)";
    const char* code8 = R"(
        local a = [1,[2,"Z"],3,null,true]
        return a[1][1]
    )";
    const char* code9 = R"(
        local a = 123
        a = 555
        return a
    )";
    const char* code10 = R"(
        local a = [123, 456]
        a[0] = "Zzz"
        return a[0]
    )";
    const char* code11 = R"(
        local w = "aqwe"
        local t = {x=123, y=-567+111, w, ["z"]=111}
        return t["w"]
    )";
    const char *code12 = R"(
        ::print(123)
        ::print("\n--------\n")
        ::print(::max)
    )";
    const char *code = R"(
        if (true)
            ::print("True\n")
        else
            ::print("False\n")

        if (false) {
            ::print("False\n")
            local z = 111
        } else {
            local x = 123
            ::print("True\n")
        }
    )";
    size_t len=scstrlen(code);
    SQInteger oldtop=sq_gettop(v);
    //if(SQ_SUCCEEDED(sq_compilebuffer(v,buffer,i,_SC("interactive console"),SQTrue))){
    if(SQ_SUCCEEDED(sq_compilepeg(v,code,len,_SC("test code"),SQTrue))){
        sq_pushroottable(v);
        SQBool retval = SQTrue;
        bool succeeded = SQ_SUCCEEDED(sq_call(v,1,retval,SQTrue));
        printf("closure call succeeded = %d, retval = %d\n", succeeded, int(retval));
        if (succeeded && retval) {
            scprintf(_SC("\n"));
            sq_pushroottable(v);
            sq_pushstring(v,_SC("print"),-1);
            sq_get(v,-2);
            sq_pushroottable(v);
            sq_push(v,-4);
            sq_call(v,2,SQFalse,SQTrue);
            retval=0;
            scprintf(_SC("\n"));
        }
    }

    sq_settop(v,oldtop);
}

int main(int argc, char* argv[])
{
    HSQUIRRELVM v;
    SQInteger retval = 0;
#if defined(_MSC_VER) && defined(_DEBUG)
    _CrtSetAllocHook(MemAllocHook);
#endif

    v=sq_open(1024);
    sq_setprintfunc(v,printfunc,errorfunc);

    sq_pushroottable(v);

    sqstd_register_bloblib(v);
    sqstd_register_iolib(v);
    sqstd_register_systemlib(v);
    sqstd_register_mathlib(v);
    sqstd_register_stringlib(v);

    //aux library
    //sets error handlers
    sqstd_seterrorhandlers(v);

    module_mgr = new SqModules(v);
    module_mgr->registerBaseLibs();
    module_mgr->registerIoLib();
    module_mgr->registerSystemLib();

    sqstd_register_command_line_args(v, argc, argv);

#if 0
    test_peg(v);
#else
    //gets arguments
    switch(getargs(v,argc,argv,&retval))
    {
    case _INTERACTIVE:
        Interactive(v);
        break;
    case _DONE:
    case _ERROR:
    default:
        break;
    }
#endif

    delete module_mgr;
    sq_close(v);

#if defined(_MSC_VER) && defined(_DEBUG)
    _getch();
    _CrtMemDumpAllObjectsSince( NULL );
#endif
    return int(retval);
}

