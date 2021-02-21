/*  see copyright notice in squirrel.h */
#ifndef _SQPEGCOMPILER_H_
#define _SQPEGCOMPILER_H_

struct SQVM;

struct SQPegParser;
struct SQAllocContextT;

SQPegParser* sq_createpegparser(SQAllocContextT *alloc_ctx);
void sq_destroypegparser(SQPegParser*, SQAllocContextT *alloc_ctx);

//typedef void(*CompilerErrorFunc)(void *ud, const SQChar *s);
bool CompilePeg(SQVM *vm, const SQChar *s, SQInteger size, const HSQOBJECT *bindings, const SQChar *sourcename, SQObjectPtr &out, bool raiseerror, bool lineinfo);
#endif //_SQPEGCOMPILER_H_
