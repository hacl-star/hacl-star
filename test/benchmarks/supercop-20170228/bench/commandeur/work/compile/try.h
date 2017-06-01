#include <stdlib.h>
#include <string.h>

/* provided by try.c: */
extern const char *primitiveimplementation;
extern void preallocate(void);
extern void allocate(void);;
extern void test(void);
extern void predoit(void);
extern void doit(void);

/* provided by try-anything.c: */
extern void fail(const char *);
extern unsigned char *alignedcalloc(unsigned long long);
extern void checksum(const unsigned char *,unsigned long long);
extern void double_canary(unsigned char *,unsigned char *,unsigned long long);
extern void input_prepare(unsigned char *,unsigned char *,unsigned long long);
extern void output_prepare(unsigned char *,unsigned char *,unsigned long long);
extern void input_compare(const unsigned char *,const unsigned char *,unsigned long long,const char *);
extern void output_compare(const unsigned char *,const unsigned char *,unsigned long long,const char *);
extern unsigned long long myrandom(void);
extern void randombytes(unsigned char *,unsigned long long);
