#ifndef __HACL_LIB_RANDOMBUFFER
#define __HACL_LIB_RANDOMBUFFER

#include <inttypes.h>
#include <stdbool.h>
#include <stddef.h>

#if ((defined(_WIN32) || defined(_WIN64)) && (! (defined(__CYGWIN__))))
#define HACL_IS_WINDOWS 1
#else
#define HACL_IS_WINDOWS 0
#endif

bool read_random_bytes(uint32_t len, uint8_t * buf);
void * hacl_aligned_malloc(size_t alignment, size_t size);
void hacl_aligned_free(void * ptr);

void randombytes(uint8_t * x,uint32_t len);

#endif // __HACL_LIB_RANDOMBUFFER

