#ifndef __HACL_TEST_UTILS
#define __HACL_TEST_UTILS

#include <inttypes.h>
#include <stdbool.h>
#include <stddef.h>

#if ((defined(_WIN32) || defined(_WIN64)) && (! (defined(__CYGWIN__))))
#define HACL_TEST_IS_WINDOWS 1
#else
#define HACL_TEST_IS_WINDOWS 0
#endif

bool read_random_bytes(uint64_t len, uint8_t * buf);

void * hacl_aligned_malloc(size_t alignment, size_t size);
void hacl_aligned_free(void * ptr);

#endif // __HACL_TEST_UTILS
