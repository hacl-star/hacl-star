#if defined(__has_include)
#if __has_include("config.h")
#include "config.h"
#endif
#endif

#ifdef _WIN32
#include <windows.h>
#endif

#if (defined(__APPLE__) && defined(__MACH__)) || defined(__linux__)
#define __STDC_WANT_LIB_EXT1__ 1
#include <string.h>
#endif

#ifdef __FreeBSD__
#include <strings.h>
#endif

#include <stdlib.h>
#include <stdio.h>
#include <limits.h>
#include <inttypes.h>

#include "Lib_Memzero0.h"
#include "krml/internal/target.h"

/* The F* formalization talks about the number of elements in the array. The C
   implementation wants a number of bytes in the array. KaRaMeL is aware of this
   and inserts a sizeof multiplication. */
void Lib_Memzero0_memzero(void *dst, uint64_t len) {
  /* This is safe: karamel checks at run-time (if needed) that all object sizes
     fit within a size_t, so the size we receive has been checked at
     allocation-time, possibly via KRML_CHECK_SIZE, to fit in a size_t. */
  size_t len_ = (size_t) len;

  #ifdef _WIN32
    SecureZeroMemory(dst, len);
  #elif defined(__APPLE__) && defined(__MACH__)
    memset_s(dst, len_, 0, len_);
  #elif (defined(__linux__) && !defined(LINUX_NO_EXPLICIT_BZERO)) || defined(__FreeBSD__)
    explicit_bzero(dst, len_);
  #elif defined(__NetBSD__)
    explicit_memset(dst, 0, len_);
  #else
    /* Default implementation for platforms with no particular support. */
    #warning "Your platform does not support any safe implementation of memzero -- consider a pull request!"
    volatile unsigned char *volatile dst_ = (volatile unsigned char *volatile) dst;
    size_t i = 0U;
    while (i < len)
      dst_[i++] = 0U;
  #endif
}
