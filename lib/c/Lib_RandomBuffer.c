#include "Lib_RandomBuffer.h"
#include <stdio.h>


#if HACL_IS_WINDOWS

#include <windows.h>
#include <wincrypt.h>
#include <malloc.h>

bool read_random_bytes(uint32_t len, uint8_t * buf) {
  HCRYPTPROV ctxt;
  if (! (CryptAcquireContext(&ctxt, NULL, NULL, PROV_RSA_FULL, CRYPT_VERIFYCONTEXT))) {
    DWORD error = GetLastError();
    printf("Cannot acquire crypto context: 0x%lx\n", error);
    return false;
  }
  bool pass = true;
  if (! (CryptGenRandom(ctxt, (uint64_t)len, buf))) {
    printf("Cannot read random bytes\n");
    pass = false;
  }
  CryptReleaseContext(ctxt, 0);
  return pass;
}

void * hacl_aligned_malloc(size_t alignment, size_t size) {
  void * res = _aligned_malloc(size, alignment);
  if (res == NULL) {
    printf("Cannot allocate %" PRIu64 " bytes aligned to %" PRIu64 "\n", (uint64_t) size, (uint64_t) alignment);
  }
  return res;
}

void hacl_aligned_free(void * ptr) {
  _aligned_free(ptr);
}

#else // ! HACL_IS_WINDOWS

/* assume POSIX here */
#include <sys/types.h>
#include <sys/stat.h>
#include <fcntl.h>
#include <unistd.h>
#include <stdlib.h>

bool read_random_bytes(uint32_t len, uint8_t * buf) {
  #ifdef SYS_getrandom
    ssize_t res = syscall(SYS_getrandom, buf, (size_t)len, 0);
    if (res == -1) {
      printf("SYS_getrandom error\n");
      return false;
    }
  #else // !defined(SYS_getrandom)
    int fd = open("/dev/urandom", O_RDONLY);
    if (fd == -1) {
      printf("Cannot open /dev/urandom\n");
      return false;
    }
    ssize_t res = read(fd, buf, (size_t)len);
    if (res == -1) {
      printf("Cannot read /dev/urandom\n");
      return false;
    }
    close(fd);
  #endif // defined(SYS_getrandom)
  bool pass = true;
  if ((size_t)res != (size_t)len) {
    printf("Error on reading, expected %" PRIu64 " bytes, got %" PRIu64 " bytes\n", (uint64_t)len, (uint64_t)res);
    pass = false;
  }
  return pass;
}

void * hacl_aligned_malloc(size_t alignment, size_t size) {
  void * res = NULL;
  if (posix_memalign(&res, alignment, size)) {
    printf("Cannot allocate %" PRIu64 " bytes aligned to %" PRIu64 "\n", (uint64_t) size, (uint64_t) alignment);
    return NULL;
  }
  return res;
}

void hacl_aligned_free(void * ptr) {
  free(ptr);
}

#endif // HACL_IS_WINDOWS

bool randombytes(uint8_t * x, uint32_t len) {
  return (read_random_bytes(len, x));
}
