#include "hacl_test_utils.h"
#include <stdio.h>

#if HACL_TEST_IS_WINDOWS

/* /dev/urandom does not exist on Windows,
     so we need to use Windows' own random number generator */

#include <windows.h>
#include <wincrypt.h>
#include <malloc.h>

bool read_random_bytes(uint64_t len, uint8_t * buf) {
  HCRYPTPROV ctxt;
  if (! (CryptAcquireContext(&ctxt, NULL, NULL, PROV_RSA_FULL, CRYPT_VERIFYCONTEXT))) {
    DWORD error = GetLastError();
    printf("Cannot acquire crypto context: 0x%lx\n", error);
    return false;
  }
  bool pass = true;
  if (! (CryptGenRandom(ctxt, len, buf))) {
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

#else // ! HACL_TEST_IS_WINDOWS

/* assume POSIX here */
#include <sys/types.h>
#include <sys/stat.h>
#include <fcntl.h>
#include <unistd.h>
#include <stdlib.h>

bool read_random_bytes(uint64_t len, uint8_t * buf) {
  int fd = open("/dev/urandom", O_RDONLY);
  if (fd == -1) {
    printf("Cannot open /dev/urandom\n");
    return false;
  }
  bool pass = true;
  uint64_t res = read(fd, buf, len);
  if (res != len) {
    printf("Error on reading, expected %" PRIu64 " bytes, got %" PRIu64 " bytes\n", len, res);
    pass = false;
  }
  close(fd);
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

#endif // HACL_TEST_IS_WINDOWS
