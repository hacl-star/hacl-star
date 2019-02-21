#include "Lib_RandomBuffer.h"
#include <stdio.h>

#if (defined(_WIN32) || defined(_WIN64))

#include <inttypes.h>
#include <stdbool.h>
#include <malloc.h>
#include <windows.h>

bool read_random_bytes(uint32_t len, uint8_t *buf) {
  HCRYPTPROV ctxt;
  if (!(CryptAcquireContext(&ctxt, NULL, NULL, PROV_RSA_FULL,
                            CRYPT_VERIFYCONTEXT))) {
    DWORD error = GetLastError();
    printf("Cannot acquire crypto context: 0x%lx\n", error);
    return false;
  }
  bool pass = true;
  if (!(CryptGenRandom(ctxt, (uint64_t)len, buf))) {
    printf("Cannot read random bytes\n");
    pass = false;
  }
  CryptReleaseContext(ctxt, 0);
  return pass;
}

void *hacl_aligned_malloc(size_t alignment, size_t size) {
  void *res = _aligned_malloc(size, alignment);
  if (res == NULL) {
    printf("Cannot allocate %" PRIu64 " bytes aligned to %" PRIu64 "\n",
           (uint64_t)size, (uint64_t)alignment);
  }
  return res;
}

void hacl_aligned_free(void *ptr) { _aligned_free(ptr); }

#else

/* assume POSIX here */
#include <fcntl.h>
#include <stdlib.h>
#include <sys/stat.h>
#include <sys/types.h>
#include <unistd.h>

bool read_random_bytes(uint32_t len, uint8_t *buf) {
  int fd = open("/dev/urandom", O_RDONLY);
  if (fd == -1) {
    printf("Cannot open /dev/urandom\n");
    return false;
  }
  bool pass = true;
  uint64_t res = read(fd, buf, (uint64_t)len);
  if (res != (uint64_t)len) {
    printf("Error on reading, expected %" PRIu32 " bytes, got %" PRIu64
           " bytes\n",
           len, res);
    pass = false;
  }
  close(fd);
  return pass;
}

void *hacl_aligned_malloc(size_t alignment, size_t size) {
  void *res = NULL;
  if (posix_memalign(&res, alignment, size)) {
    printf("Cannot allocate %" PRIu64 " bytes aligned to %" PRIu64 "\n",
           (uint64_t)size, (uint64_t)alignment);
    return NULL;
  }
  return res;
}

void hacl_aligned_free(void *ptr) { free(ptr); }

#endif

void randombytes(uint8_t *x, uint32_t len) {
  if (!(read_random_bytes(len, x)))
    exit(1);
}
