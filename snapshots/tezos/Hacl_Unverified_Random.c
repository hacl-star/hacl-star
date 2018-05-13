/* MIT License
 *
 * Copyright (c) 2016-2017 INRIA and Microsoft Corporation
 *
 * Permission is hereby granted, free of charge, to any person obtaining a copy
 * of this software and associated documentation files (the "Software"), to deal
 * in the Software without restriction, including without limitation the rights
 * to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
 * copies of the Software, and to permit persons to whom the Software is
 * furnished to do so, subject to the following conditions:
 *
 * The above copyright notice and this permission notice shall be included in all
 * copies or substantial portions of the Software.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
 * IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
 * FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
 * AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
 * LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
 * OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
 * SOFTWARE.
 */
#include "Hacl_Unverified_Random.h"
#include <stdio.h>


#if HACL_IS_WINDOWS

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

#else // ! HACL_IS_WINDOWS

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

#endif // HACL_IS_WINDOWS

void randombytes(uint8_t * x,uint64_t len) {
  if (! (read_random_bytes(len, x)))
    exit(1);
}
