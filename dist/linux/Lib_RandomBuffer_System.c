#include <Lib_RandomBuffer_System.h>

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
    /* printf("Cannot acquire crypto context: 0x%lx\n", error); */
    return false;
  }
  bool pass = true;
  if (!(CryptGenRandom(ctxt, (uint64_t)len, buf))) {
    /* printf("Cannot read random bytes\n"); */
    pass = false;
  }
  CryptReleaseContext(ctxt, 0);
  return pass;
}

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
    /* printf("Cannot open /dev/urandom\n"); */
    return false;
  }
  bool pass = true;
  uint64_t res = read(fd, buf, (uint64_t)len);
  if (res != (uint64_t)len) {
    /* printf("Error on reading, expected %" PRIu32 " bytes, got %" PRIu64 */
    /*        " bytes\n", */
    /*        len, res); */
    pass = false;
  }
  close(fd);
  return pass;
}

#endif

bool Lib_RandomBuffer_System_randombytes(uint8_t *x, uint32_t len) {
  return read_random_bytes(len, x);
}
