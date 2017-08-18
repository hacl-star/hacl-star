#include "hacl_test_utils.h"
#include <stdio.h>

#if ((defined(_WIN32) || defined(_WIN64)) && (! (defined(__CYGWIN__))))

/* /dev/urandom does not exist on Windows,
     so we need to use Windows' own random number generator */

#include <windows.h>
#include <wincrypt.h>

bool read_random_bytes(uint64_t len, uint8_t * buf) {
  HCRYPTPROV ctxt;
  if (! (CryptAcquireContext(&ctxt, NULL, NULL, PROV_RSA_FULL, CRYPT_VERIFYCONTEXT))) {
    DWORD error = GetLastError();
    printf("Cannot acquire crypto context: 0x%x\n", error);
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

#else // ! ((defined(_WIN32) || defined(_WIN64)) && (! (defined(__CYGWIN__))))

/* assume POSIX here */
#include <sys/types.h>
#include <sys/stat.h>
#include <fcntl.h>

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
  
#endif // ((defined(_WIN32) || defined(_WIN64)) && (! (defined(__CYGWIN__))))
