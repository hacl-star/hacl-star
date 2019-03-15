/******************************************************
* Hardware-based random number generation function
*******************************************************/ 

#include "random.h"
#include <stdlib.h>
#if defined(__WINDOWS__) || defined(__MINGW32__)
  #include <windows.h>
  #include <bcrypt.h>
#elif defined(__LINUX__)
  #include <unistd.h>
  #include <fcntl.h>
  #include <sys/syscall.h>
  static int lock = -1;
  #define _GNU_SOURCE
#endif

#define passed 0 
#define failed 1


static __inline void delay(unsigned int count)
{
  while (count--) {}
}


int randombytes_internal(unsigned char* random_array, unsigned int nbytes)
{ // Generation of "nbytes" of random values
    
#if defined(__WINDOWS__) || defined(__MINGW32__)
  if (!BCRYPT_SUCCESS(BCryptGenRandom(NULL, random_array, (unsigned long)nbytes, BCRYPT_USE_SYSTEM_PREFERRED_RNG))) {
    return failed;
  }

#elif defined(__LINUX__)
  int r, n = nbytes, count = 0;
    
  if (lock == -1) {
    do {
      lock = open("/dev/urandom", O_RDONLY);
      if (lock == -1) {
        delay(0xFFFFF);
      }
    } while (lock == -1);
  }

  while (n > 0) {
    do {
      r = read(lock, random_array+count, n);
      if (r == -1) {
        delay(0xFFFF);
      }
    } while (r == -1);
    count += r;
    n -= r;
  }
#endif

    return passed;
}

#if defined(__LINUX__) && defined(SYS_getrandom)

void randombytes(unsigned char* random_array, unsigned int nbytes)
{ // Generation of "nbytes" of random values
  // Randombytes using system call

  if (syscall(SYS_getrandom, random_array, (size_t)nbytes, 0) < 0)
    randombytes_internal(random_array, nbytes);
}

#else

void randombytes(unsigned char* random_array, unsigned int nbytes)
{
  randombytes_internal(random_array, nbytes);
}

#endif

// Hacl.QTesla.Random
void Hacl_QTesla_Random_randombytes_init_(unsigned char *entropy_input) {
  return;
}

void Hacl_QTesla_Random_randombytes_(unsigned long long xlen, unsigned char *x) {
  randombytes(x, xlen);
}
