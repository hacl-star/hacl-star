/*
cpucycles apple.h version 20110616
D. J. Bernstein
Public domain.
*/

#ifndef CPUCYCLES_apple_h
#define CPUCYCLES_apple_h

#ifdef __cplusplus
extern "C" {
#endif

extern long long cpucycles_apple(void);
extern long long cpucycles_apple_persecond(void);

#ifdef __cplusplus
}
#endif

#ifndef cpucycles_implementation
#define cpucycles_implementation "apple"
#define cpucycles cpucycles_apple
#define cpucycles_persecond cpucycles_apple_persecond
#endif

#endif
