/*
cpucycles vct.h version 20160726
D. J. Bernstein
Romain Dobeau
Public domain.
*/

#ifndef CPUCYCLES_vct_h
#define CPUCYCLES_vct_h

#ifdef __cplusplus
extern "C" {
#endif

extern long long cpucycles_vct(void);
extern long long cpucycles_vct_persecond(void);

#ifdef __cplusplus
}
#endif

#ifndef cpucycles_implementation
#define cpucycles_implementation "vct"
#define cpucycles cpucycles_vct
#define cpucycles_persecond cpucycles_vct_persecond
#endif

#endif
