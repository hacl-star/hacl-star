/*
cpucycles cortex_vct.h version 20100912
D. J. Bernstein
Romain Dobeau
Public domain.
*/

#ifndef CPUCYCLES_cortex_vct_h
#define CPUCYCLES_cortex_vct_h

#ifdef __cplusplus
extern "C" {
#endif

extern long long cpucycles_cortex_vct(void);
extern long long cpucycles_cortex_vct_persecond(void);

#ifdef __cplusplus
}
#endif

#ifndef cpucycles_implementation
#define cpucycles_implementation "cortex_vct"
#define cpucycles cpucycles_cortex_vct
#define cpucycles_persecond cpucycles_cortex_vct_persecond
#endif

#endif
