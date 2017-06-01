/*
cpucycles perfevent.h version 20120327
D. J. Bernstein
Public domain.
*/

#ifndef CPUCYCLES_perfevent_h
#define CPUCYCLES_perfevent_h

#ifdef __cplusplus
extern "C" {
#endif

extern long long cpucycles_perfevent(void);
extern long long cpucycles_perfevent_persecond(void);

#ifdef __cplusplus
}
#endif

#ifndef cpucycles_implementation
#define cpucycles_implementation "perfevent"
#define cpucycles cpucycles_perfevent
#define cpucycles_persecond cpucycles_perfevent_persecond
#endif

#endif
