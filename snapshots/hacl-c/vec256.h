#include <immintrin.h>
#define VEC256
const int vec_size = 32;
typedef unsigned int vec __attribute__ ((vector_size (32)));
#define ONE (vec)_mm256_set_epi32(1,0,0,0,1,0,0,0)
#define RORV(x,n) (vec)_mm256_shuffle_epi32((__m256i)x,_MM_SHUFFLE((3+n)%4,(2+n)%4,(1+n)%4,n%4))

