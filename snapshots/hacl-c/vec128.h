#include <emmintrin.h>

#define VEC128
const int vec_size = 16;
typedef unsigned int vec __attribute__ ((vector_size (16)));
#define ONE (vec){1,0,0,0}
#define RORV(x,n) (vec)_mm_shuffle_epi32((__m128i)x,_MM_SHUFFLE((3+n)%4,(2+n)%4,(1+n)%4,n%4))

