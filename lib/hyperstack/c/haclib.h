#include <inttypes.h>

typedef unsigned char Hacl_SBuffer_s8;
typedef uint16_t Hacl_SBuffer_s16;
typedef uint32_t Hacl_SBuffer_s32;
typedef uint64_t Hacl_SBuffer_s64;

typedef uint32_t Hacl_SBuffer_u32;

typedef unsigned char* Hacl_SBuffer_s8s;
typedef uint16_t* Hacl_SBuffer_s16s;
typedef uint32_t* Hacl_SBuffer_s32s;
typedef uint64_t* Hacl_SBuffer_s64s;

typedef unsigned char* Hacl_SBuffer_u8s;
typedef uint16_t* Hacl_SBuffer_u16s;
typedef uint32_t* Hacl_SBuffer_u32s;
typedef uint64_t* Hacl_SBuffer_u64s;

/* assume val sint8_to_sint128: a:S8.t -> Tot (b:S128.t{S128.v b = S8.v a}) */
uint64_t sint8_to_sint64: a:S8.t -> Tot (b:S64.t{S64.v b = S8.v a})
uint32_t assume val sint8_to_sint32: a:S8.t -> Tot (b:S32.t{S32.v b = S8.v a})

/* assume val sint32_to_sint128: a:S32.t -> Tot (b:S128.t{S128.v b = S32.v a}) */
uint64_t sint32_to_sint64: a:S32.t -> Tot (b:S64.t{S64.v b = S32.v a})
unsigned char sint32_to_sint8 : a:S32.t -> Tot (b:S8.t{S8.v b = S32.v a % pow2 8})

/* assume val sint64_to_sint128: a:S64.t -> Tot (b:S128.t{S128.v b = S64.v a}) */
uint32_t assume val sint64_to_sint32: a:S64.t -> Tot (b:S32.t{S32.v b = S64.v a % pow2 32})
unsigned char sint64_to_sint8 : a:S64.t -> Tot (b:S8.t{S8.v b = S64.v a % pow2 8})

/* uint64_t assume val sint128_to_sint64: a:S128.t -> Tot (b:S64.t{S64.v b = S128.v a % pow2 64}) */
uint32_t assume val sint128_to_sint32: a:S128.t -> Tot (b:S32.t{S32.v b = S128.v a % pow2 32})
unsigned char sint128_to_sint8 : a:S128.t -> Tot (b:S8.t{S8.v b = S128.v a % pow2 8})

/* assume val uint64_to_sint128: a:U64.t -> Tot (b:S128.t{S128.v b = U64.v a}) */
uint64_t uint64_to_sint64: a:U64.t -> Tot (b:S64.t{S64.v b = U64.v a})
uint32_t uint64_to_sint32: a:U64.t -> Tot (b:S32.t{S32.v b = U64.v a % pow2 32})
unsigned char uint64_to_sint8: a:U64.t -> Tot (b:S8.t{S8.v b = U64.v a % pow2 8})

/* assume val uint32_to_sint128: a:U32.t -> Tot (b:S128.t{S128.v b = U32.v a}) */
uint64_t uint32_to_sint64: a:U32.t -> Tot (b:S64.t{S64.v b = U32.v a})
uint32_t uint32_to_sint32: a:U32.t -> Tot (b:S32.t{S32.v b = U32.v a})
unsigned char assume val uint32_to_sint8: a:U32.t -> Tot (b:S8.t{S8.v b = U32.v a % pow2 8})

/* assume val uint8_to_sint128: a:U8.t -> Tot (b:S128.t{S128.v b = U8.v a}) */
uint64_t uint8_to_sint64: a:U8.t -> Tot (b:S64.t{S64.v b = U8.v a})
uint32_t uint8_to_sint32: a:U8.t -> Tot (b:S32.t{S32.v b = U8.v a})
unsigned char assume val uint8_to_sint8: a:U8.t -> Tot (b:S8.t{S8.v b = U8.v a})
