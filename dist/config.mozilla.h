/*
 * Mozilla doesn't want to rely on the configure script, so we hardcode the
 * assumption that AVX and AVX2 are available.
 */
#define HACL_CAN_COMPILE_INTRINSICS 1
#define HACL_CAN_COMPILE_VALE 1
#define HACL_CAN_COMPILE_INLINE_ASM 1
#define HACL_CAN_COMPILE_VEC128 1
#define HACL_CAN_COMPILE_VEC256 1
