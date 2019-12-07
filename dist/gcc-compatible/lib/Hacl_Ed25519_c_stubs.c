
#include "Hacl_Ed25519.h"
#include "ctypes_cstubs_internals.h"
value _1_Hacl_Ed25519_sign(value x4, value x3, value x2, value x1)
{
   uint8_t* x5 = CTYPES_ADDR_OF_FATPTR(x4);
   uint8_t* x6 = CTYPES_ADDR_OF_FATPTR(x3);
   uint32_t x7 = Uint32_val(x2);
   uint8_t* x10 = CTYPES_ADDR_OF_FATPTR(x1);
   Hacl_Ed25519_sign(x5, x6, x7, x10);
   return Val_unit;
}
value _2_Hacl_Ed25519_verify(value x15, value x14, value x13, value x12)
{
   uint8_t* x16 = CTYPES_ADDR_OF_FATPTR(x15);
   uint32_t x17 = Uint32_val(x14);
   uint8_t* x20 = CTYPES_ADDR_OF_FATPTR(x13);
   uint8_t* x21 = CTYPES_ADDR_OF_FATPTR(x12);
   _Bool x22 = Hacl_Ed25519_verify(x16, x17, x20, x21);
   return Val_bool(x22);
}
value _3_Hacl_Ed25519_secret_to_public(value x24, value x23)
{
   uint8_t* x25 = CTYPES_ADDR_OF_FATPTR(x24);
   uint8_t* x26 = CTYPES_ADDR_OF_FATPTR(x23);
   Hacl_Ed25519_secret_to_public(x25, x26);
   return Val_unit;
}
value _4_Hacl_Ed25519_expand_keys(value x29, value x28)
{
   uint8_t* x30 = CTYPES_ADDR_OF_FATPTR(x29);
   uint8_t* x31 = CTYPES_ADDR_OF_FATPTR(x28);
   Hacl_Ed25519_expand_keys(x30, x31);
   return Val_unit;
}
value _5_Hacl_Ed25519_sign_expanded(value x36, value x35, value x34,
                                    value x33)
{
   uint8_t* x37 = CTYPES_ADDR_OF_FATPTR(x36);
   uint8_t* x38 = CTYPES_ADDR_OF_FATPTR(x35);
   uint32_t x39 = Uint32_val(x34);
   uint8_t* x42 = CTYPES_ADDR_OF_FATPTR(x33);
   Hacl_Ed25519_sign_expanded(x37, x38, x39, x42);
   return Val_unit;
}
