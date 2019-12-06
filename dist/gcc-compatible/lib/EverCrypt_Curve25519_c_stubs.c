
#include "EverCrypt_Curve25519.h"
#include "ctypes_cstubs_internals.h"
value _1_EverCrypt_Curve25519_secret_to_public(value x2, value x1)
{
   uint8_t* x3 = CTYPES_ADDR_OF_FATPTR(x2);
   uint8_t* x4 = CTYPES_ADDR_OF_FATPTR(x1);
   EverCrypt_Curve25519_secret_to_public(x3, x4);
   return Val_unit;
}
value _2_EverCrypt_Curve25519_scalarmult(value x8, value x7, value x6)
{
   uint8_t* x9 = CTYPES_ADDR_OF_FATPTR(x8);
   uint8_t* x10 = CTYPES_ADDR_OF_FATPTR(x7);
   uint8_t* x11 = CTYPES_ADDR_OF_FATPTR(x6);
   EverCrypt_Curve25519_scalarmult(x9, x10, x11);
   return Val_unit;
}
value _3_EverCrypt_Curve25519_ecdh(value x15, value x14, value x13)
{
   uint8_t* x16 = CTYPES_ADDR_OF_FATPTR(x15);
   uint8_t* x17 = CTYPES_ADDR_OF_FATPTR(x14);
   uint8_t* x18 = CTYPES_ADDR_OF_FATPTR(x13);
   _Bool x19 = EverCrypt_Curve25519_ecdh(x16, x17, x18);
   return Val_bool(x19);
}
