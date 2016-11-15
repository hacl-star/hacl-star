#include "Hacl_Cast.h"

FStar_UInt128_t Hacl_Cast_sint8_to_sint128(uint8_t a)
{
  return FStar_Int_Cast_uint64_to_uint128((uint64_t )a);
}

uint64_t Hacl_Cast_sint8_to_sint64(uint8_t a)
{
  return (uint64_t )a;
}

uint32_t Hacl_Cast_sint8_to_sint32(uint8_t a)
{
  return (uint32_t )a;
}

FStar_UInt128_t Hacl_Cast_sint32_to_sint128(uint32_t a)
{
  return FStar_Int_Cast_uint64_to_uint128((uint64_t )a);
}

uint64_t Hacl_Cast_sint32_to_sint64(uint32_t a)
{
  return (uint64_t )a;
}

uint8_t Hacl_Cast_sint32_to_sint8(uint32_t a)
{
  return (uint8_t )a;
}

FStar_UInt128_t Hacl_Cast_sint64_to_sint128(uint64_t a)
{
  return FStar_Int_Cast_uint64_to_uint128(a);
}

uint32_t Hacl_Cast_sint64_to_sint32(uint64_t a)
{
  return (uint32_t )a;
}

uint8_t Hacl_Cast_sint64_to_sint8(uint64_t a)
{
  return (uint8_t )a;
}

uint64_t Hacl_Cast_sint128_to_sint64(FStar_UInt128_t a)
{
  return FStar_Int_Cast_uint128_to_uint64(a);
}

uint32_t Hacl_Cast_sint128_to_sint32(FStar_UInt128_t a)
{
  return (uint32_t )FStar_Int_Cast_uint128_to_uint64(a);
}

uint8_t Hacl_Cast_sint128_to_sint8(FStar_UInt128_t a)
{
  return (uint8_t )FStar_Int_Cast_uint128_to_uint64(a);
}

FStar_UInt128_t Hacl_Cast_uint64_to_sint128(uint64_t a)
{
  return FStar_Int_Cast_uint64_to_uint128(a);
}

uint64_t Hacl_Cast_uint64_to_sint64(uint64_t a)
{
  return a;
}

uint32_t Hacl_Cast_uint64_to_sint32(uint64_t a)
{
  return (uint32_t )a;
}

uint8_t Hacl_Cast_uint64_to_sint8(uint64_t a)
{
  return (uint8_t )a;
}

FStar_UInt128_t Hacl_Cast_uint32_to_sint128(uint32_t a)
{
  return FStar_Int_Cast_uint64_to_uint128((uint64_t )a);
}

uint64_t Hacl_Cast_uint32_to_sint64(uint32_t a)
{
  return (uint64_t )a;
}

uint32_t Hacl_Cast_uint32_to_sint32(uint32_t a)
{
  return a;
}

uint8_t Hacl_Cast_uint32_to_sint8(uint32_t a)
{
  return (uint8_t )a;
}

FStar_UInt128_t Hacl_Cast_uint8_to_sint128(uint8_t a)
{
  return FStar_Int_Cast_uint64_to_uint128((uint64_t )a);
}

uint64_t Hacl_Cast_uint8_to_sint64(uint8_t a)
{
  return (uint64_t )a;
}

uint32_t Hacl_Cast_uint8_to_sint32(uint8_t a)
{
  return (uint32_t )a;
}

uint8_t Hacl_Cast_uint8_to_sint8(uint8_t a)
{
  return a;
}

