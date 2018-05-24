#include "kremlib.h"
#ifdef __EverCrypt_H_DEFINED
#ifndef __Hacks_H
#define __Hacks_H

#include "Prims.h"
#include "FStar.h"
#include "kremlin/prims_int.h"
#include "kremlin/prims_string.h"

typedef struct K___uint8_t_uint8_t_s
{
  uint8_t fst;
  uint8_t snd;
}
K___uint8_t_uint8_t;

typedef struct  K___FStar_Bytes_bytes_FStar_Bytes_bytes_s
{
  FStar_Bytes_bytes fst;
  FStar_Bytes_bytes snd;
}
K___FStar_Bytes_bytes_FStar_Bytes_bytes;

typedef  enum { FStar_Pervasives_Native_None, FStar_Pervasives_Native_Some }
FStar_Pervasives_Native_option__Prims_string_tags;

typedef struct FStar_Pervasives_Native_option__Prims_string_s
{
  FStar_Pervasives_Native_option__Prims_string_tags tag;
  Prims_string v;
}
FStar_Pervasives_Native_option__Prims_string;

#include "kremlin/fstar_bytes.h"

#define __Hacks_H_DEFINED
#endif
#endif
