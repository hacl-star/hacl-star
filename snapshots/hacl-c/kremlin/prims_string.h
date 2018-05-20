#ifndef __PRIMS_STRING_H
#define __PRIMS_STRING_H

#include <inttypes.h>

#include "kremlin/prims_int.h"

typedef const char *Prims_string;

/******************************************************************************/
/* NOT LOW*: implement Prims.string as leaky heap-allocated strings           */
/******************************************************************************/

Prims_string Prims_strcat(Prims_string s0, Prims_string s1);
krml_checked_int_t FStar_String_index_of(Prims_string s1, FStar_Char_char fc);
Prims_string FStar_String_substring(Prims_string s0, krml_checked_int_t from, krml_checked_int_t length);
Prims_nat FStar_String_strlen(Prims_string s);

static inline Prims_string FStar_Int64_to_string(uint64_t i) {
  char *buf = KRML_HOST_MALLOC(24);
  snprintf(buf, 24, "%"PRId64, i);
  return buf;
}

static inline Prims_string FStar_Int32_to_string(uint32_t i) {
  char *buf = KRML_HOST_MALLOC(24);
  snprintf(buf, 24, "%"PRId32, i);
  return buf;
}

static inline Prims_string FStar_Int16_to_string(uint16_t i) {
  char *buf = KRML_HOST_MALLOC(24);
  snprintf(buf, 24, "%"PRId16, i);
  return buf;
}

static inline Prims_string FStar_Int8_to_string(uint8_t i) {
  char *buf = KRML_HOST_MALLOC(24);
  snprintf(buf, 24, "%"PRId8, i);
  return buf;
}

static inline Prims_string FStar_UInt64_to_string(uint64_t i) {
  char *buf = KRML_HOST_MALLOC(24);
  snprintf(buf, 24, "%"PRIu64, i);
  return buf;
}

static inline Prims_string FStar_UInt32_to_string(uint32_t i) {
  char *buf = KRML_HOST_MALLOC(24);
  snprintf(buf, 24, "%"PRIu32, i);
  return buf;
}

static inline Prims_string FStar_UInt16_to_string(uint16_t i) {
  char *buf = KRML_HOST_MALLOC(24);
  snprintf(buf, 24, "%"PRIu16, i);
  return buf;
}

static inline Prims_string FStar_UInt8_to_string(uint8_t i) {
  char *buf = KRML_HOST_MALLOC(24);
  snprintf(buf, 24, "%"PRIu8, i);
  return buf;
}

static inline Prims_string Prims_string_of_bool(bool b) {
  if (b) {
    return "true";
  } else {
    return "false";
  }
}

#endif
