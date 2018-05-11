#include "kremlin/c_string.h"
#include "kremlin/prims_string.h"
#include "kremlib.h"

/******************************************************************************/
/* Implementation of FStar.String and FStar.HyperIO                           */
/******************************************************************************/

/* FStar.h is generally kept for the program we wish to compile, meaning that
 * FStar.h contains extern declarations for the functions below. This provides
 * their implementation, and since the function prototypes are already in
 * FStar.h, we don't need to put these in the header, they will be resolved at
 * link-time. */

Prims_string Prims_string_of_int(krml_checked_int_t i) {
  return FStar_Int32_to_string(i);
}

Prims_nat FStar_String_strlen(Prims_string s) {
  return strlen(s);
}

Prims_string FStar_String_strcat(Prims_string s0, Prims_string s1) {
  size_t len = strlen(s0) + strlen(s1) + 1;
  char *dest = KRML_HOST_CALLOC(len, 1);
#ifdef _MSC_VER
  strcat_s(dest, len, s0);
  strcat_s(dest, len, s1);
#else
  strcat(dest, s0);
  strcat(dest, s1);
#endif
  return (Prims_string)dest;
}

Prims_string Prims_strcat(Prims_string s0, Prims_string s1) {
  return FStar_String_strcat(s0, s1);
}

void FStar_HyperStack_IO_print_string(Prims_string s) {
  KRML_HOST_PRINTF("%s", s);
}

bool FStar_IO_debug_print_string(Prims_string s) {
  KRML_HOST_PRINTF("%s", s);
  return false;
}

bool __eq__Prims_string(Prims_string s1, Prims_string s2) {
  return (strcmp(s1, s2) == 0);
}

krml_checked_int_t FStar_String_index_of(Prims_string s1, FStar_Char_char fc) {
  if (fc > 127) {
    KRML_HOST_PRINTF("FStar.Char.char overflow at %s:%d\n", __FILE__, __LINE__);
    KRML_HOST_EXIT(252);
  }
  char c = fc;
  char *pos = strchr(s1, c);
  return (pos ? pos - s1 : -1);
}

Prims_string FStar_String_substring(
    Prims_string s0, krml_checked_int_t from, krml_checked_int_t length) {
  char *dest = KRML_HOST_CALLOC(length + 1, 1); // zero terminated
#ifdef _MSC_VER
  strncpy_s(dest, length + 1, s0 + from, length);
#else
  strncpy(dest, s0 + from, length);
#endif
  return dest;
}
