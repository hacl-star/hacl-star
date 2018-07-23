#ifndef __C_STRING_H
#define __C_STRING_H

#include <stdio.h>

#include "kremlin/internal/target.h"
#include "kremlin/fstar_char.h"

/******************************************************************************/
/* Implementation of C.String                                                 */
/******************************************************************************/

/* Note: we drop C.String, which means that generated programs do not see
 * "extern" declarations, meaning that we can implement these functions via a
 * header only. */

typedef const char *C_String_t, *C_String_t_;

static inline char char_of_uint8(uint8_t x) {
  return (char) x;
}

static inline const char *C_String_of_literal (const char *str) {
  return str;
}

static inline uint32_t bufstrcpy(char *dst, const char *src) {
  /* The F* precondition guarantees that src is zero-terminated */
  return sprintf(dst, "%s", src);
}

static inline uint32_t print_u32(char *dst, uint32_t i) {
  return sprintf(dst, "%"PRIu32, i);
}

static inline void C_String_print(C_String_t str) {
  KRML_HOST_PRINTF("%s", str);
}

#endif
