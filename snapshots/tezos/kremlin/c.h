#ifndef __KREMLIN_C_H
#define __KREMLIN_C_H

#include <inttypes.h>

/******************************************************************************/
/* Implementing C.fst (part 1: misc.)                                         */
/******************************************************************************/

extern intptr_t nullptr;

/* For non-base types (i.e. not machine integers), KreMLin generates calls to
 * assumed equality functions. */
static inline bool __eq__C_char(char c1, char c2) {
  return c1 == c2;
}

/* This one allows the user to write C.EXIT_SUCCESS. Since C enjoys -no-prefix,
 * C.EXIT_SUCCESS is printed as EXIT_SUCCESS which resolves to the proper C
 * macro. */
typedef int exit_code;

/* Now also exposed via FStar.Bytes.fst */
void print_bytes(const uint8_t *b, uint32_t len);

#endif
