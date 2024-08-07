#include <assert.h>
#include <fcntl.h>
#include <inttypes.h>
#include <stdbool.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/stat.h>
#include <sys/types.h>
#include <time.h>
#include <unistd.h>

#include "Hacl_Hash_Blake2s.h"

#include "blake2_vectors.h"
#include "test_helpers.h"

typedef Hacl_Hash_Blake2s_state_t blake2_state;

int
main()
{
  bool ok = true;

  // Here, I can't really loop over the vectors... because I want to exercise
  // the streaming API with various lengths. Otherwise, in an exemplary test,
  // one would write a for-loop over the test vectors.

  uint8_t tag[32] = {};
  // Use only the vectors without keys: streaming blake2 in keyed mode is not
  // implemented.
  blake2_test_vector* v = &vectors2s[5];

  blake2_state* s = Hacl_Hash_Blake2s_malloc();
  assert(Hacl_Hash_Blake2s_update(s, NULL, 0) == 0);
  assert(Hacl_Hash_Blake2s_update(
           s, v->input, v->input_len) == 0);
  Hacl_Hash_Blake2s_digest(s, tag);
  ok &= compare_and_print(32, tag, v->expected);

  v++;
  Hacl_Hash_Blake2s_reset(s);
  assert(Hacl_Hash_Blake2s_update(s, NULL, 0) == 0);
  assert(Hacl_Hash_Blake2s_update(
           s, v->input, v->input_len) == 0);
  Hacl_Hash_Blake2s_digest(s, tag);
  ok &= compare_and_print(32, tag, v->expected);

  v++;
  Hacl_Hash_Blake2s_reset(s);
  assert(Hacl_Hash_Blake2s_update(s, NULL, 0) == 0);
  assert(Hacl_Hash_Blake2s_update(s, v->input, 8) == 0);
  assert(Hacl_Hash_Blake2s_update(s, v->input + 8, 8) ==
         0);
  assert(Hacl_Hash_Blake2s_update(s, v->input + 16, 16) ==
         0);
  assert(Hacl_Hash_Blake2s_update(s, v->input + 32, 32) ==
         0);
  assert(Hacl_Hash_Blake2s_update(s, v->input + 64, 64) ==
         0);
  assert(Hacl_Hash_Blake2s_update(
           s, v->input + 128, 127) == 0);
  Hacl_Hash_Blake2s_digest(s, tag);
  ok &= compare_and_print(32, tag, v->expected);

  v++;
  Hacl_Hash_Blake2s_reset(s);
  assert(Hacl_Hash_Blake2s_update(s, NULL, 0) == 0);
  assert(Hacl_Hash_Blake2s_update(s, v->input, 8) == 0);
  assert(Hacl_Hash_Blake2s_update(s, v->input + 8, 8) ==
         0);
  assert(Hacl_Hash_Blake2s_update(s, v->input + 16, 16) ==
         0);
  assert(Hacl_Hash_Blake2s_update(s, v->input + 32, 32) ==
         0);
  assert(Hacl_Hash_Blake2s_update(s, v->input + 64, 64) ==
         0);
  assert(Hacl_Hash_Blake2s_update(
           s, v->input + 128, v->input_len - 128) == 0);
  Hacl_Hash_Blake2s_digest(s, tag);
  ok &= compare_and_print(32, tag, v->expected);

  v++;
  Hacl_Hash_Blake2s_reset(s);
  assert(Hacl_Hash_Blake2s_update(s, NULL, 0) == 0);
  assert(Hacl_Hash_Blake2s_update(s, v->input, 8) == 0);
  assert(Hacl_Hash_Blake2s_update(s, v->input + 8, 8) ==
         0);
  assert(Hacl_Hash_Blake2s_update(s, v->input + 16, 16) ==
         0);
  assert(Hacl_Hash_Blake2s_update(
           s, v->input + 32, v->input_len - 32) == 0);
  Hacl_Hash_Blake2s_digest(s, tag);
  ok &= compare_and_print(32, tag, v->expected);

  Hacl_Hash_Blake2s_free(s);

  if (ok)
    return EXIT_SUCCESS;
  else
    return EXIT_FAILURE;
}
