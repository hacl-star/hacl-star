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

#include "Hacl_Streaming_Blake2.h"

#include "blake2_vectors.h"
#include "test_helpers.h"

typedef struct Hacl_Streaming_Blake2_blake2b_32_state_s blake2_state;

int
main()
{
  bool ok = true;

  // Here, I can't really loop over the vectors... because I want to exercise
  // the streaming API with various lengths. Otherwise, in an exemplary test,
  // one would write a for-loop over the test vectors.

  uint8_t tag[64] = {};
  // Use only the vectors without keys: streaming blake2 in keyed mode is not
  // implemented.
  blake2_test_vector* v = &vectors2b[2];

  blake2_state* s = Hacl_Streaming_Blake2_blake2b_32_no_key_create_in();
  assert(Hacl_Streaming_Blake2_blake2b_32_no_key_update(s, NULL, 0) == 0);
  assert(Hacl_Streaming_Blake2_blake2b_32_no_key_update(s, v->input, 8) == 0);
  assert(Hacl_Streaming_Blake2_blake2b_32_no_key_update(s, v->input + 8, 8) ==
         0);
  assert(Hacl_Streaming_Blake2_blake2b_32_no_key_update(s, v->input + 16, 16) ==
         0);
  assert(Hacl_Streaming_Blake2_blake2b_32_no_key_update(
           s, v->input + 32, v->input_len - 32) == 0);
  Hacl_Streaming_Blake2_blake2b_32_no_key_finish(s, tag);
  ok &= compare_and_print(64, tag, v->expected);

  v++;
  Hacl_Streaming_Blake2_blake2b_32_no_key_init(s);
  assert(Hacl_Streaming_Blake2_blake2b_32_no_key_update(s, NULL, 0) == 0);
  assert(Hacl_Streaming_Blake2_blake2b_32_no_key_update(s, v->input, 8) == 0);
  assert(Hacl_Streaming_Blake2_blake2b_32_no_key_update(s, v->input + 8, 8) ==
         0);
  assert(Hacl_Streaming_Blake2_blake2b_32_no_key_update(s, v->input + 16, 16) ==
         0);
  assert(Hacl_Streaming_Blake2_blake2b_32_no_key_update(s, v->input + 32, 32) ==
         0);
  assert(Hacl_Streaming_Blake2_blake2b_32_no_key_update(
           s, v->input + 64, v->input_len - 64) == 0);
  Hacl_Streaming_Blake2_blake2b_32_no_key_finish(s, tag);
  ok &= compare_and_print(64, tag, v->expected);

  Hacl_Streaming_Blake2_blake2b_32_no_key_free(s);

  if (ok)
    return EXIT_SUCCESS;
  else
    return EXIT_FAILURE;
}
