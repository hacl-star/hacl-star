#include <inttypes.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/types.h>
#include <sys/stat.h>
#include <fcntl.h>
#include <unistd.h>
#include <stdbool.h>
#include <time.h>

#include "Hacl_Streaming_SHA2_256.h"

#include "test_helpers.h"
#include "sha2_vectors.h"

typedef Hacl_Streaming_Functor_state_s___uint32_t____ sha2_state;

int main() {
  bool ok = true;

  // Here, I can't really loop over the vectors... because I want to exercise
  // the streaming API with various lengths. Otherwise, in an exemplary test,
  // one would write a for-loop over the test vectors.

  uint8_t tag[32] = {};
  sha2_test_vector *v = vectors;

  sha2_state *s = Hacl_Streaming_SHA2_256_create_in();
  Hacl_Streaming_SHA2_256_update(s, v->input, 3);
  Hacl_Streaming_SHA2_256_finish(s, tag);
  ok &= compare_and_print(32, tag, v->tag_256);

  v++;
  Hacl_Streaming_SHA2_256_init(s);
  Hacl_Streaming_SHA2_256_update(s, NULL, 0);
  Hacl_Streaming_SHA2_256_update(s, v->input, v->input_len);
  Hacl_Streaming_SHA2_256_finish(s, tag);
  ok &= compare_and_print(32, tag, v->tag_256);

  v++;
  Hacl_Streaming_SHA2_256_init(s);
  Hacl_Streaming_SHA2_256_update(s, NULL, 0);
  Hacl_Streaming_SHA2_256_update(s, v->input, 16);
  Hacl_Streaming_SHA2_256_update(s, v->input+16, 16);
  Hacl_Streaming_SHA2_256_update(s, v->input+32, v->input_len - 32);
  Hacl_Streaming_SHA2_256_finish(s, tag);
  ok &= compare_and_print(32, tag, v->tag_256);

  Hacl_Streaming_SHA2_256_free(s);

  if (ok)
    return EXIT_SUCCESS;
  else
    return EXIT_FAILURE;
}
