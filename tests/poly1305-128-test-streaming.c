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

#include "Hacl_Streaming_Poly1305_128.h"
#include "poly1305_vectors.h"
#include "test_helpers.h"

typedef struct Hacl_Streaming_Poly1305_128_poly1305_128_state_s poly1305_state;

int
main()
{
  bool ok = true;

  // Here, I can't really loop over the vectors... because I want to exercise
  // the streaming API with various lengths. Otherwise, in an exemplary test,
  // one would write a for-loop over the test vectors.

  uint8_t tag[16] = {};
  poly1305_test_vector* v = vectors;

  poly1305_state* s = Hacl_Streaming_Poly1305_128_create_in(v->key);
  assert(Hacl_Streaming_Poly1305_128_update(s, v->input, 8) == 0);
  assert(Hacl_Streaming_Poly1305_128_update(s, v->input + 8, 6) == 0);
  assert(Hacl_Streaming_Poly1305_128_update(
           s, v->input + 14, v->input_len - 14) == 0);
  Hacl_Streaming_Poly1305_128_finish(s, tag);
  ok &= compare_and_print(16, tag, v->tag);

  v++;
  Hacl_Streaming_Poly1305_128_init(v->key, s);
  assert(Hacl_Streaming_Poly1305_128_update(s, NULL, 0) == 0);
  assert(Hacl_Streaming_Poly1305_128_update(s, v->input, v->input_len) == 0);
  Hacl_Streaming_Poly1305_128_finish(s, tag);
  ok &= compare_and_print(16, tag, v->tag);

  v++;
  Hacl_Streaming_Poly1305_128_init(v->key, s);
  assert(Hacl_Streaming_Poly1305_128_update(s, NULL, 0) == 0);
  assert(Hacl_Streaming_Poly1305_128_update(s, v->input, 8) == 0);
  assert(Hacl_Streaming_Poly1305_128_update(s, v->input + 8, 8) == 0);
  assert(Hacl_Streaming_Poly1305_128_update(s, v->input + 16, 16) == 0);
  assert(Hacl_Streaming_Poly1305_128_update(s, v->input + 32, 8) == 0);
  assert(Hacl_Streaming_Poly1305_128_update(
           s, v->input + 40, v->input_len - 40) == 0);
  Hacl_Streaming_Poly1305_128_finish(s, tag);
  ok &= compare_and_print(16, tag, v->tag);

  Hacl_Streaming_Poly1305_128_free(s);

  if (ok)
    return EXIT_SUCCESS;
  else
    return EXIT_FAILURE;
}
