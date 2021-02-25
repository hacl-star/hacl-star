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

#include "test_helpers.h"

// Of course, it doesn't make sense to compile and run those test on a platform
// which doesn't support 256-bits vectors, but using macros directly in the files
// makes it easy to make the whole directory build on all platforms.
#if defined(SUPPORTS_256)
#include "EverCrypt_AutoConfig2.h"
#include "Hacl_Streaming_Blake2b_256.h"
#include "blake2_vectors.h"
#endif


typedef struct Hacl_Streaming_Blake2b_256_blake2b_256_state_s blake2_state;

int main() {
    bool ok = true;

#if defined(SUPPORTS_256)
    // Here, I can't really loop over the vectors... because I want to exercise
    // the streaming API with various lengths. Otherwise, in an exemplary test,
    // one would write a for-loop over the test vectors.

    uint8_t tag[64] = {};
    blake2_test_vector *v = vectors2b;

    if (EverCrypt_AutoConfig2_has_avx2()) {
      // At creation time, no_key/with_key only impacts the way the state is initialized.
      // We can thus reuse the state for all the tests.
      blake2_state *s = Hacl_Streaming_Blake2b_256_blake2b_256_with_key_create_in(64, v->key);
      Hacl_Streaming_Blake2b_256_blake2b_256_with_key_update(32, s, NULL, 0);
      Hacl_Streaming_Blake2b_256_blake2b_256_with_key_update(32, s, v->input, 8);
      Hacl_Streaming_Blake2b_256_blake2b_256_with_key_update(32, s, v->input+8, 8);
      Hacl_Streaming_Blake2b_256_blake2b_256_with_key_update(32, s, v->input+16, 16);
      Hacl_Streaming_Blake2b_256_blake2b_256_with_key_update(32, s, v->input+32, v->input_len-32);
      Hacl_Streaming_Blake2b_256_blake2b_256_with_key_finish(32, s, tag);
      ok &= compare_and_print(64, tag, v->expected);

      v++;
      Hacl_Streaming_Blake2b_256_blake2b_256_with_key_init(64, v->key, s);
      Hacl_Streaming_Blake2b_256_blake2b_256_with_key_update(64, s, NULL, 0);
      Hacl_Streaming_Blake2b_256_blake2b_256_with_key_update(64, s, v->input, 8);
      Hacl_Streaming_Blake2b_256_blake2b_256_with_key_update(64, s, v->input+8, 8);
      Hacl_Streaming_Blake2b_256_blake2b_256_with_key_update(64, s, v->input+16, 16);
      Hacl_Streaming_Blake2b_256_blake2b_256_with_key_update(64, s, v->input+32, 32);
      Hacl_Streaming_Blake2b_256_blake2b_256_with_key_update(32, s, v->input+64, v->input_len-64);
      Hacl_Streaming_Blake2b_256_blake2b_256_with_key_finish(64, s, tag);
      ok &= compare_and_print(64, tag, v->expected);

      Hacl_Streaming_Blake2b_256_blake2b_256_with_key_free(64, s);
    }
    else {
        printf("Blake2b (256-bit) streaming: no AVX2 support: ignoring tests\n");
    }
#endif

    if (ok)
        return EXIT_SUCCESS;
    else
        return EXIT_FAILURE;
}
