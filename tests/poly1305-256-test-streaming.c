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
#if defined(COMPILE_VEC256)
#include "Hacl_Streaming_Poly1305_256.h"
#include "poly1305_vectors.h"
#include "EverCrypt_AutoConfig2.h"
#endif

typedef struct Hacl_Streaming_Poly1305_256_poly1305_256_state_s poly1305_state;

int main() {
    bool ok = true;

#if defined(COMPILE_VEC256)
    // Here, I can't really loop over the vectors... because I want to exercise
    // the streaming API with various lengths. Otherwise, in an exemplary test,
    // one would write a for-loop over the test vectors.

    uint8_t tag[16] = {};
    poly1305_test_vector *v = vectors;

    if (EverCrypt_AutoConfig2_has_avx2()) {
      poly1305_state *s = Hacl_Streaming_Poly1305_256_create_in(v->key);
      Hacl_Streaming_Poly1305_256_update(s, v->input, 8);
      Hacl_Streaming_Poly1305_256_update(s, v->input+8, 6);
      Hacl_Streaming_Poly1305_256_update(s, v->input+14, v->input_len - 14);
      Hacl_Streaming_Poly1305_256_finish(s, tag);
      ok &= compare_and_print(16, tag, v->tag);

      v++;
      Hacl_Streaming_Poly1305_256_init(v->key, s);
      Hacl_Streaming_Poly1305_256_update(s, NULL, 0);
      Hacl_Streaming_Poly1305_256_update(s, v->input, v->input_len);
      Hacl_Streaming_Poly1305_256_finish(s, tag);
      ok &= compare_and_print(16, tag, v->tag);

      v++;
      Hacl_Streaming_Poly1305_256_init(v->key, s);
      Hacl_Streaming_Poly1305_256_update(s, NULL, 0);
      Hacl_Streaming_Poly1305_256_update(s, v->input, 8);
      Hacl_Streaming_Poly1305_256_update(s, v->input+8, 8);
      Hacl_Streaming_Poly1305_256_update(s, v->input+16, 16);
      Hacl_Streaming_Poly1305_256_update(s, v->input+32, 8);
      Hacl_Streaming_Poly1305_256_update(s, v->input+40, v->input_len - 40);
      Hacl_Streaming_Poly1305_256_finish(s, tag);
      ok &= compare_and_print(16, tag, v->tag);

      Hacl_Streaming_Poly1305_256_free(s);
    }
    else {
        printf("Poly1305 (256-bit) streaming: no AVX2 support: ignoring tests\n");
    }
#endif

    if (ok)
        return EXIT_SUCCESS;
    else
        return EXIT_FAILURE;

}
