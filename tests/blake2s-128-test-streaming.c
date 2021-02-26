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

#if defined(COMPILE_128)
#include "Hacl_Streaming_Blake2s_128.h"
#include "blake2_vectors.h"
#endif

typedef struct Hacl_Streaming_Blake2s_128_blake2s_128_state_s blake2_state;

int main() {
    bool ok = true;

#if defined(COMPILE_128)
    // Here, I can't really loop over the vectors... because I want to exercise
    // the streaming API with various lengths. Otherwise, in an exemplary test,
    // one would write a for-loop over the test vectors.

    uint8_t tag[32] = {};
    blake2_test_vector *v = vectors2s;

    // At creation time, no_key/with_key only impacts the way the state is initialized.
    // We can thus reuse the state for all the tests.
    blake2_state *s = Hacl_Streaming_Blake2s_128_blake2s_128_no_key_create_in();
    Hacl_Streaming_Blake2s_128_blake2s_128_no_key_update(s, NULL, 0);
    Hacl_Streaming_Blake2s_128_blake2s_128_no_key_update(s, v->input, v->input_len);
    Hacl_Streaming_Blake2s_128_blake2s_128_no_key_finish(s, tag);
    ok &= compare_and_print(32, tag, v->expected);

    v++;
    Hacl_Streaming_Blake2s_128_blake2s_128_with_key_init(32, v->key, s);
    Hacl_Streaming_Blake2s_128_blake2s_128_with_key_update(32, s, NULL, 0);
    Hacl_Streaming_Blake2s_128_blake2s_128_with_key_update(32, s, v->input, v->input_len);
    Hacl_Streaming_Blake2s_128_blake2s_128_with_key_finish(32, s, tag);
    ok &= compare_and_print(32, tag, v->expected);

    v++;
    Hacl_Streaming_Blake2s_128_blake2s_128_with_key_init(32, v->key, s);
    Hacl_Streaming_Blake2s_128_blake2s_128_with_key_update(32, s, NULL, 0);
    Hacl_Streaming_Blake2s_128_blake2s_128_with_key_update(32, s, v->input, 8);
    Hacl_Streaming_Blake2s_128_blake2s_128_with_key_update(32, s, v->input+8, 8);
    Hacl_Streaming_Blake2s_128_blake2s_128_with_key_update(32, s, v->input+16, 16);
    Hacl_Streaming_Blake2s_128_blake2s_128_with_key_update(32, s, v->input+32, 32);
    Hacl_Streaming_Blake2s_128_blake2s_128_with_key_update(32, s, v->input+64, 64);
    Hacl_Streaming_Blake2s_128_blake2s_128_with_key_update(32, s, v->input+128, 127);
    Hacl_Streaming_Blake2s_128_blake2s_128_with_key_finish(32, s, tag);
    ok &= compare_and_print(32, tag, v->expected);

    v++;
    Hacl_Streaming_Blake2s_128_blake2s_128_with_key_init(32, v->key, s);
    Hacl_Streaming_Blake2s_128_blake2s_128_with_key_update(32, s, NULL, 0);
    Hacl_Streaming_Blake2s_128_blake2s_128_with_key_update(32, s, v->input, 8);
    Hacl_Streaming_Blake2s_128_blake2s_128_with_key_update(32, s, v->input+8, 8);
    Hacl_Streaming_Blake2s_128_blake2s_128_with_key_update(32, s, v->input+16, 16);
    Hacl_Streaming_Blake2s_128_blake2s_128_with_key_update(32, s, v->input+32, 32);
    Hacl_Streaming_Blake2s_128_blake2s_128_with_key_update(32, s, v->input+64, 64);
    Hacl_Streaming_Blake2s_128_blake2s_128_with_key_update(32, s, v->input+128, v->input_len - 128);
    Hacl_Streaming_Blake2s_128_blake2s_128_with_key_finish(32, s, tag);
    ok &= compare_and_print(32, tag, v->expected);

    Hacl_Streaming_Blake2s_128_blake2s_128_with_key_free(32, s);
#endif

    if (ok)
        return EXIT_SUCCESS;
    else
        return EXIT_FAILURE;
}
