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

#include "Hacl_Streaming_Blake2.h"

#include "test_helpers.h"
#include "blake2_vectors.h"

typedef struct Hacl_Streaming_Blake2_blake2s_32_state_s blake2_state;

int main() {
    bool ok = true;

    // Here, I can't really loop over the vectors... because I want to exercise
    // the streaming API with various lengths. Otherwise, in an exemplary test,
    // one would write a for-loop over the test vectors.

    uint8_t tag[32] = {};
    // Use only the vectors without keys: streaming blake2 in keyed mode is not
    // implemented.
    blake2_test_vector *v = &vectors2s[5];

    blake2_state *s = Hacl_Streaming_Blake2_blake2s_32_no_key_create_in();
    Hacl_Streaming_Blake2_blake2s_32_no_key_update(s, NULL, 0);
    Hacl_Streaming_Blake2_blake2s_32_no_key_update(s, v->input, v->input_len);
    Hacl_Streaming_Blake2_blake2s_32_no_key_finish(s, tag);
    ok &= compare_and_print(32, tag, v->expected);

    v++;
    Hacl_Streaming_Blake2_blake2s_32_no_key_init(s);
    Hacl_Streaming_Blake2_blake2s_32_no_key_update(s, NULL, 0);
    Hacl_Streaming_Blake2_blake2s_32_no_key_update(s, v->input, v->input_len);
    Hacl_Streaming_Blake2_blake2s_32_no_key_finish(s, tag);
    ok &= compare_and_print(32, tag, v->expected);

    v++;
    Hacl_Streaming_Blake2_blake2s_32_no_key_init(s);
    Hacl_Streaming_Blake2_blake2s_32_no_key_update(s, NULL, 0);
    Hacl_Streaming_Blake2_blake2s_32_no_key_update(s, v->input, 8);
    Hacl_Streaming_Blake2_blake2s_32_no_key_update(s, v->input+8, 8);
    Hacl_Streaming_Blake2_blake2s_32_no_key_update(s, v->input+16, 16);
    Hacl_Streaming_Blake2_blake2s_32_no_key_update(s, v->input+32, 32);
    Hacl_Streaming_Blake2_blake2s_32_no_key_update(s, v->input+64, 64);
    Hacl_Streaming_Blake2_blake2s_32_no_key_update(s, v->input+128, 127);
    Hacl_Streaming_Blake2_blake2s_32_no_key_finish(s, tag);
    ok &= compare_and_print(32, tag, v->expected);

    v++;
    Hacl_Streaming_Blake2_blake2s_32_no_key_init(s);
    Hacl_Streaming_Blake2_blake2s_32_no_key_update(s, NULL, 0);
    Hacl_Streaming_Blake2_blake2s_32_no_key_update(s, v->input, 8);
    Hacl_Streaming_Blake2_blake2s_32_no_key_update(s, v->input+8, 8);
    Hacl_Streaming_Blake2_blake2s_32_no_key_update(s, v->input+16, 16);
    Hacl_Streaming_Blake2_blake2s_32_no_key_update(s, v->input+32, 32);
    Hacl_Streaming_Blake2_blake2s_32_no_key_update(s, v->input+64, 64);
    Hacl_Streaming_Blake2_blake2s_32_no_key_update(s, v->input+128, v->input_len - 128);
    Hacl_Streaming_Blake2_blake2s_32_no_key_finish(s, tag);
    ok &= compare_and_print(32, tag, v->expected);

    v++;
    Hacl_Streaming_Blake2_blake2s_32_no_key_init(s);
    Hacl_Streaming_Blake2_blake2s_32_no_key_update(s, NULL, 0);
    Hacl_Streaming_Blake2_blake2s_32_no_key_update(s, v->input, 8);
    Hacl_Streaming_Blake2_blake2s_32_no_key_update(s, v->input+8, 8);
    Hacl_Streaming_Blake2_blake2s_32_no_key_update(s, v->input+16, 16);
    Hacl_Streaming_Blake2_blake2s_32_no_key_update(s, v->input+32, v->input_len - 32);
    Hacl_Streaming_Blake2_blake2s_32_no_key_finish(s, tag);
    ok &= compare_and_print(32, tag, v->expected);

    Hacl_Streaming_Blake2_blake2s_32_no_key_free(s);

    if (ok)
        return EXIT_SUCCESS;
    else
        return EXIT_FAILURE;
}
