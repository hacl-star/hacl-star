#include <stdlib.h>
#include <stdint.h>
#include <string.h> // memcmp
#include "dut.h"
#include "random.h"
#include "api.h"
#include "crypto_stream_aes128ctr.h"


const size_t chunk_size = 16;
const size_t number_measurements = 1e4; // per test

uint8_t do_one_computation(uint8_t *data) {
  uint8_t in[16] = {0};
  uint8_t out[16] = {0};
  uint8_t key[16] = {0x01,0};
  uint8_t ret = 0;

  memcpy(in, data, 16);
  crypto_stream(out, 16, in, key);
  ret ^= out[0];
  return ret;
}

void init_dut(void) {
}

void prepare_inputs(uint8_t *input_data, uint8_t *classes) {
  randombytes(input_data, number_measurements * chunk_size);
  for (size_t i = 0; i < number_measurements; i++) {
    classes[i] = randombit();
    if (classes[i] == 0) {
      memset(input_data + (size_t)i * chunk_size, 0x00, chunk_size);
    } else {
      // leave random
    }
  }
}
