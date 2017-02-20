#include <stdlib.h>
#include <stdint.h>
#include <string.h> // memcmp
#include "Chacha20_goll.h"
#include "dut.h"
#include "random.h"

const uint8_t
key[32] =
    {
      (uint8_t )0,
      (uint8_t )1,
      (uint8_t )2,
      (uint8_t )3,
      (uint8_t )4,
      (uint8_t )5,
      (uint8_t )6,
      (uint8_t )7,
      (uint8_t )8,
      (uint8_t )9,
      (uint8_t )10,
      (uint8_t )11,
      (uint8_t )12,
      (uint8_t )13,
      (uint8_t )14,
      (uint8_t )15,
      (uint8_t )16,
      (uint8_t )17,
      (uint8_t )18,
      (uint8_t )19,
      (uint8_t )20,
      (uint8_t )21,
      (uint8_t )22,
      (uint8_t )23,
      (uint8_t )24,
      (uint8_t )25,
      (uint8_t )26,
      (uint8_t )27,
      (uint8_t )28,
      (uint8_t )29,
      (uint8_t )30,
      (uint8_t )31
    };
const uint8_t
nonce[12] =
    {
      (uint8_t )0,
      (uint8_t )0,
      (uint8_t )0,
      (uint8_t )0,
      (uint8_t )0,
      (uint8_t )0,
      (uint8_t )0,
      (uint8_t )0x4a,
      (uint8_t )0,
      (uint8_t )0,
      (uint8_t )0,
      (uint8_t )0
    };

const size_t chunk_size = 16;
const size_t number_measurements = 1e6; // per test
static uint32_t ctx[32] = { 0 };

uint8_t do_one_computation(uint8_t *data) {
  uint8_t in[16] = {0};
  uint8_t out[16] = {0};
  uint8_t ret = 0;

  memcpy(in, data, 16);

  // chain some encryptions
  for (int i = 0; i < 30; i++) {
    crypto_stream_xor(out,in,16,nonce,key);
    memcpy(in, out, 16);
  }

  ret ^= out[0];
  return ret;
}

void init_dut(void) {
  return;
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
