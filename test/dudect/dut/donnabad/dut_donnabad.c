#include <stdlib.h>
#include <stdint.h>
#include <stdio.h>
#include <string.h> // memcmp
#include "dut.h"
#include "random.h"
#include "donna.h"

const size_t chunk_size = 32;
const size_t number_measurements = 1e3; // per test

uint8_t do_one_computation(uint8_t *data) {
  uint8_t out[32] = {0};
  const uint8_t secret[32] = {1,2,3};
  uint8_t ret = 0;
  const uint8_t basepoint[32] = {9};
  curve25519_donna(out, data, basepoint); memcpy(data, out, 32);
  curve25519_donna(out, data, basepoint); memcpy(data, out, 32);
  curve25519_donna(out, data, basepoint); memcpy(data, out, 32);
  curve25519_donna(out, data, basepoint); memcpy(data, out, 32);
  curve25519_donna(out, data, basepoint); memcpy(data, out, 32);
  curve25519_donna(out, data, basepoint); memcpy(data, out, 32);
  curve25519_donna(out, data, basepoint); memcpy(data, out, 32);
  curve25519_donna(out, data, basepoint); memcpy(data, out, 32);
  curve25519_donna(out, data, basepoint); memcpy(data, out, 32);
  ret ^= out[0];
  return ret;
}

void init_dut(void) {}

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
