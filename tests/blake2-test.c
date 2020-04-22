#include <inttypes.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/types.h>
#include <sys/stat.h>
#include <fcntl.h>
#include <unistd.h>
#include <time.h>
#include <stdbool.h>
#include "Hacl_Blake2s_32.h"
#include "Hacl_Blake2b_32.h"
#include "Hacl_Blake2s_128.h"
#include "Hacl_Blake2b_256.h"

typedef uint64_t cycles;

static __inline__ cycles cpucycles_begin(void)
{
  uint64_t rax,rdx,aux;
  asm volatile ( "rdtscp\n" : "=a" (rax), "=d" (rdx), "=c" (aux) : : );
  return (rdx << 32) + rax;
}

static __inline__ cycles cpucycles_end(void)
{
  uint64_t rax,rdx,aux;
  asm volatile ( "rdtscp\n" : "=a" (rax), "=d" (rdx), "=c" (aux) : : );
  return (rdx << 32) + rax;
}


uint32_t blake2b_test1_size_plaintext = (uint32_t)44U;

uint8_t
blake2b_test1_plaintext[44U] =
  {
    (uint8_t)0x00U, (uint8_t)0x01U, (uint8_t)0x02U, (uint8_t)0x03U, (uint8_t)0x04U, (uint8_t)0x05U,
    (uint8_t)0x06U, (uint8_t)0x07U, (uint8_t)0x08U, (uint8_t)0x09U, (uint8_t)0x0aU, (uint8_t)0x0bU,
    (uint8_t)0x0cU, (uint8_t)0x0dU, (uint8_t)0x0eU, (uint8_t)0x0fU, (uint8_t)0x10U, (uint8_t)0x11U,
    (uint8_t)0x12U, (uint8_t)0x13U, (uint8_t)0x14U, (uint8_t)0x15U, (uint8_t)0x16U, (uint8_t)0x17U,
    (uint8_t)0x18U, (uint8_t)0x19U, (uint8_t)0x1aU, (uint8_t)0x1bU, (uint8_t)0x1cU, (uint8_t)0x1dU,
    (uint8_t)0x1eU, (uint8_t)0x1fU, (uint8_t)0x20U, (uint8_t)0x21U, (uint8_t)0x22U, (uint8_t)0x23U,
    (uint8_t)0x24U, (uint8_t)0x25U, (uint8_t)0x26U, (uint8_t)0x27U, (uint8_t)0x28U, (uint8_t)0x29U,
    (uint8_t)0x2aU, (uint8_t)0x2bU
  };

uint32_t blake2b_test1_size_key = (uint32_t)64U;

uint8_t
blake2b_test1_key[64U] =
  {
    (uint8_t)0x00U, (uint8_t)0x01U, (uint8_t)0x02U, (uint8_t)0x03U, (uint8_t)0x04U, (uint8_t)0x05U,
    (uint8_t)0x06U, (uint8_t)0x07U, (uint8_t)0x08U, (uint8_t)0x09U, (uint8_t)0x0aU, (uint8_t)0x0bU,
    (uint8_t)0x0cU, (uint8_t)0x0dU, (uint8_t)0x0eU, (uint8_t)0x0fU, (uint8_t)0x10U, (uint8_t)0x11U,
    (uint8_t)0x12U, (uint8_t)0x13U, (uint8_t)0x14U, (uint8_t)0x15U, (uint8_t)0x16U, (uint8_t)0x17U,
    (uint8_t)0x18U, (uint8_t)0x19U, (uint8_t)0x1aU, (uint8_t)0x1bU, (uint8_t)0x1cU, (uint8_t)0x1dU,
    (uint8_t)0x1eU, (uint8_t)0x1fU, (uint8_t)0x20U, (uint8_t)0x21U, (uint8_t)0x22U, (uint8_t)0x23U,
    (uint8_t)0x24U, (uint8_t)0x25U, (uint8_t)0x26U, (uint8_t)0x27U, (uint8_t)0x28U, (uint8_t)0x29U,
    (uint8_t)0x2aU, (uint8_t)0x2bU, (uint8_t)0x2cU, (uint8_t)0x2dU, (uint8_t)0x2eU, (uint8_t)0x2fU,
    (uint8_t)0x30U, (uint8_t)0x31U, (uint8_t)0x32U, (uint8_t)0x33U, (uint8_t)0x34U, (uint8_t)0x35U,
    (uint8_t)0x36U, (uint8_t)0x37U, (uint8_t)0x38U, (uint8_t)0x39U, (uint8_t)0x3aU, (uint8_t)0x3bU,
    (uint8_t)0x3cU, (uint8_t)0x3dU, (uint8_t)0x3eU, (uint8_t)0x3fU
  };

uint32_t blake2b_test1_size_expected = (uint32_t)64U;

uint8_t
blake2b_test1_expected[64U] =
  {
    (uint8_t)0xc8U, (uint8_t)0xf6U, (uint8_t)0x8eU, (uint8_t)0x69U, (uint8_t)0x6eU, (uint8_t)0xd2U,
    (uint8_t)0x82U, (uint8_t)0x42U, (uint8_t)0xbfU, (uint8_t)0x99U, (uint8_t)0x7fU, (uint8_t)0x5bU,
    (uint8_t)0x3bU, (uint8_t)0x34U, (uint8_t)0x95U, (uint8_t)0x95U, (uint8_t)0x08U, (uint8_t)0xe4U,
    (uint8_t)0x2dU, (uint8_t)0x61U, (uint8_t)0x38U, (uint8_t)0x10U, (uint8_t)0xf1U, (uint8_t)0xe2U,
    (uint8_t)0xa4U, (uint8_t)0x35U, (uint8_t)0xc9U, (uint8_t)0x6eU, (uint8_t)0xd2U, (uint8_t)0xffU,
    (uint8_t)0x56U, (uint8_t)0x0cU, (uint8_t)0x70U, (uint8_t)0x22U, (uint8_t)0xf3U, (uint8_t)0x61U,
    (uint8_t)0xa9U, (uint8_t)0x23U, (uint8_t)0x4bU, (uint8_t)0x98U, (uint8_t)0x37U, (uint8_t)0xfeU,
    (uint8_t)0xeeU, (uint8_t)0x90U, (uint8_t)0xbfU, (uint8_t)0x47U, (uint8_t)0x92U, (uint8_t)0x2eU,
    (uint8_t)0xe0U, (uint8_t)0xfdU, (uint8_t)0x5fU, (uint8_t)0x8dU, (uint8_t)0xdfU, (uint8_t)0x82U,
    (uint8_t)0x37U, (uint8_t)0x18U, (uint8_t)0xd8U, (uint8_t)0x6dU, (uint8_t)0x1eU, (uint8_t)0x16U,
    (uint8_t)0xc6U, (uint8_t)0x09U, (uint8_t)0x00U, (uint8_t)0x71U
  };


uint32_t blake2s_test1_size_plaintext = (uint32_t)3U;

uint8_t
blake2s_test1_plaintext[3U] = { (uint8_t)0x61U, (uint8_t)0x62U, (uint8_t)0x63U };

uint32_t blake2s_test1_size_key = (uint32_t)0U;

uint8_t blake2s_test1_key[0U] = {  };

uint32_t blake2s_test1_size_expected = (uint32_t)32U;

uint8_t
blake2s_test1_expected[32U] =
  {
    (uint8_t)0x50U, (uint8_t)0x8CU, (uint8_t)0x5EU, (uint8_t)0x8CU, (uint8_t)0x32U, (uint8_t)0x7CU,
    (uint8_t)0x14U, (uint8_t)0xE2U, (uint8_t)0xE1U, (uint8_t)0xA7U, (uint8_t)0x2BU, (uint8_t)0xA3U,
    (uint8_t)0x4EU, (uint8_t)0xEBU, (uint8_t)0x45U, (uint8_t)0x2FU, (uint8_t)0x37U, (uint8_t)0x45U,
    (uint8_t)0x8BU, (uint8_t)0x20U, (uint8_t)0x9EU, (uint8_t)0xD6U, (uint8_t)0x3AU, (uint8_t)0x29U,
    (uint8_t)0x4DU, (uint8_t)0x99U, (uint8_t)0x9BU, (uint8_t)0x4CU, (uint8_t)0x86U, (uint8_t)0x67U,
    (uint8_t)0x59U, (uint8_t)0x82U
  };

uint32_t blake2s_test2_size_plaintext = (uint32_t)1U;

uint8_t blake2s_test2_plaintext[1U] = { (uint8_t)0x00U };

uint32_t blake2s_test2_size_key = (uint32_t)32U;

uint8_t
blake2s_test2_key[32U] =
  {
    (uint8_t)0x00U, (uint8_t)0x01U, (uint8_t)0x02U, (uint8_t)0x03U, (uint8_t)0x04U, (uint8_t)0x05U,
    (uint8_t)0x06U, (uint8_t)0x07U, (uint8_t)0x08U, (uint8_t)0x09U, (uint8_t)0x0aU, (uint8_t)0x0bU,
    (uint8_t)0x0cU, (uint8_t)0x0dU, (uint8_t)0x0eU, (uint8_t)0x0fU, (uint8_t)0x10U, (uint8_t)0x11U,
    (uint8_t)0x12U, (uint8_t)0x13U, (uint8_t)0x14U, (uint8_t)0x15U, (uint8_t)0x16U, (uint8_t)0x17U,
    (uint8_t)0x18U, (uint8_t)0x19U, (uint8_t)0x1aU, (uint8_t)0x1bU, (uint8_t)0x1cU, (uint8_t)0x1dU,
    (uint8_t)0x1eU, (uint8_t)0x1fU
  };

uint32_t blake2s_test2_size_expected = (uint32_t)32U;

uint8_t
blake2s_test2_expected[32U] =
  {
    (uint8_t)0x40U, (uint8_t)0xd1U, (uint8_t)0x5fU, (uint8_t)0xeeU, (uint8_t)0x7cU, (uint8_t)0x32U,
    (uint8_t)0x88U, (uint8_t)0x30U, (uint8_t)0x16U, (uint8_t)0x6aU, (uint8_t)0xc3U, (uint8_t)0xf9U,
    (uint8_t)0x18U, (uint8_t)0x65U, (uint8_t)0x0fU, (uint8_t)0x80U, (uint8_t)0x7eU, (uint8_t)0x7eU,
    (uint8_t)0x01U, (uint8_t)0xe1U, (uint8_t)0x77U, (uint8_t)0x25U, (uint8_t)0x8cU, (uint8_t)0xdcU,
    (uint8_t)0x0aU, (uint8_t)0x39U, (uint8_t)0xb1U, (uint8_t)0x1fU, (uint8_t)0x59U, (uint8_t)0x80U,
    (uint8_t)0x66U, (uint8_t)0xf1U
  };

uint32_t blake2s_test3_size_plaintext = (uint32_t)255U;

uint8_t
blake2s_test3_plaintext[255U] =
  {
    (uint8_t)0x00U, (uint8_t)0x01U, (uint8_t)0x02U, (uint8_t)0x03U, (uint8_t)0x04U, (uint8_t)0x05U,
    (uint8_t)0x06U, (uint8_t)0x07U, (uint8_t)0x08U, (uint8_t)0x09U, (uint8_t)0x0aU, (uint8_t)0x0bU,
    (uint8_t)0x0cU, (uint8_t)0x0dU, (uint8_t)0x0eU, (uint8_t)0x0fU, (uint8_t)0x10U, (uint8_t)0x11U,
    (uint8_t)0x12U, (uint8_t)0x13U, (uint8_t)0x14U, (uint8_t)0x15U, (uint8_t)0x16U, (uint8_t)0x17U,
    (uint8_t)0x18U, (uint8_t)0x19U, (uint8_t)0x1aU, (uint8_t)0x1bU, (uint8_t)0x1cU, (uint8_t)0x1dU,
    (uint8_t)0x1eU, (uint8_t)0x1fU, (uint8_t)0x20U, (uint8_t)0x21U, (uint8_t)0x22U, (uint8_t)0x23U,
    (uint8_t)0x24U, (uint8_t)0x25U, (uint8_t)0x26U, (uint8_t)0x27U, (uint8_t)0x28U, (uint8_t)0x29U,
    (uint8_t)0x2aU, (uint8_t)0x2bU, (uint8_t)0x2cU, (uint8_t)0x2dU, (uint8_t)0x2eU, (uint8_t)0x2fU,
    (uint8_t)0x30U, (uint8_t)0x31U, (uint8_t)0x32U, (uint8_t)0x33U, (uint8_t)0x34U, (uint8_t)0x35U,
    (uint8_t)0x36U, (uint8_t)0x37U, (uint8_t)0x38U, (uint8_t)0x39U, (uint8_t)0x3aU, (uint8_t)0x3bU,
    (uint8_t)0x3cU, (uint8_t)0x3dU, (uint8_t)0x3eU, (uint8_t)0x3fU, (uint8_t)0x40U, (uint8_t)0x41U,
    (uint8_t)0x42U, (uint8_t)0x43U, (uint8_t)0x44U, (uint8_t)0x45U, (uint8_t)0x46U, (uint8_t)0x47U,
    (uint8_t)0x48U, (uint8_t)0x49U, (uint8_t)0x4aU, (uint8_t)0x4bU, (uint8_t)0x4cU, (uint8_t)0x4dU,
    (uint8_t)0x4eU, (uint8_t)0x4fU, (uint8_t)0x50U, (uint8_t)0x51U, (uint8_t)0x52U, (uint8_t)0x53U,
    (uint8_t)0x54U, (uint8_t)0x55U, (uint8_t)0x56U, (uint8_t)0x57U, (uint8_t)0x58U, (uint8_t)0x59U,
    (uint8_t)0x5aU, (uint8_t)0x5bU, (uint8_t)0x5cU, (uint8_t)0x5dU, (uint8_t)0x5eU, (uint8_t)0x5fU,
    (uint8_t)0x60U, (uint8_t)0x61U, (uint8_t)0x62U, (uint8_t)0x63U, (uint8_t)0x64U, (uint8_t)0x65U,
    (uint8_t)0x66U, (uint8_t)0x67U, (uint8_t)0x68U, (uint8_t)0x69U, (uint8_t)0x6aU, (uint8_t)0x6bU,
    (uint8_t)0x6cU, (uint8_t)0x6dU, (uint8_t)0x6eU, (uint8_t)0x6fU, (uint8_t)0x70U, (uint8_t)0x71U,
    (uint8_t)0x72U, (uint8_t)0x73U, (uint8_t)0x74U, (uint8_t)0x75U, (uint8_t)0x76U, (uint8_t)0x77U,
    (uint8_t)0x78U, (uint8_t)0x79U, (uint8_t)0x7aU, (uint8_t)0x7bU, (uint8_t)0x7cU, (uint8_t)0x7dU,
    (uint8_t)0x7eU, (uint8_t)0x7fU, (uint8_t)0x80U, (uint8_t)0x81U, (uint8_t)0x82U, (uint8_t)0x83U,
    (uint8_t)0x84U, (uint8_t)0x85U, (uint8_t)0x86U, (uint8_t)0x87U, (uint8_t)0x88U, (uint8_t)0x89U,
    (uint8_t)0x8aU, (uint8_t)0x8bU, (uint8_t)0x8cU, (uint8_t)0x8dU, (uint8_t)0x8eU, (uint8_t)0x8fU,
    (uint8_t)0x90U, (uint8_t)0x91U, (uint8_t)0x92U, (uint8_t)0x93U, (uint8_t)0x94U, (uint8_t)0x95U,
    (uint8_t)0x96U, (uint8_t)0x97U, (uint8_t)0x98U, (uint8_t)0x99U, (uint8_t)0x9aU, (uint8_t)0x9bU,
    (uint8_t)0x9cU, (uint8_t)0x9dU, (uint8_t)0x9eU, (uint8_t)0x9fU, (uint8_t)0xa0U, (uint8_t)0xa1U,
    (uint8_t)0xa2U, (uint8_t)0xa3U, (uint8_t)0xa4U, (uint8_t)0xa5U, (uint8_t)0xa6U, (uint8_t)0xa7U,
    (uint8_t)0xa8U, (uint8_t)0xa9U, (uint8_t)0xaaU, (uint8_t)0xabU, (uint8_t)0xacU, (uint8_t)0xadU,
    (uint8_t)0xaeU, (uint8_t)0xafU, (uint8_t)0xb0U, (uint8_t)0xb1U, (uint8_t)0xb2U, (uint8_t)0xb3U,
    (uint8_t)0xb4U, (uint8_t)0xb5U, (uint8_t)0xb6U, (uint8_t)0xb7U, (uint8_t)0xb8U, (uint8_t)0xb9U,
    (uint8_t)0xbaU, (uint8_t)0xbbU, (uint8_t)0xbcU, (uint8_t)0xbdU, (uint8_t)0xbeU, (uint8_t)0xbfU,
    (uint8_t)0xc0U, (uint8_t)0xc1U, (uint8_t)0xc2U, (uint8_t)0xc3U, (uint8_t)0xc4U, (uint8_t)0xc5U,
    (uint8_t)0xc6U, (uint8_t)0xc7U, (uint8_t)0xc8U, (uint8_t)0xc9U, (uint8_t)0xcaU, (uint8_t)0xcbU,
    (uint8_t)0xccU, (uint8_t)0xcdU, (uint8_t)0xceU, (uint8_t)0xcfU, (uint8_t)0xd0U, (uint8_t)0xd1U,
    (uint8_t)0xd2U, (uint8_t)0xd3U, (uint8_t)0xd4U, (uint8_t)0xd5U, (uint8_t)0xd6U, (uint8_t)0xd7U,
    (uint8_t)0xd8U, (uint8_t)0xd9U, (uint8_t)0xdaU, (uint8_t)0xdbU, (uint8_t)0xdcU, (uint8_t)0xddU,
    (uint8_t)0xdeU, (uint8_t)0xdfU, (uint8_t)0xe0U, (uint8_t)0xe1U, (uint8_t)0xe2U, (uint8_t)0xe3U,
    (uint8_t)0xe4U, (uint8_t)0xe5U, (uint8_t)0xe6U, (uint8_t)0xe7U, (uint8_t)0xe8U, (uint8_t)0xe9U,
    (uint8_t)0xeaU, (uint8_t)0xebU, (uint8_t)0xecU, (uint8_t)0xedU, (uint8_t)0xeeU, (uint8_t)0xefU,
    (uint8_t)0xf0U, (uint8_t)0xf1U, (uint8_t)0xf2U, (uint8_t)0xf3U, (uint8_t)0xf4U, (uint8_t)0xf5U,
    (uint8_t)0xf6U, (uint8_t)0xf7U, (uint8_t)0xf8U, (uint8_t)0xf9U, (uint8_t)0xfaU, (uint8_t)0xfbU,
    (uint8_t)0xfcU, (uint8_t)0xfdU, (uint8_t)0xfeU
  };

uint32_t blake2s_test3_size_key = (uint32_t)32U;

uint8_t
blake2s_test3_key[32U] =
  {
    (uint8_t)0x00U, (uint8_t)0x01U, (uint8_t)0x02U, (uint8_t)0x03U, (uint8_t)0x04U, (uint8_t)0x05U,
    (uint8_t)0x06U, (uint8_t)0x07U, (uint8_t)0x08U, (uint8_t)0x09U, (uint8_t)0x0aU, (uint8_t)0x0bU,
    (uint8_t)0x0cU, (uint8_t)0x0dU, (uint8_t)0x0eU, (uint8_t)0x0fU, (uint8_t)0x10U, (uint8_t)0x11U,
    (uint8_t)0x12U, (uint8_t)0x13U, (uint8_t)0x14U, (uint8_t)0x15U, (uint8_t)0x16U, (uint8_t)0x17U,
    (uint8_t)0x18U, (uint8_t)0x19U, (uint8_t)0x1aU, (uint8_t)0x1bU, (uint8_t)0x1cU, (uint8_t)0x1dU,
    (uint8_t)0x1eU, (uint8_t)0x1fU
  };

uint32_t blake2s_test3_size_expected = (uint32_t)32U;

uint8_t
blake2s_test3_expected[32U] =
  {
    (uint8_t)0x3fU, (uint8_t)0xb7U, (uint8_t)0x35U, (uint8_t)0x06U, (uint8_t)0x1aU, (uint8_t)0xbcU,
    (uint8_t)0x51U, (uint8_t)0x9dU, (uint8_t)0xfeU, (uint8_t)0x97U, (uint8_t)0x9eU, (uint8_t)0x54U,
    (uint8_t)0xc1U, (uint8_t)0xeeU, (uint8_t)0x5bU, (uint8_t)0xfaU, (uint8_t)0xd0U, (uint8_t)0xa9U,
    (uint8_t)0xd8U, (uint8_t)0x58U, (uint8_t)0xb3U, (uint8_t)0x31U, (uint8_t)0x5bU, (uint8_t)0xadU,
    (uint8_t)0x34U, (uint8_t)0xbdU, (uint8_t)0xe9U, (uint8_t)0x99U, (uint8_t)0xefU, (uint8_t)0xd7U,
    (uint8_t)0x24U, (uint8_t)0xddU
  };

uint32_t blake2s_test4_size_plaintext = (uint32_t)251U;

uint8_t
blake2s_test4_plaintext[251U] =
  {
    (uint8_t)0x00U, (uint8_t)0x01U, (uint8_t)0x02U, (uint8_t)0x03U, (uint8_t)0x04U, (uint8_t)0x05U,
    (uint8_t)0x06U, (uint8_t)0x07U, (uint8_t)0x08U, (uint8_t)0x09U, (uint8_t)0x0aU, (uint8_t)0x0bU,
    (uint8_t)0x0cU, (uint8_t)0x0dU, (uint8_t)0x0eU, (uint8_t)0x0fU, (uint8_t)0x10U, (uint8_t)0x11U,
    (uint8_t)0x12U, (uint8_t)0x13U, (uint8_t)0x14U, (uint8_t)0x15U, (uint8_t)0x16U, (uint8_t)0x17U,
    (uint8_t)0x18U, (uint8_t)0x19U, (uint8_t)0x1aU, (uint8_t)0x1bU, (uint8_t)0x1cU, (uint8_t)0x1dU,
    (uint8_t)0x1eU, (uint8_t)0x1fU, (uint8_t)0x20U, (uint8_t)0x21U, (uint8_t)0x22U, (uint8_t)0x23U,
    (uint8_t)0x24U, (uint8_t)0x25U, (uint8_t)0x26U, (uint8_t)0x27U, (uint8_t)0x28U, (uint8_t)0x29U,
    (uint8_t)0x2aU, (uint8_t)0x2bU, (uint8_t)0x2cU, (uint8_t)0x2dU, (uint8_t)0x2eU, (uint8_t)0x2fU,
    (uint8_t)0x30U, (uint8_t)0x31U, (uint8_t)0x32U, (uint8_t)0x33U, (uint8_t)0x34U, (uint8_t)0x35U,
    (uint8_t)0x36U, (uint8_t)0x37U, (uint8_t)0x38U, (uint8_t)0x39U, (uint8_t)0x3aU, (uint8_t)0x3bU,
    (uint8_t)0x3cU, (uint8_t)0x3dU, (uint8_t)0x3eU, (uint8_t)0x3fU, (uint8_t)0x40U, (uint8_t)0x41U,
    (uint8_t)0x42U, (uint8_t)0x43U, (uint8_t)0x44U, (uint8_t)0x45U, (uint8_t)0x46U, (uint8_t)0x47U,
    (uint8_t)0x48U, (uint8_t)0x49U, (uint8_t)0x4aU, (uint8_t)0x4bU, (uint8_t)0x4cU, (uint8_t)0x4dU,
    (uint8_t)0x4eU, (uint8_t)0x4fU, (uint8_t)0x50U, (uint8_t)0x51U, (uint8_t)0x52U, (uint8_t)0x53U,
    (uint8_t)0x54U, (uint8_t)0x55U, (uint8_t)0x56U, (uint8_t)0x57U, (uint8_t)0x58U, (uint8_t)0x59U,
    (uint8_t)0x5aU, (uint8_t)0x5bU, (uint8_t)0x5cU, (uint8_t)0x5dU, (uint8_t)0x5eU, (uint8_t)0x5fU,
    (uint8_t)0x60U, (uint8_t)0x61U, (uint8_t)0x62U, (uint8_t)0x63U, (uint8_t)0x64U, (uint8_t)0x65U,
    (uint8_t)0x66U, (uint8_t)0x67U, (uint8_t)0x68U, (uint8_t)0x69U, (uint8_t)0x6aU, (uint8_t)0x6bU,
    (uint8_t)0x6cU, (uint8_t)0x6dU, (uint8_t)0x6eU, (uint8_t)0x6fU, (uint8_t)0x70U, (uint8_t)0x71U,
    (uint8_t)0x72U, (uint8_t)0x73U, (uint8_t)0x74U, (uint8_t)0x75U, (uint8_t)0x76U, (uint8_t)0x77U,
    (uint8_t)0x78U, (uint8_t)0x79U, (uint8_t)0x7aU, (uint8_t)0x7bU, (uint8_t)0x7cU, (uint8_t)0x7dU,
    (uint8_t)0x7eU, (uint8_t)0x7fU, (uint8_t)0x80U, (uint8_t)0x81U, (uint8_t)0x82U, (uint8_t)0x83U,
    (uint8_t)0x84U, (uint8_t)0x85U, (uint8_t)0x86U, (uint8_t)0x87U, (uint8_t)0x88U, (uint8_t)0x89U,
    (uint8_t)0x8aU, (uint8_t)0x8bU, (uint8_t)0x8cU, (uint8_t)0x8dU, (uint8_t)0x8eU, (uint8_t)0x8fU,
    (uint8_t)0x90U, (uint8_t)0x91U, (uint8_t)0x92U, (uint8_t)0x93U, (uint8_t)0x94U, (uint8_t)0x95U,
    (uint8_t)0x96U, (uint8_t)0x97U, (uint8_t)0x98U, (uint8_t)0x99U, (uint8_t)0x9aU, (uint8_t)0x9bU,
    (uint8_t)0x9cU, (uint8_t)0x9dU, (uint8_t)0x9eU, (uint8_t)0x9fU, (uint8_t)0xa0U, (uint8_t)0xa1U,
    (uint8_t)0xa2U, (uint8_t)0xa3U, (uint8_t)0xa4U, (uint8_t)0xa5U, (uint8_t)0xa6U, (uint8_t)0xa7U,
    (uint8_t)0xa8U, (uint8_t)0xa9U, (uint8_t)0xaaU, (uint8_t)0xabU, (uint8_t)0xacU, (uint8_t)0xadU,
    (uint8_t)0xaeU, (uint8_t)0xafU, (uint8_t)0xb0U, (uint8_t)0xb1U, (uint8_t)0xb2U, (uint8_t)0xb3U,
    (uint8_t)0xb4U, (uint8_t)0xb5U, (uint8_t)0xb6U, (uint8_t)0xb7U, (uint8_t)0xb8U, (uint8_t)0xb9U,
    (uint8_t)0xbaU, (uint8_t)0xbbU, (uint8_t)0xbcU, (uint8_t)0xbdU, (uint8_t)0xbeU, (uint8_t)0xbfU,
    (uint8_t)0xc0U, (uint8_t)0xc1U, (uint8_t)0xc2U, (uint8_t)0xc3U, (uint8_t)0xc4U, (uint8_t)0xc5U,
    (uint8_t)0xc6U, (uint8_t)0xc7U, (uint8_t)0xc8U, (uint8_t)0xc9U, (uint8_t)0xcaU, (uint8_t)0xcbU,
    (uint8_t)0xccU, (uint8_t)0xcdU, (uint8_t)0xceU, (uint8_t)0xcfU, (uint8_t)0xd0U, (uint8_t)0xd1U,
    (uint8_t)0xd2U, (uint8_t)0xd3U, (uint8_t)0xd4U, (uint8_t)0xd5U, (uint8_t)0xd6U, (uint8_t)0xd7U,
    (uint8_t)0xd8U, (uint8_t)0xd9U, (uint8_t)0xdaU, (uint8_t)0xdbU, (uint8_t)0xdcU, (uint8_t)0xddU,
    (uint8_t)0xdeU, (uint8_t)0xdfU, (uint8_t)0xe0U, (uint8_t)0xe1U, (uint8_t)0xe2U, (uint8_t)0xe3U,
    (uint8_t)0xe4U, (uint8_t)0xe5U, (uint8_t)0xe6U, (uint8_t)0xe7U, (uint8_t)0xe8U, (uint8_t)0xe9U,
    (uint8_t)0xeaU, (uint8_t)0xebU, (uint8_t)0xecU, (uint8_t)0xedU, (uint8_t)0xeeU, (uint8_t)0xefU,
    (uint8_t)0xf0U, (uint8_t)0xf1U, (uint8_t)0xf2U, (uint8_t)0xf3U, (uint8_t)0xf4U, (uint8_t)0xf5U,
    (uint8_t)0xf6U, (uint8_t)0xf7U, (uint8_t)0xf8U, (uint8_t)0xf9U, (uint8_t)0xfaU
  };

uint32_t blake2s_test4_size_key = (uint32_t)32U;

uint8_t
blake2s_test4_key[32U] =
  {
    (uint8_t)0x00U, (uint8_t)0x01U, (uint8_t)0x02U, (uint8_t)0x03U, (uint8_t)0x04U, (uint8_t)0x05U,
    (uint8_t)0x06U, (uint8_t)0x07U, (uint8_t)0x08U, (uint8_t)0x09U, (uint8_t)0x0aU, (uint8_t)0x0bU,
    (uint8_t)0x0cU, (uint8_t)0x0dU, (uint8_t)0x0eU, (uint8_t)0x0fU, (uint8_t)0x10U, (uint8_t)0x11U,
    (uint8_t)0x12U, (uint8_t)0x13U, (uint8_t)0x14U, (uint8_t)0x15U, (uint8_t)0x16U, (uint8_t)0x17U,
    (uint8_t)0x18U, (uint8_t)0x19U, (uint8_t)0x1aU, (uint8_t)0x1bU, (uint8_t)0x1cU, (uint8_t)0x1dU,
    (uint8_t)0x1eU, (uint8_t)0x1fU
  };

uint32_t blake2s_test4_size_expected = (uint32_t)32U;

uint8_t
blake2s_test4_expected[32U] =
  {
    (uint8_t)0xd1U, (uint8_t)0x2bU, (uint8_t)0xf3U, (uint8_t)0x73U, (uint8_t)0x2eU, (uint8_t)0xf4U,
    (uint8_t)0xafU, (uint8_t)0x5cU, (uint8_t)0x22U, (uint8_t)0xfaU, (uint8_t)0x90U, (uint8_t)0x35U,
    (uint8_t)0x6aU, (uint8_t)0xf8U, (uint8_t)0xfcU, (uint8_t)0x50U, (uint8_t)0xfcU, (uint8_t)0xb4U,
    (uint8_t)0x0fU, (uint8_t)0x8fU, (uint8_t)0x2eU, (uint8_t)0xa5U, (uint8_t)0xc8U, (uint8_t)0x59U,
    (uint8_t)0x47U, (uint8_t)0x37U, (uint8_t)0xa3U, (uint8_t)0xb3U, (uint8_t)0xd5U, (uint8_t)0xabU,
    (uint8_t)0xdbU, (uint8_t)0xd7U
  };

uint32_t blake2s_test8_size_plaintext = (uint32_t)64U;

uint8_t blake2s_test8_plaintext[64] = {
  0x00U,  0x01U,  0x02U,  0x03U,  0x04U,  0x05U,  0x06U,  0x07U,  0x08U,  0x09U, 
  0x0AU,  0x0BU,  0x0CU,  0x0DU,  0x0EU,  0x0FU,  0x10U,  0x11U,  0x12U,  0x13U, 
  0x14U,  0x15U,  0x16U,  0x17U,  0x18U,  0x19U,  0x1AU,  0x1BU,  0x1CU,  0x1DU, 
  0x1EU,  0x1FU,  0x20U,  0x21U,  0x22U,  0x23U,  0x24U,  0x25U,  0x26U,  0x27U, 
  0x28U,  0x29U,  0x2AU,  0x2BU,  0x2CU,  0x2DU,  0x2EU,  0x2FU,  0x30U,  0x31U, 
  0x32U,  0x33U,  0x34U,  0x35U,  0x36U,  0x37U,  0x38U,  0x39U,  0x3AU,  0x3BU, 
  0x3CU,  0x3DU,  0x3EU,  0x3FU};

uint32_t blake2s_test8_size_key = (uint32_t)32U;

uint8_t blake2s_test8_key[32] = {
  0x00U,  0x01U,  0x02U,  0x03U,  0x04U,  0x05U,  0x06U,  0x07U,  0x08U,  0x09U, 
  0x0AU,  0x0BU,  0x0CU,  0x0DU,  0x0EU,  0x0FU,  0x10U,  0x11U,  0x12U,  0x13U, 
  0x14U,  0x15U,  0x16U,  0x17U,  0x18U,  0x19U,  0x1AU,  0x1BU,  0x1CU,  0x1DU, 
  0x1EU,  0x1FU};

uint32_t blake2s_test8_size_expected = (uint32_t)32U;

uint8_t blake2s_test8_expected[32] = {
  0x89U,  0x75U,  0xB0U,  0x57U,  0x7FU,  0xD3U,  0x55U,  0x66U,  0xD7U,  0x50U, 
  0xB3U,  0x62U,  0xB0U,  0x89U,  0x7AU,  0x26U,  0xC3U,  0x99U,  0x13U,  0x6DU, 
  0xF0U,  0x7BU,  0xABU,  0xABU,  0xBDU,  0xE6U,  0x20U,  0x3FU,  0xF2U,  0x95U, 
  0x4EU,  0xD4U };

uint32_t blake2b_test13_size_plaintext = (uint32_t)128U;

uint8_t blake2b_test13_plaintext[128] = {
  0x00U,  0x01U,  0x02U,  0x03U,  0x04U,  0x05U,  0x06U,  0x07U,  0x08U,  0x09U, 
  0x0AU,  0x0BU,  0x0CU,  0x0DU,  0x0EU,  0x0FU,  0x10U,  0x11U,  0x12U,  0x13U, 
  0x14U,  0x15U,  0x16U,  0x17U,  0x18U,  0x19U,  0x1AU,  0x1BU,  0x1CU,  0x1DU, 
  0x1EU,  0x1FU,  0x20U,  0x21U,  0x22U,  0x23U,  0x24U,  0x25U,  0x26U,  0x27U, 
  0x28U,  0x29U,  0x2AU,  0x2BU,  0x2CU,  0x2DU,  0x2EU,  0x2FU,  0x30U,  0x31U, 
  0x32U,  0x33U,  0x34U,  0x35U,  0x36U,  0x37U,  0x38U,  0x39U,  0x3AU,  0x3BU, 
  0x3CU,  0x3DU,  0x3EU,  0x3FU,  0x40U,  0x41U,  0x42U,  0x43U,  0x44U,  0x45U, 
  0x46U,  0x47U,  0x48U,  0x49U,  0x4AU,  0x4BU,  0x4CU,  0x4DU,  0x4EU,  0x4FU, 
  0x50U,  0x51U,  0x52U,  0x53U,  0x54U,  0x55U,  0x56U,  0x57U,  0x58U,  0x59U, 
  0x5AU,  0x5BU,  0x5CU,  0x5DU,  0x5EU,  0x5FU,  0x60U,  0x61U,  0x62U,  0x63U, 
  0x64U,  0x65U,  0x66U,  0x67U,  0x68U,  0x69U,  0x6AU,  0x6BU,  0x6CU,  0x6DU, 
  0x6EU,  0x6FU,  0x70U,  0x71U,  0x72U,  0x73U,  0x74U,  0x75U,  0x76U,  0x77U, 
  0x78U,  0x79U,  0x7AU,  0x7BU,  0x7CU,  0x7DU,  0x7EU,  0x7FU };

uint32_t blake2b_test13_size_key = (uint32_t)64U;
uint8_t blake2b_test13_key[64] = {
  0x00U,  0x01U,  0x02U,  0x03U,  0x04U,  0x05U,  0x06U,  0x07U,  0x08U,  0x09U, 
  0x0AU,  0x0BU,  0x0CU,  0x0DU,  0x0EU,  0x0FU,  0x10U,  0x11U,  0x12U,  0x13U, 
  0x14U,  0x15U,  0x16U,  0x17U,  0x18U,  0x19U,  0x1AU,  0x1BU,  0x1CU,  0x1DU, 
  0x1EU,  0x1FU,  0x20U,  0x21U,  0x22U,  0x23U,  0x24U,  0x25U,  0x26U,  0x27U, 
  0x28U,  0x29U,  0x2AU,  0x2BU,  0x2CU,  0x2DU,  0x2EU,  0x2FU,  0x30U,  0x31U, 
  0x32U,  0x33U,  0x34U,  0x35U,  0x36U,  0x37U,  0x38U,  0x39U,  0x3AU,  0x3BU, 
  0x3CU,  0x3DU,  0x3EU,  0x3FU};

uint32_t blake2b_test13_size_expected = (uint32_t)64U;

uint8_t blake2b_test13_expected[64] = {
  0x72U,  0x06U,  0x5EU,  0xE4U,  0xDDU,  0x91U,  0xC2U,  0xD8U,  0x50U,  0x9FU, 
  0xA1U,  0xFCU,  0x28U,  0xA3U,  0x7CU,  0x7FU,  0xC9U,  0xFAU,  0x7DU,  0x5BU, 
  0x3FU,  0x8AU,  0xD3U,  0xD0U,  0xD7U,  0xA2U,  0x56U,  0x26U,  0xB5U,  0x7BU, 
  0x1BU,  0x44U,  0x78U,  0x8DU,  0x4CU,  0xAFU,  0x80U,  0x62U,  0x90U,  0x42U, 
  0x5FU,  0x98U,  0x90U,  0xA3U,  0xA2U,  0xA3U,  0x5AU,  0x90U,  0x5AU,  0xB4U, 
  0xB3U,  0x7AU,  0xCFU,  0xD0U,  0xDAU,  0x6EU,  0x45U,  0x17U,  0xB2U,  0x52U, 
  0x5CU,  0x96U,  0x51U,  0xE4U};

#define ROUNDS 16384
#define SIZE   8196

int main()
{
  uint8_t comp_s[64] = {0};
  uint8_t comp_b[64] = {0};
  bool all_ok = true;
  bool ok = true;

  printf("testing blake2s vec-32:\n");
  Hacl_Blake2s_32_blake2s(32,comp_s,blake2s_test4_size_plaintext,blake2s_test4_plaintext,blake2s_test4_size_key,blake2s_test4_key);
  printf("computed:");
  for (int i = 0; i < 32; i++)
    printf("%02x",comp_s[i]);
  printf("\n");
  printf("expected:");
  for (int i = 0; i < 32; i++)
    printf("%02x",blake2s_test4_expected[i]);
  printf("\n");
  ok = true;
  for (int i = 0; i < 32; i++)
    ok = ok & (blake2s_test4_expected[i] == comp_s[i]);
  if (ok) printf("Success!\n");
  else printf("FAILED!\n");
  all_ok = all_ok && ok;

  Hacl_Blake2s_32_blake2s(32,comp_s,blake2s_test8_size_plaintext,blake2s_test8_plaintext,blake2s_test8_size_key,blake2s_test8_key);
  printf("computed:");
  for (int i = 0; i < 32; i++)
    printf("%02x",comp_s[i]);
  printf("\n");
  printf("expected:");
  for (int i = 0; i < 32; i++)
    printf("%02x",blake2s_test8_expected[i]);
  printf("\n");
  ok = true;
  for (int i = 0; i < 32; i++)
    ok = ok & (blake2s_test8_expected[i] == comp_s[i]);
  if (ok) printf("Success!\n");
  else printf("FAILED!\n");
  all_ok = all_ok && ok;

  printf("testing blake2s vec-128:\n");
  Hacl_Blake2s_128_blake2s(32,comp_s,blake2s_test4_size_plaintext,blake2s_test4_plaintext,blake2s_test4_size_key,blake2s_test4_key);
  printf("computed:");
  for (int i = 0; i < 32; i++)
    printf("%02x",comp_s[i]);
  printf("\n");
  printf("expected:");
  for (int i = 0; i < 32; i++)
    printf("%02x",blake2s_test4_expected[i]);
  printf("\n");
  ok = true;
  for (int i = 0; i < 32; i++)
    ok = ok & (blake2s_test4_expected[i] == comp_s[i]);
  if (ok) printf("Success!\n");
  else printf("FAILED!\n");
  all_ok = all_ok && ok;

  Hacl_Blake2s_128_blake2s(32,comp_s,blake2s_test8_size_plaintext,blake2s_test8_plaintext,blake2s_test8_size_key,blake2s_test8_key);
  printf("computed:");
  for (int i = 0; i < 32; i++)
    printf("%02x",comp_s[i]);
  printf("\n");
  printf("expected:");
  for (int i = 0; i < 32; i++)
    printf("%02x",blake2s_test8_expected[i]);
  printf("\n");
  ok = true;
  for (int i = 0; i < 32; i++)
    ok = ok & (blake2s_test8_expected[i] == comp_s[i]);
  if (ok) printf("Success!\n");
  else printf("FAILED!\n");
  all_ok = all_ok && ok;


  printf("testing blake2b vec-32:\n");
  Hacl_Blake2b_32_blake2b(64,comp_b,blake2b_test1_size_plaintext,blake2b_test1_plaintext,blake2b_test1_size_key,blake2b_test1_key);
  printf("computed:");
  for (int i = 0; i < 64; i++)
    printf("%02x",comp_b[i]);
  printf("\n");
  printf("expected:");
  for (int i = 0; i < 64; i++)
    printf("%02x",blake2b_test1_expected[i]);
  printf("\n");
  ok = true;
  for (int i = 0; i < 64; i++)
    ok = ok & (blake2b_test1_expected[i] == comp_b[i]);
  if (ok) printf("Success!\n");
  else printf("FAILED!\n");
  all_ok = all_ok && ok;

  Hacl_Blake2b_32_blake2b(64,comp_s,blake2b_test13_size_plaintext,blake2b_test13_plaintext,blake2b_test13_size_key,blake2b_test13_key);
  printf("computed:");
  for (int i = 0; i < 64; i++)
    printf("%02x",comp_s[i]);
  printf("\n");
  printf("expected:");
  for (int i = 0; i < 64; i++)
    printf("%02x",blake2b_test13_expected[i]);
  printf("\n");
  ok = true;
  for (int i = 0; i < 64; i++)
    ok = ok & (blake2b_test13_expected[i] == comp_s[i]);
  if (ok) printf("Success!\n");
  else printf("FAILED!\n");
  all_ok = all_ok && ok;

  printf("testing blake2b vec-256:\n");
  Hacl_Blake2b_256_blake2b(64,comp_b,blake2b_test1_size_plaintext,blake2b_test1_plaintext,blake2b_test1_size_key,blake2b_test1_key);
  printf("computed:");
  for (int i = 0; i < 64; i++)
    printf("%02x",comp_b[i]);
  printf("\n");
  printf("expected:");
  for (int i = 0; i < 64; i++)
    printf("%02x",blake2b_test1_expected[i]);
  printf("\n");
  ok = true;
  for (int i = 0; i < 64; i++)
    ok = ok & (blake2b_test1_expected[i] == comp_b[i]);
  if (ok) printf("Success!\n");
  else printf("FAILED!\n");
  all_ok = all_ok && ok;

  Hacl_Blake2b_256_blake2b(64,comp_s,blake2b_test13_size_plaintext,blake2b_test13_plaintext,blake2b_test13_size_key,blake2b_test13_key);
  printf("computed:");
  for (int i = 0; i < 64; i++)
    printf("%02x",comp_s[i]);
  printf("\n");
  printf("expected:");
  for (int i = 0; i < 64; i++)
    printf("%02x",blake2b_test13_expected[i]);
  printf("\n");
  ok = true;
  for (int i = 0; i < 64; i++)
    ok = ok & (blake2b_test13_expected[i] == comp_s[i]);
  if (ok) printf("Success!\n");
  else printf("FAILED!\n");
  all_ok = all_ok && ok;


  uint64_t len = SIZE;
  uint8_t plain[SIZE];
  cycles a,b;
  clock_t t1,t2;
  memset(plain,'P',SIZE);

  for (int j = 0; j < ROUNDS; j++) {
    Hacl_Blake2s_32_blake2s(32,plain,SIZE,plain,0,NULL);
  }
  t1 = clock();
  a = cpucycles_begin();
  for (int j = 0; j < ROUNDS; j++) {
    Hacl_Blake2s_32_blake2s(32,plain,SIZE,plain,0,NULL);
  }
  b = cpucycles_end();
  t2 = clock();
  double cdiff3 = b - a;
  double tdiff3 = (double)(t2 - t1)/CLOCKS_PER_SEC;

  for (int j = 0; j < ROUNDS; j++) {
    Hacl_Blake2b_32_blake2b(64,plain,SIZE,plain,0,NULL);
  }
  t1 = clock();
  a = cpucycles_begin();
  for (int j = 0; j < ROUNDS; j++) {
    Hacl_Blake2b_32_blake2b(64,plain,SIZE,plain,0,NULL);
  }
  b = cpucycles_end();
  t2 = clock();
  double cdiff4 = b - a;
  double tdiff4 = (double)(t2 - t1)/CLOCKS_PER_SEC;

  for (int j = 0; j < ROUNDS; j++) {
    Hacl_Blake2s_128_blake2s(32,plain,SIZE,plain,0,NULL);
  }
  t1 = clock();
  a = cpucycles_begin();
  for (int j = 0; j < ROUNDS; j++) {
    Hacl_Blake2s_128_blake2s(32,plain,SIZE,plain,0,NULL);
  }
  b = cpucycles_end();
  t2 = clock();
  double cdiff5 = b - a;
  double tdiff5 = (double)(t2 - t1)/CLOCKS_PER_SEC;

  for (int j = 0; j < ROUNDS; j++) {
    Hacl_Blake2b_256_blake2b(64,plain,SIZE,plain,0,NULL);
  }
  t1 = clock();
  a = cpucycles_begin();
  for (int j = 0; j < ROUNDS; j++) {
    Hacl_Blake2b_256_blake2b(64,plain,SIZE,plain,0,NULL);
  }
  b = cpucycles_end();
  t2 = clock();
  double cdiff6 = b - a;
  double tdiff6 = (double)(t2 - t1)/CLOCKS_PER_SEC;

  uint64_t count = ROUNDS * SIZE;
  printf("Blake2S (Vec 32-bit):\n");
  printf("cycles for %" PRIu64 " bytes: %" PRIu64 " (%.2fcycles/byte)\n",count,(uint64_t)cdiff3,(double)cdiff3/count);
  printf("time for %" PRIu64 " bytes: %" PRIu64 " (%.2fus/byte)\n",count,(uint64_t)tdiff3,(double)tdiff3/count);
  printf("bw %8.2f MB/s\n",(double)count/(tdiff3 * 1000000.0));

  printf("Blake2B (Vec 64-bit):\n");
  printf("cycles for %" PRIu64 " bytes: %" PRIu64 " (%.2fcycles/byte)\n",count,(uint64_t)cdiff4,(double)cdiff4/count);
  printf("time for %" PRIu64 " bytes: %" PRIu64 " (%.2fus/byte)\n",count,(uint64_t)tdiff4,(double)tdiff4/count);
  printf("bw %8.2f MB/s\n",(double)count/(tdiff4 * 1000000.0));

  printf("Blake2S (Vec 128-bit):\n");
  printf("cycles for %" PRIu64 " bytes: %" PRIu64 " (%.2fcycles/byte)\n",count,(uint64_t)cdiff5,(double)cdiff5/count);
  printf("time for %" PRIu64 " bytes: %" PRIu64 " (%.2fus/byte)\n",count,(uint64_t)tdiff5,(double)tdiff5/count);
  printf("bw %8.2f MB/s\n",(double)count/(tdiff5 * 1000000.0));

  printf("Blake2B (Vec 256-bit):\n");
  printf("cycles for %" PRIu64 " bytes: %" PRIu64 " (%.2fcycles/byte)\n",count,(uint64_t)cdiff6,(double)cdiff6/count);
  printf("time for %" PRIu64 " bytes: %" PRIu64 " (%.2fus/byte)\n",count,(uint64_t)tdiff6,(double)tdiff6/count);
  printf("bw %8.2f MB/s\n",(double)count/(tdiff6 * 1000000.0));

  if (all_ok) return EXIT_SUCCESS;
  else return EXIT_FAILURE;
}

