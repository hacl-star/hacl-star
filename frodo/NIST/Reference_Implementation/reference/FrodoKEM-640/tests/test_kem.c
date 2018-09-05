/********************************************************************************************
* FrodoKEM: Learning with Errors Key Encapsulation
*
* Abstract: benchmarking/testing KEM scheme
*********************************************************************************************/
#include "../sha3/fips202.h"
#include "../sha3-hacl/Hacl_SHA3.h"

#define KEM_TEST_ITERATIONS 1000
#define KEM_BENCH_SECONDS     1

uint8_t
test1_plaintext[16U] =
  {
    (uint8_t)0x61U, (uint8_t)0x62U, (uint8_t)0x63U, (uint8_t)0x64U, (uint8_t)0x65U, (uint8_t)0x66U,
    (uint8_t)0x67U, (uint8_t)0x68U, (uint8_t)0x62U, (uint8_t)0x63U, (uint8_t)0x64U, (uint8_t)0x65U,
    (uint8_t)0x66U, (uint8_t)0x67U, (uint8_t)0x68U, (uint8_t)0x69U
  };

uint8_t
test1_expected[64U] =
  {
    (uint8_t)0x89U, (uint8_t)0x2eU, (uint8_t)0xd8U, (uint8_t)0xb5U, (uint8_t)0x1aU, (uint8_t)0xecU,
    (uint8_t)0x70U, (uint8_t)0x3fU, (uint8_t)0xdaU, (uint8_t)0x4bU, (uint8_t)0x40U, (uint8_t)0x0eU,
    (uint8_t)0x93U, (uint8_t)0xa4U, (uint8_t)0x94U, (uint8_t)0x56U, (uint8_t)0xd3U, (uint8_t)0x28U,
    (uint8_t)0xdfU, (uint8_t)0x46U, (uint8_t)0x0dU, (uint8_t)0x35U, (uint8_t)0x80U, (uint8_t)0x2aU,
    (uint8_t)0x01U, (uint8_t)0xbfU, (uint8_t)0xcfU, (uint8_t)0xa7U, (uint8_t)0x3dU, (uint8_t)0xa3U,
    (uint8_t)0xd0U, (uint8_t)0xb1U, (uint8_t)0xb4U, (uint8_t)0x87U, (uint8_t)0x94U, (uint8_t)0x2dU,
    (uint8_t)0xe9U, (uint8_t)0x34U, (uint8_t)0x8bU, (uint8_t)0x9fU, (uint8_t)0xa0U, (uint8_t)0xbeU,
    (uint8_t)0xb0U, (uint8_t)0xedU, (uint8_t)0x09U, (uint8_t)0x29U, (uint8_t)0x5bU, (uint8_t)0x96U,
    (uint8_t)0x9bU, (uint8_t)0x2fU, (uint8_t)0x14U, (uint8_t)0x24U, (uint8_t)0xf8U, (uint8_t)0x6aU,
    (uint8_t)0x4aU, (uint8_t)0x39U, (uint8_t)0xc5U, (uint8_t)0x2eU, (uint8_t)0xb3U, (uint8_t)0xc5U,
    (uint8_t)0xe2U, (uint8_t)0xb2U, (uint8_t)0x23U, (uint8_t)0x6fU
  };

static int sha3_test(int iterations)
{
    uint8_t test[64];
    uint8_t test1[64];

    printf("\n");
    printf("=======================================================================\n");
    printf("Testing correctness of SHA3, tests for %d iterations\n", iterations);
    printf("=======================================================================\n");

    for (int i = 0; i < iterations; i++) {
        cshake128_simple(test, 64, 2, test1_plaintext, (unsigned long long)16);
        cshake128_frodo((uint32_t)16U, test1_plaintext, (uint16_t)2U, (uint32_t)64U, test1);
        if (memcmp(test, test1_expected, 64) != 0 || memcmp(test1, test1_expected, 64) != 0) {
            printf("\n ERROR!\n");
	    return false;
        }
    }
    printf("Tests PASSED. \n");
    printf("\n\n");

    return true;
}

static void sha3_bench(const int seconds)
{
    uint8_t test[64];

    TIME_OPERATION_SECONDS({ cshake128_simple(test, 64, 2, test1_plaintext, (unsigned long long)16); }, "cSHAKE128", seconds);

    TIME_OPERATION_SECONDS({ cshake128_frodo((uint32_t)16U, test1_plaintext, (uint16_t)2U, (uint32_t)64U, test); }, "cSHAKE128_hacl", seconds);
}


int main()
{
    int OK = true;

    OK = sha3_test(KEM_TEST_ITERATIONS);
    if (OK != true) {
        goto exit;
    }

    PRINT_TIMER_HEADER
    sha3_bench(KEM_BENCH_SECONDS);
    PRINT_TIMER_FOOTER

exit:
    return (OK == true) ? EXIT_SUCCESS : EXIT_FAILURE;
}
