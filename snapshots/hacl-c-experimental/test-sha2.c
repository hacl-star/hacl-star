#include "SHA2_256.h"
#include "kremlib.h"
#include "testlib.h"

void test_1a();

void test_1b();

void test_2a();

void test_2b();

void test_3a();

void test_3b();

void test_4a();

void test_4b();

void test_5();

void test_6_loop(uint8_t *plaintext, uint32_t *ctx, uint32_t max, uint32_t idx);

void test_6();

int32_t main();


void ossl_sha256(unsigned char* hash, const unsigned char *message, size_t message_len)
{
  EVP_MD_CTX *mdctx;

  if((mdctx = EVP_MD_CTX_create()) == NULL)
    {printf("ossl error\n"); exit(1);}

  if(1 != EVP_DigestInit_ex(mdctx, EVP_sha256(), NULL))
    {printf("ossl error\n"); exit(1);}


  if(1 != EVP_DigestUpdate(mdctx, message, message_len))
    {printf("ossl error\n"); exit(1);}

  int len;
  if(1 != EVP_DigestFinal_ex(mdctx, hash, &len))
    {printf("ossl error\n"); exit(1);}

  EVP_MD_CTX_destroy(mdctx);
}

void print_results(char *txt, double t1, unsigned long long d1, int rounds, int plainlen){
  printf("Testing: %s\n", txt);
  printf("Cycles for %d * %d bytes: %llu (%.2fcycles/byte)\n", rounds, plainlen, d1, (double)d1/plainlen/rounds);
  double ts = t1/CLOCKS_PER_SEC;
  printf("User time for %d times %d bytes: %fs (%fus/byte)\n", rounds, plainlen, ts, (double)(ts*1000000)/(plainlen*rounds));
}


void test_1a()
{
  uint32_t output_len = (uint32_t )32;
  uint8_t output[output_len];
  memset(output, 0, output_len * sizeof output[0]);
  uint32_t plaintext_len = (uint32_t )3;
  uint8_t plaintext[3] = { (uint8_t )0x61, (uint8_t )0x62, (uint8_t )0x63 };
  uint8_t
  expected[32] =
    {
      (uint8_t )0xBA, (uint8_t )0x78, (uint8_t )0x16, (uint8_t )0xBF, (uint8_t )0x8F, (uint8_t )0x01,
      (uint8_t )0xCF, (uint8_t )0xEA, (uint8_t )0x41, (uint8_t )0x41, (uint8_t )0x40, (uint8_t )0xDE,
      (uint8_t )0x5D, (uint8_t )0xAE, (uint8_t )0x22, (uint8_t )0x23, (uint8_t )0xB0, (uint8_t )0x03,
      (uint8_t )0x61, (uint8_t )0xA3, (uint8_t )0x96, (uint8_t )0x17, (uint8_t )0x7A, (uint8_t )0x9C,
      (uint8_t )0xB4, (uint8_t )0x10, (uint8_t )0xFF, (uint8_t )0x61, (uint8_t )0xF2, (uint8_t )0x00,
      (uint8_t )0x15, (uint8_t )0xAD
    };
  uint32_t ctx[size_state_256];
  memset(ctx, 0, size_state_256 * sizeof ctx[0]);
  sha2_init_256(ctx);
  sha2_update_last_256(ctx, plaintext, plaintext_len);
  sha2_finish_256(ctx, output);
  TestLib_compare_and_print("Test 1a", expected, output, (uint32_t )32);
}

void test_1b()
{
  uint32_t output_len = (uint32_t )32;
  uint8_t output[output_len];
  memset(output, 0, output_len * sizeof output[0]);
  uint32_t plaintext_len = (uint32_t )3;
  uint8_t plaintext[3] = { (uint8_t )0x61, (uint8_t )0x62, (uint8_t )0x63 };
  uint8_t
  expected[32] =
    {
      (uint8_t )0xba, (uint8_t )0x78, (uint8_t )0x16, (uint8_t )0xbf, (uint8_t )0x8f, (uint8_t )0x01,
      (uint8_t )0xcf, (uint8_t )0xea, (uint8_t )0x41, (uint8_t )0x41, (uint8_t )0x40, (uint8_t )0xde,
      (uint8_t )0x5d, (uint8_t )0xae, (uint8_t )0x22, (uint8_t )0x23, (uint8_t )0xb0, (uint8_t )0x03,
      (uint8_t )0x61, (uint8_t )0xa3, (uint8_t )0x96, (uint8_t )0x17, (uint8_t )0x7a, (uint8_t )0x9c,
      (uint8_t )0xb4, (uint8_t )0x10, (uint8_t )0xff, (uint8_t )0x61, (uint8_t )0xf2, (uint8_t )0x00,
      (uint8_t )0x15, (uint8_t )0xad
    };
  uint32_t ctx[size_state_256];
  memset(ctx, 0, size_state_256 * sizeof ctx[0]);
  sha2_256(output, plaintext, plaintext_len);
  TestLib_compare_and_print("Test 1b", expected, output, (uint32_t )32);
}

void test_2a()
{
  uint32_t output_len = (uint32_t )32;
  uint8_t output[output_len];
  memset(output, 0, output_len * sizeof output[0]);
  uint32_t plaintext_len = (uint32_t )0;
  uint8_t plaintext[0] = {  };
  uint8_t
  expected[32] =
    {
      (uint8_t )0xe3, (uint8_t )0xb0, (uint8_t )0xc4, (uint8_t )0x42, (uint8_t )0x98, (uint8_t )0xfc,
      (uint8_t )0x1c, (uint8_t )0x14, (uint8_t )0x9a, (uint8_t )0xfb, (uint8_t )0xf4, (uint8_t )0xc8,
      (uint8_t )0x99, (uint8_t )0x6f, (uint8_t )0xb9, (uint8_t )0x24, (uint8_t )0x27, (uint8_t )0xae,
      (uint8_t )0x41, (uint8_t )0xe4, (uint8_t )0x64, (uint8_t )0x9b, (uint8_t )0x93, (uint8_t )0x4c,
      (uint8_t )0xa4, (uint8_t )0x95, (uint8_t )0x99, (uint8_t )0x1b, (uint8_t )0x78, (uint8_t )0x52,
      (uint8_t )0xb8, (uint8_t )0x55
    };
  uint32_t ctx[size_state_256];
  memset(ctx, 0, size_state_256 * sizeof ctx[0]);
  sha2_init_256(ctx);
  sha2_update_last_256(ctx, plaintext, plaintext_len);
  sha2_finish_256(ctx, output);
  TestLib_compare_and_print("Test 2a", expected, output, (uint32_t )32);
}

void test_2b()
{
  uint32_t output_len = (uint32_t )32;
  uint8_t output[output_len];
  memset(output, 0, output_len * sizeof output[0]);
  uint32_t plaintext_len = (uint32_t )0;
  uint8_t plaintext[0] = {  };
  uint8_t
  expected[32] =
    {
      (uint8_t )0xe3, (uint8_t )0xb0, (uint8_t )0xc4, (uint8_t )0x42, (uint8_t )0x98, (uint8_t )0xfc,
      (uint8_t )0x1c, (uint8_t )0x14, (uint8_t )0x9a, (uint8_t )0xfb, (uint8_t )0xf4, (uint8_t )0xc8,
      (uint8_t )0x99, (uint8_t )0x6f, (uint8_t )0xb9, (uint8_t )0x24, (uint8_t )0x27, (uint8_t )0xae,
      (uint8_t )0x41, (uint8_t )0xe4, (uint8_t )0x64, (uint8_t )0x9b, (uint8_t )0x93, (uint8_t )0x4c,
      (uint8_t )0xa4, (uint8_t )0x95, (uint8_t )0x99, (uint8_t )0x1b, (uint8_t )0x78, (uint8_t )0x52,
      (uint8_t )0xb8, (uint8_t )0x55
    };
  uint32_t ctx[size_state_256];
  memset(ctx, 0, size_state_256 * sizeof ctx[0]);
  sha2_256(output, plaintext, plaintext_len);
  TestLib_compare_and_print("Test 2b", expected, output, (uint32_t )32);
}

void test_3a()
{
  uint32_t output_len = (uint32_t )32;
  uint8_t output[output_len];
  memset(output, 0, output_len * sizeof output[0]);
  uint32_t plaintext_len = (uint32_t )56;
  uint8_t
  plaintext[56] =
    {
      (uint8_t )0x61, (uint8_t )0x62, (uint8_t )0x63, (uint8_t )0x64, (uint8_t )0x62, (uint8_t )0x63,
      (uint8_t )0x64, (uint8_t )0x65, (uint8_t )0x63, (uint8_t )0x64, (uint8_t )0x65, (uint8_t )0x66,
      (uint8_t )0x64, (uint8_t )0x65, (uint8_t )0x66, (uint8_t )0x67, (uint8_t )0x65, (uint8_t )0x66,
      (uint8_t )0x67, (uint8_t )0x68, (uint8_t )0x66, (uint8_t )0x67, (uint8_t )0x68, (uint8_t )0x69,
      (uint8_t )0x67, (uint8_t )0x68, (uint8_t )0x69, (uint8_t )0x6a, (uint8_t )0x68, (uint8_t )0x69,
      (uint8_t )0x6a, (uint8_t )0x6b, (uint8_t )0x69, (uint8_t )0x6a, (uint8_t )0x6b, (uint8_t )0x6c,
      (uint8_t )0x6a, (uint8_t )0x6b, (uint8_t )0x6c, (uint8_t )0x6d, (uint8_t )0x6b, (uint8_t )0x6c,
      (uint8_t )0x6d, (uint8_t )0x6e, (uint8_t )0x6c, (uint8_t )0x6d, (uint8_t )0x6e, (uint8_t )0x6f,
      (uint8_t )0x6d, (uint8_t )0x6e, (uint8_t )0x6f, (uint8_t )0x70, (uint8_t )0x6e, (uint8_t )0x6f,
      (uint8_t )0x70, (uint8_t )0x71
    };
  uint8_t
  expected[32] =
    {
      (uint8_t )0x24, (uint8_t )0x8d, (uint8_t )0x6a, (uint8_t )0x61, (uint8_t )0xd2, (uint8_t )0x06,
      (uint8_t )0x38, (uint8_t )0xb8, (uint8_t )0xe5, (uint8_t )0xc0, (uint8_t )0x26, (uint8_t )0x93,
      (uint8_t )0x0c, (uint8_t )0x3e, (uint8_t )0x60, (uint8_t )0x39, (uint8_t )0xa3, (uint8_t )0x3c,
      (uint8_t )0xe4, (uint8_t )0x59, (uint8_t )0x64, (uint8_t )0xff, (uint8_t )0x21, (uint8_t )0x67,
      (uint8_t )0xf6, (uint8_t )0xec, (uint8_t )0xed, (uint8_t )0xd4, (uint8_t )0x19, (uint8_t )0xdb,
      (uint8_t )0x06, (uint8_t )0xc1
    };
  uint32_t ctx[size_state_256];
  memset(ctx, 0, size_state_256 * sizeof ctx[0]);
  sha2_init_256(ctx);
  sha2_update_last_256(ctx, plaintext, plaintext_len);
  sha2_finish_256(ctx, output);
  TestLib_compare_and_print("Test 3a", expected, output, (uint32_t )32);
}

void test_3b()
{
  uint32_t output_len = (uint32_t )32;
  uint8_t output[output_len];
  memset(output, 0, output_len * sizeof output[0]);
  uint32_t plaintext_len = (uint32_t )56;
  uint8_t
  plaintext[56] =
    {
      (uint8_t )0x61, (uint8_t )0x62, (uint8_t )0x63, (uint8_t )0x64, (uint8_t )0x62, (uint8_t )0x63,
      (uint8_t )0x64, (uint8_t )0x65, (uint8_t )0x63, (uint8_t )0x64, (uint8_t )0x65, (uint8_t )0x66,
      (uint8_t )0x64, (uint8_t )0x65, (uint8_t )0x66, (uint8_t )0x67, (uint8_t )0x65, (uint8_t )0x66,
      (uint8_t )0x67, (uint8_t )0x68, (uint8_t )0x66, (uint8_t )0x67, (uint8_t )0x68, (uint8_t )0x69,
      (uint8_t )0x67, (uint8_t )0x68, (uint8_t )0x69, (uint8_t )0x6a, (uint8_t )0x68, (uint8_t )0x69,
      (uint8_t )0x6a, (uint8_t )0x6b, (uint8_t )0x69, (uint8_t )0x6a, (uint8_t )0x6b, (uint8_t )0x6c,
      (uint8_t )0x6a, (uint8_t )0x6b, (uint8_t )0x6c, (uint8_t )0x6d, (uint8_t )0x6b, (uint8_t )0x6c,
      (uint8_t )0x6d, (uint8_t )0x6e, (uint8_t )0x6c, (uint8_t )0x6d, (uint8_t )0x6e, (uint8_t )0x6f,
      (uint8_t )0x6d, (uint8_t )0x6e, (uint8_t )0x6f, (uint8_t )0x70, (uint8_t )0x6e, (uint8_t )0x6f,
      (uint8_t )0x70, (uint8_t )0x71
    };
  uint8_t
  expected[32] =
    {
      (uint8_t )0x24, (uint8_t )0x8d, (uint8_t )0x6a, (uint8_t )0x61, (uint8_t )0xd2, (uint8_t )0x06,
      (uint8_t )0x38, (uint8_t )0xb8, (uint8_t )0xe5, (uint8_t )0xc0, (uint8_t )0x26, (uint8_t )0x93,
      (uint8_t )0x0c, (uint8_t )0x3e, (uint8_t )0x60, (uint8_t )0x39, (uint8_t )0xa3, (uint8_t )0x3c,
      (uint8_t )0xe4, (uint8_t )0x59, (uint8_t )0x64, (uint8_t )0xff, (uint8_t )0x21, (uint8_t )0x67,
      (uint8_t )0xf6, (uint8_t )0xec, (uint8_t )0xed, (uint8_t )0xd4, (uint8_t )0x19, (uint8_t )0xdb,
      (uint8_t )0x06, (uint8_t )0xc1
    };
  uint32_t ctx[size_state_256];
  memset(ctx, 0, size_state_256 * sizeof ctx[0]);
  sha2_256(output, plaintext, plaintext_len);
  TestLib_compare_and_print("Test 3b", expected, output, (uint32_t )32);
}

void test_4a()
{
  uint32_t output_len = (uint32_t )32;
  uint8_t output[output_len];
  memset(output, 0, output_len * sizeof output[0]);
  uint32_t plaintext_len = (uint32_t )112;
  uint8_t
  plaintext[112] =
    {
      (uint8_t )0x61, (uint8_t )0x62, (uint8_t )0x63, (uint8_t )0x64, (uint8_t )0x65, (uint8_t )0x66,
      (uint8_t )0x67, (uint8_t )0x68, (uint8_t )0x62, (uint8_t )0x63, (uint8_t )0x64, (uint8_t )0x65,
      (uint8_t )0x66, (uint8_t )0x67, (uint8_t )0x68, (uint8_t )0x69, (uint8_t )0x63, (uint8_t )0x64,
      (uint8_t )0x65, (uint8_t )0x66, (uint8_t )0x67, (uint8_t )0x68, (uint8_t )0x69, (uint8_t )0x6a,
      (uint8_t )0x64, (uint8_t )0x65, (uint8_t )0x66, (uint8_t )0x67, (uint8_t )0x68, (uint8_t )0x69,
      (uint8_t )0x6a, (uint8_t )0x6b, (uint8_t )0x65, (uint8_t )0x66, (uint8_t )0x67, (uint8_t )0x68,
      (uint8_t )0x69, (uint8_t )0x6a, (uint8_t )0x6b, (uint8_t )0x6c, (uint8_t )0x66, (uint8_t )0x67,
      (uint8_t )0x68, (uint8_t )0x69, (uint8_t )0x6a, (uint8_t )0x6b, (uint8_t )0x6c, (uint8_t )0x6d,
      (uint8_t )0x67, (uint8_t )0x68, (uint8_t )0x69, (uint8_t )0x6a, (uint8_t )0x6b, (uint8_t )0x6c,
      (uint8_t )0x6d, (uint8_t )0x6e, (uint8_t )0x68, (uint8_t )0x69, (uint8_t )0x6a, (uint8_t )0x6b,
      (uint8_t )0x6c, (uint8_t )0x6d, (uint8_t )0x6e, (uint8_t )0x6f, (uint8_t )0x69, (uint8_t )0x6a,
      (uint8_t )0x6b, (uint8_t )0x6c, (uint8_t )0x6d, (uint8_t )0x6e, (uint8_t )0x6f, (uint8_t )0x70,
      (uint8_t )0x6a, (uint8_t )0x6b, (uint8_t )0x6c, (uint8_t )0x6d, (uint8_t )0x6e, (uint8_t )0x6f,
      (uint8_t )0x70, (uint8_t )0x71, (uint8_t )0x6b, (uint8_t )0x6c, (uint8_t )0x6d, (uint8_t )0x6e,
      (uint8_t )0x6f, (uint8_t )0x70, (uint8_t )0x71, (uint8_t )0x72, (uint8_t )0x6c, (uint8_t )0x6d,
      (uint8_t )0x6e, (uint8_t )0x6f, (uint8_t )0x70, (uint8_t )0x71, (uint8_t )0x72, (uint8_t )0x73,
      (uint8_t )0x6d, (uint8_t )0x6e, (uint8_t )0x6f, (uint8_t )0x70, (uint8_t )0x71, (uint8_t )0x72,
      (uint8_t )0x73, (uint8_t )0x74, (uint8_t )0x6e, (uint8_t )0x6f, (uint8_t )0x70, (uint8_t )0x71,
      (uint8_t )0x72, (uint8_t )0x73, (uint8_t )0x74, (uint8_t )0x75
    };
  uint8_t
  expected[32] =
    {
      (uint8_t )0xcf, (uint8_t )0x5b, (uint8_t )0x16, (uint8_t )0xa7, (uint8_t )0x78, (uint8_t )0xaf,
      (uint8_t )0x83, (uint8_t )0x80, (uint8_t )0x03, (uint8_t )0x6c, (uint8_t )0xe5, (uint8_t )0x9e,
      (uint8_t )0x7b, (uint8_t )0x04, (uint8_t )0x92, (uint8_t )0x37, (uint8_t )0x0b, (uint8_t )0x24,
      (uint8_t )0x9b, (uint8_t )0x11, (uint8_t )0xe8, (uint8_t )0xf0, (uint8_t )0x7a, (uint8_t )0x51,
      (uint8_t )0xaf, (uint8_t )0xac, (uint8_t )0x45, (uint8_t )0x03, (uint8_t )0x7a, (uint8_t )0xfe,
      (uint8_t )0xe9, (uint8_t )0xd1
    };
  uint32_t ctx[size_state_256];
  memset(ctx, 0, size_state_256 * sizeof ctx[0]);
  sha2_init_256(ctx);
  sha2_update_last_256(ctx, plaintext, plaintext_len);
  sha2_finish_256(ctx, output);
  TestLib_compare_and_print("Test 4a", expected, output, (uint32_t )32);
}

void test_4b()
{
  uint32_t output_len = (uint32_t )32;
  uint8_t output[output_len];
  memset(output, 0, output_len * sizeof output[0]);
  uint32_t plaintext_len = (uint32_t )112;
  uint8_t
  plaintext[112] =
    {
      (uint8_t )0x61, (uint8_t )0x62, (uint8_t )0x63, (uint8_t )0x64, (uint8_t )0x65, (uint8_t )0x66,
      (uint8_t )0x67, (uint8_t )0x68, (uint8_t )0x62, (uint8_t )0x63, (uint8_t )0x64, (uint8_t )0x65,
      (uint8_t )0x66, (uint8_t )0x67, (uint8_t )0x68, (uint8_t )0x69, (uint8_t )0x63, (uint8_t )0x64,
      (uint8_t )0x65, (uint8_t )0x66, (uint8_t )0x67, (uint8_t )0x68, (uint8_t )0x69, (uint8_t )0x6a,
      (uint8_t )0x64, (uint8_t )0x65, (uint8_t )0x66, (uint8_t )0x67, (uint8_t )0x68, (uint8_t )0x69,
      (uint8_t )0x6a, (uint8_t )0x6b, (uint8_t )0x65, (uint8_t )0x66, (uint8_t )0x67, (uint8_t )0x68,
      (uint8_t )0x69, (uint8_t )0x6a, (uint8_t )0x6b, (uint8_t )0x6c, (uint8_t )0x66, (uint8_t )0x67,
      (uint8_t )0x68, (uint8_t )0x69, (uint8_t )0x6a, (uint8_t )0x6b, (uint8_t )0x6c, (uint8_t )0x6d,
      (uint8_t )0x67, (uint8_t )0x68, (uint8_t )0x69, (uint8_t )0x6a, (uint8_t )0x6b, (uint8_t )0x6c,
      (uint8_t )0x6d, (uint8_t )0x6e, (uint8_t )0x68, (uint8_t )0x69, (uint8_t )0x6a, (uint8_t )0x6b,
      (uint8_t )0x6c, (uint8_t )0x6d, (uint8_t )0x6e, (uint8_t )0x6f, (uint8_t )0x69, (uint8_t )0x6a,
      (uint8_t )0x6b, (uint8_t )0x6c, (uint8_t )0x6d, (uint8_t )0x6e, (uint8_t )0x6f, (uint8_t )0x70,
      (uint8_t )0x6a, (uint8_t )0x6b, (uint8_t )0x6c, (uint8_t )0x6d, (uint8_t )0x6e, (uint8_t )0x6f,
      (uint8_t )0x70, (uint8_t )0x71, (uint8_t )0x6b, (uint8_t )0x6c, (uint8_t )0x6d, (uint8_t )0x6e,
      (uint8_t )0x6f, (uint8_t )0x70, (uint8_t )0x71, (uint8_t )0x72, (uint8_t )0x6c, (uint8_t )0x6d,
      (uint8_t )0x6e, (uint8_t )0x6f, (uint8_t )0x70, (uint8_t )0x71, (uint8_t )0x72, (uint8_t )0x73,
      (uint8_t )0x6d, (uint8_t )0x6e, (uint8_t )0x6f, (uint8_t )0x70, (uint8_t )0x71, (uint8_t )0x72,
      (uint8_t )0x73, (uint8_t )0x74, (uint8_t )0x6e, (uint8_t )0x6f, (uint8_t )0x70, (uint8_t )0x71,
      (uint8_t )0x72, (uint8_t )0x73, (uint8_t )0x74, (uint8_t )0x75
    };
  uint8_t
  expected[32] =
    {
      (uint8_t )0xcf, (uint8_t )0x5b, (uint8_t )0x16, (uint8_t )0xa7, (uint8_t )0x78, (uint8_t )0xaf,
      (uint8_t )0x83, (uint8_t )0x80, (uint8_t )0x03, (uint8_t )0x6c, (uint8_t )0xe5, (uint8_t )0x9e,
      (uint8_t )0x7b, (uint8_t )0x04, (uint8_t )0x92, (uint8_t )0x37, (uint8_t )0x0b, (uint8_t )0x24,
      (uint8_t )0x9b, (uint8_t )0x11, (uint8_t )0xe8, (uint8_t )0xf0, (uint8_t )0x7a, (uint8_t )0x51,
      (uint8_t )0xaf, (uint8_t )0xac, (uint8_t )0x45, (uint8_t )0x03, (uint8_t )0x7a, (uint8_t )0xfe,
      (uint8_t )0xe9, (uint8_t )0xd1
    };
  uint32_t ctx[size_state_256];
  memset(ctx, 0, size_state_256 * sizeof ctx[0]);
  sha2_256(output, plaintext, plaintext_len);
  TestLib_compare_and_print("Test 4b", expected, output, (uint32_t )32);
}

void test_5()
{
  uint32_t output_len = (uint32_t )32;
  uint8_t output[output_len];
  memset(output, 0, output_len * sizeof output[0]);
  uint32_t plaintext_len = (uint32_t )1000000;
  uint8_t plaintext[plaintext_len];
  for (uintmax_t i = 0; i < plaintext_len; ++i)
    plaintext[i] = (uint8_t )0x61;
  uint8_t
  expected[32] =
    {
      (uint8_t )0xcd, (uint8_t )0xc7, (uint8_t )0x6e, (uint8_t )0x5c, (uint8_t )0x99, (uint8_t )0x14,
      (uint8_t )0xfb, (uint8_t )0x92, (uint8_t )0x81, (uint8_t )0xa1, (uint8_t )0xc7, (uint8_t )0xe2,
      (uint8_t )0x84, (uint8_t )0xd7, (uint8_t )0x3e, (uint8_t )0x67, (uint8_t )0xf1, (uint8_t )0x80,
      (uint8_t )0x9a, (uint8_t )0x48, (uint8_t )0xa4, (uint8_t )0x97, (uint8_t )0x20, (uint8_t )0x0e,
      (uint8_t )0x04, (uint8_t )0x6d, (uint8_t )0x39, (uint8_t )0xcc, (uint8_t )0xc7, (uint8_t )0x11,
      (uint8_t )0x2c, (uint8_t )0xd0
    };
  uint32_t ctx[size_state_256];
  memset(ctx, 0, size_state_256 * sizeof ctx[0]);
  sha2_256(output, plaintext, plaintext_len);
  TestLib_compare_and_print("Test 5", expected, output, (uint32_t )32);
}

void test_6_loop(uint8_t *plaintext, uint32_t *ctx, uint32_t max, uint32_t idx)
{
  if (idx == max)
    return;
  else
  {
    sha2_update_256(ctx, plaintext);
    test_6_loop(plaintext, ctx, max, idx + (uint32_t )1);
    return;
  }
}

void test_6()
{
  uint32_t output_len = (uint32_t )32;
  uint8_t output[output_len];
  memset(output, 0, output_len * sizeof output[0]);
  uint32_t plaintext_len = (uint32_t )64;
  uint8_t
  plaintext[64] =
    {
      (uint8_t )0x61, (uint8_t )0x62, (uint8_t )0x63, (uint8_t )0x64, (uint8_t )0x65, (uint8_t )0x66,
      (uint8_t )0x67, (uint8_t )0x68, (uint8_t )0x62, (uint8_t )0x63, (uint8_t )0x64, (uint8_t )0x65,
      (uint8_t )0x66, (uint8_t )0x67, (uint8_t )0x68, (uint8_t )0x69, (uint8_t )0x63, (uint8_t )0x64,
      (uint8_t )0x65, (uint8_t )0x66, (uint8_t )0x67, (uint8_t )0x68, (uint8_t )0x69, (uint8_t )0x6a,
      (uint8_t )0x64, (uint8_t )0x65, (uint8_t )0x66, (uint8_t )0x67, (uint8_t )0x68, (uint8_t )0x69,
      (uint8_t )0x6a, (uint8_t )0x6b, (uint8_t )0x65, (uint8_t )0x66, (uint8_t )0x67, (uint8_t )0x68,
      (uint8_t )0x69, (uint8_t )0x6a, (uint8_t )0x6b, (uint8_t )0x6c, (uint8_t )0x66, (uint8_t )0x67,
      (uint8_t )0x68, (uint8_t )0x69, (uint8_t )0x6a, (uint8_t )0x6b, (uint8_t )0x6c, (uint8_t )0x6d,
      (uint8_t )0x67, (uint8_t )0x68, (uint8_t )0x69, (uint8_t )0x6a, (uint8_t )0x6b, (uint8_t )0x6c,
      (uint8_t )0x6d, (uint8_t )0x6e, (uint8_t )0x68, (uint8_t )0x69, (uint8_t )0x6a, (uint8_t )0x6b,
      (uint8_t )0x6c, (uint8_t )0x6d, (uint8_t )0x6e, (uint8_t )0x6f
    };
  uint8_t
  expected[32] =
    {
      (uint8_t )0x50, (uint8_t )0xe7, (uint8_t )0x2a, (uint8_t )0x0e, (uint8_t )0x26, (uint8_t )0x44,
      (uint8_t )0x2f, (uint8_t )0xe2, (uint8_t )0x55, (uint8_t )0x2d, (uint8_t )0xc3, (uint8_t )0x93,
      (uint8_t )0x8a, (uint8_t )0xc5, (uint8_t )0x86, (uint8_t )0x58, (uint8_t )0x22, (uint8_t )0x8c,
      (uint8_t )0x0c, (uint8_t )0xbf, (uint8_t )0xb1, (uint8_t )0xd2, (uint8_t )0xca, (uint8_t )0x87,
      (uint8_t )0x2a, (uint8_t )0xe4, (uint8_t )0x35, (uint8_t )0x26, (uint8_t )0x6f, (uint8_t )0xcd,
      (uint8_t )0x05, (uint8_t )0x5e
    };
  uint32_t ctx[size_state_256];
  memset(ctx, 0, size_state_256 * sizeof ctx[0]);
  sha2_init_256(ctx);
  test_6_loop(plaintext, ctx, (uint32_t )16777215, (uint32_t )0);
  sha2_update_last_256(ctx, plaintext, plaintext_len);
  sha2_finish_256(ctx, output);
  TestLib_compare_and_print("Test 6", expected, output, (uint32_t )32);
}

#define PLAINLEN (1024*1024)
#define ROUNDS 1000

int32_t perf_sha() {
  uint32_t len = PLAINLEN * sizeof(char);
  uint8_t* plain = malloc(len);
  uint8_t* cipher = malloc(len);
  int fd = open("/dev/urandom", O_RDONLY);
  uint64_t res = read(fd, plain, len);
  if (res != len) {
    printf("Error on reading, got %llu bytes\n", res);
    return 1;
  }

  uint8_t hash[32];
  cycles a,b;
  clock_t t1,t2;

  t1 = clock();
  a = TestLib_cpucycles_begin();
  for (int i = 0; i < ROUNDS; i++){
    sha2_256(hash,plain,len);
    plain[0] = hash[0];
  }
  b = TestLib_cpucycles_end();
  t2 = clock();
  print_results("HACL SHA256 speed", (double)t2-t1,
		(double) b - a, ROUNDS, PLAINLEN);
  for (int i = 0; i < PLAINLEN; i++) 
    res += (uint64_t) plain[i];
  printf("Composite result (ignore): %llx\n", res);

  /*
  t1 = clock();
  a = TestLib_cpucycles_begin();
  for (int i = 0; i < ROUNDS; i++){
    crypto_stream_chacha20_ietf_xor(plain,plain, len, nonce, key);
  }
  b = TestLib_cpucycles_end();
  t2 = clock();
  print_results("Sodium ChaCha20 speed", (double)t2-t1,
		(double) b - a, ROUNDS, PLAINLEN);
  for (int i = 0; i < PLAINLEN; i++) 
    res += (uint64_t) plain[i];
  printf("Composite result (ignore): %llx\n", res);
  */
  t1 = clock();
  a = TestLib_cpucycles_begin();
  for (int i = 0; i < ROUNDS; i++){
    ossl_sha256(hash,plain, len);
  }
  b = TestLib_cpucycles_end();
  t2 = clock();
  print_results("OpenSSL SHA256 speed", (double)t2-t1,
		(double) b - a, ROUNDS, PLAINLEN);
  for (int i = 0; i < PLAINLEN; i++) 
    res += (uint64_t) plain[i];
  printf("Composite result (ignore): %llx\n", res);
  return exit_success;
}

int32_t main()
{
  test_1a();
  test_1b();
  test_2a();
  test_2b();
  test_3a();
  test_3b();
  test_4a();
  test_4b();
  test_5();
  //  test_6();
  perf_sha();
  return exit_success;
}

