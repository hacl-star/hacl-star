#include "kremlib.h"
#include "testlib.h"
#include "sodium.h"
#include <fcntl.h>
#include <sys/stat.h>
#include "openssl/evp.h"
#include "SHA2_512.h"



void ossl_sha512(unsigned char* hash, const unsigned char *message, size_t message_len)
{
  EVP_MD_CTX *mdctx;

  if((mdctx = EVP_MD_CTX_create()) == NULL)
    {printf("ossl error\n"); exit(1);}

  if(1 != EVP_DigestInit_ex(mdctx, EVP_sha512(), NULL))
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
  uint32_t output_len = (uint32_t )64;
  KRML_CHECK_SIZE((uint8_t )0, output_len);
  uint8_t output[output_len];
  memset(output, 0, output_len * sizeof output[0]);
  uint32_t plaintext_len = (uint32_t )3;
  uint8_t plaintext[3] = { (uint8_t )0x61, (uint8_t )0x62, (uint8_t )0x63 };
  uint8_t
  expected[64] =
    {
      (uint8_t )0xdd, (uint8_t )0xaf, (uint8_t )0x35, (uint8_t )0xa1, (uint8_t )0x93, (uint8_t )0x61,
      (uint8_t )0x7a, (uint8_t )0xba, (uint8_t )0xcc, (uint8_t )0x41, (uint8_t )0x73, (uint8_t )0x49,
      (uint8_t )0xae, (uint8_t )0x20, (uint8_t )0x41, (uint8_t )0x31, (uint8_t )0x12, (uint8_t )0xe6,
      (uint8_t )0xfa, (uint8_t )0x4e, (uint8_t )0x89, (uint8_t )0xa9, (uint8_t )0x7e, (uint8_t )0xa2,
      (uint8_t )0x0a, (uint8_t )0x9e, (uint8_t )0xee, (uint8_t )0xe6, (uint8_t )0x4b, (uint8_t )0x55,
      (uint8_t )0xd3, (uint8_t )0x9a, (uint8_t )0x21, (uint8_t )0x92, (uint8_t )0x99, (uint8_t )0x2a,
      (uint8_t )0x27, (uint8_t )0x4f, (uint8_t )0xc1, (uint8_t )0xa8, (uint8_t )0x36, (uint8_t )0xba,
      (uint8_t )0x3c, (uint8_t )0x23, (uint8_t )0xa3, (uint8_t )0xfe, (uint8_t )0xeb, (uint8_t )0xbd,
      (uint8_t )0x45, (uint8_t )0x4d, (uint8_t )0x44, (uint8_t )0x23, (uint8_t )0x64, (uint8_t )0x3c,
      (uint8_t )0xe8, (uint8_t )0x0e, (uint8_t )0x2a, (uint8_t )0x9a, (uint8_t )0xc9, (uint8_t )0x4f,
      (uint8_t )0xa5, (uint8_t )0x4c, (uint8_t )0xa4, (uint8_t )0x9f
    };
  KRML_CHECK_SIZE((uint64_t )0, size_state);
  uint64_t state[size_state];
  memset(state, 0, size_state * sizeof state[0]);
  init(state);
  update_last(state, plaintext, (uint64_t )plaintext_len);
  finish(state, output);
  TestLib_compare_and_print("Test 1a", expected, output, (uint32_t )64);
}

void test_1b()
{
  uint32_t output_len = (uint32_t )64;
  KRML_CHECK_SIZE((uint8_t )0, output_len);
  uint8_t output[output_len];
  memset(output, 0, output_len * sizeof output[0]);
  uint32_t plaintext_len = (uint32_t )3;
  uint8_t plaintext[3] = { (uint8_t )0x61, (uint8_t )0x62, (uint8_t )0x63 };
  uint8_t
  expected[64] =
    {
      (uint8_t )0xdd, (uint8_t )0xaf, (uint8_t )0x35, (uint8_t )0xa1, (uint8_t )0x93, (uint8_t )0x61,
      (uint8_t )0x7a, (uint8_t )0xba, (uint8_t )0xcc, (uint8_t )0x41, (uint8_t )0x73, (uint8_t )0x49,
      (uint8_t )0xae, (uint8_t )0x20, (uint8_t )0x41, (uint8_t )0x31, (uint8_t )0x12, (uint8_t )0xe6,
      (uint8_t )0xfa, (uint8_t )0x4e, (uint8_t )0x89, (uint8_t )0xa9, (uint8_t )0x7e, (uint8_t )0xa2,
      (uint8_t )0x0a, (uint8_t )0x9e, (uint8_t )0xee, (uint8_t )0xe6, (uint8_t )0x4b, (uint8_t )0x55,
      (uint8_t )0xd3, (uint8_t )0x9a, (uint8_t )0x21, (uint8_t )0x92, (uint8_t )0x99, (uint8_t )0x2a,
      (uint8_t )0x27, (uint8_t )0x4f, (uint8_t )0xc1, (uint8_t )0xa8, (uint8_t )0x36, (uint8_t )0xba,
      (uint8_t )0x3c, (uint8_t )0x23, (uint8_t )0xa3, (uint8_t )0xfe, (uint8_t )0xeb, (uint8_t )0xbd,
      (uint8_t )0x45, (uint8_t )0x4d, (uint8_t )0x44, (uint8_t )0x23, (uint8_t )0x64, (uint8_t )0x3c,
      (uint8_t )0xe8, (uint8_t )0x0e, (uint8_t )0x2a, (uint8_t )0x9a, (uint8_t )0xc9, (uint8_t )0x4f,
      (uint8_t )0xa5, (uint8_t )0x4c, (uint8_t )0xa4, (uint8_t )0x9f
    };
  KRML_CHECK_SIZE((uint64_t )0, size_state);
  uint64_t buf[size_state];
  memset(buf, 0, size_state * sizeof buf[0]);
  hash(output, plaintext, plaintext_len);
  TestLib_compare_and_print("Test 1b", expected, output, (uint32_t )64);
}

void test_2a()
{
  uint32_t output_len = (uint32_t )64;
  KRML_CHECK_SIZE((uint8_t )0, output_len);
  uint8_t output[output_len];
  memset(output, 0, output_len * sizeof output[0]);
  uint32_t plaintext_len = (uint32_t )0;
  uint8_t plaintext[0] = {  };
  uint8_t
  expected[64] =
    {
      (uint8_t )0xcf, (uint8_t )0x83, (uint8_t )0xe1, (uint8_t )0x35, (uint8_t )0x7e, (uint8_t )0xef,
      (uint8_t )0xb8, (uint8_t )0xbd, (uint8_t )0xf1, (uint8_t )0x54, (uint8_t )0x28, (uint8_t )0x50,
      (uint8_t )0xd6, (uint8_t )0x6d, (uint8_t )0x80, (uint8_t )0x07, (uint8_t )0xd6, (uint8_t )0x20,
      (uint8_t )0xe4, (uint8_t )0x05, (uint8_t )0x0b, (uint8_t )0x57, (uint8_t )0x15, (uint8_t )0xdc,
      (uint8_t )0x83, (uint8_t )0xf4, (uint8_t )0xa9, (uint8_t )0x21, (uint8_t )0xd3, (uint8_t )0x6c,
      (uint8_t )0xe9, (uint8_t )0xce, (uint8_t )0x47, (uint8_t )0xd0, (uint8_t )0xd1, (uint8_t )0x3c,
      (uint8_t )0x5d, (uint8_t )0x85, (uint8_t )0xf2, (uint8_t )0xb0, (uint8_t )0xff, (uint8_t )0x83,
      (uint8_t )0x18, (uint8_t )0xd2, (uint8_t )0x87, (uint8_t )0x7e, (uint8_t )0xec, (uint8_t )0x2f,
      (uint8_t )0x63, (uint8_t )0xb9, (uint8_t )0x31, (uint8_t )0xbd, (uint8_t )0x47, (uint8_t )0x41,
      (uint8_t )0x7a, (uint8_t )0x81, (uint8_t )0xa5, (uint8_t )0x38, (uint8_t )0x32, (uint8_t )0x7a,
      (uint8_t )0xf9, (uint8_t )0x27, (uint8_t )0xda, (uint8_t )0x3e
    };
  KRML_CHECK_SIZE((uint64_t )0, size_state);
  uint64_t state[size_state];
  memset(state, 0, size_state * sizeof state[0]);
  init(state);
  update_last(state, plaintext, (uint64_t )plaintext_len);
  finish(state, output);
  TestLib_compare_and_print("Test 2a", expected, output, (uint32_t )64);
}

void test_2b()
{
  uint32_t output_len = (uint32_t )64;
  KRML_CHECK_SIZE((uint8_t )0, output_len);
  uint8_t output[output_len];
  memset(output, 0, output_len * sizeof output[0]);
  uint32_t plaintext_len = (uint32_t )0;
  uint8_t plaintext[0] = {  };
  uint8_t
  expected[64] =
    {
      (uint8_t )0xcf, (uint8_t )0x83, (uint8_t )0xe1, (uint8_t )0x35, (uint8_t )0x7e, (uint8_t )0xef,
      (uint8_t )0xb8, (uint8_t )0xbd, (uint8_t )0xf1, (uint8_t )0x54, (uint8_t )0x28, (uint8_t )0x50,
      (uint8_t )0xd6, (uint8_t )0x6d, (uint8_t )0x80, (uint8_t )0x07, (uint8_t )0xd6, (uint8_t )0x20,
      (uint8_t )0xe4, (uint8_t )0x05, (uint8_t )0x0b, (uint8_t )0x57, (uint8_t )0x15, (uint8_t )0xdc,
      (uint8_t )0x83, (uint8_t )0xf4, (uint8_t )0xa9, (uint8_t )0x21, (uint8_t )0xd3, (uint8_t )0x6c,
      (uint8_t )0xe9, (uint8_t )0xce, (uint8_t )0x47, (uint8_t )0xd0, (uint8_t )0xd1, (uint8_t )0x3c,
      (uint8_t )0x5d, (uint8_t )0x85, (uint8_t )0xf2, (uint8_t )0xb0, (uint8_t )0xff, (uint8_t )0x83,
      (uint8_t )0x18, (uint8_t )0xd2, (uint8_t )0x87, (uint8_t )0x7e, (uint8_t )0xec, (uint8_t )0x2f,
      (uint8_t )0x63, (uint8_t )0xb9, (uint8_t )0x31, (uint8_t )0xbd, (uint8_t )0x47, (uint8_t )0x41,
      (uint8_t )0x7a, (uint8_t )0x81, (uint8_t )0xa5, (uint8_t )0x38, (uint8_t )0x32, (uint8_t )0x7a,
      (uint8_t )0xf9, (uint8_t )0x27, (uint8_t )0xda, (uint8_t )0x3e
    };
  KRML_CHECK_SIZE((uint64_t )0, size_state);
  uint64_t buf[size_state];
  memset(buf, 0, size_state * sizeof buf[0]);
  hash(output, plaintext, plaintext_len);
  TestLib_compare_and_print("Test 2b", expected, output, (uint32_t )64);
}

void test_3a()
{
  uint32_t output_len = (uint32_t )64;
  KRML_CHECK_SIZE((uint8_t )0, output_len);
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
  expected[64] =
    {
      (uint8_t )0x20, (uint8_t )0x4a, (uint8_t )0x8f, (uint8_t )0xc6, (uint8_t )0xdd, (uint8_t )0xa8,
      (uint8_t )0x2f, (uint8_t )0x0a, (uint8_t )0x0c, (uint8_t )0xed, (uint8_t )0x7b, (uint8_t )0xeb,
      (uint8_t )0x8e, (uint8_t )0x08, (uint8_t )0xa4, (uint8_t )0x16, (uint8_t )0x57, (uint8_t )0xc1,
      (uint8_t )0x6e, (uint8_t )0xf4, (uint8_t )0x68, (uint8_t )0xb2, (uint8_t )0x28, (uint8_t )0xa8,
      (uint8_t )0x27, (uint8_t )0x9b, (uint8_t )0xe3, (uint8_t )0x31, (uint8_t )0xa7, (uint8_t )0x03,
      (uint8_t )0xc3, (uint8_t )0x35, (uint8_t )0x96, (uint8_t )0xfd, (uint8_t )0x15, (uint8_t )0xc1,
      (uint8_t )0x3b, (uint8_t )0x1b, (uint8_t )0x07, (uint8_t )0xf9, (uint8_t )0xaa, (uint8_t )0x1d,
      (uint8_t )0x3b, (uint8_t )0xea, (uint8_t )0x57, (uint8_t )0x78, (uint8_t )0x9c, (uint8_t )0xa0,
      (uint8_t )0x31, (uint8_t )0xad, (uint8_t )0x85, (uint8_t )0xc7, (uint8_t )0xa7, (uint8_t )0x1d,
      (uint8_t )0xd7, (uint8_t )0x03, (uint8_t )0x54, (uint8_t )0xec, (uint8_t )0x63, (uint8_t )0x12,
      (uint8_t )0x38, (uint8_t )0xca, (uint8_t )0x34, (uint8_t )0x45
    };
  KRML_CHECK_SIZE((uint64_t )0, size_state);
  uint64_t state[size_state];
  memset(state, 0, size_state * sizeof state[0]);
  init(state);
  update_last(state, plaintext, (uint64_t )plaintext_len);
  finish(state, output);
  TestLib_compare_and_print("Test 3a", expected, output, (uint32_t )64);
}

void test_3b()
{
  uint32_t output_len = (uint32_t )64;
  KRML_CHECK_SIZE((uint8_t )0, output_len);
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
  expected[64] =
    {
      (uint8_t )0x20, (uint8_t )0x4a, (uint8_t )0x8f, (uint8_t )0xc6, (uint8_t )0xdd, (uint8_t )0xa8,
      (uint8_t )0x2f, (uint8_t )0x0a, (uint8_t )0x0c, (uint8_t )0xed, (uint8_t )0x7b, (uint8_t )0xeb,
      (uint8_t )0x8e, (uint8_t )0x08, (uint8_t )0xa4, (uint8_t )0x16, (uint8_t )0x57, (uint8_t )0xc1,
      (uint8_t )0x6e, (uint8_t )0xf4, (uint8_t )0x68, (uint8_t )0xb2, (uint8_t )0x28, (uint8_t )0xa8,
      (uint8_t )0x27, (uint8_t )0x9b, (uint8_t )0xe3, (uint8_t )0x31, (uint8_t )0xa7, (uint8_t )0x03,
      (uint8_t )0xc3, (uint8_t )0x35, (uint8_t )0x96, (uint8_t )0xfd, (uint8_t )0x15, (uint8_t )0xc1,
      (uint8_t )0x3b, (uint8_t )0x1b, (uint8_t )0x07, (uint8_t )0xf9, (uint8_t )0xaa, (uint8_t )0x1d,
      (uint8_t )0x3b, (uint8_t )0xea, (uint8_t )0x57, (uint8_t )0x78, (uint8_t )0x9c, (uint8_t )0xa0,
      (uint8_t )0x31, (uint8_t )0xad, (uint8_t )0x85, (uint8_t )0xc7, (uint8_t )0xa7, (uint8_t )0x1d,
      (uint8_t )0xd7, (uint8_t )0x03, (uint8_t )0x54, (uint8_t )0xec, (uint8_t )0x63, (uint8_t )0x12,
      (uint8_t )0x38, (uint8_t )0xca, (uint8_t )0x34, (uint8_t )0x45
    };
  KRML_CHECK_SIZE((uint64_t )0, size_state);
  uint64_t buf[size_state];
  memset(buf, 0, size_state * sizeof buf[0]);
  hash(output, plaintext, plaintext_len);
  TestLib_compare_and_print("Test 3b", expected, output, (uint32_t )64);
}

void test_4a()
{
  uint32_t output_len = (uint32_t )64;
  KRML_CHECK_SIZE((uint8_t )0, output_len);
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
  expected[64] =
    {
      (uint8_t )0x8e, (uint8_t )0x95, (uint8_t )0x9b, (uint8_t )0x75, (uint8_t )0xda, (uint8_t )0xe3,
      (uint8_t )0x13, (uint8_t )0xda, (uint8_t )0x8c, (uint8_t )0xf4, (uint8_t )0xf7, (uint8_t )0x28,
      (uint8_t )0x14, (uint8_t )0xfc, (uint8_t )0x14, (uint8_t )0x3f, (uint8_t )0x8f, (uint8_t )0x77,
      (uint8_t )0x79, (uint8_t )0xc6, (uint8_t )0xeb, (uint8_t )0x9f, (uint8_t )0x7f, (uint8_t )0xa1,
      (uint8_t )0x72, (uint8_t )0x99, (uint8_t )0xae, (uint8_t )0xad, (uint8_t )0xb6, (uint8_t )0x88,
      (uint8_t )0x90, (uint8_t )0x18, (uint8_t )0x50, (uint8_t )0x1d, (uint8_t )0x28, (uint8_t )0x9e,
      (uint8_t )0x49, (uint8_t )0x00, (uint8_t )0xf7, (uint8_t )0xe4, (uint8_t )0x33, (uint8_t )0x1b,
      (uint8_t )0x99, (uint8_t )0xde, (uint8_t )0xc4, (uint8_t )0xb5, (uint8_t )0x43, (uint8_t )0x3a,
      (uint8_t )0xc7, (uint8_t )0xd3, (uint8_t )0x29, (uint8_t )0xee, (uint8_t )0xb6, (uint8_t )0xdd,
      (uint8_t )0x26, (uint8_t )0x54, (uint8_t )0x5e, (uint8_t )0x96, (uint8_t )0xe5, (uint8_t )0x5b,
      (uint8_t )0x87, (uint8_t )0x4b, (uint8_t )0xe9, (uint8_t )0x09
    };
  KRML_CHECK_SIZE((uint64_t )0, size_state);
  uint64_t state[size_state];
  memset(state, 0, size_state * sizeof state[0]);
  init(state);
  update_last(state, plaintext, (uint64_t )plaintext_len);
  finish(state, output);
  TestLib_compare_and_print("Test 4a", expected, output, (uint32_t )64);
}

void test_4b()
{
  uint32_t output_len = (uint32_t )64;
  KRML_CHECK_SIZE((uint8_t )0, output_len);
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
  expected[64] =
    {
      (uint8_t )0x8e, (uint8_t )0x95, (uint8_t )0x9b, (uint8_t )0x75, (uint8_t )0xda, (uint8_t )0xe3,
      (uint8_t )0x13, (uint8_t )0xda, (uint8_t )0x8c, (uint8_t )0xf4, (uint8_t )0xf7, (uint8_t )0x28,
      (uint8_t )0x14, (uint8_t )0xfc, (uint8_t )0x14, (uint8_t )0x3f, (uint8_t )0x8f, (uint8_t )0x77,
      (uint8_t )0x79, (uint8_t )0xc6, (uint8_t )0xeb, (uint8_t )0x9f, (uint8_t )0x7f, (uint8_t )0xa1,
      (uint8_t )0x72, (uint8_t )0x99, (uint8_t )0xae, (uint8_t )0xad, (uint8_t )0xb6, (uint8_t )0x88,
      (uint8_t )0x90, (uint8_t )0x18, (uint8_t )0x50, (uint8_t )0x1d, (uint8_t )0x28, (uint8_t )0x9e,
      (uint8_t )0x49, (uint8_t )0x00, (uint8_t )0xf7, (uint8_t )0xe4, (uint8_t )0x33, (uint8_t )0x1b,
      (uint8_t )0x99, (uint8_t )0xde, (uint8_t )0xc4, (uint8_t )0xb5, (uint8_t )0x43, (uint8_t )0x3a,
      (uint8_t )0xc7, (uint8_t )0xd3, (uint8_t )0x29, (uint8_t )0xee, (uint8_t )0xb6, (uint8_t )0xdd,
      (uint8_t )0x26, (uint8_t )0x54, (uint8_t )0x5e, (uint8_t )0x96, (uint8_t )0xe5, (uint8_t )0x5b,
      (uint8_t )0x87, (uint8_t )0x4b, (uint8_t )0xe9, (uint8_t )0x09
    };
  KRML_CHECK_SIZE((uint64_t )0, size_state);
  uint64_t buf[size_state];
  memset(buf, 0, size_state * sizeof buf[0]);
  hash(output, plaintext, plaintext_len);
  TestLib_compare_and_print("Test 4b", expected, output, (uint32_t )64);
}

void test_5()
{
  uint32_t output_len = (uint32_t )64;
  KRML_CHECK_SIZE((uint8_t )0, output_len);
  uint8_t output[output_len];
  memset(output, 0, output_len * sizeof output[0]);
  uint32_t plaintext_len = (uint32_t )1000000;
  KRML_CHECK_SIZE((uint8_t )0x61, plaintext_len);
  uint8_t plaintext[plaintext_len];
  for (uintmax_t _i = 0; _i < plaintext_len; ++_i)
    plaintext[_i] = (uint8_t )0x61;
  uint8_t
  expected[64] =
    {
      (uint8_t )0xe7, (uint8_t )0x18, (uint8_t )0x48, (uint8_t )0x3d, (uint8_t )0x0c, (uint8_t )0xe7,
      (uint8_t )0x69, (uint8_t )0x64, (uint8_t )0x4e, (uint8_t )0x2e, (uint8_t )0x42, (uint8_t )0xc7,
      (uint8_t )0xbc, (uint8_t )0x15, (uint8_t )0xb4, (uint8_t )0x63, (uint8_t )0x8e, (uint8_t )0x1f,
      (uint8_t )0x98, (uint8_t )0xb1, (uint8_t )0x3b, (uint8_t )0x20, (uint8_t )0x44, (uint8_t )0x28,
      (uint8_t )0x56, (uint8_t )0x32, (uint8_t )0xa8, (uint8_t )0x03, (uint8_t )0xaf, (uint8_t )0xa9,
      (uint8_t )0x73, (uint8_t )0xeb, (uint8_t )0xde, (uint8_t )0x0f, (uint8_t )0xf2, (uint8_t )0x44,
      (uint8_t )0x87, (uint8_t )0x7e, (uint8_t )0xa6, (uint8_t )0x0a, (uint8_t )0x4c, (uint8_t )0xb0,
      (uint8_t )0x43, (uint8_t )0x2c, (uint8_t )0xe5, (uint8_t )0x77, (uint8_t )0xc3, (uint8_t )0x1b,
      (uint8_t )0xeb, (uint8_t )0x00, (uint8_t )0x9c, (uint8_t )0x5c, (uint8_t )0x2c, (uint8_t )0x49,
      (uint8_t )0xaa, (uint8_t )0x2e, (uint8_t )0x4e, (uint8_t )0xad, (uint8_t )0xb2, (uint8_t )0x17,
      (uint8_t )0xad, (uint8_t )0x8c, (uint8_t )0xc0, (uint8_t )0x9b
    };
  KRML_CHECK_SIZE((uint64_t )0, size_state);
  uint64_t buf[size_state];
  memset(buf, 0, size_state * sizeof buf[0]);
  hash(output, plaintext, plaintext_len);
  TestLib_compare_and_print("Test 5", expected, output, (uint32_t )64);
}

void test_6_loop(uint8_t *plaintext, uint64_t *state, uint32_t max1, uint32_t idx1)
{
  if (idx1 == max1)
    return;
  else
  {
    update(state, plaintext);
    test_6_loop(plaintext, state, max1, idx1 + (uint32_t )1);
    return;
  }
}

void test_6()
{
  uint32_t output_len = (uint32_t )64;
  KRML_CHECK_SIZE((uint8_t )0, output_len);
  uint8_t output[output_len];
  memset(output, 0, output_len * sizeof output[0]);
  uint32_t plaintext_len = (uint32_t )128;
  uint8_t
  plaintext[128] =
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
      (uint8_t )0x6c, (uint8_t )0x6d, (uint8_t )0x6e, (uint8_t )0x6f, (uint8_t )0x61, (uint8_t )0x62,
      (uint8_t )0x63, (uint8_t )0x64, (uint8_t )0x65, (uint8_t )0x66, (uint8_t )0x67, (uint8_t )0x68,
      (uint8_t )0x62, (uint8_t )0x63, (uint8_t )0x64, (uint8_t )0x65, (uint8_t )0x66, (uint8_t )0x67,
      (uint8_t )0x68, (uint8_t )0x69, (uint8_t )0x63, (uint8_t )0x64, (uint8_t )0x65, (uint8_t )0x66,
      (uint8_t )0x67, (uint8_t )0x68, (uint8_t )0x69, (uint8_t )0x6a, (uint8_t )0x64, (uint8_t )0x65,
      (uint8_t )0x66, (uint8_t )0x67, (uint8_t )0x68, (uint8_t )0x69, (uint8_t )0x6a, (uint8_t )0x6b,
      (uint8_t )0x65, (uint8_t )0x66, (uint8_t )0x67, (uint8_t )0x68, (uint8_t )0x69, (uint8_t )0x6a,
      (uint8_t )0x6b, (uint8_t )0x6c, (uint8_t )0x66, (uint8_t )0x67, (uint8_t )0x68, (uint8_t )0x69,
      (uint8_t )0x6a, (uint8_t )0x6b, (uint8_t )0x6c, (uint8_t )0x6d, (uint8_t )0x67, (uint8_t )0x68,
      (uint8_t )0x69, (uint8_t )0x6a, (uint8_t )0x6b, (uint8_t )0x6c, (uint8_t )0x6d, (uint8_t )0x6e,
      (uint8_t )0x68, (uint8_t )0x69, (uint8_t )0x6a, (uint8_t )0x6b, (uint8_t )0x6c, (uint8_t )0x6d,
      (uint8_t )0x6e, (uint8_t )0x6f
    };
  uint8_t
  expected[64] =
    {
      (uint8_t )0xb4, (uint8_t )0x7c, (uint8_t )0x93, (uint8_t )0x34, (uint8_t )0x21, (uint8_t )0xea,
      (uint8_t )0x2d, (uint8_t )0xb1, (uint8_t )0x49, (uint8_t )0xad, (uint8_t )0x6e, (uint8_t )0x10,
      (uint8_t )0xfc, (uint8_t )0xe6, (uint8_t )0xc7, (uint8_t )0xf9, (uint8_t )0x3d, (uint8_t )0x07,
      (uint8_t )0x52, (uint8_t )0x38, (uint8_t )0x01, (uint8_t )0x80, (uint8_t )0xff, (uint8_t )0xd7,
      (uint8_t )0xf4, (uint8_t )0x62, (uint8_t )0x9a, (uint8_t )0x71, (uint8_t )0x21, (uint8_t )0x34,
      (uint8_t )0x83, (uint8_t )0x1d, (uint8_t )0x77, (uint8_t )0xbe, (uint8_t )0x60, (uint8_t )0x91,
      (uint8_t )0xb8, (uint8_t )0x19, (uint8_t )0xed, (uint8_t )0x35, (uint8_t )0x2c, (uint8_t )0x29,
      (uint8_t )0x67, (uint8_t )0xa2, (uint8_t )0xe2, (uint8_t )0xd4, (uint8_t )0xfa, (uint8_t )0x50,
      (uint8_t )0x50, (uint8_t )0x72, (uint8_t )0x3c, (uint8_t )0x96, (uint8_t )0x30, (uint8_t )0x69,
      (uint8_t )0x1f, (uint8_t )0x1a, (uint8_t )0x05, (uint8_t )0xa7, (uint8_t )0x28, (uint8_t )0x1d,
      (uint8_t )0xbe, (uint8_t )0x6c, (uint8_t )0x10, (uint8_t )0x86
    };
  KRML_CHECK_SIZE((uint64_t )0, size_state);
  uint64_t state[size_state];
  memset(state, 0, size_state * sizeof state[0]);
  init(state);
  test_6_loop(plaintext, state, (uint32_t )8388607, (uint32_t )0);
  (void )((uint32_t )128 * (uint32_t )8388607 % size_block);
  update_last(state, plaintext, (uint64_t )plaintext_len);
  finish(state, output);
  TestLib_compare_and_print("Test 6", expected, output, (uint32_t )64);
}

#define PLAINLEN (16*1024)
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

  uint8_t hash_res[32];
  TestLib_cycles a,b;
  clock_t t1,t2;

  // HaCl
  t1 = clock();
  a = TestLib_cpucycles_begin();
  for (int i = 0; i < ROUNDS; i++){
    hash(hash_res,plain,len);
    plain[0] = hash_res[0];
  }
  b = TestLib_cpucycles_end();
  t2 = clock();
  print_results("HACL SHA512 speed", (double)t2-t1,
		(double) b - a, ROUNDS, PLAINLEN);
  for (int i = 0; i < PLAINLEN; i++)
    res += (uint64_t) plain[i];
  printf("Composite result (ignore): %llx\n", res);

  // Libsodium
  t1 = clock();
  a = TestLib_cpucycles_begin();
  for (int i = 0; i < ROUNDS; i++){
    crypto_hash_sha512(hash_res, plain, len);
  }
  b = TestLib_cpucycles_end();
  t2 = clock();
  print_results("Sodium SHA512 speed", (double)t2-t1,
		(double) b - a, ROUNDS, PLAINLEN);
  for (int i = 0; i < PLAINLEN; i++)
    res += (uint64_t) plain[i];
  printf("Composite result (ignore): %llx\n", res);

  // OpenSSL
  t1 = clock();
  a = TestLib_cpucycles_begin();
  for (int i = 0; i < ROUNDS; i++){
    ossl_sha512(hash_res,plain, len);
  }
  b = TestLib_cpucycles_end();
  t2 = clock();
  print_results("OpenSSL SHA512 speed", (double)t2-t1,
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
  test_6();
  perf_sha();
  return exit_success;
}

