#include "HMAC_SHA2_256.h"
#include "kremlib.h"
#include "testlib.h"

void test_1();

void test_2();

void test_3();

void test_4();

void test_5();

void test_6();

void test_7();

int32_t main();


void test_1()
{
  uint32_t output_len = (uint32_t )32;
  uint8_t output[output_len];
  memset(output, 0, output_len * sizeof output[0]);
  uint8_t key0[3] = { (uint8_t )0x61, (uint8_t )0x62, (uint8_t )0x63 };
  uint32_t key_len = (uint32_t )20;
  uint8_t key[key_len];
  for (uintmax_t i = 0; i < key_len; ++i)
    key[i] = (uint8_t )0x0b;
  uint32_t data_len = (uint32_t )8;
  uint8_t
  data[8] =
    {
      (uint8_t )0x48, (uint8_t )0x69, (uint8_t )0x20, (uint8_t )0x54, (uint8_t )0x68, (uint8_t )0x65,
      (uint8_t )0x72, (uint8_t )0x65
    };
  uint8_t
  expected[32] =
    {
      (uint8_t )0xb0, (uint8_t )0x34, (uint8_t )0x4c, (uint8_t )0x61, (uint8_t )0xd8, (uint8_t )0xdb,
      (uint8_t )0x38, (uint8_t )0x53, (uint8_t )0x5c, (uint8_t )0xa8, (uint8_t )0xaf, (uint8_t )0xce,
      (uint8_t )0xaf, (uint8_t )0x0b, (uint8_t )0xf1, (uint8_t )0x2b, (uint8_t )0x88, (uint8_t )0x1d,
      (uint8_t )0xc2, (uint8_t )0x00, (uint8_t )0xc9, (uint8_t )0x83, (uint8_t )0x3d, (uint8_t )0xa7,
      (uint8_t )0x26, (uint8_t )0xe9, (uint8_t )0x37, (uint8_t )0x6c, (uint8_t )0x2e, (uint8_t )0x32,
      (uint8_t )0xcf, (uint8_t )0xf7
    };
  uint32_t ctx[153] = { 0 };
  HMAC_SHA2_256_hmac_sha2_256(output, key, key_len, data, data_len);
  TestLib_compare_and_print("Test 1", expected, output, (uint32_t )32);
}

void test_2()
{
  uint32_t output_len = (uint32_t )32;
  uint8_t output[output_len];
  memset(output, 0, output_len * sizeof output[0]);
  uint8_t key0[3] = { (uint8_t )0x61, (uint8_t )0x62, (uint8_t )0x63 };
  uint32_t key_len = (uint32_t )4;
  uint8_t key[4] = { (uint8_t )0x4a, (uint8_t )0x65, (uint8_t )0x66, (uint8_t )0x65 };
  uint32_t data_len = (uint32_t )28;
  uint8_t
  data[28] =
    {
      (uint8_t )0x77, (uint8_t )0x68, (uint8_t )0x61, (uint8_t )0x74, (uint8_t )0x20, (uint8_t )0x64,
      (uint8_t )0x6f, (uint8_t )0x20, (uint8_t )0x79, (uint8_t )0x61, (uint8_t )0x20, (uint8_t )0x77,
      (uint8_t )0x61, (uint8_t )0x6e, (uint8_t )0x74, (uint8_t )0x20, (uint8_t )0x66, (uint8_t )0x6f,
      (uint8_t )0x72, (uint8_t )0x20, (uint8_t )0x6e, (uint8_t )0x6f, (uint8_t )0x74, (uint8_t )0x68,
      (uint8_t )0x69, (uint8_t )0x6e, (uint8_t )0x67, (uint8_t )0x3f
    };
  uint8_t
  expected[32] =
    {
      (uint8_t )0x5b, (uint8_t )0xdc, (uint8_t )0xc1, (uint8_t )0x46, (uint8_t )0xbf, (uint8_t )0x60,
      (uint8_t )0x75, (uint8_t )0x4e, (uint8_t )0x6a, (uint8_t )0x04, (uint8_t )0x24, (uint8_t )0x26,
      (uint8_t )0x08, (uint8_t )0x95, (uint8_t )0x75, (uint8_t )0xc7, (uint8_t )0x5a, (uint8_t )0x00,
      (uint8_t )0x3f, (uint8_t )0x08, (uint8_t )0x9d, (uint8_t )0x27, (uint8_t )0x39, (uint8_t )0x83,
      (uint8_t )0x9d, (uint8_t )0xec, (uint8_t )0x58, (uint8_t )0xb9, (uint8_t )0x64, (uint8_t )0xec,
      (uint8_t )0x38, (uint8_t )0x43
    };
  uint32_t ctx[153] = { 0 };
  HMAC_SHA2_256_hmac_sha2_256(output, key, key_len, data, data_len);
  TestLib_compare_and_print("Test 2", expected, output, (uint32_t )32);
}

void test_3()
{
  uint32_t output_len = (uint32_t )32;
  uint8_t output[output_len];
  memset(output, 0, output_len * sizeof output[0]);
  uint8_t key0[3] = { (uint8_t )0x61, (uint8_t )0x62, (uint8_t )0x63 };
  uint32_t key_len = (uint32_t )20;
  uint8_t key[key_len];
  for (uintmax_t i = 0; i < key_len; ++i)
    key[i] = (uint8_t )0xaa;
  uint32_t data_len = (uint32_t )50;
  uint8_t data[data_len];
  for (uintmax_t i = 0; i < data_len; ++i)
    data[i] = (uint8_t )0xdd;
  uint8_t
  expected[32] =
    {
      (uint8_t )0x77, (uint8_t )0x3e, (uint8_t )0xa9, (uint8_t )0x1e, (uint8_t )0x36, (uint8_t )0x80,
      (uint8_t )0x0e, (uint8_t )0x46, (uint8_t )0x85, (uint8_t )0x4d, (uint8_t )0xb8, (uint8_t )0xeb,
      (uint8_t )0xd0, (uint8_t )0x91, (uint8_t )0x81, (uint8_t )0xa7, (uint8_t )0x29, (uint8_t )0x59,
      (uint8_t )0x09, (uint8_t )0x8b, (uint8_t )0x3e, (uint8_t )0xf8, (uint8_t )0xc1, (uint8_t )0x22,
      (uint8_t )0xd9, (uint8_t )0x63, (uint8_t )0x55, (uint8_t )0x14, (uint8_t )0xce, (uint8_t )0xd5,
      (uint8_t )0x65, (uint8_t )0xfe
    };
  uint32_t ctx[153] = { 0 };
  HMAC_SHA2_256_hmac_sha2_256(output, key, key_len, data, data_len);
  TestLib_compare_and_print("Test 3", expected, output, (uint32_t )32);
}

void test_4()
{
  uint32_t output_len = (uint32_t )32;
  uint8_t output[output_len];
  memset(output, 0, output_len * sizeof output[0]);
  uint8_t key0[3] = { (uint8_t )0x61, (uint8_t )0x62, (uint8_t )0x63 };
  uint32_t key_len = (uint32_t )25;
  uint8_t
  key[25] =
    {
      (uint8_t )0x01, (uint8_t )0x02, (uint8_t )0x03, (uint8_t )0x04, (uint8_t )0x05, (uint8_t )0x06,
      (uint8_t )0x07, (uint8_t )0x08, (uint8_t )0x09, (uint8_t )0x0a, (uint8_t )0x0b, (uint8_t )0x0c,
      (uint8_t )0x0d, (uint8_t )0x0e, (uint8_t )0x0f, (uint8_t )0x10, (uint8_t )0x11, (uint8_t )0x12,
      (uint8_t )0x13, (uint8_t )0x14, (uint8_t )0x15, (uint8_t )0x16, (uint8_t )0x17, (uint8_t )0x18,
      (uint8_t )0x19
    };
  uint32_t data_len = (uint32_t )50;
  uint8_t data[data_len];
  for (uintmax_t i = 0; i < data_len; ++i)
    data[i] = (uint8_t )0xcd;
  uint8_t
  expected[32] =
    {
      (uint8_t )0x82, (uint8_t )0x55, (uint8_t )0x8a, (uint8_t )0x38, (uint8_t )0x9a, (uint8_t )0x44,
      (uint8_t )0x3c, (uint8_t )0x0e, (uint8_t )0xa4, (uint8_t )0xcc, (uint8_t )0x81, (uint8_t )0x98,
      (uint8_t )0x99, (uint8_t )0xf2, (uint8_t )0x08, (uint8_t )0x3a, (uint8_t )0x85, (uint8_t )0xf0,
      (uint8_t )0xfa, (uint8_t )0xa3, (uint8_t )0xe5, (uint8_t )0x78, (uint8_t )0xf8, (uint8_t )0x07,
      (uint8_t )0x7a, (uint8_t )0x2e, (uint8_t )0x3f, (uint8_t )0xf4, (uint8_t )0x67, (uint8_t )0x29,
      (uint8_t )0x66, (uint8_t )0x5b
    };
  uint32_t ctx[153] = { 0 };
  HMAC_SHA2_256_hmac_sha2_256(output, key, key_len, data, data_len);
  TestLib_compare_and_print("Test 4", expected, output, (uint32_t )32);
}

void test_5()
{
  uint32_t output_len = (uint32_t )32;
  uint8_t output[output_len];
  for (uintmax_t i = 0; i < output_len; ++i)
    output[i] = (uint8_t )0x00;
  uint32_t key_len = (uint32_t )20;
  uint8_t key[key_len];
  for (uintmax_t i = 0; i < key_len; ++i)
    key[i] = (uint8_t )0x0c;
  uint32_t data_len = (uint32_t )20;
  uint8_t
  data[20] =
    {
      (uint8_t )0x54, (uint8_t )0x65, (uint8_t )0x73, (uint8_t )0x74, (uint8_t )0x20, (uint8_t )0x57,
      (uint8_t )0x69, (uint8_t )0x74, (uint8_t )0x68, (uint8_t )0x20, (uint8_t )0x54, (uint8_t )0x72,
      (uint8_t )0x75, (uint8_t )0x6e, (uint8_t )0x63, (uint8_t )0x61, (uint8_t )0x74, (uint8_t )0x69,
      (uint8_t )0x6f, (uint8_t )0x6e
    };
  uint8_t
  expected[16] =
    {
      (uint8_t )0xa3, (uint8_t )0xb6, (uint8_t )0x16, (uint8_t )0x74, (uint8_t )0x73, (uint8_t )0x10,
      (uint8_t )0x0e, (uint8_t )0xe0, (uint8_t )0x6e, (uint8_t )0x0c, (uint8_t )0x79, (uint8_t )0x6c,
      (uint8_t )0x29, (uint8_t )0x55, (uint8_t )0x55, (uint8_t )0x2b
    };
  uint32_t ctx[153] = { 0 };
  HMAC_SHA2_256_hmac_sha2_256(output, key, key_len, data, data_len);
  TestLib_compare_and_print("Test 5", expected, output, (uint32_t )16);
}

void test_6()
{
  uint32_t output_len = (uint32_t )32;
  uint8_t output[output_len];
  memset(output, 0, output_len * sizeof output[0]);
  uint32_t key_len = (uint32_t )131;
  uint8_t key[key_len];
  for (uintmax_t i = 0; i < key_len; ++i)
    key[i] = (uint8_t )0xaa;
  uint32_t data_len = (uint32_t )54;
  uint8_t
  data[54] =
    {
      (uint8_t )0x54, (uint8_t )0x65, (uint8_t )0x73, (uint8_t )0x74, (uint8_t )0x20, (uint8_t )0x55,
      (uint8_t )0x73, (uint8_t )0x69, (uint8_t )0x6e, (uint8_t )0x67, (uint8_t )0x20, (uint8_t )0x4c,
      (uint8_t )0x61, (uint8_t )0x72, (uint8_t )0x67, (uint8_t )0x65, (uint8_t )0x72, (uint8_t )0x20,
      (uint8_t )0x54, (uint8_t )0x68, (uint8_t )0x61, (uint8_t )0x6e, (uint8_t )0x20, (uint8_t )0x42,
      (uint8_t )0x6c, (uint8_t )0x6f, (uint8_t )0x63, (uint8_t )0x6b, (uint8_t )0x2d, (uint8_t )0x53,
      (uint8_t )0x69, (uint8_t )0x7a, (uint8_t )0x65, (uint8_t )0x20, (uint8_t )0x4b, (uint8_t )0x65,
      (uint8_t )0x79, (uint8_t )0x20, (uint8_t )0x2d, (uint8_t )0x20, (uint8_t )0x48, (uint8_t )0x61,
      (uint8_t )0x73, (uint8_t )0x68, (uint8_t )0x20, (uint8_t )0x4b, (uint8_t )0x65, (uint8_t )0x79,
      (uint8_t )0x20, (uint8_t )0x46, (uint8_t )0x69, (uint8_t )0x72, (uint8_t )0x73, (uint8_t )0x74
    };
  uint8_t
  expected[32] =
    {
      (uint8_t )0x60, (uint8_t )0xe4, (uint8_t )0x31, (uint8_t )0x59, (uint8_t )0x1e, (uint8_t )0xe0,
      (uint8_t )0xb6, (uint8_t )0x7f, (uint8_t )0x0d, (uint8_t )0x8a, (uint8_t )0x26, (uint8_t )0xaa,
      (uint8_t )0xcb, (uint8_t )0xf5, (uint8_t )0xb7, (uint8_t )0x7f, (uint8_t )0x8e, (uint8_t )0x0b,
      (uint8_t )0xc6, (uint8_t )0x21, (uint8_t )0x37, (uint8_t )0x28, (uint8_t )0xc5, (uint8_t )0x14,
      (uint8_t )0x05, (uint8_t )0x46, (uint8_t )0x04, (uint8_t )0x0f, (uint8_t )0x0e, (uint8_t )0xe3,
      (uint8_t )0x7f, (uint8_t )0x54
    };
  uint32_t ctx[153] = { 0 };
  HMAC_SHA2_256_hmac_sha2_256(output, key, key_len, data, data_len);
  TestLib_compare_and_print("Test 6", expected, output, (uint32_t )32);
}

void test_7()
{
  uint32_t output_len = (uint32_t )32;
  uint8_t output[output_len];
  memset(output, 0, output_len * sizeof output[0]);
  uint32_t key_len = (uint32_t )131;
  uint8_t key[key_len];
  for (uintmax_t i = 0; i < key_len; ++i)
    key[i] = (uint8_t )0xaa;
  uint32_t data_len = (uint32_t )152;
  uint8_t
  data[152] =
    {
      (uint8_t )0x54, (uint8_t )0x68, (uint8_t )0x69, (uint8_t )0x73, (uint8_t )0x20, (uint8_t )0x69,
      (uint8_t )0x73, (uint8_t )0x20, (uint8_t )0x61, (uint8_t )0x20, (uint8_t )0x74, (uint8_t )0x65,
      (uint8_t )0x73, (uint8_t )0x74, (uint8_t )0x20, (uint8_t )0x75, (uint8_t )0x73, (uint8_t )0x69,
      (uint8_t )0x6e, (uint8_t )0x67, (uint8_t )0x20, (uint8_t )0x61, (uint8_t )0x20, (uint8_t )0x6c,
      (uint8_t )0x61, (uint8_t )0x72, (uint8_t )0x67, (uint8_t )0x65, (uint8_t )0x72, (uint8_t )0x20,
      (uint8_t )0x74, (uint8_t )0x68, (uint8_t )0x61, (uint8_t )0x6e, (uint8_t )0x20, (uint8_t )0x62,
      (uint8_t )0x6c, (uint8_t )0x6f, (uint8_t )0x63, (uint8_t )0x6b, (uint8_t )0x2d, (uint8_t )0x73,
      (uint8_t )0x69, (uint8_t )0x7a, (uint8_t )0x65, (uint8_t )0x20, (uint8_t )0x6b, (uint8_t )0x65,
      (uint8_t )0x79, (uint8_t )0x20, (uint8_t )0x61, (uint8_t )0x6e, (uint8_t )0x64, (uint8_t )0x20,
      (uint8_t )0x61, (uint8_t )0x20, (uint8_t )0x6c, (uint8_t )0x61, (uint8_t )0x72, (uint8_t )0x67,
      (uint8_t )0x65, (uint8_t )0x72, (uint8_t )0x20, (uint8_t )0x74, (uint8_t )0x68, (uint8_t )0x61,
      (uint8_t )0x6e, (uint8_t )0x20, (uint8_t )0x62, (uint8_t )0x6c, (uint8_t )0x6f, (uint8_t )0x63,
      (uint8_t )0x6b, (uint8_t )0x2d, (uint8_t )0x73, (uint8_t )0x69, (uint8_t )0x7a, (uint8_t )0x65,
      (uint8_t )0x20, (uint8_t )0x64, (uint8_t )0x61, (uint8_t )0x74, (uint8_t )0x61, (uint8_t )0x2e,
      (uint8_t )0x20, (uint8_t )0x54, (uint8_t )0x68, (uint8_t )0x65, (uint8_t )0x20, (uint8_t )0x6b,
      (uint8_t )0x65, (uint8_t )0x79, (uint8_t )0x20, (uint8_t )0x6e, (uint8_t )0x65, (uint8_t )0x65,
      (uint8_t )0x64, (uint8_t )0x73, (uint8_t )0x20, (uint8_t )0x74, (uint8_t )0x6f, (uint8_t )0x20,
      (uint8_t )0x62, (uint8_t )0x65, (uint8_t )0x20, (uint8_t )0x68, (uint8_t )0x61, (uint8_t )0x73,
      (uint8_t )0x68, (uint8_t )0x65, (uint8_t )0x64, (uint8_t )0x20, (uint8_t )0x62, (uint8_t )0x65,
      (uint8_t )0x66, (uint8_t )0x6f, (uint8_t )0x72, (uint8_t )0x65, (uint8_t )0x20, (uint8_t )0x62,
      (uint8_t )0x65, (uint8_t )0x69, (uint8_t )0x6e, (uint8_t )0x67, (uint8_t )0x20, (uint8_t )0x75,
      (uint8_t )0x73, (uint8_t )0x65, (uint8_t )0x64, (uint8_t )0x20, (uint8_t )0x62, (uint8_t )0x79,
      (uint8_t )0x20, (uint8_t )0x74, (uint8_t )0x68, (uint8_t )0x65, (uint8_t )0x20, (uint8_t )0x48,
      (uint8_t )0x4d, (uint8_t )0x41, (uint8_t )0x43, (uint8_t )0x20, (uint8_t )0x61, (uint8_t )0x6c,
      (uint8_t )0x67, (uint8_t )0x6f, (uint8_t )0x72, (uint8_t )0x69, (uint8_t )0x74, (uint8_t )0x68,
      (uint8_t )0x6d, (uint8_t )0x2e
    };
  uint8_t
  expected[32] =
    {
      (uint8_t )0x9b, (uint8_t )0x09, (uint8_t )0xff, (uint8_t )0xa7, (uint8_t )0x1b, (uint8_t )0x94,
      (uint8_t )0x2f, (uint8_t )0xcb, (uint8_t )0x27, (uint8_t )0x63, (uint8_t )0x5f, (uint8_t )0xbc,
      (uint8_t )0xd5, (uint8_t )0xb0, (uint8_t )0xe9, (uint8_t )0x44, (uint8_t )0xbf, (uint8_t )0xdc,
      (uint8_t )0x63, (uint8_t )0x64, (uint8_t )0x4f, (uint8_t )0x07, (uint8_t )0x13, (uint8_t )0x93,
      (uint8_t )0x8a, (uint8_t )0x7f, (uint8_t )0x51, (uint8_t )0x53, (uint8_t )0x5c, (uint8_t )0x3a,
      (uint8_t )0x35, (uint8_t )0xe2
    };
  uint32_t ctx[153] = { 0 };
  HMAC_SHA2_256_hmac_sha2_256(output, key, key_len, data, data_len);
  TestLib_compare_and_print("Test 7", expected, output, (uint32_t )32);
}

int32_t main()
{
  test_1();
  test_2();
  test_3();
  test_4();
  test_5();
  test_6();
  test_7();
  return exit_success;
}

