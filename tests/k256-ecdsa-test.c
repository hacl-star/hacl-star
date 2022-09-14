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
#include <secp256k1.h>

#include "Hacl_K256_ECDSA.h"

#include "test_helpers.h"
#include "k256-ecdsa_vectors.h"

#define ROUNDS 32768

static uint8_t sk2[32U] = {
    (uint8_t)0xebU, (uint8_t)0xb2U, (uint8_t)0xc0U, (uint8_t)0x82U, (uint8_t)0xfdU, (uint8_t)0x77U,
    (uint8_t)0x27U, (uint8_t)0x89U, (uint8_t)0x0aU, (uint8_t)0x28U, (uint8_t)0xacU, (uint8_t)0x82U,
    (uint8_t)0xf6U, (uint8_t)0xbdU, (uint8_t)0xf9U, (uint8_t)0x7bU, (uint8_t)0xadU, (uint8_t)0x8dU,
    (uint8_t)0xe9U, (uint8_t)0xf5U, (uint8_t)0xd7U, (uint8_t)0xc9U, (uint8_t)0x02U, (uint8_t)0x86U,
    (uint8_t)0x92U, (uint8_t)0xdeU, (uint8_t)0x1aU, (uint8_t)0x25U, (uint8_t)0x5cU, (uint8_t)0xadU,
    (uint8_t)0x3eU, (uint8_t)0x0fU };

static uint8_t pk2[64U] = {
    (uint8_t)0x77U, (uint8_t)0x9dU, (uint8_t)0xd1U, (uint8_t)0x97U, (uint8_t)0xa5U, (uint8_t)0xdfU,
    (uint8_t)0x97U, (uint8_t)0x7eU, (uint8_t)0xd2U, (uint8_t)0xcfU, (uint8_t)0x6cU, (uint8_t)0xb3U,
    (uint8_t)0x1dU, (uint8_t)0x82U, (uint8_t)0xd4U, (uint8_t)0x33U, (uint8_t)0x28U, (uint8_t)0xb7U,
    (uint8_t)0x90U, (uint8_t)0xdcU, (uint8_t)0x6bU, (uint8_t)0x3bU, (uint8_t)0x7dU, (uint8_t)0x44U,
    (uint8_t)0x37U, (uint8_t)0xa4U, (uint8_t)0x27U, (uint8_t)0xbdU, (uint8_t)0x58U, (uint8_t)0x47U,
    (uint8_t)0xdfU, (uint8_t)0xcdU, (uint8_t)0xe9U, (uint8_t)0x4bU, (uint8_t)0x72U, (uint8_t)0x4aU,
    (uint8_t)0x55U, (uint8_t)0x5bU, (uint8_t)0x6dU, (uint8_t)0x01U, (uint8_t)0x7bU, (uint8_t)0xb7U,
    (uint8_t)0x60U, (uint8_t)0x7cU, (uint8_t)0x3eU, (uint8_t)0x32U, (uint8_t)0x81U, (uint8_t)0xdaU,
    (uint8_t)0xf5U, (uint8_t)0xb1U, (uint8_t)0x69U, (uint8_t)0x9dU, (uint8_t)0x6eU, (uint8_t)0xf4U,
    (uint8_t)0x12U, (uint8_t)0x49U, (uint8_t)0x75U, (uint8_t)0xc9U, (uint8_t)0x23U, (uint8_t)0x7bU,
    (uint8_t)0x91U, (uint8_t)0x7dU, (uint8_t)0x42U, (uint8_t)0x6fU };

static uint8_t nonce2[32U] = {
    (uint8_t)0x49U, (uint8_t)0xa0U, (uint8_t)0xd7U, (uint8_t)0xb7U, (uint8_t)0x86U, (uint8_t)0xecU,
    (uint8_t)0x9cU, (uint8_t)0xdeU, (uint8_t)0x0dU, (uint8_t)0x07U, (uint8_t)0x21U, (uint8_t)0xd7U,
    (uint8_t)0x28U, (uint8_t)0x04U, (uint8_t)0xbeU, (uint8_t)0xfdU, (uint8_t)0x06U, (uint8_t)0x57U,
    (uint8_t)0x1cU, (uint8_t)0x97U, (uint8_t)0x4bU, (uint8_t)0x19U, (uint8_t)0x1eU, (uint8_t)0xfbU,
    (uint8_t)0x42U, (uint8_t)0xecU, (uint8_t)0xf3U, (uint8_t)0x22U, (uint8_t)0xbaU, (uint8_t)0x9dU,
    (uint8_t)0xddU, (uint8_t)0x9aU };

static uint8_t msgHash2[32U] = {
    (uint8_t)0x4bU, (uint8_t)0x68U, (uint8_t)0x8dU, (uint8_t)0xf4U, (uint8_t)0x0bU, (uint8_t)0xceU,
    (uint8_t)0xdbU, (uint8_t)0xe6U, (uint8_t)0x41U, (uint8_t)0xddU, (uint8_t)0xb1U, (uint8_t)0x6fU,
    (uint8_t)0xf0U, (uint8_t)0xa1U, (uint8_t)0x84U, (uint8_t)0x2dU, (uint8_t)0x9cU, (uint8_t)0x67U,
    (uint8_t)0xeaU, (uint8_t)0x1cU, (uint8_t)0x3bU, (uint8_t)0xf6U, (uint8_t)0x3fU, (uint8_t)0x3eU,
    (uint8_t)0x04U, (uint8_t)0x71U, (uint8_t)0xbaU, (uint8_t)0xa6U, (uint8_t)0x64U, (uint8_t)0x53U,
    (uint8_t)0x1dU, (uint8_t)0x1aU };

static uint8_t sgnt2[64U] = {
    (uint8_t)0x24U, (uint8_t)0x10U, (uint8_t)0x97U, (uint8_t)0xefU, (uint8_t)0xbfU, (uint8_t)0x8bU,
    (uint8_t)0x63U, (uint8_t)0xbfU, (uint8_t)0x14U, (uint8_t)0x5cU, (uint8_t)0x89U, (uint8_t)0x61U,
    (uint8_t)0xdbU, (uint8_t)0xdfU, (uint8_t)0x10U, (uint8_t)0xc3U, (uint8_t)0x10U, (uint8_t)0xefU,
    (uint8_t)0xbbU, (uint8_t)0x3bU, (uint8_t)0x26U, (uint8_t)0x76U, (uint8_t)0xbbU, (uint8_t)0xc0U,
    (uint8_t)0xf8U, (uint8_t)0xb0U, (uint8_t)0x85U, (uint8_t)0x05U, (uint8_t)0xc9U, (uint8_t)0xe2U,
    (uint8_t)0xf7U, (uint8_t)0x95U,
    (uint8_t)0x02U, (uint8_t)0x10U, (uint8_t)0x06U, (uint8_t)0xb7U, (uint8_t)0x83U, (uint8_t)0x86U,
    (uint8_t)0x09U, (uint8_t)0x33U, (uint8_t)0x9eU, (uint8_t)0x8bU, (uint8_t)0x41U, (uint8_t)0x5aU,
    (uint8_t)0x7fU, (uint8_t)0x9aU, (uint8_t)0xcbU, (uint8_t)0x1bU, (uint8_t)0x66U, (uint8_t)0x18U,
    (uint8_t)0x28U, (uint8_t)0x13U, (uint8_t)0x1aU, (uint8_t)0xefU, (uint8_t)0x1eU, (uint8_t)0xcbU,
    (uint8_t)0xc7U, (uint8_t)0x95U, (uint8_t)0x5dU, (uint8_t)0xfbU, (uint8_t)0x01U, (uint8_t)0xf3U,
    (uint8_t)0xcaU, (uint8_t)0x0eU };


bool print_test(
  uint8_t *pk_x, // 32 bytes
  uint8_t *pk_y, // 32 bytes
  size_t msg_len,
  uint8_t *msg,
  uint8_t *sgnt_r, // 32 bytes
  uint8_t *sgnt_s, // 32 bytes
  int id,
  bool valid
){
  uint8_t pk_raw[64];
  memcpy(pk_raw, pk_x, (uint32_t)32U * sizeof (uint8_t));
  memcpy(pk_raw + (uint32_t)32U, pk_y, (uint32_t)32U * sizeof (uint8_t));

  uint8_t signature[64];
  memcpy(signature, sgnt_r, (uint32_t)32U * sizeof (uint8_t));
  memcpy(signature + (uint32_t)32U, sgnt_s, (uint32_t)32U * sizeof (uint8_t));

  printf("K256 ECDSA verify Result: ");
  bool ver = Hacl_K256_ECDSA_ecdsa_verify_sha256(msg_len, msg, pk_raw, signature);
  if (ver == valid) printf("Success! %d \n", id);
  else printf("Failed %d \n", id);
  return (ver == valid);
}


bool test_public_key_compressed(
  uint8_t *pk_x, // 32 bytes
  uint8_t *pk_y, // 32 bytes
  int id)
{
  uint8_t pk_raw[64];
  memcpy(pk_raw, pk_x, (uint32_t)32U * sizeof (uint8_t));
  memcpy(pk_raw + (uint32_t)32U, pk_y, (uint32_t)32U * sizeof (uint8_t));

  uint8_t pk_c[33U] = { 0U };
  uint8_t pk_raw_c[64U] = { 0U };
  Hacl_K256_ECDSA_public_key_compressed_from_raw(pk_c, pk_raw);
  bool b = Hacl_K256_ECDSA_public_key_compressed_to_raw(pk_raw_c, pk_c);

  printf("K256 public-key-compressed Result %d : ", id);
  if (!b) {
    printf("Failed (None)! \n");
    return false;
  }

  bool ver = compare(64U, pk_raw, pk_raw_c);
  return ver;
}


bool test_public_key_uncompressed(
  uint8_t *pk_x, // 32 bytes
  uint8_t *pk_y, // 32 bytes
  int id)
{
  uint8_t pk_raw[64];
  memcpy(pk_raw, pk_x, (uint32_t)32U * sizeof (uint8_t));
  memcpy(pk_raw + (uint32_t)32U, pk_y, (uint32_t)32U * sizeof (uint8_t));

  uint8_t pk_u[65U] = { 0U };
  uint8_t pk_raw_u[64U] = { 0U };
  Hacl_K256_ECDSA_public_key_uncompressed_from_raw(pk_u, pk_raw);
  bool b = Hacl_K256_ECDSA_public_key_uncompressed_to_raw(pk_raw_u, pk_u);

  printf("K256 public-key-uncompressed Result %d : ", id);
  if (!b) {
    printf("Failed (None)! \n");
    return false;
  }

  bool ver = compare(64U, pk_raw, pk_raw_u);
  return ver;
}


int main() {
  bool ok = true;
  for (int i = 0; i < sizeof(vectors)/sizeof(k256ecdsa_verify_test_vector); ++i) {
    ok &= print_test(vectors[i].pk_x,vectors[i].pk_y,vectors[i].msg_len,vectors[i].msg,
                     vectors[i].sgnt_r,vectors[i].sgnt_s,vectors[i].id,vectors[i].valid);
    ok &= test_public_key_uncompressed(vectors[i].pk_x,vectors[i].pk_y,vectors[i].id);
    ok &= test_public_key_compressed(vectors[i].pk_x,vectors[i].pk_y,vectors[i].id);
    printf("\n");
  }

  if (ok)
    printf ("\n Success :) \n");
  else
    printf ("\n Failed :( \n");


  // Benchmarking for signing (HACL)
  uint64_t count = ROUNDS;
  uint8_t signature[64U] = { 0U };
  bool b1 = true;
  bool b2 = true;

  for (int j = 0; j < ROUNDS; j++) {
    b1 &= Hacl_K256_ECDSA_ecdsa_sign_hashed_msg(signature, msgHash2, sk2, nonce2);
  }

  cycles a,b;
  clock_t t1,t2;
  t1 = clock();
  a = cpucycles_begin();
  for (int j = 0; j < ROUNDS; j++) {
    b1 &= Hacl_K256_ECDSA_ecdsa_sign_hashed_msg(signature, msgHash2, sk2, nonce2);
  }
  b = cpucycles_end();
  t2 = clock();
  double diff1 = t2 - t1;
  uint64_t cyc1 = b - a;

  // Benchmarking for verifying (HACL)
  for (int j = 0; j < ROUNDS; j++) {
    b2 &= Hacl_K256_ECDSA_ecdsa_verify_hashed_msg(msgHash2, pk2, sgnt2);
  }

  t1 = clock();
  a = cpucycles_begin();
  for (int j = 0; j < ROUNDS; j++) {
    b2 &= Hacl_K256_ECDSA_ecdsa_verify_hashed_msg(msgHash2, pk2, sgnt2);
  }
  b = cpucycles_end();
  t2 = clock();
  double diff2 = t2 - t1;
  uint64_t cyc2 = b - a;

  printf("\n ECDSA K256 Signing:\n");
  print_time(count,diff1,cyc1);
  printf("\n ECDSA K256 Verifying:\n");
  print_time(count,diff2,cyc2);


  // Benchmarking for signing (libsecp256k-latest)
  secp256k1_pubkey pubkey;
  secp256k1_ecdsa_signature sig;
  unsigned char serialized_signature[64];
  unsigned char compressed_pubkey[33];
  secp256k1_context* ctx = secp256k1_context_create(SECP256K1_CONTEXT_SIGN | SECP256K1_CONTEXT_VERIFY);

  int b3 = 1;
  int b4 = 1;

  for (int j = 0; j < ROUNDS; j++) {
    b3 &= secp256k1_ecdsa_sign(ctx, &sig, msgHash2, sk2, NULL, NULL);
  }

  t1 = clock();
  a = cpucycles_begin();
  for (int j = 0; j < ROUNDS; j++) {
    b3 &= secp256k1_ecdsa_sign(ctx, &sig, msgHash2, sk2, NULL, NULL);
  }
  b = cpucycles_end();
  t2 = clock();
  double diff3 = t2 - t1;
  uint64_t cyc3 = b - a;

  //b3 &= secp256k1_ecdsa_signature_serialize_compact(ctx, serialized_signature, &sig);
  b3 &= secp256k1_ecdsa_signature_parse_compact(ctx, &sig, sgnt2);
  Hacl_K256_ECDSA_public_key_compressed_from_raw(compressed_pubkey, pk2);
  b3 &= secp256k1_ec_pubkey_parse(ctx, &pubkey, compressed_pubkey, sizeof(compressed_pubkey));


  for (int j = 0; j < ROUNDS; j++) {
    b4 &= secp256k1_ecdsa_verify(ctx, &sig, msgHash2, &pubkey);
  }

  t1 = clock();
  a = cpucycles_begin();
  for (int j = 0; j < ROUNDS; j++) {
    b4 &= secp256k1_ecdsa_verify(ctx, &sig, msgHash2, &pubkey);
  }
  b = cpucycles_end();
  t2 = clock();
  double diff4 = t2 - t1;
  uint64_t cyc4 = b - a;


  printf("\n libsecp256k: \n");
  printf("\n ECDSA K256 Signing:\n");
  print_time(count,diff3,cyc3);
  printf("\n ECDSA K256 Verifying:\n");
  print_time(count,diff4,cyc4);


  if (ok) return EXIT_SUCCESS;
  else return EXIT_FAILURE;
}
