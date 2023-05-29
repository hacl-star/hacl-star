#include <fcntl.h>
#include <inttypes.h>
#include <stdbool.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/stat.h>
#include <sys/types.h>
#include <time.h>
#include <unistd.h>

#include "test_helpers.h"

#include "Hacl_P256.h"

#define ROUNDS 4096

static uint8_t msg[128U] = {
  (uint8_t)89U,  (uint8_t)5U,   (uint8_t)35U,  (uint8_t)136U, (uint8_t)119U,
  (uint8_t)199U, (uint8_t)116U, (uint8_t)33U,  (uint8_t)247U, (uint8_t)62U,
  (uint8_t)67U,  (uint8_t)238U, (uint8_t)61U,  (uint8_t)166U, (uint8_t)242U,
  (uint8_t)217U, (uint8_t)226U, (uint8_t)204U, (uint8_t)173U, (uint8_t)95U,
  (uint8_t)201U, (uint8_t)66U,  (uint8_t)220U, (uint8_t)236U, (uint8_t)12U,
  (uint8_t)189U, (uint8_t)37U,  (uint8_t)72U,  (uint8_t)41U,  (uint8_t)53U,
  (uint8_t)250U, (uint8_t)175U, (uint8_t)65U,  (uint8_t)105U, (uint8_t)131U,
  (uint8_t)254U, (uint8_t)22U,  (uint8_t)91U,  (uint8_t)26U,  (uint8_t)4U,
  (uint8_t)94U,  (uint8_t)226U, (uint8_t)188U, (uint8_t)210U, (uint8_t)230U,
  (uint8_t)220U, (uint8_t)163U, (uint8_t)189U, (uint8_t)244U, (uint8_t)108U,
  (uint8_t)67U,  (uint8_t)16U,  (uint8_t)167U, (uint8_t)70U,  (uint8_t)31U,
  (uint8_t)154U, (uint8_t)55U,  (uint8_t)150U, (uint8_t)12U,  (uint8_t)166U,
  (uint8_t)114U, (uint8_t)211U, (uint8_t)254U, (uint8_t)181U, (uint8_t)71U,
  (uint8_t)62U,  (uint8_t)37U,  (uint8_t)54U,  (uint8_t)5U,   (uint8_t)251U,
  (uint8_t)29U,  (uint8_t)223U, (uint8_t)210U, (uint8_t)128U, (uint8_t)101U,
  (uint8_t)181U, (uint8_t)60U,  (uint8_t)181U, (uint8_t)133U, (uint8_t)138U,
  (uint8_t)138U, (uint8_t)210U, (uint8_t)129U, (uint8_t)117U, (uint8_t)191U,
  (uint8_t)155U, (uint8_t)211U, (uint8_t)134U, (uint8_t)165U, (uint8_t)228U,
  (uint8_t)113U, (uint8_t)234U, (uint8_t)122U, (uint8_t)101U, (uint8_t)193U,
  (uint8_t)124U, (uint8_t)201U, (uint8_t)52U,  (uint8_t)169U, (uint8_t)215U,
  (uint8_t)145U, (uint8_t)233U, (uint8_t)20U,  (uint8_t)145U, (uint8_t)235U,
  (uint8_t)55U,  (uint8_t)84U,  (uint8_t)208U, (uint8_t)55U,  (uint8_t)153U,
  (uint8_t)121U, (uint8_t)15U,  (uint8_t)226U, (uint8_t)211U, (uint8_t)8U,
  (uint8_t)209U, (uint8_t)97U,  (uint8_t)70U,  (uint8_t)213U, (uint8_t)201U,
  (uint8_t)176U, (uint8_t)208U, (uint8_t)222U, (uint8_t)189U, (uint8_t)151U,
  (uint8_t)215U, (uint8_t)156U, (uint8_t)232U
};

static uint8_t private_key[32U] = {
  (uint8_t)81U,  (uint8_t)155U, (uint8_t)66U,  (uint8_t)61U,  (uint8_t)113U,
  (uint8_t)95U,  (uint8_t)139U, (uint8_t)88U,  (uint8_t)31U,  (uint8_t)79U,
  (uint8_t)168U, (uint8_t)238U, (uint8_t)89U,  (uint8_t)244U, (uint8_t)119U,
  (uint8_t)26U,  (uint8_t)91U,  (uint8_t)68U,  (uint8_t)200U, (uint8_t)19U,
  (uint8_t)11U,  (uint8_t)78U,  (uint8_t)62U,  (uint8_t)172U, (uint8_t)202U,
  (uint8_t)84U,  (uint8_t)165U, (uint8_t)109U, (uint8_t)218U, (uint8_t)114U,
  (uint8_t)180U, (uint8_t)100U
};

static uint8_t public_key[64U] = {
  (uint8_t)28U,  (uint8_t)203U, (uint8_t)233U, (uint8_t)28U,  (uint8_t)7U,
  (uint8_t)95U,  (uint8_t)199U, (uint8_t)244U, (uint8_t)240U, (uint8_t)51U,
  (uint8_t)191U, (uint8_t)162U, (uint8_t)72U,  (uint8_t)219U, (uint8_t)143U,
  (uint8_t)204U, (uint8_t)211U, (uint8_t)86U,  (uint8_t)93U,  (uint8_t)233U,
  (uint8_t)75U,  (uint8_t)191U, (uint8_t)177U, (uint8_t)47U,  (uint8_t)60U,
  (uint8_t)89U,  (uint8_t)255U, (uint8_t)70U,  (uint8_t)194U, (uint8_t)113U,
  (uint8_t)191U, (uint8_t)131U, (uint8_t)206U, (uint8_t)64U,  (uint8_t)20U,
  (uint8_t)198U, (uint8_t)136U, (uint8_t)17U,  (uint8_t)249U, (uint8_t)162U,
  (uint8_t)26U,  (uint8_t)31U,  (uint8_t)219U, (uint8_t)44U,  (uint8_t)14U,
  (uint8_t)97U,  (uint8_t)19U,  (uint8_t)224U, (uint8_t)109U, (uint8_t)183U,
  (uint8_t)202U, (uint8_t)147U, (uint8_t)183U, (uint8_t)64U,  (uint8_t)78U,
  (uint8_t)120U, (uint8_t)220U, (uint8_t)124U, (uint8_t)205U, (uint8_t)92U,
  (uint8_t)168U, (uint8_t)154U, (uint8_t)76U,  (uint8_t)169U
};

static uint8_t nonce[32U] = {
  (uint8_t)148U, (uint8_t)161U, (uint8_t)187U, (uint8_t)177U, (uint8_t)75U,
  (uint8_t)144U, (uint8_t)106U, (uint8_t)97U,  (uint8_t)162U, (uint8_t)128U,
  (uint8_t)242U, (uint8_t)69U,  (uint8_t)249U, (uint8_t)233U, (uint8_t)60U,
  (uint8_t)127U, (uint8_t)59U,  (uint8_t)74U,  (uint8_t)98U,  (uint8_t)71U,
  (uint8_t)130U, (uint8_t)79U,  (uint8_t)93U,  (uint8_t)51U,  (uint8_t)185U,
  (uint8_t)103U, (uint8_t)7U,   (uint8_t)135U, (uint8_t)100U, (uint8_t)42U,
  (uint8_t)104U, (uint8_t)222U
};

static uint8_t sgnt[64U] = {
  (uint8_t)243U, (uint8_t)172U, (uint8_t)128U, (uint8_t)97U,  (uint8_t)181U,
  (uint8_t)20U,  (uint8_t)121U, (uint8_t)91U,  (uint8_t)136U, (uint8_t)67U,
  (uint8_t)227U, (uint8_t)214U, (uint8_t)98U,  (uint8_t)149U, (uint8_t)39U,
  (uint8_t)237U, (uint8_t)42U,  (uint8_t)253U, (uint8_t)107U, (uint8_t)31U,
  (uint8_t)106U, (uint8_t)85U,  (uint8_t)90U,  (uint8_t)122U, (uint8_t)202U,
  (uint8_t)187U, (uint8_t)94U,  (uint8_t)111U, (uint8_t)121U, (uint8_t)200U,
  (uint8_t)194U, (uint8_t)172U, (uint8_t)139U, (uint8_t)247U, (uint8_t)120U,
  (uint8_t)25U,  (uint8_t)202U, (uint8_t)5U,   (uint8_t)166U, (uint8_t)178U,
  (uint8_t)120U, (uint8_t)108U, (uint8_t)118U, (uint8_t)38U,  (uint8_t)43U,
  (uint8_t)247U, (uint8_t)55U,  (uint8_t)28U,  (uint8_t)239U, (uint8_t)151U,
  (uint8_t)178U, (uint8_t)24U,  (uint8_t)233U, (uint8_t)111U, (uint8_t)23U,
  (uint8_t)90U,  (uint8_t)60U,  (uint8_t)205U, (uint8_t)218U, (uint8_t)42U,
  (uint8_t)204U, (uint8_t)5U,   (uint8_t)137U, (uint8_t)3U
};

static uint8_t dh_public_key[64] = {
  0x70, 0x0c, 0x48, 0xf7, 0x7f, 0x56, 0x58, 0x4c, 0x5c, 0xc6, 0x32, 0xca, 0x65,
  0x64, 0x0d, 0xb9, 0x1b, 0x6b, 0xac, 0xce, 0x3a, 0x4d, 0xf6, 0xb4, 0x2c, 0xe7,
  0xcc, 0x83, 0x88, 0x33, 0xd2, 0x87, 0xdb, 0x71, 0xe5, 0x09, 0xe3, 0xfd, 0x9b,
  0x06, 0x0d, 0xdb, 0x20, 0xba, 0x5c, 0x51, 0xdc, 0xc5, 0x94, 0x8d, 0x46, 0xfb,
  0xf6, 0x40, 0xdf, 0xe0, 0x44, 0x17, 0x82, 0xca, 0xb8, 0x5f, 0xa4, 0xac
};

static uint8_t dh_scalar0[32] = {
  0x7d, 0x7d, 0xc5, 0xf7, 0x1e, 0xb2, 0x9d, 0xda, 0xf8, 0x0d, 0x62,
  0x14, 0x63, 0x2e, 0xea, 0xe0, 0x3d, 0x90, 0x58, 0xaf, 0x1f, 0xb6,
  0xd2, 0x2e, 0xd8, 0x0b, 0xad, 0xb6, 0x2b, 0xc1, 0xa5, 0x34

};

bool
testImplementationHacl()
{
  uint8_t sig[64] = { 0U };
  uint8_t pk[64] = { 0U };

  bool valid = Hacl_P256_dh_initiator(pk, private_key);
  bool s0 = compare_and_print(64, pk, public_key);

  bool flag = Hacl_P256_ecdsa_sign_p256_sha2(sig, 128, msg, private_key, nonce);
  bool s1 = compare_and_print(64, sig, sgnt);
  bool ver =
    Hacl_P256_ecdsa_verif_p256_sha2(128, msg, public_key, sgnt, sgnt + 32);

  return s0 && s1 && ver && flag;
}

int
main()
{
  if (!testImplementationHacl()) {
    printf("%s\n", "Test Implementation failed for Hacl* ECDSA");
    return EXIT_FAILURE;
  }

  cycles a, b;
  clock_t t1, t2;
  uint8_t sgnt_comp[64] = { 0 };

  uint8_t pk[64];
  memcpy(pk, dh_public_key, 64);

  // Benchmarking ECDSA-P256-sign
  for (int j = 0; j < ROUNDS; j++) {
    Hacl_P256_ecdsa_sign_p256_sha2(sgnt_comp, 128, msg, private_key, nonce);
  }

  t1 = clock();
  a = cpucycles_begin();
  for (int j = 0; j < ROUNDS; j++) {
    Hacl_P256_ecdsa_sign_p256_sha2(sgnt_comp, 128, msg, private_key, nonce);
  }
  b = cpucycles_end();
  t2 = clock();
  clock_t tdiff1 = t2 - t1;
  cycles cdiff1 = b - a;

  // Benchmarking ECDSA-P256-verify
  for (int j = 0; j < ROUNDS; j++) {
    Hacl_P256_ecdsa_verif_p256_sha2(128, msg, public_key, sgnt, sgnt + 32);
  }

  t1 = clock();
  a = cpucycles_begin();
  for (int j = 0; j < ROUNDS; j++) {
    Hacl_P256_ecdsa_verif_p256_sha2(128, msg, public_key, sgnt, sgnt + 32);
  }
  b = cpucycles_end();
  t2 = clock();
  clock_t tdiff2 = t2 - t1;
  cycles cdiff2 = b - a;

  // Benchmarking ECDH-P256
  for (int j = 0; j < ROUNDS; j++) {
    Hacl_P256_dh_responder(pk, pk, dh_scalar0);
  }

  t1 = clock();
  a = cpucycles_begin();
  for (int j = 0; j < ROUNDS; j++) {
    Hacl_P256_dh_responder(pk, pk, dh_scalar0);
  }
  b = cpucycles_end();
  t2 = clock();
  clock_t tdiff3 = t2 - t1;
  cycles cdiff3 = b - a;


  // Benchmarking S2P-P256
  for (int j = 0; j < ROUNDS; j++) {
    Hacl_P256_dh_initiator(pk, private_key);
  }

  t1 = clock();
  a = cpucycles_begin();
  for (int j = 0; j < ROUNDS; j++) {
    Hacl_P256_dh_initiator(pk, private_key);
  }
  b = cpucycles_end();
  t2 = clock();
  clock_t tdiff4 = t2 - t1;
  cycles cdiff4 = b - a;

  uint64_t count = ROUNDS;
  printf("Hacl ECDSA-P256-sign PERF: \n");
  print_time(count, tdiff1, cdiff1);

  printf("Hacl ECDSA-P256-verify PERF: \n");
  print_time(count, tdiff2, cdiff2);

  printf("Hacl ECDH-P256 PERF: \n");
  print_time(count, tdiff3, cdiff3);

  printf("Hacl secret-to-public-P256 PERF: \n");
  print_time(count, tdiff4, cdiff4);
}
