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

#include "openssl/crypto.h"
//#include "openssl/digest.h"
#include "openssl/err.h"
#include "openssl/evp.h"
#include "openssl/rsa.h"
//#include "openssl/opensslv.h"
#include "openssl/sha.h"

#include "Hacl_RSAPSS.h"

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


#define ROUNDS 1000
#define SIZE   1

void print_time(double tdiff, uint64_t cdiff){
  uint64_t count = ROUNDS * SIZE;
  printf("cycles for %" PRIu64 " bytes: %" PRIu64 " (%.2fcycles/byte)\n",count,(uint64_t)cdiff,(double)cdiff/count);
  printf("bw %8.2f MB/s\n",(double)count/(tdiff * 1000000.0));
}

bool print_result(uint8_t* comp, uint8_t* exp) {
  printf("computed:");
  for (int i = 0; i < 256; i++)
    printf("%02x",comp[i]);
  printf("\n");
  printf("expected:");
  for (int i = 0; i < 256; i++)
    printf("%02x",exp[i]);
  printf("\n");
  bool ok = true;
  for (int i = 0; i < 256; i++)
    ok = ok & (exp[i] == comp[i]);
  if (ok) printf("Success!\n");
  else printf("**FAILED**\n");
  return ok;
}


bool
hacl_sign(
  uint32_t modBits,
  uint8_t *n1,
  uint32_t pkeyBits,
  uint8_t *e,
  uint32_t skeyBits,
  uint8_t *d,
  uint32_t msgLen,
  uint8_t *msg,
  uint32_t saltLen,
  uint8_t *salt,
  uint8_t *sgnt
)
{
  uint32_t nLen = (modBits - (uint32_t)1U) / (uint32_t)64U + (uint32_t)1U;
  uint32_t eLen = (pkeyBits - (uint32_t)1U) / (uint32_t)64U + (uint32_t)1U;
  uint32_t dLen = (skeyBits - (uint32_t)1U) / (uint32_t)64U + (uint32_t)1U;
  uint32_t pkeyLen = nLen + eLen;
  uint32_t skeyLen = pkeyLen + dLen;

  uint64_t skey[skeyLen];
  memset(skey, 0U, skeyLen * sizeof (skey[0U]));
  uint64_t *pkey = skey;
  uint64_t *nNat = skey;
  uint64_t *eNat = skey + nLen;
  uint64_t *dNat = skey + pkeyLen;
  Hacl_Bignum_Convert_bn_from_bytes_be((modBits - (uint32_t)1U) / (uint32_t)8U + (uint32_t)1U, n1, nNat);
  Hacl_Bignum_Convert_bn_from_bytes_be((pkeyBits - (uint32_t)1U) / (uint32_t)8U + (uint32_t)1U, e, eNat);
  Hacl_Bignum_Convert_bn_from_bytes_be((skeyBits - (uint32_t)1U) / (uint32_t)8U + (uint32_t)1U, d, dNat);
  Hacl_RSAPSS_rsapss_sign(modBits, pkeyBits, skeyBits, skey, saltLen, salt, msgLen, msg, sgnt);
  return 1;
}


bool
hacl_verify(
  uint32_t modBits,
  uint8_t *n1,
  uint32_t pkeyBits,
  uint8_t *e,
  uint32_t msgLen,
  uint8_t *msg,
  uint32_t saltLen,
  uint8_t *sgnt
)
{
  uint32_t nLen = (modBits - (uint32_t)1U) / (uint32_t)64U + (uint32_t)1U;
  uint32_t eLen = (pkeyBits - (uint32_t)1U) / (uint32_t)64U + (uint32_t)1U;
  uint32_t pkeyLen = nLen + eLen + nLen;

  uint64_t pkey[pkeyLen];
  memset(pkey, 0U, pkeyLen * sizeof pkey[0U]);
  uint64_t *nNat = pkey;
  uint64_t *eNat = pkey + nLen;
  Hacl_Bignum_Convert_bn_from_bytes_be((modBits - (uint32_t)1U) / (uint32_t)8U + (uint32_t)1U, n1, nNat);
  Hacl_Bignum_Convert_bn_from_bytes_be((pkeyBits - (uint32_t)1U) / (uint32_t)8U + (uint32_t)1U, e, eNat);

  bool verify_sgnt = Hacl_RSAPSS_rsapss_verify(modBits, pkeyBits, pkey, saltLen, sgnt, msgLen, msg);
  return verify_sgnt;
}


RSA*
createPrivateKey(
  uint8_t* kN,
  uint32_t kN_len,
  uint8_t* kE,
  uint32_t kE_len,
  uint8_t* kD,
  uint32_t kD_len
)
{
  RSA* pRsaKey = RSA_new();
  BIGNUM *n = BN_new();
  BIGNUM *e = BN_new();
  BIGNUM *d = BN_new();

  BN_bin2bn(kN, kN_len, n);
  BN_bin2bn(kE, kE_len, e);
  BN_bin2bn(kD, kD_len, d);

  RSA_set0_key(pRsaKey, n, e, d);

  return pRsaKey;
}

RSA*
createPublicKey(
  uint8_t* kN,
  uint32_t kN_len,
  uint8_t* kE,
  uint32_t kE_len
)
{
  RSA* pRsaKey = RSA_new();
  BIGNUM *n = BN_new();
  BIGNUM *e = BN_new();

  BN_bin2bn(kN, kN_len, n);
  BN_bin2bn(kE, kE_len, e);

  RSA_set0_key(pRsaKey, n, e, NULL);

  return pRsaKey;
}


int
openssl_sign(
  RSA* pRsaKey,
  uint8_t* msg,
  uint32_t msg_len,
  uint8_t* pSignature,
  size_t sig_len
)
{
  EVP_PKEY *pkey;
  pkey = EVP_PKEY_new();
  EVP_PKEY_set1_RSA(pkey, pRsaKey);

  EVP_MD_CTX *md_ctx = NULL;
  md_ctx = EVP_MD_CTX_create();

  EVP_PKEY_CTX *pkey_ctx;
  pkey_ctx = EVP_PKEY_CTX_new(pkey, NULL);

  unsigned char pDigest[32];
  unsigned digest_len;
  digest_len = sizeof(pDigest);

  int ret =
    EVP_DigestInit(md_ctx, EVP_sha256()) &&
    EVP_DigestUpdate(md_ctx, msg, msg_len) &&
    EVP_DigestFinal(md_ctx, pDigest, &digest_len) &&

    EVP_PKEY_sign_init(pkey_ctx) &&
    EVP_PKEY_CTX_set_rsa_padding(pkey_ctx, RSA_PKCS1_PSS_PADDING) &&
    EVP_PKEY_CTX_set_rsa_pss_saltlen(pkey_ctx, 20U) &&
    EVP_PKEY_CTX_set_rsa_mgf1_md(pkey_ctx, EVP_sha256()) &&
    EVP_PKEY_sign(pkey_ctx, pSignature, &sig_len, pDigest, digest_len);

  return ret;
}


int
openssl_verify(
  RSA* pRsaKey,
  uint8_t* msg,
  uint32_t msg_len,
  uint8_t* pSignature,
  size_t sig_len
)
{
  EVP_PKEY *pkey;
  pkey = EVP_PKEY_new();
  EVP_PKEY_set1_RSA(pkey, pRsaKey);

  EVP_MD_CTX *md_ctx = NULL;
  md_ctx = EVP_MD_CTX_create();

  EVP_PKEY_CTX *pkey_ctx;
  pkey_ctx = EVP_PKEY_CTX_new(pkey, NULL);

  unsigned char pDigest[32];
  unsigned digest_len;
  digest_len = sizeof(pDigest);

  int ret =
    EVP_DigestInit(md_ctx, EVP_sha256()) &&
    EVP_DigestUpdate(md_ctx, msg, msg_len) &&
    EVP_DigestFinal(md_ctx, pDigest, &digest_len) &&

    EVP_PKEY_verify_init(pkey_ctx) &&
    EVP_PKEY_CTX_set_rsa_padding(pkey_ctx, RSA_PKCS1_PSS_PADDING) &&
    EVP_PKEY_CTX_set_signature_md(pkey_ctx, EVP_sha256()) &&
    EVP_PKEY_verify(pkey_ctx, pSignature, sig_len, pDigest, digest_len);

  return ret;
}

int main() {
  uint8_t test4_n[256U] =
  {
    (uint8_t)0xa5U, (uint8_t)0xddU, (uint8_t)0x86U, (uint8_t)0x7aU, (uint8_t)0xc4U, (uint8_t)0xcbU,
    (uint8_t)0x02U, (uint8_t)0xf9U, (uint8_t)0x0bU, (uint8_t)0x94U, (uint8_t)0x57U, (uint8_t)0xd4U,
    (uint8_t)0x8cU, (uint8_t)0x14U, (uint8_t)0xa7U, (uint8_t)0x70U, (uint8_t)0xefU, (uint8_t)0x99U,
    (uint8_t)0x1cU, (uint8_t)0x56U, (uint8_t)0xc3U, (uint8_t)0x9cU, (uint8_t)0x0eU, (uint8_t)0xc6U,
    (uint8_t)0x5fU, (uint8_t)0xd1U, (uint8_t)0x1aU, (uint8_t)0xfaU, (uint8_t)0x89U, (uint8_t)0x37U,
    (uint8_t)0xceU, (uint8_t)0xa5U, (uint8_t)0x7bU, (uint8_t)0x9bU, (uint8_t)0xe7U, (uint8_t)0xacU,
    (uint8_t)0x73U, (uint8_t)0xb4U, (uint8_t)0x5cU, (uint8_t)0x00U, (uint8_t)0x17U, (uint8_t)0x61U,
    (uint8_t)0x5bU, (uint8_t)0x82U, (uint8_t)0xd6U, (uint8_t)0x22U, (uint8_t)0xe3U, (uint8_t)0x18U,
    (uint8_t)0x75U, (uint8_t)0x3bU, (uint8_t)0x60U, (uint8_t)0x27U, (uint8_t)0xc0U, (uint8_t)0xfdU,
    (uint8_t)0x15U, (uint8_t)0x7bU, (uint8_t)0xe1U, (uint8_t)0x2fU, (uint8_t)0x80U, (uint8_t)0x90U,
    (uint8_t)0xfeU, (uint8_t)0xe2U, (uint8_t)0xa7U, (uint8_t)0xadU, (uint8_t)0xcdU, (uint8_t)0x0eU,
    (uint8_t)0xefU, (uint8_t)0x75U, (uint8_t)0x9fU, (uint8_t)0x88U, (uint8_t)0xbaU, (uint8_t)0x49U,
    (uint8_t)0x97U, (uint8_t)0xc7U, (uint8_t)0xa4U, (uint8_t)0x2dU, (uint8_t)0x58U, (uint8_t)0xc9U,
    (uint8_t)0xaaU, (uint8_t)0x12U, (uint8_t)0xcbU, (uint8_t)0x99U, (uint8_t)0xaeU, (uint8_t)0x00U,
    (uint8_t)0x1fU, (uint8_t)0xe5U, (uint8_t)0x21U, (uint8_t)0xc1U, (uint8_t)0x3bU, (uint8_t)0xb5U,
    (uint8_t)0x43U, (uint8_t)0x14U, (uint8_t)0x45U, (uint8_t)0xa8U, (uint8_t)0xd5U, (uint8_t)0xaeU,
    (uint8_t)0x4fU, (uint8_t)0x5eU, (uint8_t)0x4cU, (uint8_t)0x7eU, (uint8_t)0x94U, (uint8_t)0x8aU,
    (uint8_t)0xc2U, (uint8_t)0x27U, (uint8_t)0xd3U, (uint8_t)0x60U, (uint8_t)0x40U, (uint8_t)0x71U,
    (uint8_t)0xf2U, (uint8_t)0x0eU, (uint8_t)0x57U, (uint8_t)0x7eU, (uint8_t)0x90U, (uint8_t)0x5fU,
    (uint8_t)0xbeU, (uint8_t)0xb1U, (uint8_t)0x5dU, (uint8_t)0xfaU, (uint8_t)0xf0U, (uint8_t)0x6dU,
    (uint8_t)0x1dU, (uint8_t)0xe5U, (uint8_t)0xaeU, (uint8_t)0x62U, (uint8_t)0x53U, (uint8_t)0xd6U,
    (uint8_t)0x3aU, (uint8_t)0x6aU, (uint8_t)0x21U, (uint8_t)0x20U, (uint8_t)0xb3U, (uint8_t)0x1aU,
    (uint8_t)0x5dU, (uint8_t)0xa5U, (uint8_t)0xdaU, (uint8_t)0xbcU, (uint8_t)0x95U, (uint8_t)0x50U,
    (uint8_t)0x60U, (uint8_t)0x0eU, (uint8_t)0x20U, (uint8_t)0xf2U, (uint8_t)0x7dU, (uint8_t)0x37U,
    (uint8_t)0x39U, (uint8_t)0xe2U, (uint8_t)0x62U, (uint8_t)0x79U, (uint8_t)0x25U, (uint8_t)0xfeU,
    (uint8_t)0xa3U, (uint8_t)0xccU, (uint8_t)0x50U, (uint8_t)0x9fU, (uint8_t)0x21U, (uint8_t)0xdfU,
    (uint8_t)0xf0U, (uint8_t)0x4eU, (uint8_t)0x6eU, (uint8_t)0xeaU, (uint8_t)0x45U, (uint8_t)0x49U,
    (uint8_t)0xc5U, (uint8_t)0x40U, (uint8_t)0xd6U, (uint8_t)0x80U, (uint8_t)0x9fU, (uint8_t)0xf9U,
    (uint8_t)0x30U, (uint8_t)0x7eU, (uint8_t)0xedU, (uint8_t)0xe9U, (uint8_t)0x1fU, (uint8_t)0xffU,
    (uint8_t)0x58U, (uint8_t)0x73U, (uint8_t)0x3dU, (uint8_t)0x83U, (uint8_t)0x85U, (uint8_t)0xa2U,
    (uint8_t)0x37U, (uint8_t)0xd6U, (uint8_t)0xd3U, (uint8_t)0x70U, (uint8_t)0x5aU, (uint8_t)0x33U,
    (uint8_t)0xe3U, (uint8_t)0x91U, (uint8_t)0x90U, (uint8_t)0x09U, (uint8_t)0x92U, (uint8_t)0x07U,
    (uint8_t)0x0dU, (uint8_t)0xf7U, (uint8_t)0xadU, (uint8_t)0xf1U, (uint8_t)0x35U, (uint8_t)0x7cU,
    (uint8_t)0xf7U, (uint8_t)0xe3U, (uint8_t)0x70U, (uint8_t)0x0cU, (uint8_t)0xe3U, (uint8_t)0x66U,
    (uint8_t)0x7dU, (uint8_t)0xe8U, (uint8_t)0x3fU, (uint8_t)0x17U, (uint8_t)0xb8U, (uint8_t)0xdfU,
    (uint8_t)0x17U, (uint8_t)0x78U, (uint8_t)0xdbU, (uint8_t)0x38U, (uint8_t)0x1dU, (uint8_t)0xceU,
    (uint8_t)0x09U, (uint8_t)0xcbU, (uint8_t)0x4aU, (uint8_t)0xd0U, (uint8_t)0x58U, (uint8_t)0xa5U,
    (uint8_t)0x11U, (uint8_t)0x00U, (uint8_t)0x1aU, (uint8_t)0x73U, (uint8_t)0x81U, (uint8_t)0x98U,
    (uint8_t)0xeeU, (uint8_t)0x27U, (uint8_t)0xcfU, (uint8_t)0x55U, (uint8_t)0xa1U, (uint8_t)0x3bU,
    (uint8_t)0x75U, (uint8_t)0x45U, (uint8_t)0x39U, (uint8_t)0x90U, (uint8_t)0x65U, (uint8_t)0x82U,
    (uint8_t)0xecU, (uint8_t)0x8bU, (uint8_t)0x17U, (uint8_t)0x4bU, (uint8_t)0xd5U, (uint8_t)0x8dU,
    (uint8_t)0x5dU, (uint8_t)0x1fU, (uint8_t)0x3dU, (uint8_t)0x76U, (uint8_t)0x7cU, (uint8_t)0x61U,
    (uint8_t)0x37U, (uint8_t)0x21U, (uint8_t)0xaeU, (uint8_t)0x05U
  };

  uint8_t test4_e[3U] = { (uint8_t)0x01U, (uint8_t)0x00U, (uint8_t)0x01U };

  uint8_t test4_d[256U] =
  {
    (uint8_t)0x2dU, (uint8_t)0x2fU, (uint8_t)0xf5U, (uint8_t)0x67U, (uint8_t)0xb3U, (uint8_t)0xfeU,
    (uint8_t)0x74U, (uint8_t)0xe0U, (uint8_t)0x61U, (uint8_t)0x91U, (uint8_t)0xb7U, (uint8_t)0xfdU,
    (uint8_t)0xedU, (uint8_t)0x6dU, (uint8_t)0xe1U, (uint8_t)0x12U, (uint8_t)0x29U, (uint8_t)0x0cU,
    (uint8_t)0x67U, (uint8_t)0x06U, (uint8_t)0x92U, (uint8_t)0x43U, (uint8_t)0x0dU, (uint8_t)0x59U,
    (uint8_t)0x69U, (uint8_t)0x18U, (uint8_t)0x40U, (uint8_t)0x47U, (uint8_t)0xdaU, (uint8_t)0x23U,
    (uint8_t)0x4cU, (uint8_t)0x96U, (uint8_t)0x93U, (uint8_t)0xdeU, (uint8_t)0xedU, (uint8_t)0x16U,
    (uint8_t)0x73U, (uint8_t)0xedU, (uint8_t)0x42U, (uint8_t)0x95U, (uint8_t)0x39U, (uint8_t)0xc9U,
    (uint8_t)0x69U, (uint8_t)0xd3U, (uint8_t)0x72U, (uint8_t)0xc0U, (uint8_t)0x4dU, (uint8_t)0x6bU,
    (uint8_t)0x47U, (uint8_t)0xe0U, (uint8_t)0xf5U, (uint8_t)0xb8U, (uint8_t)0xceU, (uint8_t)0xe0U,
    (uint8_t)0x84U, (uint8_t)0x3eU, (uint8_t)0x5cU, (uint8_t)0x22U, (uint8_t)0x83U, (uint8_t)0x5dU,
    (uint8_t)0xbdU, (uint8_t)0x3bU, (uint8_t)0x05U, (uint8_t)0xa0U, (uint8_t)0x99U, (uint8_t)0x79U,
    (uint8_t)0x84U, (uint8_t)0xaeU, (uint8_t)0x60U, (uint8_t)0x58U, (uint8_t)0xb1U, (uint8_t)0x1bU,
    (uint8_t)0xc4U, (uint8_t)0x90U, (uint8_t)0x7cU, (uint8_t)0xbfU, (uint8_t)0x67U, (uint8_t)0xedU,
    (uint8_t)0x84U, (uint8_t)0xfaU, (uint8_t)0x9aU, (uint8_t)0xe2U, (uint8_t)0x52U, (uint8_t)0xdfU,
    (uint8_t)0xb0U, (uint8_t)0xd0U, (uint8_t)0xcdU, (uint8_t)0x49U, (uint8_t)0xe6U, (uint8_t)0x18U,
    (uint8_t)0xe3U, (uint8_t)0x5dU, (uint8_t)0xfdU, (uint8_t)0xfeU, (uint8_t)0x59U, (uint8_t)0xbcU,
    (uint8_t)0xa3U, (uint8_t)0xddU, (uint8_t)0xd6U, (uint8_t)0x6cU, (uint8_t)0x33U, (uint8_t)0xceU,
    (uint8_t)0xbbU, (uint8_t)0xc7U, (uint8_t)0x7aU, (uint8_t)0xd4U, (uint8_t)0x41U, (uint8_t)0xaaU,
    (uint8_t)0x69U, (uint8_t)0x5eU, (uint8_t)0x13U, (uint8_t)0xe3U, (uint8_t)0x24U, (uint8_t)0xb5U,
    (uint8_t)0x18U, (uint8_t)0xf0U, (uint8_t)0x1cU, (uint8_t)0x60U, (uint8_t)0xf5U, (uint8_t)0xa8U,
    (uint8_t)0x5cU, (uint8_t)0x99U, (uint8_t)0x4aU, (uint8_t)0xd1U, (uint8_t)0x79U, (uint8_t)0xf2U,
    (uint8_t)0xa6U, (uint8_t)0xb5U, (uint8_t)0xfbU, (uint8_t)0xe9U, (uint8_t)0x34U, (uint8_t)0x02U,
    (uint8_t)0xb1U, (uint8_t)0x17U, (uint8_t)0x67U, (uint8_t)0xbeU, (uint8_t)0x01U, (uint8_t)0xbfU,
    (uint8_t)0x07U, (uint8_t)0x34U, (uint8_t)0x44U, (uint8_t)0xd6U, (uint8_t)0xbaU, (uint8_t)0x1dU,
    (uint8_t)0xd2U, (uint8_t)0xbcU, (uint8_t)0xa5U, (uint8_t)0xbdU, (uint8_t)0x07U, (uint8_t)0x4dU,
    (uint8_t)0x4aU, (uint8_t)0x5fU, (uint8_t)0xaeU, (uint8_t)0x35U, (uint8_t)0x31U, (uint8_t)0xadU,
    (uint8_t)0x13U, (uint8_t)0x03U, (uint8_t)0xd8U, (uint8_t)0x4bU, (uint8_t)0x30U, (uint8_t)0xd8U,
    (uint8_t)0x97U, (uint8_t)0x31U, (uint8_t)0x8cU, (uint8_t)0xbbU, (uint8_t)0xbaU, (uint8_t)0x04U,
    (uint8_t)0xe0U, (uint8_t)0x3cU, (uint8_t)0x2eU, (uint8_t)0x66U, (uint8_t)0xdeU, (uint8_t)0x6dU,
    (uint8_t)0x91U, (uint8_t)0xf8U, (uint8_t)0x2fU, (uint8_t)0x96U, (uint8_t)0xeaU, (uint8_t)0x1dU,
    (uint8_t)0x4bU, (uint8_t)0xb5U, (uint8_t)0x4aU, (uint8_t)0x5aU, (uint8_t)0xaeU, (uint8_t)0x10U,
    (uint8_t)0x2dU, (uint8_t)0x59U, (uint8_t)0x46U, (uint8_t)0x57U, (uint8_t)0xf5U, (uint8_t)0xc9U,
    (uint8_t)0x78U, (uint8_t)0x95U, (uint8_t)0x53U, (uint8_t)0x51U, (uint8_t)0x2bU, (uint8_t)0x29U,
    (uint8_t)0x6dU, (uint8_t)0xeaU, (uint8_t)0x29U, (uint8_t)0xd8U, (uint8_t)0x02U, (uint8_t)0x31U,
    (uint8_t)0x96U, (uint8_t)0x35U, (uint8_t)0x7eU, (uint8_t)0x3eU, (uint8_t)0x3aU, (uint8_t)0x6eU,
    (uint8_t)0x95U, (uint8_t)0x8fU, (uint8_t)0x39U, (uint8_t)0xe3U, (uint8_t)0xc2U, (uint8_t)0x34U,
    (uint8_t)0x40U, (uint8_t)0x38U, (uint8_t)0xeaU, (uint8_t)0x60U, (uint8_t)0x4bU, (uint8_t)0x31U,
    (uint8_t)0xedU, (uint8_t)0xc6U, (uint8_t)0xf0U, (uint8_t)0xf7U, (uint8_t)0xffU, (uint8_t)0x6eU,
    (uint8_t)0x71U, (uint8_t)0x81U, (uint8_t)0xa5U, (uint8_t)0x7cU, (uint8_t)0x92U, (uint8_t)0x82U,
    (uint8_t)0x6aU, (uint8_t)0x26U, (uint8_t)0x8fU, (uint8_t)0x86U, (uint8_t)0x76U, (uint8_t)0x8eU,
    (uint8_t)0x96U, (uint8_t)0xf8U, (uint8_t)0x78U, (uint8_t)0x56U, (uint8_t)0x2fU, (uint8_t)0xc7U,
    (uint8_t)0x1dU, (uint8_t)0x85U, (uint8_t)0xd6U, (uint8_t)0x9eU, (uint8_t)0x44U, (uint8_t)0x86U,
    (uint8_t)0x12U, (uint8_t)0xf7U, (uint8_t)0x04U, (uint8_t)0x8fU
  };

  uint8_t test4_msg[128U] =
  {
    (uint8_t)0xddU, (uint8_t)0x67U, (uint8_t)0x0aU, (uint8_t)0x01U, (uint8_t)0x46U, (uint8_t)0x58U,
    (uint8_t)0x68U, (uint8_t)0xadU, (uint8_t)0xc9U, (uint8_t)0x3fU, (uint8_t)0x26U, (uint8_t)0x13U,
    (uint8_t)0x19U, (uint8_t)0x57U, (uint8_t)0xa5U, (uint8_t)0x0cU, (uint8_t)0x52U, (uint8_t)0xfbU,
    (uint8_t)0x77U, (uint8_t)0x7cU, (uint8_t)0xdbU, (uint8_t)0xaaU, (uint8_t)0x30U, (uint8_t)0x89U,
    (uint8_t)0x2cU, (uint8_t)0x9eU, (uint8_t)0x12U, (uint8_t)0x36U, (uint8_t)0x11U, (uint8_t)0x64U,
    (uint8_t)0xecU, (uint8_t)0x13U, (uint8_t)0x97U, (uint8_t)0x9dU, (uint8_t)0x43U, (uint8_t)0x04U,
    (uint8_t)0x81U, (uint8_t)0x18U, (uint8_t)0xe4U, (uint8_t)0x44U, (uint8_t)0x5dU, (uint8_t)0xb8U,
    (uint8_t)0x7bU, (uint8_t)0xeeU, (uint8_t)0x58U, (uint8_t)0xddU, (uint8_t)0x98U, (uint8_t)0x7bU,
    (uint8_t)0x34U, (uint8_t)0x25U, (uint8_t)0xd0U, (uint8_t)0x20U, (uint8_t)0x71U, (uint8_t)0xd8U,
    (uint8_t)0xdbU, (uint8_t)0xaeU, (uint8_t)0x80U, (uint8_t)0x70U, (uint8_t)0x8bU, (uint8_t)0x03U,
    (uint8_t)0x9dU, (uint8_t)0xbbU, (uint8_t)0x64U, (uint8_t)0xdbU, (uint8_t)0xd1U, (uint8_t)0xdeU,
    (uint8_t)0x56U, (uint8_t)0x57U, (uint8_t)0xd9U, (uint8_t)0xfeU, (uint8_t)0xd0U, (uint8_t)0xc1U,
    (uint8_t)0x18U, (uint8_t)0xa5U, (uint8_t)0x41U, (uint8_t)0x43U, (uint8_t)0x74U, (uint8_t)0x2eU,
    (uint8_t)0x0fU, (uint8_t)0xf3U, (uint8_t)0xc8U, (uint8_t)0x7fU, (uint8_t)0x74U, (uint8_t)0xe4U,
    (uint8_t)0x58U, (uint8_t)0x57U, (uint8_t)0x64U, (uint8_t)0x7aU, (uint8_t)0xf3U, (uint8_t)0xf7U,
    (uint8_t)0x9eU, (uint8_t)0xb0U, (uint8_t)0xa1U, (uint8_t)0x4cU, (uint8_t)0x9dU, (uint8_t)0x75U,
    (uint8_t)0xeaU, (uint8_t)0x9aU, (uint8_t)0x1aU, (uint8_t)0x04U, (uint8_t)0xb7U, (uint8_t)0xcfU,
    (uint8_t)0x47U, (uint8_t)0x8aU, (uint8_t)0x89U, (uint8_t)0x7aU, (uint8_t)0x70U, (uint8_t)0x8fU,
    (uint8_t)0xd9U, (uint8_t)0x88U, (uint8_t)0xf4U, (uint8_t)0x8eU, (uint8_t)0x80U, (uint8_t)0x1eU,
    (uint8_t)0xdbU, (uint8_t)0x0bU, (uint8_t)0x70U, (uint8_t)0x39U, (uint8_t)0xdfU, (uint8_t)0x8cU,
    (uint8_t)0x23U, (uint8_t)0xbbU, (uint8_t)0x3cU, (uint8_t)0x56U, (uint8_t)0xf4U, (uint8_t)0xe8U,
    (uint8_t)0x21U, (uint8_t)0xacU
  };

  uint8_t test4_salt[20U] =
  {
    (uint8_t)0x8bU, (uint8_t)0x2bU, (uint8_t)0xddU, (uint8_t)0x4bU, (uint8_t)0x40U, (uint8_t)0xfaU,
    (uint8_t)0xf5U, (uint8_t)0x45U, (uint8_t)0xc7U, (uint8_t)0x78U, (uint8_t)0xddU, (uint8_t)0xf9U,
    (uint8_t)0xbcU, (uint8_t)0x1aU, (uint8_t)0x49U, (uint8_t)0xcbU, (uint8_t)0x57U, (uint8_t)0xf9U,
    (uint8_t)0xb7U, (uint8_t)0x1bU
  };

  uint8_t test4_sgnt_expected[256U] =
  {
    (uint8_t)0xa4U, (uint8_t)0x4eU, (uint8_t)0x5cU, (uint8_t)0x83U, (uint8_t)0xc6U, (uint8_t)0xfeU,
    (uint8_t)0xdfU, (uint8_t)0x7fU, (uint8_t)0x44U, (uint8_t)0x33U, (uint8_t)0x78U, (uint8_t)0x82U,
    (uint8_t)0x54U, (uint8_t)0x2aU, (uint8_t)0x96U, (uint8_t)0x10U, (uint8_t)0x72U, (uint8_t)0x4aU,
    (uint8_t)0xa6U, (uint8_t)0xf5U, (uint8_t)0xb8U, (uint8_t)0xf1U, (uint8_t)0x3bU, (uint8_t)0x4fU,
    (uint8_t)0x51U, (uint8_t)0xebU, (uint8_t)0x9eU, (uint8_t)0xf9U, (uint8_t)0x84U, (uint8_t)0xf5U,
    (uint8_t)0x19U, (uint8_t)0xaaU, (uint8_t)0xe9U, (uint8_t)0xe3U, (uint8_t)0x4bU, (uint8_t)0x26U,
    (uint8_t)0x4eU, (uint8_t)0x8dU, (uint8_t)0x06U, (uint8_t)0xb6U, (uint8_t)0x93U, (uint8_t)0x66U,
    (uint8_t)0x4dU, (uint8_t)0xe1U, (uint8_t)0xccU, (uint8_t)0xe1U, (uint8_t)0x36U, (uint8_t)0xd0U,
    (uint8_t)0x6dU, (uint8_t)0x10U, (uint8_t)0x7fU, (uint8_t)0x64U, (uint8_t)0x51U, (uint8_t)0x99U,
    (uint8_t)0x8aU, (uint8_t)0xf9U, (uint8_t)0x01U, (uint8_t)0x21U, (uint8_t)0x3fU, (uint8_t)0xc8U,
    (uint8_t)0x95U, (uint8_t)0x83U, (uint8_t)0xe6U, (uint8_t)0xbeU, (uint8_t)0xfeU, (uint8_t)0x1eU,
    (uint8_t)0xd1U, (uint8_t)0x12U, (uint8_t)0x35U, (uint8_t)0xf5U, (uint8_t)0xb5U, (uint8_t)0xceU,
    (uint8_t)0x8bU, (uint8_t)0xd4U, (uint8_t)0x72U, (uint8_t)0xb3U, (uint8_t)0x84U, (uint8_t)0xefU,
    (uint8_t)0xf0U, (uint8_t)0xcdU, (uint8_t)0x80U, (uint8_t)0xd3U, (uint8_t)0x75U, (uint8_t)0xbdU,
    (uint8_t)0x6aU, (uint8_t)0x88U, (uint8_t)0xaeU, (uint8_t)0x6fU, (uint8_t)0x5bU, (uint8_t)0x76U,
    (uint8_t)0x75U, (uint8_t)0xc2U, (uint8_t)0x50U, (uint8_t)0x8bU, (uint8_t)0xa9U, (uint8_t)0xb9U,
    (uint8_t)0xf0U, (uint8_t)0x17U, (uint8_t)0x1eU, (uint8_t)0x10U, (uint8_t)0xc9U, (uint8_t)0x58U,
    (uint8_t)0xd4U, (uint8_t)0xc0U, (uint8_t)0x4cU, (uint8_t)0x10U, (uint8_t)0x0eU, (uint8_t)0xf9U,
    (uint8_t)0x06U, (uint8_t)0xccU, (uint8_t)0x97U, (uint8_t)0x58U, (uint8_t)0x0dU, (uint8_t)0xe7U,
    (uint8_t)0x73U, (uint8_t)0xadU, (uint8_t)0x9dU, (uint8_t)0xf4U, (uint8_t)0xdaU, (uint8_t)0x13U,
    (uint8_t)0xd5U, (uint8_t)0x95U, (uint8_t)0xbeU, (uint8_t)0xe2U, (uint8_t)0x4aU, (uint8_t)0xf8U,
    (uint8_t)0x12U, (uint8_t)0x88U, (uint8_t)0x4eU, (uint8_t)0xd4U, (uint8_t)0xdcU, (uint8_t)0xe8U,
    (uint8_t)0x09U, (uint8_t)0x51U, (uint8_t)0xecU, (uint8_t)0xd0U, (uint8_t)0x4bU, (uint8_t)0x1bU,
    (uint8_t)0xa6U, (uint8_t)0xd7U, (uint8_t)0x8cU, (uint8_t)0x29U, (uint8_t)0x34U, (uint8_t)0xe6U,
    (uint8_t)0xabU, (uint8_t)0x0aU, (uint8_t)0x77U, (uint8_t)0x36U, (uint8_t)0x83U, (uint8_t)0x91U,
    (uint8_t)0x1fU, (uint8_t)0xccU, (uint8_t)0x68U, (uint8_t)0x91U, (uint8_t)0x35U, (uint8_t)0x37U,
    (uint8_t)0x67U, (uint8_t)0x27U, (uint8_t)0x78U, (uint8_t)0x09U, (uint8_t)0xecU, (uint8_t)0x74U,
    (uint8_t)0x6fU, (uint8_t)0x95U, (uint8_t)0x98U, (uint8_t)0xe4U, (uint8_t)0xf8U, (uint8_t)0xf0U,
    (uint8_t)0xcbU, (uint8_t)0x1dU, (uint8_t)0x3dU, (uint8_t)0x37U, (uint8_t)0x84U, (uint8_t)0x3fU,
    (uint8_t)0xeaU, (uint8_t)0x2aU, (uint8_t)0x8cU, (uint8_t)0xb0U, (uint8_t)0x91U, (uint8_t)0xf2U,
    (uint8_t)0x91U, (uint8_t)0x91U, (uint8_t)0x22U, (uint8_t)0x76U, (uint8_t)0x9eU, (uint8_t)0xe4U,
    (uint8_t)0x17U, (uint8_t)0xdaU, (uint8_t)0x18U, (uint8_t)0xd6U, (uint8_t)0x03U, (uint8_t)0xf7U,
    (uint8_t)0x98U, (uint8_t)0x37U, (uint8_t)0x0cU, (uint8_t)0xadU, (uint8_t)0x7bU, (uint8_t)0x76U,
    (uint8_t)0x0aU, (uint8_t)0x7fU, (uint8_t)0x57U, (uint8_t)0x3aU, (uint8_t)0xeaU, (uint8_t)0xf5U,
    (uint8_t)0x16U, (uint8_t)0xa0U, (uint8_t)0xf9U, (uint8_t)0x0dU, (uint8_t)0x95U, (uint8_t)0x25U,
    (uint8_t)0x65U, (uint8_t)0xb8U, (uint8_t)0xa1U, (uint8_t)0x9aU, (uint8_t)0x8fU, (uint8_t)0xc3U,
    (uint8_t)0xf0U, (uint8_t)0xeeU, (uint8_t)0x7dU, (uint8_t)0x39U, (uint8_t)0x1dU, (uint8_t)0x9bU,
    (uint8_t)0x8bU, (uint8_t)0x3fU, (uint8_t)0x98U, (uint8_t)0xbeU, (uint8_t)0xbbU, (uint8_t)0x0dU,
    (uint8_t)0x5dU, (uint8_t)0x01U, (uint8_t)0x0eU, (uint8_t)0x32U, (uint8_t)0xe0U, (uint8_t)0xb8U,
    (uint8_t)0x00U, (uint8_t)0xe9U, (uint8_t)0x65U, (uint8_t)0x6fU, (uint8_t)0x64U, (uint8_t)0x08U,
    (uint8_t)0x2bU, (uint8_t)0xb1U, (uint8_t)0xacU, (uint8_t)0x95U, (uint8_t)0xa2U, (uint8_t)0x23U,
    (uint8_t)0xf4U, (uint8_t)0x31U, (uint8_t)0xecU, (uint8_t)0x40U, (uint8_t)0x6aU, (uint8_t)0x42U,
    (uint8_t)0x95U, (uint8_t)0x4bU, (uint8_t)0x2dU, (uint8_t)0x57U
  };

  RSA* privkey = createPrivateKey(test4_n, 256U, test4_e, 3U, test4_d, 256U);
  RSA* pubkey = createPublicKey(test4_n, 256U, test4_e, 3U);

  uint8_t sgnt_comp[256U];
  hacl_sign(2048U, test4_n, 24U, test4_e, 2048U, test4_d, 128U, test4_msg, 20U, test4_salt, sgnt_comp);
  printf("RSAPSS signature HACL*:\n");
  bool ok = print_result(sgnt_comp,test4_sgnt_expected);

  openssl_sign(privkey, test4_msg, 128U, sgnt_comp, 256U);
  printf("RSAPSS signature OpenSSL:\n");
  ok = ok && print_result(sgnt_comp,test4_sgnt_expected);


  printf("RSAPSS verification HACL*:\n");
  bool res_ver = hacl_verify(2048U, test4_n, 24U, test4_e, 128U, test4_msg, 20U, test4_sgnt_expected);
  //ok = ok && res_ver;
  if (res_ver) printf("Success!\n");
  else printf("**FAILED**\n");

  printf("RSAPSS verification OpenSSL:\n");
  res_ver = openssl_verify(pubkey, test4_msg, 128U, test4_sgnt_expected, 256U);
  //ok = ok && res_ver;
  if (res_ver) printf("Success!\n");
  else printf("**FAILED**\n");


  //uint8_t plain[SIZE];
  //memset(plain,'P',SIZE);
  uint8_t res = 1;
  uint8_t comp[256U];
  cycles a,b;
  clock_t t1,t2;

  ok = true;
  for (int j = 0; j < ROUNDS; j++) {
    hacl_sign(2048U, test4_n, 24U, test4_e, 2048U, test4_d, 128U, test4_msg, 20U, test4_salt, comp);
    res = res ^ comp[0];
  }

  t1 = clock();
  a = cpucycles_begin();
  for (int j = 0; j < ROUNDS; j++) {
    hacl_sign(2048U, test4_n, 24U, test4_e, 2048U, test4_d, 128U, test4_msg, 20U, test4_salt, comp);
    res = res ^ comp[0];
  }
  b = cpucycles_end();
  t2 = clock();
  double diff1 = (double)(t2 - t1)/CLOCKS_PER_SEC;
  uint64_t cyc1 = b - a;



  for (int j = 0; j < ROUNDS; j++) {
    int r = hacl_verify(2048U, test4_n, 24U, test4_e, 128U, test4_msg, 20U, comp);
    res = res ^ r;
  }

  t1 = clock();
  a = cpucycles_begin();
  for (int j = 0; j < ROUNDS; j++) {
    int r = hacl_verify(2048U, test4_n, 24U, test4_e, 128U, test4_msg, 20U, comp);
    res = res ^ r;
  }
  b = cpucycles_end();
  t2 = clock();
  double diff2 = (double)(t2 - t1)/CLOCKS_PER_SEC;
  uint64_t cyc2 = b - a;


  for (int j = 0; j < ROUNDS; j++) {
    openssl_sign(privkey, test4_msg, 128U, comp, 256U);
    res = res ^ comp[0];
  }

  t1 = clock();
  a = cpucycles_begin();
  for (int j = 0; j < ROUNDS; j++) {
    openssl_sign(privkey, test4_msg, 128U, comp, 256U);
    res = res ^ comp[0];
  }
  b = cpucycles_end();
  t2 = clock();
  double diff3 = (double)(t2 - t1)/CLOCKS_PER_SEC;
  uint64_t cyc3 = b - a;



  for (int j = 0; j < ROUNDS; j++) {
    int r = openssl_verify(pubkey, test4_msg, 128U, comp, 256U);
    res = res ^ r;
  }

  t1 = clock();
  a = cpucycles_begin();
  for (int j = 0; j < ROUNDS; j++) {
    int r = openssl_verify(pubkey, test4_msg, 128U, comp, 256U);
    res = res ^ r;
  }
  b = cpucycles_end();
  t2 = clock();
  double diff4 = (double)(t2 - t1)/CLOCKS_PER_SEC;
  uint64_t cyc4 = b - a;

  printf("\nHACL* RSAPSS signature\n"); print_time(diff1,cyc1);
  printf("\nHACL* RSAPSS verification\n"); print_time(diff2,cyc2);
  printf("\nOpenSSL RSAPSS signature\n"); print_time(diff3,cyc3);
  printf("\nOpenSSL RSAPSS verification\n"); print_time(diff4,cyc4);
  printf ("\n res: %d \n",res);

  if (ok) return EXIT_SUCCESS;
  else return EXIT_FAILURE;

}
