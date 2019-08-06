#include "Hacl_Impl_Bignum_Openssl.h"
#include <openssl/bn.h>
#include <openssl/bn.h>


void Hacl_Impl_Bignum_Openssl_ossl_mod_add(
  uint32_t nLen,
  uint64_t *n,
  uint64_t *a,
  uint64_t *b,
  uint64_t *res) {
    BN_CTX *ctx = BN_CTX_new();

    int nLenBytes = ((int)nLen)*8;

    BIGNUM *bn_n = BN_lebin2bn((unsigned char*) n,nLenBytes,NULL);
    BIGNUM *bn_a = BN_lebin2bn((unsigned char*) a,nLenBytes,NULL);
    BIGNUM *bn_b = BN_lebin2bn((unsigned char*) b,nLenBytes,NULL);
    BIGNUM *bn_res = BN_new ();

    BN_mod_add(bn_res,bn_a,bn_b,bn_n,ctx);

    if (BN_num_bytes(bn_res) > nLenBytes) {
        printf ("nlen: %u, retlen: %u\n", nLen, BN_num_bytes(bn_res));
        exit(1);
    }

    BN_bn2lebinpad(bn_res,(unsigned char*)res,nLenBytes);

    BN_free(bn_n);
    BN_free(bn_a);
    BN_free(bn_b);
    BN_free(bn_res);

    BN_CTX_free(ctx);
}

void Hacl_Impl_Bignum_Openssl_ossl_mod_sub(
  uint32_t nLen,
  uint64_t *n,
  uint64_t *a,
  uint64_t *b,
  uint64_t *res) {
    BN_CTX *ctx = BN_CTX_new();

    int nLenBytes = ((int)nLen)*8;

    BIGNUM *bn_n = BN_lebin2bn((unsigned char*) n,nLenBytes,NULL);
    BIGNUM *bn_a = BN_lebin2bn((unsigned char*) a,nLenBytes,NULL);
    BIGNUM *bn_b = BN_lebin2bn((unsigned char*) b,nLenBytes,NULL);
    BIGNUM *bn_res = BN_new ();

    BN_mod_sub(bn_res,bn_a,bn_b,bn_n,ctx);

    if (BN_num_bytes(bn_res) > nLenBytes) {
        printf ("nlen: %u, retlen: %u\n", nLen, BN_num_bytes(bn_res));
        exit(1);
    }

    BN_bn2lebinpad(bn_res,(unsigned char*)res,nLenBytes);

    BN_free(bn_n);
    BN_free(bn_a);
    BN_free(bn_b);
    BN_free(bn_res);

    BN_CTX_free(ctx);
}

void Hacl_Impl_Bignum_Openssl_ossl_mod_mul(
  uint32_t nLen,
  uint64_t *n,
  uint64_t *a,
  uint64_t *b,
  uint64_t *res) {
    BN_CTX *ctx = BN_CTX_new();

    int nLenBytes = ((int)nLen)*8;

    BIGNUM *bn_n = BN_lebin2bn((unsigned char*) n,nLenBytes,NULL);
    BIGNUM *bn_a = BN_lebin2bn((unsigned char*) a,nLenBytes,NULL);
    BIGNUM *bn_b = BN_lebin2bn((unsigned char*) b,nLenBytes,NULL);
    BIGNUM *bn_res = BN_new ();

    BN_mod_mul(bn_res,bn_a,bn_b,bn_n,ctx);

    if (BN_num_bytes(bn_res) > nLenBytes) {
        printf ("nlen: %u, retlen: %u\n", nLen, BN_num_bytes(bn_res));
        exit(1);
    }

    BN_bn2lebinpad(bn_res,(unsigned char*)res,nLenBytes);

    BN_free(bn_n);
    BN_free(bn_a);
    BN_free(bn_b);
    BN_free(bn_res);

    BN_CTX_free(ctx);
}


void Hacl_Impl_Bignum_Openssl_ossl_mod_exp(
  uint32_t nLen,
  uint32_t expLen,
  uint64_t *n,
  uint64_t *a,
  uint64_t *b,
  uint64_t *res) {

    BN_CTX *ctx = BN_CTX_new();

    int nLenBytes = ((int)nLen)*8;
    int expLenBytes = ((int)expLen)*8;

    BIGNUM *bn_n = BN_lebin2bn((unsigned char*) n,nLenBytes,NULL);
    BIGNUM *bn_a = BN_lebin2bn((unsigned char*) a,nLenBytes,NULL);
    BIGNUM *bn_b = BN_lebin2bn((unsigned char*) b,expLenBytes,NULL);
    BIGNUM *bn_res = BN_new ();

    BN_mod_exp(bn_res,bn_a,bn_b,bn_n,ctx);

    if (BN_num_bytes(bn_res) > nLenBytes) {
        printf ("nlen: %u, retlen: %u\n", nLen, BN_num_bytes(bn_res));
        exit(1);
    }

    BN_bn2lebinpad(bn_res,(unsigned char*)res,nLenBytes);

    BN_free(bn_n);
    BN_free(bn_a);
    BN_free(bn_b);
    BN_free(bn_res);

    BN_CTX_free(ctx);

}
