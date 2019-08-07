#include "Hacl_Impl_Bignum_Openssl.h"
#include <openssl/bn.h>
#include <openssl/bn.h>


void Hacl_Impl_Bignum_Openssl_ossl_divide(
  uint32_t aLen,
  uint64_t *a,
  uint64_t *b,
  uint64_t *q,
  uint64_t *r) {
    BN_CTX *ctx = BN_CTX_new();

    int aLenBytes = ((int)aLen)*8;

    BIGNUM *bn_a = BN_lebin2bn((unsigned char*) a,aLenBytes,NULL);
    BIGNUM *bn_b = BN_lebin2bn((unsigned char*) b,aLenBytes,NULL);
    BIGNUM *bn_q = BN_new();
    BIGNUM *bn_r = BN_new();

    BN_div(bn_q,bn_r,bn_a,bn_b,ctx);

    if (BN_num_bytes(bn_q) > aLenBytes) {
        printf ("div 1: nlen: %u, retlen: %u\n", aLen, BN_num_bytes(bn_q));
        exit(1);
    }

    if (BN_num_bytes(bn_r) > aLenBytes) {
        printf ("div 2: nlen: %u, retlen: %u\n", aLen, BN_num_bytes(bn_r));
        exit(1);
    }

    BN_bn2lebinpad(bn_q,(unsigned char*)q,aLenBytes);
    BN_bn2lebinpad(bn_r,(unsigned char*)r,aLenBytes);

    BN_free(bn_a);
    BN_free(bn_b);
    BN_free(bn_q);
    BN_free(bn_r);

    BN_CTX_free(ctx);
}

void Hacl_Impl_Bignum_Openssl_ossl_mod(
  uint32_t aLen,
  uint32_t modLen,
  uint64_t *a,
  uint64_t *mod,
  uint64_t *r) {
    BN_CTX *ctx = BN_CTX_new();

    int aLenBytes = ((int)aLen)*8;
    int modLenBytes = ((int)modLen)*8;

    BIGNUM *bn_a = BN_lebin2bn((unsigned char*) a,aLenBytes,NULL);
    BIGNUM *bn_mod = BN_lebin2bn((unsigned char*) mod,modLenBytes,NULL);
    BIGNUM *bn_r = BN_new();

    BN_mod(bn_r,bn_a,bn_mod,ctx);

    if (BN_num_bytes(bn_r) > aLenBytes) {
        printf ("mod: nlen: %u, retlen: %u\n", aLen, BN_num_bytes(bn_r));
        exit(1);
    }

    BN_bn2lebinpad(bn_r,(unsigned char*)r,modLenBytes);

    BN_free(bn_a);
    BN_free(bn_mod);
    BN_free(bn_r);

    BN_CTX_free(ctx);
}

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
