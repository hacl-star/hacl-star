#include "Hacl_Impl_Bignum_Openssl.h"
#include <openssl/bn.h>


void convert_endianness(void *pv, size_t n)
{
    char *p = pv;
    size_t lo, hi;
    for(lo=0, hi=n-1; hi>lo; lo++, hi--)
    {
        char tmp=p[lo];
        p[lo] = p[hi];
        p[hi] = tmp;
    }
}

void Hacl_Impl_Bignum_Openssl_ossl_mod_exp(
  uint32_t nLen,
  uint32_t expLen,
  uint64_t *n,
  uint64_t *a,
  uint64_t *b,
  uint64_t *res) {
    convert_endianness((unsigned char*) n,((int)nLen)*8);
    BIGNUM *bn_n = BN_bin2bn((unsigned char*) n,((int)nLen)*8,NULL);
    convert_endianness((unsigned char*) a,((int)nLen)*8);
    BIGNUM *bn_a = BN_bin2bn((unsigned char*) a,((int)nLen)*8,NULL);
    convert_endianness((unsigned char*) b,((int)nLen)*8);
    BIGNUM *bn_b = BN_bin2bn((unsigned char*) b,((int)expLen)*8,NULL);

    convert_endianness((unsigned char*) n,((int)nLen)*8);
    convert_endianness((unsigned char*) a,((int)nLen)*8);
    convert_endianness((unsigned char*) b,((int)nLen)*8);

    BIGNUM *bn_res = BN_new ();

    BN_CTX *ctx = BN_CTX_new();

    BN_mod_exp(bn_res,bn_a,bn_b,bn_n,ctx);

    if (bn_res->dmax > nLen) {
        printf ("nlen: %u, dmax: %u\n", nLen, bn_res->dmax);
    }

    //printf ("STEP2");
    BN_bn2bin(bn_res,(unsigned char*)res);
    convert_endianness((unsigned char*) res,((int)nLen)*8);

    //printf ("STEP3");
    BN_free(bn_n);
    BN_free(bn_a);
    BN_free(bn_b);
    BN_free(bn_res);

    BN_CTX_free(ctx);
    //printf ("STEP4");

}
