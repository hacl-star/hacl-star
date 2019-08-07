#include "Hacl_Impl_Bignum_Openssl.h"
#include <openssl/bn.h>
#include <sys/time.h>

bool Hacl_Impl_Bignum_Openssl_ossl_is_prm(
  uint32_t pLen,
  uint64_t *p) {
    BN_CTX *ctx = BN_CTX_new();

    int pLenBytes = ((int)pLen)*8;
    BIGNUM *bn_p = BN_lebin2bn((unsigned char*) p,pLenBytes,NULL);

    bool res = BN_is_prime_ex(bn_p, BN_prime_checks, ctx, NULL) == 1;

    BN_CTX_free(ctx);

    return res;
}

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

void print_time (char* label) {
    struct timeval tv;
    gettimeofday(&tv,NULL);
    printf ("%lu.%lu %s\n", tv.tv_sec, tv.tv_usec, label);
}


inline void rho_map(BN_CTX *ctx,

             const BIGNUM *n,
             const BIGNUM *n1, // n / 3
             const BIGNUM *n2, // 2n / 3
             const BIGNUM *u, // p^e

             const BIGNUM *g,
             const BIGNUM *h,

             const BIGNUM *one,
             const BIGNUM *two,

             BIGNUM *tmp,

             BIGNUM *x,
             BIGNUM *a,
             BIGNUM *b) {

    if (BN_cmp(x, n1) == -1) {
        BN_mod_mul(x,x,g,n,ctx);
        BN_mod_add(a,a,one,u,ctx);
    } else if (BN_cmp(x,n2) == -1) {
        BN_mod_mul(x,x,x,n,ctx);
        BN_mod_mul(a,a,two,u,ctx);
        BN_mod_mul(b,b,two,u,ctx);
    } else {
        BN_mod_mul(x,x,h,n,ctx);
        BN_mod_add(b,b,one,u,ctx);
    }
}


void Hacl_Impl_Bignum_Openssl_solve_dlp_single_external(
  uint32_t nLen,
  uint64_t *raw_n,
  uint64_t *raw_p,
  uint64_t *raw_e,
  uint64_t *raw_g,
  uint64_t *raw_h,
  uint64_t *raw_res) {

    BN_CTX *ctx = BN_CTX_new();

    int nLenBytes = ((int)nLen)*8;

    BIGNUM *n = BN_lebin2bn((unsigned char*) raw_n,nLenBytes,NULL);
    BIGNUM *p = BN_lebin2bn((unsigned char*) raw_p,nLenBytes,NULL);
    BIGNUM *e = BN_lebin2bn((unsigned char*) raw_e,nLenBytes,NULL);
    BIGNUM *g = BN_lebin2bn((unsigned char*) raw_g,nLenBytes,NULL);
    BIGNUM *h = BN_lebin2bn((unsigned char*) raw_h,nLenBytes,NULL);
    BIGNUM *res = BN_new ();

    BIGNUM *one = BN_new();
    BN_dec2bn(&one, "1");
    BIGNUM *two = BN_new();
    BN_dec2bn(&two, "2");
    BIGNUM *three = BN_new();
    BN_dec2bn(&three, "3");

    BIGNUM *tmp = BN_new ();

    BIGNUM *u = BN_new ();
    BN_exp(u,p,e,ctx);

    BIGNUM *n1 = BN_new();
    BIGNUM *n2 = BN_new();
    BN_div(n1,NULL,n,three,ctx);
    BN_mul(n2,n1,two,ctx);

    BIGNUM *x = BN_new ();
    BN_copy(x,one);
    BIGNUM *y = BN_new ();
    BN_copy(y,one);
    BIGNUM *a = BN_new ();
    BIGNUM *b = BN_new ();
    BIGNUM *c = BN_new ();
    BIGNUM *d = BN_new ();

    BIGNUM *s1 = BN_new ();
    BIGNUM *s2 = BN_new ();

    for (size_t i = 0; true; i++) {
        if (i > 0 && BN_cmp(x,y) == 0) break;

        rho_map(ctx,n,n1,n2,u,g,h,one,two,tmp,x,a,b);

        rho_map(ctx,n,n1,n2,u,g,h,one,two,tmp,y,c,d);
        rho_map(ctx,n,n1,n2,u,g,h,one,two,tmp,y,c,d);
    }

    BN_mod_sub(s1,a,c,u,ctx);
    BN_mod_sub(s2,d,b,u,ctx);

    BN_gcd(tmp,s2,u,ctx);
    if (BN_cmp(tmp,one) == 0) {
        BN_mod_inverse(tmp,s2,u,ctx);
        BN_mod_mul(res,s1,tmp,u,ctx);
    } else {
        fprintf(stderr,"We're not yet ready for this\n");
        BN_print_fp(stderr, p);
        fprintf(stderr,"\n");
        BN_print_fp(stderr, e);
        fprintf(stderr,"\n");
        BN_print_fp(stderr, u);
        fprintf(stderr,"\n");
        BN_print_fp(stderr, s1);
        fprintf(stderr,"\n");
        BN_print_fp(stderr, s2);
        fprintf(stderr,"\n");
        exit(4);
    }

    // Functional check
    //BN_mod_exp(tmp,g,res,n,ctx);
    //if (BN_cmp(tmp,h) != 0) {
    //    fprintf(stderr, "Rho: failed to produce a correct result\n");
    //}

    BN_bn2lebinpad(res,(unsigned char*)raw_res,nLenBytes);


    BN_free(a);
    BN_free(b);
    BN_free(c);
    BN_free(d);
    BN_free(x);
    BN_free(y);

    BN_free(n);
    BN_free(p);
    BN_free(e);
    BN_free(g);
    BN_free(h);
    BN_free(res);

    BN_free(one);
    BN_free(two);
    BN_free(three);

    BN_free(u);

    BN_free(tmp);

    BN_free(n1);
    BN_free(n2);

    BN_CTX_free(ctx);


}
