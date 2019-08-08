#include "Hacl_Impl_Bignum_Openssl.h"
#include <openssl/bn.h>
#include <sys/time.h>

size_t Hacl_Impl_Bignum_Openssl_ossl_is_prm(
  uint32_t pLen,
  uint32_t tries,
  uint64_t *p) {
    BN_CTX *ctx = BN_CTX_new();

    int pLenBytes = ((int)pLen)*8;
    BIGNUM *bn_p = BN_lebin2bn((unsigned char*) p,pLenBytes,NULL);

    int t = BN_is_prime_ex(bn_p, tries, ctx, NULL);

    BN_CTX_free(ctx);

    return t;
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

void extended_gcd(  BIGNUM *a
                  , BIGNUM *b
                  , BIGNUM *g
                  , BIGNUM *u
                  , BIGNUM *v
                  , BN_CTX *ctx
                  , BIGNUM *tmp1
                    )
{
    if (BN_is_zero(a)) {
        BN_dec2bn(&u, "0");
        BN_dec2bn(&v, "1");
        BN_copy(g, b);
    } else {
        BIGNUM *tmp2 = BN_new ();
        BN_div(tmp2,tmp1,b,a,ctx);
        BN_copy(b,a);
        BN_copy(a,tmp1);
        extended_gcd(a,b,g,u,v,ctx,tmp1);

        BN_swap(u,v);
        BN_mul(tmp1,tmp2,v,ctx);
        BN_sub(u,u,tmp1);
    }
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

void dlp_simple_iterative ( const BIGNUM *n
                          , const BIGNUM *u
                          , const BIGNUM *g
                          , const BIGNUM *h
                          , BIGNUM *res
                            , BN_CTX *ctx
                            ) {


    BIGNUM *zero = BN_new();
    BIGNUM *one = BN_new();
    BN_dec2bn(&one, "1");

    BIGNUM *counter = BN_new();
    BIGNUM *val = BN_new ();

    BN_copy(val,one);
    BN_copy(res,zero);
    while (BN_cmp(res,u) < 0) {
        if (BN_cmp(val,h) == 0) break;
        BN_mod_mul(val,val,g,n,ctx);
        BN_add(res,res,one);
    }

    BN_free (zero);
    BN_free (one);
    BN_free (counter);
    BN_free (val);
}


void Hacl_Impl_Bignum_Openssl_solve_dlp_single_external(
  uint32_t nLen,
  uint64_t *raw_n,
  uint64_t *raw_p,
  uint64_t *raw_e,
  uint64_t *raw_g,
  uint64_t *raw_h,
  uint64_t *raw_res) {
    //    fprintf(stderr, "Rho started\n");
    BN_CTX *ctx = BN_CTX_new();

    int nLenBytes = ((int)nLen)*8;

    BIGNUM *n = BN_lebin2bn((unsigned char*) raw_n,nLenBytes,NULL);
    BIGNUM *p = BN_lebin2bn((unsigned char*) raw_p,nLenBytes,NULL);
    BIGNUM *e = BN_lebin2bn((unsigned char*) raw_e,nLenBytes,NULL);
    BIGNUM *g = BN_lebin2bn((unsigned char*) raw_g,nLenBytes,NULL);
    BIGNUM *h = BN_lebin2bn((unsigned char*) raw_h,nLenBytes,NULL);
    BIGNUM *res = BN_new ();

    BIGNUM *limit = BN_new ();
    BN_dec2bn(&limit, "256");
    BIGNUM *u = BN_new ();
    BN_exp(u,p,e,ctx);

    if (BN_cmp(u,limit) < 0) {
        //fprintf(stderr, "Simple iteration solution works");
        dlp_simple_iterative(n,u,g,h,res,ctx);
        BN_bn2lebinpad(res,(unsigned char*)raw_res,nLenBytes);
        BN_free(n);
        BN_free(p);
        BN_free(e);
        BN_free(g);
        BN_free(h);
        BN_free(limit);
        BN_free(u);
        BN_CTX_free(ctx);
        //fprintf(stderr, "Simple iteration solution works");
        return;
    }

    BN_free(limit);

    BIGNUM *zero = BN_new();
    BIGNUM *one = BN_new();
    BN_dec2bn(&one, "1");
    BIGNUM *two = BN_new();
    BN_dec2bn(&two, "2");
    BIGNUM *three = BN_new();
    BN_dec2bn(&three, "3");

    BIGNUM *tmp = BN_new ();
    BIGNUM *tmp2 = BN_new ();


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

    //    fprintf(stderr, "Main collision loop started\n");
    int j = 0;
    for (size_t i = 0; true; i++) {
        if (i > 0 && BN_cmp(x,y) == 0) {
            if (BN_cmp(a,c) == 0 && BN_cmp(b,d) == 0) {

                if (j > 100) {
                    fprintf(stderr, "Rho is in loop, aborting\n");
                    exit(1);
                }

                BN_mod_mul(x,x,g,n,ctx);
                BN_mod_add(a,a,one,u,ctx);

                j++;
            } else break;
        }

        rho_map(ctx,n,n1,n2,u,g,h,one,two,tmp,x,a,b);

        rho_map(ctx,n,n1,n2,u,g,h,one,two,tmp,y,c,d);
        rho_map(ctx,n,n1,n2,u,g,h,one,two,tmp,y,c,d);
    }
    //fprintf(stderr, "Main collision loop ended\n");

    BN_mod_sub(s1,a,c,u,ctx);
    BN_mod_sub(s2,d,b,u,ctx);

    //fprintf(stderr, "S1 and S2 \n");
    //BN_print_fp(stderr, s1);
    //fprintf(stderr, "\n");
    //BN_print_fp(stderr, s2);
    //fprintf(stderr, "\n");

    BN_gcd(tmp,s2,u,ctx);
    if (BN_is_one(tmp)) {
        BN_mod_inverse(tmp,s2,u,ctx);
        BN_mod_mul(res,s1,tmp,u,ctx);
    } else {
        //fprintf(stderr, "Rho GCD 1 IS: ");
        //BN_print_fp(stderr, tmp);
        //fprintf(stderr, "\n");

        BIGNUM *s2_2 = BN_new ();
        BN_copy (s2_2, s2);
        BIGNUM *u_2 = BN_new ();
        BN_copy (u_2, u);
        BIGNUM *g0 = BN_new ();
        BIGNUM *g1 = BN_new ();
        BIGNUM *g2 = BN_new ();
        extended_gcd(s2_2,u_2,g0,g1,g2,ctx,tmp);
        // g0 is gcd
        // s2 * g1 + u * g2 = g0
        // s2 * g1 = g0 mod u

        BIGNUM *tmpG1 = BN_new ();
        BIGNUM *tmpG2 = BN_new ();
        BN_mul(tmpG1,s2,g1,ctx);
        BN_mul(tmpG2,u,g2,ctx);
        BN_add(tmp,tmpG1,tmpG2);
        if (BN_cmp(tmp,g0) != 0) {
            fprintf(stderr, "Rho GCD failure\n");
        }

        //fprintf(stderr, "Rho GCD 2 IS: ");
        //BN_print_fp(stderr, g0);
        //fprintf(stderr, "\n");

        // now s1 = w
        BN_mod_mul(s1,s1,g1,u,ctx);

        // w / d
        BIGNUM *wd = BN_new ();
        BN_div(wd,NULL,s1,g0,ctx);
        // u / d
        BIGNUM *ud = BN_new ();
        BN_div(ud,NULL,u,g0,ctx);

        BN_copy(tmp,zero);

        //fprintf(stderr, "Rho postloop started\n");
        while (true) {
            // check gcd
            BN_mod_mul(tmp2,g0,wd,u,ctx);
            if (BN_cmp(tmp2,s2) == 0) {
                //fprintf(stderr, "Post-gcd loop: success\n");
                break;
            }

            BN_add(wd,wd,ud);

            BN_add(tmp,tmp,one);
            //fprintf(stderr, "Rho loop iteration: ");
            //BN_print_fp(stderr, tmp);
            //fprintf(stderr, "\n");
            if (BN_cmp(tmp,g0) >= 0) {
                fprintf(stderr, "Post-gcd decryption loop: exiting, broken\n");
                exit(5);
            }
        }
        //fprintf(stderr, "Rho postloop ended\n");

        BN_copy(res,wd);

        BN_free(wd);
        BN_free(ud);
        BN_free(s2_2);
        BN_free(u_2);
        BN_free(g0);
        BN_free(g1);
        BN_free(g2);

        BN_free(tmpG1);
        BN_free(tmpG2);
    }

    // Functional check
    BN_mod_exp(tmp,g,res,n,ctx);
    if (BN_cmp(tmp,h) != 0) {
        fprintf(stderr, "!!!!!!!!!!!!  Rho: failed to produce a correct result\n");

        fprintf(stderr,"\np: ");
        BN_print_fp(stderr, p);
        fprintf(stderr,"\ne: ");
        BN_print_fp(stderr, e);
        fprintf(stderr,"\ng: ");
        BN_print_fp(stderr, g);
        fprintf(stderr,"\nh: ");
        BN_print_fp(stderr, h);
        fprintf(stderr,"\ns1: ");
        BN_print_fp(stderr, s1);
        fprintf(stderr,"\ns2:");
        BN_print_fp(stderr, s2);
        fprintf(stderr,"\nres: ");
        BN_print_fp(stderr, res);
        fprintf(stderr,"\n");

        exit(5);
    }

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
    BN_free(tmp2);

    BN_free(n1);
    BN_free(n2);

    BN_CTX_free(ctx);

    //    fprintf(stderr, "Rho ended\n");

}
