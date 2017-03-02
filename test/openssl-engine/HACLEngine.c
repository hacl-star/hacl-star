// Everest OpenSSL crypto engine for Curve25519
//
// This allows us to rely on OpenSSL's benchmarking infrastructure while
// multiplexing between:
// - the HACL* implementation
// - the OpenSSL implementation, which *we* call back into, so as to keep the
//   overhead of the testing infrastructure and have a fair performance
//   comparison (EVP_Digest allocates and frees on the heap on every inner loop
//   in the "speed" test).
// The Windows/BCrypt implementation now lies in a separate file since the
// potential for sharing is actually minimal. This file can potentially be
// extended with any other algorithm that easily exposes the X25519
// multiplication.
#include <stdint.h>
#include <stdio.h>
#include <openssl/engine.h>
#include <openssl/aes.h>
#include <openssl/ec.h>

#include "Curve25519.h"

// The multiplexing is done at compile-time; pass -DIMPL=IMPL_OPENSSL to your
// compiler to override the default HACL implementation.
#define IMPL_HACL 0
#define IMPL_OPENSSL 1
#ifndef IMPL
#define IMPL IMPL_HACL
#endif

static const char *engine_Everest_id = "Everest";

#if IMPL == IMPL_OPENSSL
static const char *engine_Everest_name = "Everest engine (OpenSSL crypto)";
#elif IMPL == IMPL_HACL
static const char *engine_Everest_name = "Everest engine (HACL* crypto)";
#else
#error "Unknown implementation"
#endif

int bind_helper(ENGINE * e, const char *id);

IMPLEMENT_DYNAMIC_CHECK_FN();
IMPLEMENT_DYNAMIC_BIND_FN(bind_helper);

int Everest_init(ENGINE *e) {
  return 1;
}

// The simplest way to get *our* implementation of X25519 running is to clone
// the original implementation, then override the pointer to the salient
// function with our code.
// Going down the rabbit hole:
// - crypto/ec/ecx_meth.c defines the EVP_PKEY_METHOD
// - EVP_PKEY_METHOD is actually a struct containing a bunch of function
//   pointers; in the case of X25519, many of them are NULL
// - the specific field we wish to override is pkey_ecx_derive which in turn
//   calls X25519
// - this is a copy/pasted implementation of the function below, rewired to call
//   into HACL
//
#define X25519_KEYLEN        32

// This is the internal struct type that I ended up copy/pasting from the
// original OpenSSL implementation. If they ever change their internal
// representation, this code will segfault. Everything else uses their public
// API.
typedef struct {
    unsigned char pubkey[X25519_KEYLEN];
    unsigned char *privkey;
} X25519_KEY;

#if IMPL == IMPL_HACL
static int X25519(uint8_t out_shared_key[32], uint8_t private_key[32],
  const uint8_t peer_public_value[32])
{
  static const uint8_t kZeros[32] = {0};
  // KreMLin does not have a concept of "const"-ness yet, but it is understood
  // that the function does not modify its third argument.
  Hacl_EC_crypto_scalarmult(out_shared_key, private_key, (uint8_t *) peer_public_value);
  /* The all-zero output results when the input is a point of small order. */
  return CRYPTO_memcmp(kZeros, out_shared_key, 32) != 0;
}

// This is a version of pkey_ecx_derive in ecx_meth.c that i) uses the public
// API and ii) calls our own X25519 function
static int hacl_derive(EVP_PKEY_CTX *ctx, unsigned char *key, size_t *keylen)
{
    const X25519_KEY *pkey, *peerkey;

    pkey = EVP_PKEY_get0(EVP_PKEY_CTX_get0_pkey(ctx));
    peerkey = EVP_PKEY_get0(EVP_PKEY_CTX_get0_peerkey(ctx));

    if (pkey == NULL || pkey->privkey == NULL) {
        ECerr(EC_F_PKEY_ECX_DERIVE, EC_R_INVALID_PRIVATE_KEY);
        return 0;
    }
    if (peerkey == NULL) {
        ECerr(EC_F_PKEY_ECX_DERIVE, EC_R_INVALID_PEER_KEY);
        return 0;
    }
    *keylen = X25519_KEYLEN;
    if (key != NULL && X25519(key, pkey->privkey, peerkey->pubkey) == 0)
        return 0;
    return 1;
}
#endif

// A lazy initializer
EVP_PKEY_METHOD *get_hacl_x25519_meth() {
  static EVP_PKEY_METHOD *hacl_x25519_meth = NULL;

  if (hacl_x25519_meth)
    return hacl_x25519_meth;

  const EVP_PKEY_METHOD *openssl_meth = EVP_PKEY_meth_find(NID_X25519);
  if (!openssl_meth) {
    fprintf(stderr, "Couldn't find OpenSSL X25519\n");
    exit(1);
  }

  hacl_x25519_meth = EVP_PKEY_meth_new(NID_X25519, 0);
  EVP_PKEY_meth_copy(hacl_x25519_meth, openssl_meth);

#if IMPL == IMPL_HACL
  EVP_PKEY_meth_set_derive(hacl_x25519_meth, NULL, hacl_derive);
#elif IMPL == IMPL_OPENSSL
  ;
#else
#error "Unsupported implementation"
#endif

  return hacl_x25519_meth;
}

static int Everest_digest_nids(const int **nids)
{
  static int digest_nids[16];
  static int init = 0;
  int count = 0;

  if (!init) {
    // NULL-terminate the list
    digest_nids[count] = 0;
    init = 1;
  }
  *nids = digest_nids;
  return count;
}

static int Everest_ciphers_nids(const int **nids)
{
  static int cipher_nids[16];
  static int init = 0;
  int count = 0;

  if (!init) {
    // NULL-terminate the lst
    cipher_nids[count] = 0;
    init = 1;
  }
  *nids = cipher_nids;
  return count;
}

static int Everest_pkey_meths_nids(const int **nids)
{
  static int pkey_meth_nids[16];
  static int init = 0;
  int count = 0;

  if (!init) {
    pkey_meth_nids[count++] = NID_X25519;

    // NULL-terminate the lst
    pkey_meth_nids[count] = 0;
    init = 1;
  }
  *nids = pkey_meth_nids;
  return count;
}

// These three functions follow the protocol explained in
// include/openssl/engine.h near line 280.
int Everest_digest(ENGINE *e, const EVP_MD **digest, const int **nids, int nid)
{
  if (digest == NULL) {
    return Everest_digest_nids(nids);
  } else {
    return 0;
  }
}

int Everest_ciphers(ENGINE *e, const EVP_CIPHER **cipher, const int **nids, int nid)
{
  if (cipher == NULL) {
    return Everest_ciphers_nids(nids);
  } else {
    return 0;
  }
}

int Everest_pkey_meths(ENGINE *e, EVP_PKEY_METHOD **method, const int **nids, int nid)
{
  if (method == NULL) {
    return Everest_pkey_meths_nids(nids);
  } else if (nid == NID_X25519) {
    *method = get_hacl_x25519_meth();
    return 1;
  } else {
    return 0;
  }
}

// See https://wiki.openssl.org/index.php/Creating_an_OpenSSL_Engine_to_use_indigenous_ECDH_ECDSA_and_HASH_Algorithms

int bind_helper(ENGINE * e, const char *id)
{
  if (!ENGINE_set_id(e, engine_Everest_id) ||
    !ENGINE_set_name(e, engine_Everest_name) ||
    !ENGINE_set_init_function(e,Everest_init) ||
    !ENGINE_set_ciphers(e, Everest_ciphers) ||
    !ENGINE_set_digests(e, Everest_digest) ||
    !ENGINE_set_pkey_meths(e, Everest_pkey_meths)
  )
    return 0;

  return 1;
}
