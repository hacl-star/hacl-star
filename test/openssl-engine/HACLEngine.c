// Everest OpenSSL crypto engine for Chacah20, Curve25519, Poly1305
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
#include <openssl/evp.h>

#define Hacl_Impl_Poly1305_64_poly1305_state whatever
#include "Curve25519.h"
#include "Poly1305_64.h"
#undef Hacl_Impl_Poly1305_64_poly1305_state
#include "Chacha20.h"
#include "Chacha20Poly1305.h"
#include "SHA2_512.h"

// OpenSSL private header for benchmarking purposes
#include "crypto/include/internal/poly1305.h"
#ifdef _WIN32
void OPENSSL_cpuid_setup() {
}
#endif

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

// X25519 ----------------------------------------------------------------------

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
#endif // IMPL_HACL

// Chacha20 --------------------------------------------------------------------

#define CHACHA20_KEY_SIZE 32
#define CHACHA20_IV_SIZE 12

// TODO: use a struct here rather than a contiguous chunk of memory
#if IMPL == IMPL_HACL
static int Wrapper_Chacha20_Init(EVP_CIPHER_CTX *ctx, const unsigned char *key, const unsigned char *iv, int enc) {
  uint8_t *my_ctx = EVP_CIPHER_CTX_get_cipher_data(ctx);
  memcpy(my_ctx, key, CHACHA20_KEY_SIZE);
  memcpy(my_ctx+CHACHA20_KEY_SIZE, iv, CHACHA20_IV_SIZE);
  return 1;
}

static int Wrapper_Chacha20_Cipher(EVP_CIPHER_CTX *ctx, unsigned char *out, const unsigned char *in, size_t len) {
  uint8_t *my_ctx = EVP_CIPHER_CTX_get_cipher_data(ctx);
  Chacha20_chacha20(out, in, len, my_ctx, my_ctx + CHACHA20_KEY_SIZE, 0);
  return 1;
}
#endif // IMPL_HACL

// SHA2_512 --------------------------------------------------------------------

#if IMPL==IMPL_HACL

// In 64-bit words
#define HACL_SHA2_512_STATE_SIZE 169
// In bytes
#define HACL_SHA2_512_BLOCK_SIZE_B 16

static int hacl_sha2_512_init(EVP_MD_CTX *ctx) {
  uint64_t *state = EVP_MD_CTX_md_data(ctx);
  SHA2_512_init(state);
  return 1;
}

static int hacl_sha2_512_update(EVP_MD_CTX *ctx, const void *data_r, size_t count) {
  uint64_t *state = EVP_MD_CTX_md_data(ctx);
  // Same remark as poly1305
  uint32_t n_blocks = count / HACL_SHA2_512_BLOCK_SIZE_B;
  uint8_t *data = data_r;
  while (n_blocks--) {
    SHA2_512_update(state, data);
    data += HACL_SHA2_512_BLOCK_SIZE_B;
  }
  return 1;
}

static int hacl_sha2_512_final(EVP_MD_CTX *ctx, unsigned char *md) {
  uint64_t *state = EVP_MD_CTX_md_data(ctx);
  SHA2_512_update_last(state, NULL, 0);
  SHA2_512_finish(state, md);
  return 1;
}

static int hacl_sha2_512_copy(EVP_MD_CTX *to, const EVP_MD_CTX *from) {
  return 1;
}

static int hacl_sha2_512_cleanup(EVP_MD_CTX *ctx) {
  return 1;
}

#endif

// Poly1305 --------------------------------------------------------------------

// Dummy key for benchmarking purposes.
static /* const */ uint8_t poly1305_dummy_key[] =
{
  0x85, 0xd6, 0xbe, 0x78, 0x57, 0x55, 0x6d, 0x33, 0x7f, 0x44, 0x52, 0xfe, 0x42, 0xd5, 0x06, 0xa8,
  0x01, 0x03, 0x80, 0x8a, 0xfb, 0x0d, 0xb2, 0xfd, 0x4a, 0xbf, 0xf6, 0xaf, 0x41, 0x49, 0xf5, 0x1b
};

static int hacl_poly1305_init(EVP_MD_CTX *ctx) {
  #if IMPL==IMPL_HACL
  Poly1305_64_state *state = EVP_MD_CTX_md_data(ctx);
  uint64_t *buf = malloc(sizeof (uint64_t) * 6);
  state->r = buf;
  state->h = buf + 3;

  Poly1305_64_init(*state, poly1305_dummy_key);
  #elif IMPL == IMPL_OPENSSL
  Poly1305_Init(EVP_MD_CTX_md_data(ctx), poly1305_dummy_key);
  #endif
  return 1;
}

static int hacl_poly1305_update(EVP_MD_CTX *ctx, const void *data, size_t count) {
  #if IMPL==IMPL_HACL
  Poly1305_64_state *state = EVP_MD_CTX_md_data(ctx);
  // update takes a number of blocks (16 bytes) while update_last takes the
  // number of remaining bytes...
  // i) If OpenSSL always calls us with multiples of 16 bytes except for the
  //    last chunk, we could call update_last here
  // ii) If this doesn't hold, we could have a buffer of bytes in our state
  //     until we match a block boundary (this is what OpenSSL does in
  //     poly1305.c) -- JK says this is not constant time
  // iii) Right now, we just ignore any bytes that are not on the boundary.
  uint32_t n_blocks = count / 16;
  Poly1305_64_update(*state, (uint8_t *) data, (uint32_t) n_blocks);
  #elif IMPL == IMPL_OPENSSL
  Poly1305_Update(EVP_MD_CTX_md_data(ctx), data, count);
  #endif
  return 1;
}

static int hacl_poly1305_final(EVP_MD_CTX *ctx, unsigned char *md) {
  #if IMPL==IMPL_HACL
  Poly1305_64_state *state = EVP_MD_CTX_md_data(ctx);
  Poly1305_64_update_last(*state, NULL, 0);
  Poly1305_64_finish(*state, md, poly1305_dummy_key + 16);
  #elif IMPL == IMPL_OPENSSL
  Poly1305_Final(EVP_MD_CTX_md_data(ctx), md);
  #endif
  return 1;
}

// Chacha-Poly -----------------------------------------------------------------

#if IMPL==IMPL_HACL
int hacl_chachapoly_init (EVP_CIPHER_CTX *ctx,
  const unsigned char *key,
  const unsigned char *iv,
  int enc)
{
  return 1;
}

// Begin copy/paste from OpenSSL
#define CHACHA_KEY_SIZE		32
#define CHACHA_CTR_SIZE		16
#define CHACHA_BLK_SIZE		64

typedef struct {
    union {
        double align;   /* this ensures even sizeof(EVP_CHACHA_KEY)%8==0 */
        unsigned int d[CHACHA_KEY_SIZE / 4];
    } key;
    unsigned int  counter[CHACHA_CTR_SIZE / 4];
    unsigned char buf[CHACHA_BLK_SIZE];
    unsigned int  partial_len;
} EVP_CHACHA_KEY;

typedef struct {
    EVP_CHACHA_KEY key;
    unsigned int nonce[12/4];
    unsigned char tag[POLY1305_BLOCK_SIZE];
    struct { uint64_t aad, text; } len;
    int aad, mac_inited, tag_len, nonce_len;
    size_t tls_payload_length;
} EVP_CHACHA_AEAD_CTX;
// End copy/paste

int hacl_chachapoly_do_cipher(EVP_CIPHER_CTX *ctx,
  unsigned char *out,
  const unsigned char *in,
  size_t inl)
{
  // printf("Trace: out=%p, in=%p, inl=%zu\n", out, in, inl);

  // Note: the benchmarking engine never uses a CTRL call to set the AAD; it
  // also never calls us with out = NULL which, according to the OpenSSL source
  // code, is the way the caller indicates that it's about to switch to AAD.
  // Therefore, we provide a NULL AAD pointer, which is enough to have a
  // representative performance test. This is, naturally, highly non-functional.
  static bool warned = false;
  if (!warned) {
    printf("Warning: this is a non-functional cipher intended for benchmarking "
      "purposes only!\n");
    warned = true;
  }

  EVP_CHACHA_AEAD_CTX *aead_data = EVP_CIPHER_CTX_get_cipher_data(ctx);

  uint8_t mac[16] = { 0 };
  Chacha20Poly1305_aead_encrypt(out,
    mac,
    in,
    inl,
    NULL,
    0,
    aead_data->key.buf,
    aead_data->nonce);

  return 1;
}

int hacl_chachapoly_cleanup(EVP_CIPHER_CTX *ctx) {
  return 1;
}

int hacl_chachapoly_ctrl(EVP_CIPHER_CTX *ctx, int type, int arg, void *ptr) {
  // This should implement all the operations that its counterpart in
  // e_chacha20_poly1305.c implements; specifically, the minute we start to
  // implement this, we should at least implement EVP_CTRL_INIT to make sure we
  // properly allocate our data structures, and make sure we return 0 otherwise.
  return 0;
}
#endif

// Registering our algorithms within the engine infrastructure -----------------

static int Everest_digest_nids(const int **nids)
{
  static int digest_nids[16];
  static int init = 0;
  int count = 0;

  if (!init) {
    digest_nids[count++] = NID_poly1305;
    digest_nids[count++] = NID_sha512;

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
    cipher_nids[count++] = NID_chacha20;
    cipher_nids[count++] = NID_chacha20_poly1305;

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

static EVP_MD *hacl_poly1305_digest = NULL;
static EVP_MD *hacl_sha2_512_digest = NULL;

// These three functions follow the protocol explained in
// include/openssl/engine.h near line 280.
int Everest_digest(ENGINE *e, const EVP_MD **digest, const int **nids, int nid)
{
  if (digest == NULL) {
    return Everest_digest_nids(nids);
  } else if (nid == NID_poly1305) {
    *digest = hacl_poly1305_digest;
    return 1;
  } else if (nid == NID_sha512) {
    *digest = hacl_sha2_512_digest;
    return 1;
  } else {
    return 0;
  }
}

static EVP_CIPHER *hacl_chacha20_cipher = NULL;
static EVP_CIPHER *hacl_chachapoly_cipher = NULL;

int Everest_ciphers(ENGINE *e, const EVP_CIPHER **cipher, const int **nids, int nid)
{
  if (cipher == NULL) {
    return Everest_ciphers_nids(nids);
  } else if (nid == NID_chacha20) {
    *cipher = hacl_chacha20_cipher;
    return 1;
  } else if (nid == NID_chacha20_poly1305) {
    *cipher = hacl_chachapoly_cipher;
    return 1;
  } else {
    return 0;
  }
}

static EVP_PKEY_METHOD *hacl_x25519_meth = NULL;

int Everest_pkey_meths(ENGINE *e, EVP_PKEY_METHOD **method, const int **nids, int nid)
{
  if (method == NULL) {
    return Everest_pkey_meths_nids(nids);
  } else if (nid == NID_X25519) {
    *method = hacl_x25519_meth;
    return 1;
  } else {
    return 0;
  }
}

// Allocate the EVP_* data structures for our algorithms -----------------------

int Everest_init(ENGINE *e) {
  return 1;
}

int Everest_destroy(ENGINE *e) {
  // Because meth_copy frees the destination pointer? Need to look at the
  // implementation...
  // EVP_PKEY_meth_free(hacl_x25519_meth);
  #if IMPL==IMPL_HACL
  EVP_CIPHER_meth_free(hacl_chacha20_cipher);
  #endif
  EVP_MD_meth_free(hacl_poly1305_digest);
  return 1;
}

void Everest_create_all_the_things() {
  // X25519
  // ------
  // We copy the existing OpenSSL code and just swap in our
  // multiplication, so that we don't have to duplicate the rest of the logic.
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
  // Let the benchmarking go through the Engine framework, but redirect back to
  // OpenSSL.
  #else
  #error "Unsupported implementation"
  #endif

  // Chacha20
  // --------
  #if IMPL == IMPL_HACL
  hacl_chacha20_cipher = EVP_CIPHER_meth_new(NID_chacha20, 1, CHACHA20_KEY_SIZE);
  EVP_CIPHER_meth_set_iv_length(hacl_chacha20_cipher, CHACHA20_IV_SIZE);
  EVP_CIPHER_meth_set_flags(hacl_chacha20_cipher, EVP_CIPH_CUSTOM_IV | EVP_CIPH_ALWAYS_CALL_INIT);
  EVP_CIPHER_meth_set_init(hacl_chacha20_cipher, Wrapper_Chacha20_Init);
  EVP_CIPHER_meth_set_do_cipher(hacl_chacha20_cipher, Wrapper_Chacha20_Cipher);
  // We just store the key (32) and the iv (12)
  EVP_CIPHER_meth_set_impl_ctx_size(hacl_chacha20_cipher, CHACHA20_KEY_SIZE + CHACHA20_IV_SIZE);
  #elif IMPL == IMPL_OPENSSL
  // Let the benchmarking go through the Engine framework, but redirect back to
  // OpenSSL.
  hacl_chacha20_cipher = EVP_chacha20();
  #else
  #error "Unsupported implementation"
  #endif

  // SHA512
  // --------
  #if IMPL == IMPL_HACL
  hacl_sha2_512_digest = EVP_MD_meth_new(NID_sha512, NID_undef);
  if (hacl_sha2_512_digest == NULL ||
    !EVP_MD_meth_set_result_size(hacl_sha2_512_digest, 64) ||
    !EVP_MD_meth_set_init(hacl_sha2_512_digest, hacl_sha2_512_init) ||
    !EVP_MD_meth_set_update(hacl_sha2_512_digest, hacl_sha2_512_update) ||
    !EVP_MD_meth_set_final(hacl_sha2_512_digest, hacl_sha2_512_final) ||
    !EVP_MD_meth_set_cleanup(hacl_sha2_512_digest, hacl_sha2_512_cleanup) ||
    !EVP_MD_meth_set_copy(hacl_sha2_512_digest, hacl_sha2_512_copy) ||
    !EVP_MD_meth_set_app_datasize(hacl_sha2_512_digest, HACL_SHA2_512_STATE_SIZE * 8) ||
    !EVP_MD_meth_set_input_blocksize(hacl_sha2_512_digest, HACL_SHA2_512_BLOCK_SIZE_B) ||
    !EVP_MD_meth_set_flags(hacl_sha2_512_digest, EVP_MD_FLAG_ONESHOT))
  {
    fprintf(stderr, "Error creating SHA512\n");
    EVP_MD_meth_free(hacl_sha2_512_digest);
    exit(1);
  }
  #elif IMPL == IMPL_OPENSSL
  hacl_sha2_512_digest = EVP_sha512();
  #else
  #error "Unsupported implementation"
  #endif

  // Poly1305
  // --------
  hacl_poly1305_digest = EVP_MD_meth_new(NID_poly1305, NID_undef);
  EVP_MD_meth_set_init(hacl_poly1305_digest, hacl_poly1305_init);
  EVP_MD_meth_set_update(hacl_poly1305_digest, hacl_poly1305_update);
  EVP_MD_meth_set_final(hacl_poly1305_digest, hacl_poly1305_final);
  #if IMPL == IMPL_HACL
  // There's ZERO documentation, but reading the implementation, it seems like
  // this does what I want, i.e. OpenSSL allocates that many bytes when the MD
  // is created, and then I can get it via md_data.
  EVP_MD_meth_set_app_datasize(hacl_poly1305_digest, sizeof(Poly1305_64_state));
  #elif IMPL == IMPL_OPENSSL
  EVP_MD_meth_set_app_datasize(hacl_poly1305_digest, Poly1305_ctx_size());
  #else
  #error "Unsupported implementation"
  #endif
  EVP_MD_meth_set_input_blocksize(hacl_poly1305_digest, 16);

  // Chacha-Poly
  // -----------
  hacl_chachapoly_cipher = EVP_CIPHER_meth_dup(EVP_chacha20_poly1305());
  #if IMPL == IMPL_HACL
  //EVP_CIPHER_meth_set_init(hacl_chachapoly_cipher, hacl_chachapoly_init);
  EVP_CIPHER_meth_set_do_cipher(hacl_chachapoly_cipher, hacl_chachapoly_do_cipher);
  //EVP_CIPHER_meth_set_cleanup(hacl_chachapoly_cipher, hacl_chachapoly_cleanup);
  //EVP_CIPHER_meth_set_ctrl(hacl_chachapoly_cipher, hacl_chachapoly_ctrl);
  #elif IMPL == IMPL_OPENSSL
  #else
  #error "Unsupported implementation"
  #endif
}

// Registering everything as an engine -----------------------------------------

// See https://wiki.openssl.org/index.php/Creating_an_OpenSSL_Engine_to_use_indigenous_ECDH_ECDSA_and_HASH_Algorithms
int bind_helper(ENGINE * e, const char *id)
{
  Everest_create_all_the_things();

  if (!ENGINE_set_id(e, engine_Everest_id) ||
    !ENGINE_set_name(e, engine_Everest_name) ||
    !ENGINE_set_init_function(e, Everest_init) ||
    !ENGINE_set_destroy_function(e, Everest_destroy) ||
    !ENGINE_set_ciphers(e, Everest_ciphers) ||
    !ENGINE_set_digests(e, Everest_digest) ||
    !ENGINE_set_pkey_meths(e, Everest_pkey_meths) ||
    !EVP_add_digest(hacl_poly1305_digest)
  ) {
    fprintf(stderr, "Error initializing the Everest engine!\n");
    return 0;
  }

  return 1;
}

IMPLEMENT_DYNAMIC_CHECK_FN();
IMPLEMENT_DYNAMIC_BIND_FN(bind_helper);
