#include <stdint.h>
#include <stdio.h>
#include <openssl/engine.h>
#include <openssl/aes.h>
#include <openssl/ec.h>
#include <windows.h>
#include <bcrypt.h>

#define NT_SUCCESS(Status)          (((NTSTATUS)(Status)) >= 0)

// This file contains an OpenSSL engine that implements X25519 using the Windows
// BCrypt APIs (i.e. the modern Windows Cryptographic APIs). Since Curve25519 is
// Windows-10 only, and since mingw exposes the Windows SDK headers circa 8.1
// (which do NOT contain the APIs we want), the missing defines are brutally
// copy-pasted here.
#define BCRYPT_ECDH_ALGORITHM   L"ECDH"
#define BCRYPT_ECC_CURVE_NAME   L"ECCCurveName"
#define BCRYPT_ECC_CURVE_25519  L"curve25519"

// An alternative is to drop any use of a function from the C runtime system
// (e.g. printf and friends), and compile the present file with MSVC, as
// follows:
//   cl /c /FoBCryptWrapper.o /I"c:/Program Files (x86)/Windows Kits/10/Include/10.0.14393.0/shared" BCryptWrapper.c /link /nod:msvcrt14.lib msvcrt.lib
//
// Then, MinGW will link the object file happily, in spite of a spurious
// warning:
//   Warning: corrupt .drectve at end of def file
//
// Barry says:
// > The .drective warning is from the mingw linker complaining that it couldn't
//   support metadata embedded inside a .obj or .lib file.  Likely something like
//   a Win10 manifest record and ignorable.
// > The error message text is completely misleading.

static BCRYPT_ALG_HANDLE hAlg = NULL;

typedef struct {
  BCRYPT_KEY_HANDLE pair;
} bcrypt_x25519_key;

#define X25519_KEYLEN        32

static int bcrypt_keygen(EVP_PKEY_CTX *ctx, EVP_PKEY *pkey)
{
  // A quick reminder on the OpenSSL "public" API. Keys are defined as a union
  // field (we don't know that) that, for "exotic" key types (i.e. none of the
  // classic RSA, DSA, etc.), features a void* field. The void* field can then
  // point to a custom, heap-allocated data structure.
  bcrypt_x25519_key *key = malloc(sizeof(bcrypt_x25519_key));

  // TODO: no clue whether that generates a proper key pair or not. Are we
  // expected to fill it with random bytes?
  if (!NT_SUCCESS(BCryptGenerateKeyPair(hAlg, &key->pair, X25519_KEYLEN*8, 0))) {
    fprintf(stderr, "Cannot generate key pair\n");
    return 0;
  }
  if (!NT_SUCCESS(BCryptFinalizeKeyPair(key->pair, 0))) {
    fprintf(stderr, "Cannot finalize key pair\n");
    return 0;
  }
  EVP_PKEY_assign(pkey, EVP_PKEY_NONE, key);
  return 1;
}

static int bcrypt_derive(EVP_PKEY_CTX *ctx, unsigned char *outKey, size_t *outKeyLen)
{
  *outKeyLen = X25519_KEYLEN;
  if (outKey == NULL)
    return 0;

  // Note: this does NOT give you the actual bytes for the SECRET_HANDLE. (See
  // http://stackoverflow.com/questions/87694/im-using-wincrypt-for-diffie-hellman-can-i-export-the-shared-secret-in-plain
  // for something vaguely related). BCryptExportKey works for a KEY_HANDLE, not
  // a SECRET_HANDLE... and the type is defined as void* in the public Windows
  // 10 headers.
  bcrypt_x25519_key *pkey = EVP_PKEY_get0(EVP_PKEY_CTX_get0_pkey(ctx));
  bcrypt_x25519_key *peerkey = EVP_PKEY_get0(EVP_PKEY_CTX_get0_peerkey(ctx));
  BCRYPT_SECRET_HANDLE hSecret = NULL;
  if (!NT_SUCCESS(BCryptSecretAgreement(pkey->pair, peerkey->pair, &hSecret, 0))) {
    fprintf(stderr, "Cannot compute agreement\n");
    return 0;
  }
  // Writing out a dummy value in the meanwhile...
  memset(outKey, 0, X25519_KEYLEN*8);

  return 1;
}

static int bcrypt_ctrl(EVP_PKEY_CTX *ctx, int type, int p1, void *p2)
{
    if (type == EVP_PKEY_CTRL_PEER_KEY)
        return 1;
    return -2;
}

// OpenSSL engine-specific registration ---------------------------------------

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

static EVP_PKEY_METHOD *bcrypt_x25519_meth = NULL;

int Everest_pkey_meths(ENGINE *e, EVP_PKEY_METHOD **method, const int **nids, int nid)
{
  if (method == NULL) {
    return Everest_pkey_meths_nids(nids);
  } else if (nid == NID_X25519) {
    *method = bcrypt_x25519_meth;
    return 1;
  } else {
    return 0;
  }
}

int Everest_init(ENGINE *e) {
  // Initialize the global variables needed for BCrypt
  if (!NT_SUCCESS(BCryptOpenAlgorithmProvider(&hAlg, BCRYPT_ECDH_ALGORITHM, NULL, 0))) {
    fprintf(stderr, "Cannot open algorithm provider\n");
    return 0;
  }
  if (!NT_SUCCESS(BCryptSetProperty(hAlg,
          BCRYPT_ECC_CURVE_NAME,
          (PUCHAR) BCRYPT_ECC_CURVE_25519,
          sizeof(BCRYPT_ECC_CURVE_25519),
          0))) {
    fprintf(stderr, "Cannot select the right curve\n");
    return 0;
  }

  // Initialize our new method
  bcrypt_x25519_meth = EVP_PKEY_meth_new(NID_X25519, 0);
  EVP_PKEY_meth_set_derive(bcrypt_x25519_meth, NULL, bcrypt_derive);
  EVP_PKEY_meth_set_ctrl(bcrypt_x25519_meth, bcrypt_ctrl, NULL);
  EVP_PKEY_meth_set_keygen(bcrypt_x25519_meth, NULL, bcrypt_keygen);

  return 1;
}

static const char *engine_Everest_id = "Everest";
static const char *engine_Everest_name = "Everest engine (Windows/CNG/BestCrypt)";

int bind_helper(ENGINE * e, const char *id)
{
  if (!ENGINE_set_id(e, engine_Everest_id) ||
    !ENGINE_set_name(e, engine_Everest_name) ||
    !ENGINE_set_init_function(e,Everest_init) ||
    !ENGINE_set_pkey_meths(e, Everest_pkey_meths)
  )
    return 0;

  return 1;
}

IMPLEMENT_DYNAMIC_CHECK_FN();
IMPLEMENT_DYNAMIC_BIND_FN(bind_helper);
