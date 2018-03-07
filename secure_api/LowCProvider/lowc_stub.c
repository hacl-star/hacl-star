/* This file implements the OCaml/C interface for the functions exposed in
 * LowCProvider.ml. It relies on insider knowledge and leverages the OCaml
 * representation of FStar.Byte.{bytes,lbytes} specified in
 * ulib/ml/FStar_Bytes.ml. Furthermore, this file makes assumptions about the
 * way [secure_api] was extracted; specifically, it assumes run-time dynamic
 * switching between AES implementations and a specific definition of the id
 * type. */
#include <assert.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <stdbool.h>
#include <string.h>
#include <sys/stat.h>
#include <sys/types.h>
#include <time.h>
#include <inttypes.h>

#include <caml/alloc.h>
#include <caml/callback.h>
#include <caml/custom.h>
#include <caml/fail.h>
#include <caml/memory.h>
#include <caml/mlvalues.h>

#include "FStar_UInt128.h"
#include "Crypto_AEAD_Main_Crypto_Indexing.h"
#include "Crypto_Symmetric_Bytes.h"
#include "Crypto_HKDF_Crypto_HMAC.h"
#include "Curve25519.h"
#include "FStar.h"

typedef Crypto_AEAD_Invariant_aead_state AEAD_ST;
typedef Crypto_Indexing_id ID;

typedef struct {
  AEAD_ST *st;
  ID id;
} ST;

#define ST_val(v) (*((ST **)Data_custom_val(v)))

static value Val_some(value mlvalue) {
  CAMLparam1(mlvalue);
  CAMLlocal1(aout);

  aout = caml_alloc(1, 0);
  Store_field(aout, 0, mlvalue);

  CAMLreturn(aout);
}

#define Val_none Val_int(0)

static void ocaml_ST_finalize(value st) {
  ST *s = ST_val(st);

  if (s != NULL) {
    AEAD_ST *st = s->st;
    if (st != NULL) {
      free(st);
    }
    free(s);
  }
}

static struct custom_operations st_ops = {
    .identifier = "ocaml_st",
    .finalize = ocaml_ST_finalize,
    .compare = custom_compare_default,
    .hash = custom_hash_default,
    .serialize = custom_serialize_default,
    .deserialize = custom_deserialize_default,
};

CAMLprim value ocaml_AEAD_create(value alg, value impl, value key) {
  CAMLparam2(alg, key);
  Crypto_Indexing_aeadAlg calg;
  Crypto_Indexing_aesImpl aesimpl;

  switch (Int_val(alg)) {
  case 0:
    calg = Crypto_Indexing_AES_128_GCM;
    break;
  case 1:
    calg = Crypto_Indexing_AES_256_GCM;
    break;
  case 2:
    calg = Crypto_Indexing_CHACHA20_POLY1305;
    break;
  default:
    caml_failwith("LowCProvider: unsupported AEAD alg");
  }

  switch (Int_val(impl)) {
  case 0:
    aesimpl = Crypto_Indexing_HaclAES;
    break;
  case 1:
    aesimpl = Crypto_Indexing_ValeAES;
    break;
  default:
    caml_failwith("LowCProvider: invalid AES implementation");
  }

#ifdef KRML_NOSTRUCT_PASSING
  Crypto_Indexing_id id;
  Crypto_Indexing_testId(calg, &id);
#else
  Crypto_Indexing_id id = Crypto_Indexing_testId(calg);
#endif
  id.aesImpl = aesimpl;

  AEAD_ST *st = malloc(sizeof(AEAD_ST));
#ifdef KRML_NOSTRUCT_PASSING
  Crypto_AEAD_Main_coerce(&id, (uint8_t *)String_val(key), st);
#else
  *st = Crypto_AEAD_Main_coerce(id, (uint8_t *)String_val(key));
#endif
  ST *s = malloc(sizeof(ST));
  s->st = st;
  s->id = id;

  CAMLlocal1(mlret);
  mlret = caml_alloc_custom(&st_ops, sizeof(ST *), 0, 1);
  ST_val(mlret) = s;
  CAMLreturn(mlret);
}

CAMLprim value ocaml_AEAD_encrypt(value state, value iv, value ad,
                                  value plain) {
  CAMLparam4(state, iv, ad, plain);

  ST *st = ST_val(state);
  AEAD_ST *ast = st->st;
  ID id = st->id;
  uint8_t *civ = (uint8_t *)String_val(iv);
#ifdef KRML_NOSTRUCT_PASSING
  FStar_UInt128_uint128 n;
  Crypto_Symmetric_Bytes_load_uint128(
      (uint32_t)caml_string_length(iv), civ, &n);
#else
  FStar_UInt128_uint128 n = Crypto_Symmetric_Bytes_load_uint128(
      (uint32_t)caml_string_length(iv), civ);
#endif
  uint8_t *cad = (uint8_t *)String_val(ad);
  uint32_t adlen = caml_string_length(ad);
  uint8_t *cplain = (uint8_t *)String_val(plain);
  uint32_t plainlen = caml_string_length(plain);

  CAMLlocal1(cipher);
  cipher = caml_alloc_string(plainlen + Crypto_AEAD_Main_taglen);
  uint8_t *ccipher = (uint8_t *)String_val(cipher);
#ifdef KRML_NOSTRUCT_PASSING
  Crypto_AEAD_Main_encrypt(&id, ast, &n, adlen, cad, plainlen, cplain,
                              ccipher);
#else
  Crypto_AEAD_Main_encrypt(id, *ast, n, adlen, cad, plainlen, cplain,
                              ccipher);
#endif
  CAMLreturn(cipher);
}

CAMLprim value ocaml_AEAD_decrypt(value state, value iv, value ad,
                                  value cipher) {
  CAMLparam4(state, iv, ad, cipher);

  ST *st = ST_val(state);
  AEAD_ST *ast = st->st;
  ID id = st->id;
  uint8_t *civ = (uint8_t *)String_val(iv);
  FStar_UInt128_uint128 n;
#ifdef KRML_NOSTRUCT_PASSING
  Crypto_Symmetric_Bytes_load_uint128((uint32_t)caml_string_length(iv), civ, &n);
#else
  n = Crypto_Symmetric_Bytes_load_uint128((uint32_t)caml_string_length(iv), civ);
#endif
  uint8_t *cad = (uint8_t *)String_val(ad);
  uint32_t adlen = caml_string_length(ad);
  uint8_t *ccipher = (uint8_t *)String_val(cipher);
  uint32_t cipherlen = caml_string_length(cipher);
  if (cipherlen < Crypto_AEAD_Main_taglen)
    CAMLreturn(Val_none);

  CAMLlocal1(plain);
  uint32_t plainlen = cipherlen - Crypto_AEAD_Main_taglen;
  plain = caml_alloc_string(plainlen);
  uint8_t *cplain = (uint8_t *)String_val(plain);

#ifdef KRML_NOSTRUCT_PASSING
  int ret = Crypto_AEAD_Main_decrypt(&id, ast, &n, adlen, cad, plainlen, cplain,
                                  ccipher);
#else
  int ret = Crypto_AEAD_Main_decrypt(id, *ast, n, adlen, cad, plainlen, cplain,
                                  ccipher);
#endif

  if (ret) {
    CAMLreturn(Val_some(plain));
  }

  CAMLreturn(Val_none);
}

CAMLprim value ocaml_crypto_scalarmult(value secret, value base) {
  CAMLparam2(secret, base);
  CAMLlocal1(out);
  out = caml_alloc_string(32);
  uint8_t *out_p = (uint8_t *) String_val(out);
  uint8_t *secret_p = (uint8_t *) String_val(secret);
  uint8_t *base_p = (uint8_t *) String_val(base);
  Curve25519_crypto_scalarmult(out_p, secret_p, base_p);
  CAMLreturn(out);
}

static inline Crypto_HMAC_alg alg_of_int(int i) {
  switch (i) {
    case 0:
      return Crypto_HMAC_SHA256;
    case 1:
      return Crypto_HMAC_SHA384;
    case 2:
      return Crypto_HMAC_SHA512;
  }
  return 0;
}

static inline size_t hash_size(Crypto_HMAC_alg h) {
  switch (h) {
    case Crypto_HMAC_SHA256:
      return 32;
    case Crypto_HMAC_SHA384:
      return 48;
    case Crypto_HMAC_SHA512:
      return 64;
  }
  return 32;
}

CAMLprim value ocaml_crypto_hash(value alg, value msg) {
  CAMLparam2(alg, msg);
  CAMLlocal1(out);

  Crypto_HMAC_alg h = alg_of_int(Int_val(alg));
  out = caml_alloc_string(hash_size(h));

  uint8_t *out_p = (uint8_t *) String_val(out);
  uint8_t *msg_p = (uint8_t *) String_val(msg);
  Crypto_HMAC_agile_hash(h, out_p, msg_p, caml_string_length(msg));
  CAMLreturn(out);
}

CAMLprim value ocaml_crypto_hmac(value alg, value key, value msg) {
  CAMLparam3(alg, key, msg);
  CAMLlocal1(out);

  Crypto_HMAC_alg h = alg_of_int(Int_val(alg));
  out = caml_alloc_string(hash_size(h));

  uint8_t *out_p = (uint8_t *) String_val(out);
  uint8_t *key_p = (uint8_t *) String_val(key);
  size_t key_l = caml_string_length(key);
  uint8_t *msg_p = (uint8_t *) String_val(msg);
  size_t msg_l = caml_string_length(msg);

  Crypto_HMAC_hmac(h, out_p, key_p, key_l, msg_p, msg_l);
  CAMLreturn(out);
}
