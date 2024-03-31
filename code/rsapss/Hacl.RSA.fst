module Hacl.RSA

open FStar.Mul
open Lib.IntTypes

module S = Spec.RSAPSS
module Hash = Spec.Agile.Hash

module RI = Hacl.Impl.RSAPSS
module RK = Hacl.Impl.RSA.Keys
module RR = Hacl.Impl.RSA

module BN = Hacl.Bignum
module BM = Hacl.Bignum.Montgomery
module BE = Hacl.Bignum.Exponentiation
module BD = Hacl.Bignum.Definitions

#reset-options "--z3rlimit 50 --fuel 0 --ifuel 0"

inline_for_extraction noextract
let t_limbs = U64

inline_for_extraction noextract
let modBits_t = RR.modBits_t t_limbs

inline_for_extraction noextract
let ke (modBits:modBits_t) =
  BE.mk_runtime_exp #t_limbs (BD.blocks modBits (size (bits t_limbs)))


private
[@CInline]
let load_pkey (modBits:modBits_t) : RK.rsa_load_pkey_st t_limbs (ke modBits) modBits =
  RK.rsa_load_pkey (ke modBits) modBits RK.mk_runtime_rsa_checks

private
[@CInline]
let load_skey (modBits:modBits_t) : RK.rsa_load_skey_st t_limbs (ke modBits) modBits =
  RK.rsa_load_skey (ke modBits) modBits RK.mk_runtime_rsa_checks (load_pkey modBits)

[@@ Comment "Decrypt a message `cipher` and write the plaintext to `plain`.

@param modBits Count of bits in the modulus (`n`).
@param eBits Count of bits in `e` value.
@param dBits Count of bits in `d` value.
@param skey Pointer to secret key created by `Hacl_RSA_new_rsa_load_skey`.
@param cipher Pointer to `ceil(modBits - 1 / 8)` bytes where the ciphertext is read from.
@param plain Pointer to `ceil(modBits / 8)` bytes where the plaintext is written to.

@return Returns true if and only if decryption was successful."]
val rsa_dec:
  modBits:modBits_t ->
  RR.rsa_dec_st t_limbs (ke modBits) modBits
let rsa_dec modBits eBits dBits skey cipher plain =
  RR.rsa_dec (ke modBits) modBits eBits dBits skey cipher plain


[@@ Comment "Encrypt a message `plain` and write the ciphertext to `cipher`.

@param modBits Count of bits in the modulus (`n`).
@param eBits Count of bits in `e` value.
@param dBits Count of bits in `d` value.
@param skey Pointer to secret key created by `Hacl_RSA_new_rsa_load_skey`.
@param plain Pointer to `ceil(modBits / 8)` bytes where the plaintext is written to.
@param cipher Pointer to `ceil(modBits - 1 / 8)` bytes where the ciphertext is read from.

@return Returns true if and only if decryption was successful."]
val rsa_enc:
  modBits:modBits_t ->
  RR.rsa_enc_st t_limbs (ke modBits) modBits
let rsa_enc modBits eBits pkey plain cipher =
  RR.rsa_enc #t_limbs (ke modBits) modBits eBits pkey plain cipher

[@@ Comment "Load a public key from key parts.

@param modBits Count of bits in modulus (`n`).
@param eBits Count of bits in `e` value.
@param nb Pointer to `ceil(modBits / 8)` bytes where the modulus (`n`), in big-endian byte order, is read from.
@param eb Pointer to `ceil(modBits / 8)` bytes where the `e` value, in big-endian byte order, is read from.

@return Returns an allocated public key upon success, otherwise, `NULL` if key part arguments are invalid or memory allocation fails. Note: caller must take care to `free()` the created key."]
val new_rsa_load_pkey: modBits:modBits_t -> RK.new_rsa_load_pkey_st t_limbs (ke modBits) modBits
let new_rsa_load_pkey modBits r eBits nb eb =
  RK.new_rsa_load_pkey (ke modBits) modBits RK.mk_runtime_rsa_checks r eBits nb eb


[@@ Comment "Load a secret key from key parts.

@param modBits Count of bits in modulus (`n`).
@param eBits Count of bits in `e` value.
@param dBits Count of bits in `d` value.
@param nb Pointer to `ceil(modBits / 8)` bytes where the modulus (`n`), in big-endian byte order, is read from.
@param eb Pointer to `ceil(modBits / 8)` bytes where the `e` value, in big-endian byte order, is read from.
@param db Pointer to `ceil(modBits / 8)` bytes where the `d` value, in big-endian byte order, is read from.

@return Returns an allocated secret key upon success, otherwise, `NULL` if key part arguments are invalid or memory allocation fails. Note: caller must take care to `free()` the created key."]
val new_rsa_load_skey: modBits:modBits_t -> RK.new_rsa_load_skey_st t_limbs (ke modBits) modBits
let new_rsa_load_skey modBits r eBits dBits nb eb db =
  RK.new_rsa_load_skey (ke modBits) modBits RK.mk_runtime_rsa_checks r eBits dBits nb eb db

