module Hacl.RSAPSS

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


[@@ Comment "Sign a message `msg` and write the signature to `sgnt`.

@param a Hash algorithm to use. Allowed values for `a` are ...
  - Spec_Hash_Definitions_SHA2_256,
  - Spec_Hash_Definitions_SHA2_384, and
  - Spec_Hash_Definitions_SHA2_512.
@param modBits Count of bits in the modulus (`n`).
@param eBits Count of bits in `e` value.
@param dBits Count of bits in `d` value.
@param skey Pointer to secret key created by `Hacl_RSAPSS_new_rsapss_load_skey`.
@param saltLen Length of salt.
@param salt Pointer to `saltLen` bytes where the salt is read from.
@param msgLen Length of message.
@param msg Pointer to `msgLen` bytes where the message is read from.
@param sgnt Pointer to `ceil(modBits / 8)` bytes where the signature is written to.

@return Returns true if and only if signing was successful."]
val rsapss_sign:
    a:Hash.hash_alg{S.hash_is_supported a}
  -> modBits:modBits_t ->
  RI.rsapss_sign_st t_limbs (ke modBits) a modBits

let rsapss_sign a modBits eBits dBits skey saltLen salt msgLen msg sgnt =
  RI.rsapss_sign (ke modBits) a modBits (Hacl.RSA.rsa_dec modBits) eBits dBits skey saltLen salt msgLen msg sgnt

[@@ Comment "Verify the signature `sgnt` of a message `msg`.

@param a Hash algorithm to use. Allowed values for `a` are ...
  - Spec_Hash_Definitions_SHA2_256,
  - Spec_Hash_Definitions_SHA2_384, and
  - Spec_Hash_Definitions_SHA2_512.
@param modBits Count of bits in the modulus (`n`).
@param eBits Count of bits in `e` value.
@param pkey Pointer to public key created by `Hacl_RSAPSS_new_rsapss_load_pkey`.
@param saltLen Length of salt.
@param sgntLen Length of signature.
@param sgnt Pointer to `sgntLen` bytes where the signature is read from.
@param msgLen Length of message.
@param msg Pointer to `msgLen` bytes where the message is read from.

@return Returns true if and only if the signature is valid."]
val rsapss_verify:
    a:Hash.hash_alg{S.hash_is_supported a}
  -> modBits:modBits_t ->
  RI.rsapss_verify_st t_limbs (ke modBits) a modBits

let rsapss_verify a modBits eBits pkey saltLen sgntLen sgnt msgLen msg =
  RI.rsapss_verify (ke modBits) a modBits (Hacl.RSA.rsa_enc modBits) eBits pkey saltLen sgntLen sgnt msgLen msg


[@@ Comment "Sign a message `msg` and write the signature to `sgnt`.

@param a Hash algorithm to use. Allowed values for `a` are ...
  - Spec_Hash_Definitions_SHA2_256,
  - Spec_Hash_Definitions_SHA2_384, and
  - Spec_Hash_Definitions_SHA2_512.
@param modBits Count of bits in the modulus (`n`).
@param eBits Count of bits in `e` value.
@param dBits Count of bits in `d` value.
@param nb Pointer to `ceil(modBits / 8)` bytes where the modulus (`n`), in big-endian byte order, is read from.
@param eb Pointer to `ceil(modBits / 8)` bytes where the `e` value, in big-endian byte order, is read from.
@param db Pointer to `ceil(modBits / 8)` bytes where the `d` value, in big-endian byte order, is read from.
@param saltLen Length of salt.
@param salt Pointer to `saltLen` bytes where the salt is read from.
@param msgLen Length of message.
@param msg Pointer to `msgLen` bytes where the message is read from.
@param sgnt Pointer to `ceil(modBits / 8)` bytes where the signature is written to.

@return Returns true if and only if signing was successful."]
val rsapss_skey_sign:
    a:Hash.hash_alg{S.hash_is_supported a}
  -> modBits:modBits_t ->
  RI.rsapss_skey_sign_st t_limbs (ke modBits) a modBits

let rsapss_skey_sign a modBits eBits dBits nb eb db saltLen salt msgLen msg sgnt =
  RI.rsapss_skey_sign (ke modBits) a modBits
    (load_skey modBits) (rsapss_sign a modBits) eBits dBits nb eb db saltLen salt msgLen msg sgnt


[@@ Comment "Verify the signature `sgnt` of a message `msg`.

@param a Hash algorithm to use. Allowed values for `a` are ...
  - Spec_Hash_Definitions_SHA2_256,
  - Spec_Hash_Definitions_SHA2_384, and
  - Spec_Hash_Definitions_SHA2_512.
@param modBits Count of bits in the modulus (`n`).
@param eBits Count of bits in `e` value.
@param nb Pointer to `ceil(modBits / 8)` bytes where the modulus (`n`), in big-endian byte order, is read from.
@param eb Pointer to `ceil(modBits / 8)` bytes where the `e` value, in big-endian byte order, is read from.
@param saltLen Length of salt.
@param sgntLen Length of signature.
@param sgnt Pointer to `sgntLen` bytes where the signature is read from.
@param msgLen Length of message.
@param msg Pointer to `msgLen` bytes where the message is read from.

@return Returns true if and only if the signature is valid."]
val rsapss_pkey_verify:
    a:Hash.hash_alg{S.hash_is_supported a}
  -> modBits:modBits_t ->
  RI.rsapss_pkey_verify_st t_limbs (ke modBits) a modBits

let rsapss_pkey_verify a modBits eBits nb eb saltLen sgntLen sgnt msgLen msg =
  RI.rsapss_pkey_verify (ke modBits) a modBits
    (load_pkey modBits) (rsapss_verify a modBits) eBits nb eb saltLen sgntLen sgnt msgLen msg


[@@ Comment "  The mask generation function defined in the Public Key Cryptography Standard #1
  (https://www.ietf.org/rfc/rfc2437.txt Section 10.2.1) "]
val mgf_hash: a:Hash.hash_alg{S.hash_is_supported a} -> Hacl.Impl.RSAPSS.MGF.mgf_hash_st a

let mgf_hash a len mgfseed maskLen res = Hacl.Impl.RSAPSS.MGF.mgf_hash a len mgfseed maskLen res
