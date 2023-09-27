module Hacl.P256

open FStar.Mul
open FStar.HyperStack.All
open FStar.HyperStack
module ST = FStar.HyperStack.ST

open Lib.IntTypes
open Lib.Buffer

open Spec.Hash.Definitions

module S = Spec.P256
module BSeq = Lib.ByteSequence

#set-options "--z3rlimit 30 --fuel 0 --ifuel 0"

// TODO?: change API for `ecdsa_verify`, namely, take `signature` as an argument

inline_for_extraction noextract
let ecdsa_sign_p256_st (alg:S.hash_alg_ecdsa) =
    signature:lbuffer uint8 64ul
  -> msg_len:size_t{v msg_len >= S.min_input_length alg}
  -> msg:lbuffer uint8 msg_len
  -> private_key:lbuffer uint8 32ul
  -> nonce:lbuffer uint8 32ul ->
  Stack bool
  (requires fun h ->
    live h signature /\ live h msg /\ live h private_key /\ live h nonce /\
    disjoint signature msg /\ disjoint signature private_key /\ disjoint signature nonce)
  (ensures fun h0 flag h1 -> modifies (loc signature) h0 h1 /\
    (let sgnt = S.ecdsa_signature_agile alg (v msg_len)
      (as_seq h0 msg) (as_seq h0 private_key) (as_seq h0 nonce) in
     (flag <==> Some? sgnt) /\ (flag ==> (as_seq h1 signature == Some?.v sgnt))))


inline_for_extraction noextract
let ecdsa_verify_p256_st (alg:S.hash_alg_ecdsa) =
    msg_len:size_t{v msg_len >= S.min_input_length alg}
  -> msg:lbuffer uint8 msg_len
  -> public_key:lbuffer uint8 64ul
  -> signature_r:lbuffer uint8 32ul
  -> signature_s:lbuffer uint8 32ul ->
  Stack bool
  (requires fun h ->
    live h public_key /\ live h signature_r /\ live h signature_s /\ live h msg)
  (ensures fun h0 res h1 -> modifies0 h0 h1 /\
    res == S.ecdsa_verification_agile alg (v msg_len) (as_seq h0 msg)
      (as_seq h0 public_key) (as_seq h0 signature_r) (as_seq h0 signature_s))


[@@ CPrologue "
/*******************************************************************************

 Verified C library for ECDSA and ECDH functions over the P-256 NIST curve.

 This module implements signing and verification, key validation, conversions
 between various point representations, and ECDH key agreement.

*******************************************************************************/

/*****************/
/* ECDSA signing */
/*****************/

/*
  As per the standard, a hash function *shall* be used. Therefore, we recommend
  using one of the three combined hash-and-sign variants.
*/";

Comment "Create an ECDSA signature using SHA2-256.

  The function returns `true` for successful creation of an ECDSA signature and `false` otherwise.

  The outparam `signature` (R || S) points to 64 bytes of valid memory, i.e., uint8_t[64].
  The argument `msg` points to `msg_len` bytes of valid memory, i.e., uint8_t[msg_len].
  The arguments `private_key` and `nonce` point to 32 bytes of valid memory, i.e., uint8_t[32].

  The function also checks whether `private_key` and `nonce` are valid:
    • 0 < `private_key` < the order of the curve
    • 0 < `nonce` < the order of the curve"]
val ecdsa_sign_p256_sha2: ecdsa_sign_p256_st (S.Hash SHA2_256)


[@@ Comment "Create an ECDSA signature using SHA2-384.

  The function returns `true` for successful creation of an ECDSA signature and `false` otherwise.

  The outparam `signature` (R || S) points to 64 bytes of valid memory, i.e., uint8_t[64].
  The argument `msg` points to `msg_len` bytes of valid memory, i.e., uint8_t[msg_len].
  The arguments `private_key` and `nonce` point to 32 bytes of valid memory, i.e., uint8_t[32].

  The function also checks whether `private_key` and `nonce` are valid:
    • 0 < `private_key` < the order of the curve
    • 0 < `nonce` < the order of the curve"]
val ecdsa_sign_p256_sha384: ecdsa_sign_p256_st (S.Hash SHA2_384)


[@@ Comment "Create an ECDSA signature using SHA2-512.

  The function returns `true` for successful creation of an ECDSA signature and `false` otherwise.

  The outparam `signature` (R || S) points to 64 bytes of valid memory, i.e., uint8_t[64].
  The argument `msg` points to `msg_len` bytes of valid memory, i.e., uint8_t[msg_len].
  The arguments `private_key` and `nonce` point to 32 bytes of valid memory, i.e., uint8_t[32].

  The function also checks whether `private_key` and `nonce` are valid:
    • 0 < `private_key` < the order of the curve
    • 0 < `nonce` < the order of the curve"]
val ecdsa_sign_p256_sha512: ecdsa_sign_p256_st (S.Hash SHA2_512)


[@@ Comment "Create an ECDSA signature WITHOUT hashing first.

  This function is intended to receive a hash of the input.
  For convenience, we recommend using one of the hash-and-sign combined functions above.

  The argument `msg` MUST be at least 32 bytes (i.e. `msg_len >= 32`).

  NOTE: The equivalent functions in OpenSSL and Fiat-Crypto both accept inputs
  smaller than 32 bytes. These libraries left-pad the input with enough zeroes to
  reach the minimum 32 byte size. Clients who need behavior identical to OpenSSL
  need to perform the left-padding themselves.

  The function returns `true` for successful creation of an ECDSA signature and `false` otherwise.

  The outparam `signature` (R || S) points to 64 bytes of valid memory, i.e., uint8_t[64].
  The argument `msg` points to `msg_len` bytes of valid memory, i.e., uint8_t[msg_len].
  The arguments `private_key` and `nonce` point to 32 bytes of valid memory, i.e., uint8_t[32].

  The function also checks whether `private_key` and `nonce` are valid values:
    • 0 < `private_key` < the order of the curve
    • 0 < `nonce` < the order of the curve"]
val ecdsa_sign_p256_without_hash: ecdsa_sign_p256_st (S.NoHash)


[@@ CPrologue "
/**********************/
/* ECDSA verification */
/**********************/";

Comment "Verify an ECDSA signature using SHA2-256.

  The function returns `true` if the signature is valid and `false` otherwise.

  The argument `msg` points to `msg_len` bytes of valid memory, i.e., uint8_t[msg_len].
  The argument `public_key` (x || y) points to 64 bytes of valid memory, i.e., uint8_t[64].
  The arguments `signature_r` and `signature_s` point to 32 bytes of valid memory, i.e., uint8_t[32].

  The function also checks whether `public_key` is valid"]
val ecdsa_verif_p256_sha2: ecdsa_verify_p256_st (S.Hash SHA2_256)


[@@ Comment "Verify an ECDSA signature using SHA2-384.

  The function returns `true` if the signature is valid and `false` otherwise.

  The argument `msg` points to `msg_len` bytes of valid memory, i.e., uint8_t[msg_len].
  The argument `public_key` (x || y) points to 64 bytes of valid memory, i.e., uint8_t[64].
  The arguments `signature_r` and `signature_s` point to 32 bytes of valid memory, i.e., uint8_t[32].

  The function also checks whether `public_key` is valid"]
val ecdsa_verif_p256_sha384: ecdsa_verify_p256_st (S.Hash SHA2_384)


[@@ Comment "Verify an ECDSA signature using SHA2-512.

  The function returns `true` if the signature is valid and `false` otherwise.

  The argument `msg` points to `msg_len` bytes of valid memory, i.e., uint8_t[msg_len].
  The argument `public_key` (x || y) points to 64 bytes of valid memory, i.e., uint8_t[64].
  The arguments `signature_r` and `signature_s` point to 32 bytes of valid memory, i.e., uint8_t[32].

  The function also checks whether `public_key` is valid"]
val ecdsa_verif_p256_sha512: ecdsa_verify_p256_st (S.Hash SHA2_512)


[@@ Comment "Verify an ECDSA signature WITHOUT hashing first.

  This function is intended to receive a hash of the input.
  For convenience, we recommend using one of the hash-and-verify combined functions above.

  The argument `msg` MUST be at least 32 bytes (i.e. `msg_len >= 32`).

  The function returns `true` if the signature is valid and `false` otherwise.

  The argument `msg` points to `msg_len` bytes of valid memory, i.e., uint8_t[msg_len].
  The argument `public_key` (x || y) points to 64 bytes of valid memory, i.e., uint8_t[64].
  The arguments `signature_r` and `signature_s` point to 32 bytes of valid memory, i.e., uint8_t[32].

  The function also checks whether `public_key` is valid"]
val ecdsa_verif_without_hash: ecdsa_verify_p256_st S.NoHash


[@@ CPrologue "
/******************/
/* Key validation */
/******************/";

Comment "Public key validation.

  The function returns `true` if a public key is valid and `false` otherwise.

  The argument `public_key` points to 64 bytes of valid memory, i.e., uint8_t[64].

  The public key (x || y) is valid (with respect to SP 800-56A):
    • the public key is not the “point at infinity”, represented as O.
    • the affine x and y coordinates of the point represented by the public key are
      in the range [0, p – 1] where p is the prime defining the finite field.
    • y^2 = x^3 + ax + b where a and b are the coefficients of the curve equation.
  The last extract is taken from: https://neilmadden.blog/2017/05/17/so-how-do-you-validate-nist-ecdh-public-keys/"]
val validate_public_key: public_key:lbuffer uint8 64ul -> Stack bool
  (requires fun h -> live h public_key)
  (ensures  fun h0 r h1 -> modifies0 h0 h1 /\
    r == S.validate_public_key (as_seq h0 public_key))


[@@ Comment "Private key validation.

  The function returns `true` if a private key is valid and `false` otherwise.

  The argument `private_key` points to 32 bytes of valid memory, i.e., uint8_t[32].

  The private key is valid:
    • 0 < `private_key` < the order of the curve"]
val validate_private_key: private_key:lbuffer uint8 32ul -> Stack bool
  (requires fun h -> live h private_key)
  (ensures  fun h0 r h1 -> modifies0 h0 h1 /\
    (let s = BSeq.nat_from_bytes_be (as_seq h0 private_key) in
    r <==> (0 < s && s < S.order)))


[@@ CPrologue
"/*******************************************************************************
  Parsing and Serializing public keys.

  A public key is a point (x, y) on the P-256 NIST curve.

  The point can be represented in the following three ways.
    • raw          = [ x || y ], 64 bytes
    • uncompressed = [ 0x04 || x || y ], 65 bytes
    • compressed   = [ (0x02 for even `y` and 0x03 for odd `y`) || x ], 33 bytes

*******************************************************************************/\n";

 Comment "Convert a public key from uncompressed to its raw form.

  The function returns `true` for successful conversion of a public key and `false` otherwise.

  The outparam `pk_raw` points to 64 bytes of valid memory, i.e., uint8_t[64].
  The argument `pk` points to 65 bytes of valid memory, i.e., uint8_t[65].

  The function DOESN'T check whether (x, y) is a valid point."]
val uncompressed_to_raw: pk:lbuffer uint8 65ul -> pk_raw:lbuffer uint8 64ul -> Stack bool
  (requires fun h -> live h pk /\ live h pk_raw /\ disjoint pk pk_raw)
  (ensures fun h0 b h1 -> modifies (loc pk_raw) h0 h1 /\
    (b <==> Some? (S.pk_uncompressed_to_raw (as_seq h0 pk))) /\
    (b ==> (as_seq h1 pk_raw == Some?.v (S.pk_uncompressed_to_raw (as_seq h0 pk)))))


[@@ Comment "Convert a public key from compressed to its raw form.

  The function returns `true` for successful conversion of a public key and `false` otherwise.

  The outparam `pk_raw` points to 64 bytes of valid memory, i.e., uint8_t[64].
  The argument `pk` points to 33 bytes of valid memory, i.e., uint8_t[33].

  The function also checks whether (x, y) is a valid point."]
val compressed_to_raw: pk:lbuffer uint8 33ul -> pk_raw:lbuffer uint8 64ul -> Stack bool
  (requires fun h -> live h pk /\ live h pk_raw /\ disjoint pk pk_raw)
  (ensures  fun h0 b h1 -> modifies (loc pk_raw) h0 h1 /\
    (b <==> Some? (S.pk_compressed_to_raw (as_seq h0 pk))) /\
    (b ==> (as_seq h1 pk_raw == Some?.v (S.pk_compressed_to_raw (as_seq h0 pk)))))


[@@ Comment "Convert a public key from raw to its uncompressed form.

  The outparam `pk` points to 65 bytes of valid memory, i.e., uint8_t[65].
  The argument `pk_raw` points to 64 bytes of valid memory, i.e., uint8_t[64].

  The function DOESN'T check whether (x, y) is a valid point."]
val raw_to_uncompressed: pk_raw:lbuffer uint8 64ul -> pk:lbuffer uint8 65ul -> Stack unit
  (requires fun h -> live h pk /\ live h pk_raw /\ disjoint pk pk_raw)
  (ensures fun h0 _ h1 -> modifies (loc pk) h0 h1 /\
    as_seq h1 pk == S.pk_uncompressed_from_raw (as_seq h0 pk_raw))


[@@ Comment "Convert a public key from raw to its compressed form.

  The outparam `pk` points to 33 bytes of valid memory, i.e., uint8_t[33].
  The argument `pk_raw` points to 64 bytes of valid memory, i.e., uint8_t[64].

  The function DOESN'T check whether (x, y) is a valid point."]
val raw_to_compressed: pk_raw:lbuffer uint8 64ul -> pk:lbuffer uint8 33ul -> Stack unit
  (requires fun h -> live h pk /\ live h pk_raw /\ disjoint pk pk_raw)
  (ensures  fun h0 _ h1 -> modifies (loc pk) h0 h1 /\
    as_seq h1 pk == S.pk_compressed_from_raw (as_seq h0 pk_raw))


[@@ CPrologue "
/******************/
/* ECDH agreement */
/******************/";

Comment "Compute the public key from the private key.

  The function returns `true` if a private key is valid and `false` otherwise.

  The outparam `public_key`  points to 64 bytes of valid memory, i.e., uint8_t[64].
  The argument `private_key` points to 32 bytes of valid memory, i.e., uint8_t[32].

  The private key is valid:
    • 0 < `private_key` < the order of the curve."]
val dh_initiator:
    public_key:lbuffer uint8 64ul
  -> private_key:lbuffer uint8 32ul ->
  Stack bool
  (requires fun h ->
    live h public_key /\ live h private_key /\ disjoint public_key private_key)
  (ensures fun h0 r h1 -> modifies (loc public_key) h0 h1 /\
    (let pk = S.secret_to_public (as_seq h0 private_key) in
    (r <==> Some? pk) /\ (r ==> (as_seq h1 public_key == Some?.v pk))))


[@@ Comment "Execute the diffie-hellmann key exchange.

  The function returns `true` for successful creation of an ECDH shared secret and
  `false` otherwise.

  The outparam `shared_secret` points to 64 bytes of valid memory, i.e., uint8_t[64].
  The argument `their_pubkey` points to 64 bytes of valid memory, i.e., uint8_t[64].
  The argument `private_key` points to 32 bytes of valid memory, i.e., uint8_t[32].

  The function also checks whether `private_key` and `their_pubkey` are valid."]
val dh_responder:
    shared_secret:lbuffer uint8 64ul
  -> their_pubkey:lbuffer uint8 64ul
  -> private_key:lbuffer uint8 32ul ->
  Stack bool
  (requires fun h ->
    live h shared_secret /\ live h their_pubkey /\ live h private_key /\
    disjoint shared_secret their_pubkey /\ disjoint shared_secret private_key)
  (ensures fun h0 r h1 -> modifies (loc shared_secret) h0 h1 /\
    (let ss = S.ecdh (as_seq h0 their_pubkey) (as_seq h0 private_key) in
    (r <==> Some? ss) /\ (r ==> (as_seq h1 shared_secret == Some?.v ss))))
