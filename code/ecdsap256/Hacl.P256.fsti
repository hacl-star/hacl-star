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

// TODO: clean up the documentation

inline_for_extraction noextract
let ecdsa_sign_p256_st (a:S.hash_alg_ecdsa) =
    signature:lbuffer uint8 64ul
  -> msg_len:size_t{v msg_len >= S.min_input_length a}
  -> msg:lbuffer uint8 msg_len
  -> private_key:lbuffer uint8 32ul
  -> nonce:lbuffer uint8 32ul ->
  Stack bool
  (requires fun h ->
    live h signature /\ live h msg /\ live h private_key /\ live h nonce /\
    disjoint signature msg /\ disjoint signature private_key /\ disjoint signature nonce /\

    0 < BSeq.nat_from_bytes_be (as_seq h private_key) /\
    BSeq.nat_from_bytes_be (as_seq h private_key) < S.order /\
    0 < BSeq.nat_from_bytes_be (as_seq h nonce) /\
    BSeq.nat_from_bytes_be (as_seq h nonce) < S.order)
  (ensures fun h0 flag h1 -> modifies (loc signature) h0 h1 /\
    (let sgnt = S.ecdsa_signature_agile a (v msg_len)
      (as_seq h0 msg) (as_seq h0 private_key) (as_seq h0 nonce) in
     (flag <==> Some? sgnt) /\ (flag ==> (as_seq h1 signature == Some?.v sgnt))))


inline_for_extraction noextract
let ecdsa_verify_p256_st (a:S.hash_alg_ecdsa) =
    msg_len:size_t{v msg_len >= S.min_input_length a}
  -> msg:lbuffer uint8 msg_len
  -> public_key:lbuffer uint8 64ul
  -> signature_r:lbuffer uint8 32ul
  -> signature_s:lbuffer uint8 32ul ->
  Stack bool
  (requires fun h ->
    live h public_key /\ live h signature_r /\ live h signature_s /\ live h msg)
  (ensures fun h0 result h1 -> modifies0 h0 h1 /\
    result == S.ecdsa_verification_agile a (as_seq h0 public_key)
      (as_seq h0 signature_r) (as_seq h0 signature_s) (v msg_len) (as_seq h0 msg))


[@@ CPrologue "
/*******************************************************************************

ECDSA and ECDH functions over the P-256 NIST curve.

This module implements signing and verification, key validation, conversions
between various point representations, and ECDH key agreement.

*******************************************************************************/

/**************/
/* Signatures */
/**************/

/*
  Per the standard, a hash function *shall* be used. Therefore, we recommend
  using one of the three combined hash-and-sign variants.
*/";

Comment "Hash the message with SHA2-256, then sign the resulting digest with the P256 signature function.

  Input:
  • signature: uint8 [64]
  • msg: uint8 [msg_len]
  • private_key: uint8 [32]
  • nonce: uint8 [32]
  Output: bool, where True stands for the correct signature generation.
  False value means that an error has occurred.

  The private key and the nonce are expected to be more than 0 and less than the curve order."]
val ecdsa_sign_p256_sha2: ecdsa_sign_p256_st (S.Hash SHA2_256)


[@@ Comment "Hash the message with SHA2-384, then sign the resulting digest with the P256 signature function.

  Input:
  • signature: uint8 [64]
  • msg: uint8 [msg_len]
  • private_key: uint8 [32]
  • nonce: uint8 [32]
  Output: bool, where True stands for the correct signature generation.
  False value means that an error has occurred.

  The private key and the nonce are expected to be more than 0 and less than the curve order."]
val ecdsa_sign_p256_sha384: ecdsa_sign_p256_st (S.Hash SHA2_384)


[@@ Comment "Hash the message with SHA2-512, then sign the resulting digest with the P256 signature function.

  Input:
  • signature: uint8 [64]
  • msg: uint8 [msg_len]
  • private_key: uint8 [32]
  • nonce: uint8 [32]
  Output: bool, where True stands for the correct signature generation.
  False value means that an error has occurred.

  The private key and the nonce are expected to be more than 0 and less than the curve order."]
val ecdsa_sign_p256_sha512: ecdsa_sign_p256_st (S.Hash SHA2_512)


[@@ Comment "P256 signature WITHOUT hashing first.

  This function is intended to receive a hash of the input.
  For convenience, we recommend using one of the hash-and-sign combined functions above.

  The argument `msg` MUST be at least 32 bytes (i.e. `msg_len >= 32`).

  NOTE: The equivalent functions in OpenSSL and Fiat-Crypto both accept inputs
  smaller than 32 bytes. These libraries left-pad the input with enough zeroes to
  reach the minimum 32 byte size. Clients who need behavior identical to OpenSSL
  need to perform the left-padding themselves.

  Input:
  • signature: uint8 [64]
  • msg: uint8 [msg_len]
  • private_key: uint8 [32]
  • nonce: uint8 [32]
  Output: bool, where True stands for the correct signature generation.
  False value means that an error has occurred.

  The private key and the nonce are expected to be more than 0 and less than the curve order.
  The message msg is expected to be hashed by a strong hash function,
  the lenght of the message is expected to be 32 bytes and more."]
val ecdsa_sign_p256_without_hash: ecdsa_sign_p256_st (S.NoHash)


[@@ CPrologue "
/****************/
/* Verification */
/****************/

/*
  Verify a message signature. These functions internally validate the public key using validate_public_key.
*/";

Comment "
  Input:
  • msg: uint8 [msg_len]
  • public_key: uint8 [64]
  • signature_r: uint8 [32]
  • signature_s: uint8 [32]
  Output: bool, where true stands for the correct signature verification."]
val ecdsa_verif_p256_sha2: ecdsa_verify_p256_st (S.Hash SHA2_256)


[@@ Comment "
  Input:
  • msg: uint8 [msg_len]
  • public_key: uint8 [64]
  • signature_r: uint8 [32]
  • signature_s: uint8 [32]
  Output: bool, where true stands for the correct signature verification."]
val ecdsa_verif_p256_sha384: ecdsa_verify_p256_st (S.Hash SHA2_384)


[@@ Comment "
  Input:
  • msg: uint8 [msg_len]
  • public_key: uint8 [64]
  • signature_r: uint8 [32]
  • signature_s: uint8 [32]
  Output: bool, where true stands for the correct signature verification."]
val ecdsa_verif_p256_sha512: ecdsa_verify_p256_st (S.Hash SHA2_512)

[@@ Comment "
  Input:
  • msg: uint8 [msg_len]
  • public_key: uint8 [64]
  • signature_r: uint8 [32]
  • signature_s: uint8 [32]
  Output: bool, where true stands for the correct signature verification.
  The message m is expected to be hashed by a strong hash function,
  the lenght of the message is expected to be 32 bytes and more."]
val ecdsa_verif_without_hash: ecdsa_verify_p256_st S.NoHash


[@@ CPrologue "
/******************/
/* Key validation */
/******************/";

Comment "Validate a public key.

  Input: public_key: uint8 [64].
  Output: bool, where 0 stands for the public key to be correct with respect to SP 800-56A:
    • Verify that the public key is not the “point at infinity”, represented as O.
    • Verify that the affine x and y coordinates of the point represented by the public key are
      in the range [0, p – 1] where p is the prime defining the finite field.
    • Verify that y^2 = x^3 + ax + b where a and b are the coefficients of the curve equation.
  The last extract is taken from: https://neilmadden.blog/2017/05/17/so-how-do-you-validate-nist-ecdh-public-keys/"]
val validate_public_key: public_key:lbuffer uint8 64ul -> Stack bool
  (requires fun h -> live h public_key)
  (ensures  fun h0 r h1 -> modifies0 h0 h1 /\
    r == S.validate_pubkey_point (as_seq h0 public_key))


[@@ Comment "Validate a private key, e.g. prior to signing.

  Input: private_key: uint8 [32].
  Output: bool, where true stands for the scalar to be more than 0 and less than order."]
val validate_private_key: private_key:lbuffer uint8 32ul -> Stack bool
  (requires fun h -> live h private_key)
  (ensures  fun h0 r h1 -> modifies0 h0 h1 /\
    (let s = BSeq.nat_from_bytes_be (as_seq h0 private_key) in
    r <==> (0 < s && s < S.order)))


[@@ CPrologue "
/*****************************************/
/* Point representations and conversions */
/*****************************************/

/*
  Elliptic curve points have 2 32-byte coordinates (x, y) and can be represented in 3 ways:

  - \"raw\" form (64 bytes): the concatenation of the 2 coordinates, also known as \"internal\"
  - \"compressed\" form (33 bytes): first the sign byte of y (either 0x02 or 0x03), followed by x
  - \"uncompressed\" form (65 bytes): first a constant byte (always 0x04), followed by the \"raw\" form

  For all of the conversation functions below, the input and output MUST NOT overlap.
*/";

Comment "Convert 65-byte uncompressed to raw.

  The function errors out if the first byte is incorrect, or if the resulting point is invalid.

  Input:
  • pk: uint8 [65]
  • pk_raw: uint8 [64]
  Output: bool, where true stands for the correct decompression."]
val uncompressed_to_raw: pk:lbuffer uint8 65ul -> pk_raw:lbuffer uint8 64ul -> Stack bool
  (requires fun h -> live h pk /\ live h pk_raw /\ disjoint pk pk_raw)
  (ensures fun h0 b h1 -> modifies (loc pk_raw) h0 h1 /\
    (b <==> Some? (S.pk_uncompressed_to_raw (as_seq h0 pk))) /\
    (b ==> (as_seq h1 pk_raw == Some?.v (S.pk_uncompressed_to_raw (as_seq h0 pk)))))


[@@ Comment "Convert 33-byte compressed to raw.

  The function errors out if the first byte is incorrect, or if the resulting point is invalid.

  Input:
  • pk: uint8 [33]
  • pk_raw: uint8 [64]
  Output: bool, where true stands for the correct decompression."]
val compressed_to_raw: pk:lbuffer uint8 33ul -> pk_raw:lbuffer uint8 64ul -> Stack bool
  (requires fun h -> live h pk /\ live h pk_raw /\ disjoint pk pk_raw)
  (ensures  fun h0 b h1 -> modifies (loc pk_raw) h0 h1 /\
    (b <==> Some? (S.pk_compressed_to_raw (as_seq h0 pk))) /\
    (b ==> (as_seq h1 pk_raw == Some?.v (S.pk_compressed_to_raw (as_seq h0 pk)))))


[@@ Comment "Convert raw to 65-byte uncompressed.

  This function effectively prepends a 0x04 byte.

  Input:
  • pk_raw: uint8 [64]
  • pk: uint8 [65]"]
val raw_to_uncompressed: pk_raw:lbuffer uint8 64ul -> pk:lbuffer uint8 65ul -> Stack unit
  (requires fun h -> live h pk /\ live h pk_raw /\ disjoint pk pk_raw)
  (ensures fun h0 _ h1 -> modifies (loc pk) h0 h1 /\
    as_seq h1 pk == S.pk_uncompressed_from_raw (as_seq h0 pk_raw))


[@@ Comment "Convert raw to 33-byte compressed.

  Input: pk_raw: uint8 [64]
  Output: pk: uint8 [33]"]
val raw_to_compressed: pk_raw:lbuffer uint8 64ul -> pk:lbuffer uint8 33ul -> Stack unit
  (requires fun h -> live h pk /\ live h pk_raw /\ disjoint pk pk_raw)
  (ensures  fun h0 _ h1 -> modifies (loc pk) h0 h1 /\
    as_seq h1 pk == S.pk_compressed_from_raw (as_seq h0 pk_raw))


[@@ CPrologue "
/******************/
/* ECDH agreement */
/******************/";

Comment "Convert a private key into a raw public key.

  This function performs no key validation.

  Input: private_key: uint8 [32]
  Output: public_key: uint8 [64]
  Returns:
  - `true`, for success, meaning the public key is not a point at infinity
  - `false`, otherwise.

  `scalar` and `result` MUST NOT overlap."]
val dh_initiator:
    public_key:lbuffer uint8 64ul
  -> private_key:lbuffer uint8 32ul ->
  Stack bool
  (requires fun h ->
    live h public_key /\ live h private_key /\ disjoint public_key private_key)
  (ensures fun h0 r h1 -> modifies (loc public_key) h0 h1 /\
    (as_seq h1 public_key, r) == S.ecp256_dh_i (as_seq h0 private_key))


[@@ Comment "ECDH key agreement.

  This function takes a 32-byte secret key, another party's 64-byte raw public key,
  and computeds the 64-byte ECDH shared key.

  This function ONLY validates the public key.

  Input:
  • their_public_key: uint8 [64]
  • private_key: uint8 [32]
  • shared_secret: uint8 [64]
  Output: bool, where True stands for the correct key generation.
  False value means that an error has occurred (possibly the provided public key was incorrect or
  the result represents point at infinity)."]
val dh_responder:
    shared_secret:lbuffer uint8 64ul
  -> their_pubkey:lbuffer uint8 64ul
  -> private_key:lbuffer uint8 32ul ->
  Stack bool
  (requires fun h ->
    live h shared_secret /\ live h their_pubkey /\ live h private_key /\
    disjoint shared_secret their_pubkey /\ disjoint shared_secret private_key)
  (ensures fun h0 r h1 -> modifies (loc shared_secret) h0 h1 /\
    (as_seq h1 shared_secret, r) == S.ecp256_dh_r (as_seq h0 their_pubkey) (as_seq h0 private_key))
