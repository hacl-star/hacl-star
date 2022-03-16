module Hacl.K256.ECDSA

open FStar.HyperStack
open FStar.HyperStack.ST
open FStar.Mul

open Lib.IntTypes
open Lib.Buffer

module ST = FStar.HyperStack.ST
module LSeq = Lib.Sequence
module BSeq = Lib.ByteSequence

module S = Spec.K256


#set-options "--z3rlimit 50 --fuel 0 --ifuel 0"

inline_for_extraction noextract
let lbytes len = lbuffer uint8 len


val ecdsa_sign_hashed_msg (signature:lbytes 64ul)
  (msgHash private_key nonce:lbytes 32ul) : Stack bool
  (requires fun h ->
    live h msgHash /\ live h private_key /\ live h nonce /\ live h signature /\
    disjoint signature msgHash /\ disjoint signature private_key /\ disjoint signature nonce)
  (ensures fun h0 b h1 -> modifies (loc signature) h0 h1 /\
    (let sgnt = S.ecdsa_sign_hashed_msg (as_seq h0 msgHash) (as_seq h0 private_key) (as_seq h0 nonce) in
    (b <==> Some? sgnt) /\ (b ==> (as_seq h1 signature == Some?.v sgnt))))


val ecdsa_verify_hashed_msg (msgHash:lbytes 32ul) (public_key signature:lbytes 64ul) : Stack bool
  (requires fun h ->
    live h msgHash /\ live h public_key /\ live h signature)
  (ensures fun h0 b h1 -> modifies0 h0 h1 /\
    b == S.ecdsa_verify_hashed_msg (as_seq h0 msgHash) (as_seq h0 public_key) (as_seq h0 signature))


val ecdsa_sign_sha256 (signature:lbytes 64ul)
  (msg_len:size_t) (msg:lbytes msg_len) (private_key nonce:lbytes 32ul) : Stack bool
  (requires fun h ->
    live h msg /\ live h private_key /\ live h nonce /\ live h signature /\
    disjoint signature msg /\ disjoint signature private_key /\ disjoint signature nonce)
  (ensures fun h0 b h1 -> modifies (loc signature) h0 h1 /\
    (let sgnt = S.ecdsa_sign_sha256 (v msg_len) (as_seq h0 msg) (as_seq h0 private_key) (as_seq h0 nonce) in
    (b <==> Some? sgnt) /\ (b ==> (as_seq h1 signature == Some?.v sgnt))))


val ecdsa_verify_sha256 (msg_len:size_t) (msg:lbytes msg_len) (public_key signature:lbytes 64ul) : Stack bool
  (requires fun h ->
    live h msg /\ live h public_key /\ live h signature)
  (ensures fun h0 b h1 -> modifies0 h0 h1 /\
    b == S.ecdsa_verify_sha256 (v msg_len) (as_seq h0 msg) (as_seq h0 public_key) (as_seq h0 signature))


///  Parsing and Serializing public keys

val public_key_uncompressed_to_raw: pk_raw:lbytes 64ul -> pk:lbytes 65ul -> Stack bool
  (requires fun h -> live h pk /\ live h pk_raw /\ disjoint pk pk_raw)
  (ensures  fun h0 b h1 -> modifies (loc pk_raw) h0 h1 /\
    (b <==> Some? (S.pk_uncompressed_to_raw (as_seq h0 pk))) /\
    (b ==> (as_seq h1 pk_raw == Some?.v (S.pk_uncompressed_to_raw (as_seq h0 pk)))))


val public_key_uncompressed_from_raw: pk:lbytes 65ul -> pk_raw:lbytes 64ul -> Stack unit
  (requires fun h -> live h pk /\ live h pk_raw /\ disjoint pk pk_raw)
  (ensures  fun h0 _ h1 -> modifies (loc pk) h0 h1 /\
    as_seq h1 pk == S.pk_uncompressed_from_raw (as_seq h0 pk_raw))


val public_key_compressed_to_raw: pk_raw:lbytes 64ul -> pk:lbytes 33ul -> Stack bool
  (requires fun h -> live h pk /\ live h pk_raw /\ disjoint pk pk_raw)
  (ensures  fun h0 b h1 -> modifies (loc pk_raw) h0 h1 /\
    (b <==> Some? (S.pk_compressed_to_raw (as_seq h0 pk))) /\
    (b ==> (as_seq h1 pk_raw == Some?.v (S.pk_compressed_to_raw (as_seq h0 pk)))))


val public_key_compressed_from_raw: pk:lbytes 33ul -> pk_raw:lbytes 64ul -> Stack unit
  (requires fun h -> live h pk /\ live h pk_raw /\ disjoint pk pk_raw)
  (ensures  fun h0 _ h1 -> modifies (loc pk) h0 h1 /\
    as_seq h1 pk == S.pk_compressed_from_raw (as_seq h0 pk_raw))


///  Low-S normalization used in secp256k1

val secp256k1_ecdsa_signature_normalize: signature: lbytes 64ul -> Stack bool
  (requires fun h -> live h signature)
  (ensures  fun h0 b h1 -> modifies (loc signature) h0 h1 /\
    (let sgnt = S.secp256k1_ecdsa_signature_normalize (as_seq h0 signature) in
    (b <==> Some? sgnt) /\ (b ==> (as_seq h1 signature == Some?.v sgnt))))

val secp256k1_ecdsa_is_signature_normalized: signature: lbytes 64ul -> Stack bool
  (requires fun h -> live h signature)
  (ensures  fun h0 b h1 -> modifies0 h0 h1 /\
    b == S.secp256k1_ecdsa_is_signature_normalized (as_seq h0 signature))


val secp256k1_ecdsa_sign_hashed_msg (signature:lbytes 64ul)
  (msgHash private_key nonce:lbytes 32ul) : Stack bool
  (requires fun h ->
    live h msgHash /\ live h private_key /\ live h nonce /\ live h signature /\
    disjoint signature msgHash /\ disjoint signature private_key /\ disjoint signature nonce)
  (ensures fun h0 b h1 -> modifies (loc signature) h0 h1 /\
    (let sgnt = S.secp256k1_ecdsa_sign_hashed_msg (as_seq h0 msgHash) (as_seq h0 private_key) (as_seq h0 nonce) in
    (b <==> Some? sgnt) /\ (b ==> (as_seq h1 signature == Some?.v sgnt))))


val secp256k1_ecdsa_sign_sha256 (signature:lbytes 64ul)
  (msg_len:size_t) (msg:lbytes msg_len) (private_key nonce:lbytes 32ul) : Stack bool
  (requires fun h ->
    live h msg /\ live h private_key /\ live h nonce /\ live h signature /\
    disjoint signature msg /\ disjoint signature private_key /\ disjoint signature nonce)
  (ensures fun h0 b h1 -> modifies (loc signature) h0 h1 /\
    (let sgnt = S.secp256k1_ecdsa_sign_sha256 (v msg_len) (as_seq h0 msg) (as_seq h0 private_key) (as_seq h0 nonce) in
    (b <==> Some? sgnt) /\ (b ==> (as_seq h1 signature == Some?.v sgnt))))


val secp256k1_ecdsa_verify_hashed_msg (msgHash:lbytes 32ul) (public_key signature:lbytes 64ul) : Stack bool
  (requires fun h ->
    live h msgHash /\ live h public_key /\ live h signature)
  (ensures fun h0 b h1 -> modifies0 h0 h1 /\
    b == S.secp256k1_ecdsa_verify_hashed_msg (as_seq h0 msgHash) (as_seq h0 public_key) (as_seq h0 signature))


val secp256k1_ecdsa_verify_sha256 (msg_len:size_t) (msg:lbytes msg_len) (public_key signature:lbytes 64ul) : Stack bool
  (requires fun h ->
    live h msg /\ live h public_key /\ live h signature)
  (ensures fun h0 b h1 -> modifies0 h0 h1 /\
    b == S.secp256k1_ecdsa_verify_sha256 (v msg_len) (as_seq h0 msg) (as_seq h0 public_key) (as_seq h0 signature))
