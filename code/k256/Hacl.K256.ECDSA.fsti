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

val ecdsa_sign_hashed_msg (r s m private_key k:lbytes 32ul) : Stack bool
  (requires fun h ->
    live h m /\ live h private_key /\ live h k /\
    live h r /\ live h s /\ disjoint r s /\

   (let sk_nat = BSeq.nat_from_bytes_be (as_seq h private_key) in
    let k_nat = BSeq.nat_from_bytes_be (as_seq h k) in
    0 < sk_nat /\ sk_nat < S.q /\ 0 < k_nat /\ k_nat < S.q))
  (ensures fun h0 b h1 -> modifies (loc r |+| loc s) h0 h1 /\
    (let (r_s, s_s, b_s) =
      S.ecdsa_sign_hashed_msg (as_seq h0 m) (as_seq h0 private_key) (as_seq h0 k) in
     as_seq h1 r == r_s /\ as_seq h1 s == s_s /\ b == b_s))


val ecdsa_verify_hashed_msg (m:lbytes 32ul) (public_key:lbytes 64ul) (r s:lbytes 32ul) : Stack bool
  (requires fun h ->
    live h m /\ live h public_key /\ live h r /\
    live h s /\ disjoint r s)
  (ensures fun h0 b h1 -> modifies0 h0 h1 /\
    b == S.ecdsa_verify_hashed_msg (as_seq h0 m) (as_seq h0 public_key) (as_seq h0 r) (as_seq h0 s))


val ecdsa_sign_sha256 (r s:lbytes 32ul) (msg_len:size_t) (msg:lbytes msg_len) (private_key k:lbytes 32ul) : Stack bool
  (requires fun h ->
    live h msg /\ live h private_key /\ live h k /\
    live h r /\ live h s /\ disjoint r s /\

   (let sk_nat = BSeq.nat_from_bytes_be (as_seq h private_key) in
    let k_nat = BSeq.nat_from_bytes_be (as_seq h k) in
    0 < sk_nat /\ sk_nat < S.q /\ 0 < k_nat /\ k_nat < S.q))
  (ensures fun h0 b h1 -> modifies (loc r |+| loc s) h0 h1 /\
    (let (r_s, s_s, b_s) =
      S.ecdsa_sign_sha256 (v msg_len) (as_seq h0 msg) (as_seq h0 private_key) (as_seq h0 k) in
     as_seq h1 r == r_s /\ as_seq h1 s == s_s /\ b == b_s))


val ecdsa_verify_sha256 (msg_len:size_t) (msg:lbytes msg_len) (public_key:lbytes 64ul) (r s:lbytes 32ul) : Stack bool
  (requires fun h ->
    live h msg /\ live h public_key /\ live h r /\
    live h s /\ disjoint r s)
  (ensures fun h0 b h1 -> modifies0 h0 h1 /\
    b == S.ecdsa_verify_sha256 (v msg_len) (as_seq h0 msg) (as_seq h0 public_key) (as_seq h0 r) (as_seq h0 s))


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
