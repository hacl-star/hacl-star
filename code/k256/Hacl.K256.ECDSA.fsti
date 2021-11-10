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
let lbytes32 = lbuffer uint8 32ul

val ecdsa_sign_hashed_msg (r s m private_key k:lbytes32) : Stack bool
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


val ecdsa_verify_hashed_msg (m public_key_x public_key_y r s:lbytes32) : Stack bool
  (requires fun h ->
    live h m /\ live h public_key_x /\ live h public_key_y /\
    live h r /\ live h s /\ disjoint r s /\

   (let pk_x = BSeq.nat_from_bytes_be (as_seq h public_key_x) in
    let pk_y = BSeq.nat_from_bytes_be (as_seq h public_key_y) in
    pk_x < S.prime /\ pk_y < S.prime))
  (ensures fun h0 b h1 -> modifies0 h0 h1 /\
    b == S.ecdsa_verify_hashed_msg (as_seq h0 m)
      (as_seq h0 public_key_x) (as_seq h0 public_key_y) (as_seq h0 r) (as_seq h0 s))


val ecdsa_sign_sha256 (r s:lbytes32) (msg_len:size_t) (msg:lbuffer uint8 msg_len) (private_key k:lbytes32) : Stack bool
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


val ecdsa_verify_sha256 (msg_len:size_t) (msg:lbuffer uint8 msg_len) (public_key_x public_key_y r s:lbytes32) : Stack bool
  (requires fun h ->
    live h msg /\ live h public_key_x /\ live h public_key_y /\
    live h r /\ live h s /\ disjoint r s /\

   (let pk_x = BSeq.nat_from_bytes_be (as_seq h public_key_x) in
    let pk_y = BSeq.nat_from_bytes_be (as_seq h public_key_y) in
    pk_x < S.prime /\ pk_y < S.prime))
  (ensures fun h0 b h1 -> modifies0 h0 h1 /\
    b == S.ecdsa_verify_sha256 (v msg_len) (as_seq h0 msg)
      (as_seq h0 public_key_x) (as_seq h0 public_key_y) (as_seq h0 r) (as_seq h0 s))
