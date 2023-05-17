module Hacl.Ed25519

module ST = FStar.HyperStack.ST
open FStar.HyperStack.All
open FStar.Mul

open Lib.IntTypes
open Lib.Buffer

module S = Spec.Ed25519

#set-options "--z3rlimit 50 --fuel 0 --ifuel 0"

val secret_expand: expanded:lbuffer uint8 64ul -> secret:lbuffer uint8 32ul -> Stack unit
  (requires fun h -> live h expanded /\ live h secret /\ disjoint expanded secret)
  (ensures  fun h0 _ h1 -> modifies (loc expanded) h0 h1 /\
   (let a, prefix = S.secret_expand (as_seq h0 secret) in
    as_seq h1 (gsub expanded 0ul 32ul) == a /\
    as_seq h1 (gsub expanded 32ul 32ul) == prefix))

[@CInline]
let secret_expand expanded secret =
  assert_norm (pow2 32 <= pow2 125 - 1);
  Hacl.Streaming.SHA2.hash_512 secret 32ul expanded;
  let h_low  = sub expanded 0ul 32ul in
  let h_low0  = h_low.( 0ul) in
  let h_low31 = h_low.(31ul) in
  h_low.( 0ul) <- h_low0 &. u8 0xf8;
  h_low.(31ul) <- (h_low31 &. u8 127) |. u8 64


let secret_to_public public_key private_key =
  push_frame ();
  let expanded_secret = create 64ul (u8 0) in
  secret_expand expanded_secret private_key;
  let a = sub expanded_secret 0ul 32ul in
  Hacl.Impl.Ed25519.Sign.point_mul_g_compress public_key a;
  pop_frame ()


let expand_keys expanded_keys private_key =
  let public_key = sub expanded_keys 0ul 32ul in
  let s_prefix   = sub expanded_keys 32ul 64ul in
  let s          = sub expanded_keys 32ul 32ul in
  secret_expand s_prefix private_key;
  Hacl.Impl.Ed25519.Sign.point_mul_g_compress public_key s


let sign_expanded signature expanded_keys msg_len msg =
  Hacl.Impl.Ed25519.Sign.sign_expanded signature expanded_keys msg_len msg


let sign signature private_key msg_len msg =
  push_frame ();
  let expanded_keys = create 96ul (u8 0) in
  expand_keys expanded_keys private_key;
  sign_expanded signature expanded_keys msg_len msg;
  pop_frame ()


let verify public_key msg_len msg signature =
  Hacl.Impl.Ed25519.Verify.verify public_key msg_len msg signature
