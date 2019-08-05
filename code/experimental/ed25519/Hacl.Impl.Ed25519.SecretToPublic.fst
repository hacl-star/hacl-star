module Hacl.Impl.Ed25519.SecretToPublic

module ST = FStar.HyperStack.ST
open FStar.HyperStack.All

open Lib.IntTypes
open Lib.Buffer

open Hacl.Bignum25519
open Hacl.Impl.Ed25519.SecretExpand
open Hacl.Impl.Ed25519.PointCompress
open Hacl.Impl.Ed25519.Ladder

#set-options "--z3rlimit 20 --max_fuel 0 --max_ifuel 0"

val secret_to_public:
    out:lbuffer uint8 32ul
  -> secret:lbuffer uint8 32ul ->
  Stack unit
    (requires fun h -> live h out /\ live h secret /\ disjoint out secret)
    (ensures  fun h0 _ h1 -> modifies (loc out) h0 h1 /\
      as_seq h1 out == Spec.Ed25519.secret_to_public (as_seq h0 secret)
    )
let secret_to_public out secret =
  push_frame();
  let expanded_secret = create 64ul (u8 0) in
  let res = create 20ul (u64 0) in
  secret_expand expanded_secret secret;
  let a = sub expanded_secret 0ul 32ul in
  point_mul_g res a;
  point_compress out res;
  pop_frame()
