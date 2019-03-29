module Hacl.EC

module ST = FStar.HyperStack.ST

open FStar.HyperStack.All

open FStar.Mul
open FStar.HyperStack
open FStar.Ghost
open FStar.Buffer
open FStar.Buffer.Quantifiers

open Hacl.Bignum.Constants
open Hacl.Bignum.Parameters
open Hacl.Bignum.Limb
open Hacl.EC.Point
open Hacl.EC.Format
open Hacl.EC.Ladder
open Hacl.Spec.Endianness
open Hacl.Spec.EC

module U32 = FStar.UInt32
module H8 = Hacl.UInt8

#reset-options "--initial_fuel 0 --max_fuel 0 --z3rlimit 100"

[@"substitute"]
val crypto_scalarmult__:
  mypublic:uint8_p{length mypublic = 32} ->
  secret:uint8_p{length secret = 32} ->
  basepoint:uint8_p{length basepoint = 32} ->
  q:point ->
  Stack unit
    (requires (fun h -> live h q /\ Buffer.live h mypublic /\ Buffer.live h secret
      /\ Buffer.live h basepoint
      /\ Hacl.Spec.EC.AddAndDouble.red_513 (as_seq h (getx q))
      /\ Hacl.Spec.EC.AddAndDouble.red_513 (as_seq h (getz q))
      /\ Hacl.Spec.Bignum.selem (as_seq h (getz q)) = 1
    ))
    (ensures (fun h0 _ h1 -> live h0 q /\ Buffer.live h0 mypublic /\ Buffer.live h0 secret
      /\ Buffer.live h0 basepoint
      /\ Hacl.Spec.EC.AddAndDouble.red_513 (as_seq h0 (getx q))
      /\ Hacl.Spec.EC.AddAndDouble.red_513 (as_seq h0 (getz q))
      /\ Buffer.live h1 mypublic /\ modifies_1 mypublic h0 h1
      /\ (let secret = reveal_sbytes (as_seq h0 secret) in
         let basepoint = reveal_sbytes (as_seq h0 basepoint) in
         let mypublic = reveal_sbytes (as_seq h1 mypublic) in
         let q        = Hacl.Spec.Bignum.selem (as_seq h0 (getx q)) in
         mypublic == Spec.Curve25519.(encodePoint (montgomery_ladder q secret)))
      ))
#reset-options "--initial_fuel 0 --max_fuel 0 --z3rlimit 1000"
[@"substitute"]
let crypto_scalarmult__ mypublic scalar basepoint q =
  let h0 = ST.get() in
  push_frame();
  let h1 = ST.get() in
  let buf   = Buffer.create limb_zero 15ul in
  let nq    = Buffer.sub buf 0ul 10ul in
  let x     = getx nq in
  let z     = getz nq in
  let zmone = Buffer.sub buf 5ul 5ul in
  let h2 = ST.get() in
  x.(0ul) <- limb_one;
  let h3 = ST.get() in
  (**) modifies_subbuffer_1 h2 h3 x buf;
  Hacl.Spec.Bignum.Modulo.lemma_seval_5 (as_seq h3 x);
  no_upd_lemma_1 h2 h3 x z;
  no_upd_lemma_1 h2 h3 x (getx q);
  no_upd_lemma_1 h2 h3 x (getz q);
  no_upd_lemma_1 h2 h3 x zmone;
  no_upd_lemma_1 h2 h3 x scalar;
  cut (v (get h3 x 0) = 1); cut (v (get h3 x 1) = 0); cut (v (get h3 x 2) = 0);
  cut (v (get h3 x 3) = 0); cut (v (get h3 x 4) = 0); cut (v (get h3 z 0) = 0);
  cut (v (get h3 z 1) = 0); cut (v (get h3 z 2) = 0); cut (v (get h3 z 3) = 0);
  cut (v (get h3 z 4) = 0); cut (v (get h3 zmone 0) = 0); cut (v (get h3 zmone 1) = 0);
  cut (v (get h3 zmone 2) = 0); cut (v (get h3 zmone 3) = 0); cut (v (get h3 zmone 4) = 0);
  cmult nq scalar q;
  let h5 = ST.get() in
  (**) modifies_subbuffer_1 h3 h5 nq buf;
  (**) lemma_modifies_1_trans buf h2 h3 h5;
  (**) lemma_modifies_0_1' buf h1 h2 h5;
  scalar_of_point mypublic nq;
  let h6 = ST.get() in
  (**) lemma_modifies_0_1 mypublic h1 h5 h6;
  pop_frame();
  let h7 = ST.get() in
  (**) modifies_popped_1 mypublic h0 h1 h6 h7


[@"substitute"]
val crypto_scalarmult_:
  mypublic:uint8_p{length mypublic = 32} ->
  secret:uint8_p{length secret = 32} ->
  basepoint:uint8_p{length basepoint = 32} ->
  q:point ->
  Stack unit
    (requires (fun h -> live h q /\ Buffer.live h mypublic /\ Buffer.live h secret
      /\ Buffer.live h basepoint
      /\ Hacl.Spec.EC.AddAndDouble.red_513 (as_seq h (getx q))
      /\ Hacl.Spec.EC.AddAndDouble.red_513 (as_seq h (getz q))
      /\ Hacl.Spec.Bignum.selem (as_seq h (getz q)) = 1
    ))
    (ensures (fun h0 _ h1 -> Buffer.live h1 mypublic /\ modifies_1 mypublic h0 h1
     /\ live h0 q /\ Buffer.live h0 mypublic /\ Buffer.live h0 secret
     /\ Buffer.live h0 basepoint
     /\ Hacl.Spec.EC.AddAndDouble.red_513 (as_seq h0 (getx q))
     /\ Hacl.Spec.EC.AddAndDouble.red_513 (as_seq h0 (getz q))
     /\ (let secret = reveal_sbytes (as_seq h0 secret) in
        let basepoint = reveal_sbytes (as_seq h0 basepoint) in
        let mypublic = reveal_sbytes (as_seq h1 mypublic) in
         let q        = Hacl.Spec.Bignum.selem (as_seq h0 (getx q)) in
        mypublic == Spec.Curve25519.(encodePoint (montgomery_ladder q (decodeScalar25519 secret))))
    ))
[@"substitute"]
let crypto_scalarmult_ mypublic secret basepoint q =
  let h0 = ST.get() in
  push_frame();
  let h1 = ST.get() in
  let scalar = format_secret secret in
  crypto_scalarmult__ mypublic scalar basepoint q;
  pop_frame()

inline_for_extraction
val crypto_scalarmult:
  mypublic:uint8_p{length mypublic = 32} ->
  secret:uint8_p{length secret = 32} ->
  basepoint:uint8_p{length basepoint = 32} ->
  Stack unit
    (requires (fun h -> Buffer.live h mypublic /\ Buffer.live h secret /\ Buffer.live h basepoint))
    (ensures (fun h0 _ h1 -> Buffer.live h1 mypublic /\ modifies_1 mypublic h0 h1
     /\ Buffer.live h0 mypublic /\ Buffer.live h0 secret /\ Buffer.live h0 basepoint
     /\ (let secret = reveal_sbytes (as_seq h0 secret) in
        let basepoint = reveal_sbytes (as_seq h0 basepoint) in
        let mypublic = reveal_sbytes (as_seq h1 mypublic) in
        mypublic == Spec.Curve25519.(scalarmult secret basepoint))
    ))
let crypto_scalarmult mypublic secret basepoint =
  push_frame();
  let q  = point_of_scalar basepoint in
  crypto_scalarmult_ mypublic secret basepoint q;
  pop_frame()
