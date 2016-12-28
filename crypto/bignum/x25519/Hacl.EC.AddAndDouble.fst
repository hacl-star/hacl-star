module Hacl.EC.AddAndDouble

open FStar.HyperStack
open FStar.Buffer

open Hacl.Bignum.Constants
open Hacl.Bignum.Parameters
open Hacl.Bignum
open Hacl.EC.Point
open Hacl.Spec.EC.AddAndDouble2


let all_disjoint ppx ppz ppqx ppqz px pz pqx pqz qx qz =
  disjoint ppx ppz /\ disjoint ppx ppqx /\ disjoint ppx ppqz /\ disjoint ppx px /\ disjoint ppx pz
  /\ disjoint ppx pqx /\ disjoint ppx pqz /\ disjoint ppx qx /\ disjoint ppx qz
  /\ disjoint ppz ppqx /\ disjoint ppz ppqz /\ disjoint ppz px /\ disjoint ppz pz
  /\ disjoint ppz pqx /\ disjoint ppz pqz /\ disjoint ppz qx /\ disjoint ppz qz
  /\ disjoint ppqx ppqz /\ disjoint ppqx px /\ disjoint ppqx pz
  /\ disjoint ppqx pqx /\ disjoint ppqx pqz /\ disjoint ppqx qx /\ disjoint ppqx qz
  /\ disjoint ppqz px /\ disjoint ppqz pz
  /\ disjoint ppqz pqx /\ disjoint ppqz pqz /\ disjoint ppqz qx /\ disjoint ppqz qz
  /\ disjoint px pz /\ disjoint px pqx /\ disjoint px pqz /\ disjoint px qx /\ disjoint px qz
  /\ disjoint pz pqx /\ disjoint pz pqz /\ disjoint pz qx /\ disjoint pz qz
  /\ disjoint pqx pqz /\ disjoint pqx qx /\ disjoint pqx qz
  /\ disjoint pqz qx /\ disjoint pqz qz
  /\ disjoint qx qz


val fmonty:
  ppx:felem -> ppz:felem -> ppqx:felem -> ppqz:felem ->
  px:felem -> pz:felem -> pqx:felem -> pqz:felem ->
  qx:felem -> qz:felem -> Stack unit
    (requires (fun h -> live h ppx /\ live h ppz /\ live h ppqx /\ live h ppqz
      /\ live h px /\ live h pz /\ live h pqx /\ live h pqz
      /\ all_disjoint ppx ppz ppqx ppqz px pz pqx pqz qx qz))
    (ensures (fun h -> live h ppx /\ live h ppz /\ live h ppqx /\ live h ppqz
      /\ live h px /\ live h pz /\ live h pqx /\ live h pqz
      /\ as_seq

val fmonty:
  pp:point ->
  ppq:point ->
  p:point ->
  pq:point ->
  q:point ->
  Stack unit
    (requires (fun _ -> true))
    (ensures (fun _ _ _ -> true))
let fmonty pp ppq p pq qmqp =
  let qx = getx qmqp in
  let x2 = getx pp in
  let z2 = getz pp in
  let x3 = getx ppq in
  let z3 = getz ppq in
  let x  = getx p in
  let z  = getz p in
  let xprime  = getx pq in
  let zprime  = getz pq in
  push_frame();
  let buf = create limb_zero 40ul in
  let origx      = Buffer.sub buf 0ul  5ul in
  let origxprime = Buffer.sub buf 5ul  5ul in
  let zzz        = Buffer.sub buf 10ul 5ul in
  let xx         = Buffer.sub buf 15ul 5ul in
  let zz         = Buffer.sub buf 20ul 5ul in
  let xxprime    = Buffer.sub buf 25ul 5ul in
  let zzprime    = Buffer.sub buf 30ul 5ul in
  let zzzprime   = Buffer.sub buf 35ul 5ul in
  blit x 0ul origx 0ul 5ul;
  fsum x z; // x < x + z
  fdifference z origx; // z <- 8p + x - z
  blit xprime 0ul origxprime 0ul 5ul;
  fsum xprime zprime; // xprime <- xprime + zprime
  fdifference zprime origxprime; // zprime <- 8p + xprime - zprime
  fmul xxprime xprime z; // xxprime <- sum * sub
  fmul zzprime x zprime; // zzprime <- sum * sub
  blit xxprime 0ul origxprime 0ul 5ul;
  fsum xxprime zzprime; // xxprime <- sum
  fdifference zzprime origxprime; // zzprime <- sub
  fsquare_times x3 xxprime 1ul; // sum sum
  fsquare_times zzzprime zzprime 1ul; // sub sub 
  fmul z3 zzzprime qx;
  fsquare_times xx x 1ul; // sum red
  fsquare_times zz z 1ul; // red sub 
  fmul x2 xx zz; // red red
  fdifference zz xx; // red red
  fscalar zzz zz (uint64_to_limb Hacl.Bignum.Constants.a24);
  fsum zzz xx; // red red
  fmul z2 zz zzz;
  pop_frame()
