module Hacl.EC.AddAndDouble

module ST = FStar.HyperStack.ST
module HS = FStar.HyperStack

open FStar.HyperStack.All

open FStar.HyperStack
open FStar.Buffer

open Hacl.Bignum.Constants
open Hacl.Bignum.Parameters
open Hacl.Bignum
open Hacl.Bignum.Fsquare
open Hacl.Spec.EC.AddAndDouble2


#reset-options "--initial_fuel 0 --max_fuel 0 --z3rlimit 20"

let all_disjoint (ppx:felem) (ppz:felem) (ppqx:felem) (ppqz:felem)
                 (px:felem) (pz:felem) (pqx:felem) (pqz:felem) (qx:felem) : GTot Type0 =
  disjoint ppx ppz /\ disjoint ppx ppqx /\ disjoint ppx ppqz /\ disjoint ppx px /\ disjoint ppx pz
  /\ disjoint ppx pqx /\ disjoint ppx pqz /\ disjoint ppx qx
  /\ disjoint ppz ppqx /\ disjoint ppz ppqz /\ disjoint ppz px /\ disjoint ppz pz
  /\ disjoint ppz pqx /\ disjoint ppz pqz /\ disjoint ppz qx
  /\ disjoint ppqx ppqz /\ disjoint ppqx px /\ disjoint ppqx pz
  /\ disjoint ppqx pqx /\ disjoint ppqx pqz /\ disjoint ppqx qx
  /\ disjoint ppqz px /\ disjoint ppqz pz
  /\ disjoint ppqz pqx /\ disjoint ppqz pqz /\ disjoint ppqz qx
  /\ disjoint px pz /\ disjoint px pqx /\ disjoint px pqz /\ disjoint px qx
  /\ disjoint pz pqx /\ disjoint pz pqz /\ disjoint pz qx
  /\ disjoint pqx pqz /\ disjoint pqx qx
  /\ disjoint pqz qx

let same_frame (ppx:felem) (ppz:felem) (ppqx:felem) (ppqz:felem)
               (px:felem) (pz:felem) (pqx:felem) (pqz:felem) : GTot Type0 =
  frameOf ppx = frameOf ppz /\ frameOf ppx = frameOf ppqx /\ frameOf ppx = frameOf ppqz
  /\ frameOf ppx = frameOf px /\ frameOf ppx = frameOf pz /\ frameOf ppx = frameOf pqx
  /\ frameOf pqx = frameOf pqz


[@"substitute"]
inline_for_extraction let red_513 s = Hacl.Spec.EC.AddAndDouble.red_513 s
[@"substitute"]
inline_for_extraction let red_53 s = Hacl.Spec.EC.AddAndDouble.red_53 s
[@"substitute"]
inline_for_extraction let red_5413 s = Hacl.Spec.EC.AddAndDouble.red_5413 s


private val lemma_modifies_composition: s1:Set.set HS.rid -> r2:HS.rid -> h0:mem -> h1:mem -> h2:mem -> Lemma
  (requires (modifies s1 h0 h1 /\ modifies (Set.singleton r2) h1 h2))
  (ensures (modifies (Set.union s1 (Set.singleton r2)) h0 h2))
private let lemma_modifies_composition s1 r2 h0 h1 h2 = ()


private val lemma_set_union: s:Set.set HS.rid -> r:HS.rid{Set.mem r s} -> Lemma
  (Set.union s (Set.singleton r) == s)
private let lemma_set_union s r = Set.lemma_equal_intro s (Set.union s (Set.singleton r))


private val lemma_fmonty__1_modifies:
  tmp:buffer limb{length tmp = 40} ->
  ppx:felem -> ppz:felem -> ppqx:felem -> ppqz:felem ->
  px:felem -> pz:felem -> pqx:felem -> pqz:felem ->
  qx:felem ->
  h0:mem -> h1:mem -> h2:mem -> h3:mem -> h4:mem -> h5:mem -> h6:mem -> h7:mem -> h8:mem ->
  Lemma
    (requires (
      let origx      = Buffer.sub tmp 0ul  5ul in
      let origxprime = Buffer.sub tmp 5ul  5ul in
      let xxprime    = Buffer.sub tmp 25ul 5ul in
      let zzprime    = Buffer.sub tmp 30ul 5ul in
      live h0 ppx /\ live h0 ppz /\ live h0 ppqx /\ live h0 ppqz
      /\ live h0 px /\ live h0 pz /\ live h0 pqx /\ live h0 pqz
      /\ live h0 qx /\ live h0 tmp
      /\ all_disjoint ppx ppz ppqx ppqz px pz pqx pqz qx
      /\ same_frame ppx ppz ppqx ppqz px pz pqx pqz
      /\ frameOf ppx <> frameOf tmp /\ frameOf ppx <> frameOf qx /\ frameOf qx <> frameOf tmp
      /\ modifies_1 origx h0 h1
      /\ modifies_1 px h1 h2
      /\ modifies_1 pz h2 h3
      /\ modifies_1 origxprime h3 h4
      /\ modifies_1 pqx h4 h5
      /\ modifies_1 pqz h5 h6
      /\ modifies_1 xxprime h6 h7
      /\ modifies_1 zzprime h7 h8
      ))
    (ensures (modifies (Set.union (Set.singleton (frameOf tmp)) (Set.singleton (frameOf ppx))) h0 h8))
#reset-options "--initial_fuel 0 --max_fuel 0 --z3rlimit 100"
private let lemma_fmonty__1_modifies tmp ppx ppz ppqx ppqz px pz pqx pqz qx h0 h1 h2 h3 h4 h5 h6 h7 h8 =
  let origx    = Buffer.sub tmp 0ul  5ul in
  let origxprime = Buffer.sub tmp 5ul  5ul in
  let xxprime  = Buffer.sub tmp 25ul 5ul in
  let zzprime  = Buffer.sub tmp 30ul 5ul in
  lemma_reveal_modifies_1 origx h0 h1;
  lemma_reveal_modifies_1 px h1 h2;
  lemma_reveal_modifies_1 pz h2 h3;
  lemma_reveal_modifies_1 origxprime h3 h4;
  lemma_reveal_modifies_1 pqx h4 h5;
  lemma_reveal_modifies_1 pqz h5 h6;
  lemma_reveal_modifies_1 xxprime h6 h7;
  lemma_reveal_modifies_1 zzprime h7 h8;
  let s = Set.union (Set.singleton (frameOf tmp)) (Set.singleton (frameOf ppx)) in
  lemma_set_union s (frameOf tmp);
  lemma_set_union s (frameOf ppx);
  lemma_modifies_composition (Set.singleton (frameOf tmp)) (frameOf ppx) h0 h1 h2;
  lemma_modifies_composition s (frameOf ppx) h0 h2 h3;
  lemma_modifies_composition s (frameOf tmp) h0 h3 h4;
  lemma_modifies_composition s (frameOf ppx) h0 h4 h5;
  lemma_modifies_composition s (frameOf ppx) h0 h5 h6;
  lemma_modifies_composition s (frameOf tmp) h0 h6 h7;
  lemma_modifies_composition s (frameOf tmp) h0 h7 h8


private val lemma_fmonty__2_modifies:
  tmp:buffer limb{length tmp = 40} ->
  ppx:felem -> ppz:felem -> ppqx:felem -> ppqz:felem ->
  px:felem -> pz:felem -> pqx:felem -> pqz:felem ->
  qx:felem ->
  h8:mem -> h9:mem -> h10:mem -> h11:mem -> h12:mem -> h13:mem -> h14:mem -> h15:mem -> h16:mem ->
  Lemma
    (requires (
      let origxprime = Buffer.sub tmp 5ul  5ul in
      let xx         = Buffer.sub tmp 15ul 5ul in
      let zz         = Buffer.sub tmp 20ul 5ul in
      let xxprime    = Buffer.sub tmp 25ul 5ul in
      let zzprime    = Buffer.sub tmp 30ul 5ul in
      let zzzprime   = Buffer.sub tmp 35ul 5ul in
      live h8 ppx /\ live h8 ppz /\ live h8 ppqx /\ live h8 ppqz
      /\ live h8 px /\ live h8 pz /\ live h8 pqx /\ live h8 pqz
      /\ live h8 qx /\ live h8 tmp
      /\ all_disjoint ppx ppz ppqx ppqz px pz pqx pqz qx
      /\ same_frame ppx ppz ppqx ppqz px pz pqx pqz
      /\ frameOf ppx <> frameOf tmp /\ frameOf ppx <> frameOf qx /\ frameOf qx <> frameOf tmp
      /\ modifies_1 origxprime h8 h9
      /\ modifies_1 xxprime h9 h10
      /\ modifies_1 zzprime h10 h11
      /\ modifies_1 ppqx h11 h12
      /\ modifies_1 zzzprime h12 h13
      /\ modifies_1 ppqz h13 h14
      /\ modifies_1 xx h14 h15
      /\ modifies_1 zz h15 h16
      ))
    (ensures (modifies (Set.union (Set.singleton (frameOf tmp)) (Set.singleton (frameOf ppx))) h8 h16))
#reset-options "--initial_fuel 0 --max_fuel 0 --z3rlimit 10"
private let lemma_fmonty__2_modifies tmp ppx ppz x3 z3 px pz pqx pqz qx h8 h9 h10 h11 h12 h13 h14 h15 h16 =
  let origxprime = Buffer.sub tmp 5ul  5ul in
  let xx         = Buffer.sub tmp 15ul 5ul in
  let zz         = Buffer.sub tmp 20ul 5ul in
  let xxprime    = Buffer.sub tmp 25ul 5ul in
  let zzprime    = Buffer.sub tmp 30ul 5ul in
  let zzzprime   = Buffer.sub tmp 35ul 5ul in
  lemma_reveal_modifies_1 origxprime h8 h9;
  lemma_reveal_modifies_1 xxprime h9 h10;
  lemma_reveal_modifies_1 zzprime h10 h11;
  lemma_reveal_modifies_1 x3 h11 h12;
  lemma_reveal_modifies_1 zzzprime h12 h13;
  lemma_reveal_modifies_1 z3 h13 h14;
  lemma_reveal_modifies_1 xx h14 h15;
  lemma_reveal_modifies_1 zz h15 h16;
  let s = Set.union (Set.singleton (frameOf tmp)) (Set.singleton (frameOf ppx)) in
  lemma_set_union (Set.singleton (frameOf tmp)) (frameOf tmp);
  lemma_set_union s (frameOf tmp);
  lemma_set_union s (frameOf ppx);
  lemma_modifies_composition (Set.singleton (frameOf tmp)) (frameOf tmp) h8 h9 h10;
  lemma_modifies_composition (Set.singleton (frameOf tmp)) (frameOf tmp) h8 h10 h11;
  lemma_modifies_composition (Set.singleton (frameOf tmp)) (frameOf ppx) h8 h11 h12;
  lemma_modifies_composition s (frameOf tmp) h8 h12 h13;
  lemma_modifies_composition s (frameOf ppx) h8 h13 h14;
  lemma_modifies_composition s (frameOf tmp) h8 h14 h15;
  lemma_modifies_composition s (frameOf tmp) h8 h15 h16


private val lemma_fmonty__3_modifies:
  tmp:buffer limb{length tmp = 40} ->
  ppx:felem -> ppz:felem -> ppqx:felem -> ppqz:felem ->
  px:felem -> pz:felem -> pqx:felem -> pqz:felem ->
  qx:felem ->
  h16:mem -> h17:mem -> h18:mem -> h19:mem -> h20:mem -> h21:mem ->
  Lemma
    (requires (
      let zz         = Buffer.sub tmp 20ul 5ul in
      let zzz        = Buffer.sub tmp 10ul 5ul in
      live h16 ppx /\ live h16 ppz /\ live h16 ppqx /\ live h16 ppqz
      /\ live h16 px /\ live h16 pz /\ live h16 pqx /\ live h16 pqz
      /\ live h16 qx /\ live h16 tmp
      /\ all_disjoint ppx ppz ppqx ppqz px pz pqx pqz qx
      /\ same_frame ppx ppz ppqx ppqz px pz pqx pqz
      /\ frameOf ppx <> frameOf tmp /\ frameOf ppx <> frameOf qx /\ frameOf qx <> frameOf tmp
      /\ modifies_1 ppx h16 h17
      /\ modifies_1 zz h17 h18
      /\ modifies_1 zzz h18 h19
      /\ modifies_1 zzz h19 h20
      /\ modifies_1 ppz h20 h21
      ))
    (ensures (modifies (Set.union (Set.singleton (frameOf tmp)) (Set.singleton (frameOf ppx))) h16 h21))
#reset-options "--initial_fuel 0 --max_fuel 0 --z3rlimit 100"
private let lemma_fmonty__3_modifies tmp x2 z2 x3 z3 px pz pqx pqz qx h16 h17 h18 h19 h20 h21 =
  let ppx = x2 in
  let zz         = Buffer.sub tmp 20ul 5ul in
  let zzz        = Buffer.sub tmp 10ul 5ul in
  lemma_reveal_modifies_1 x2 h16 h17;
  lemma_reveal_modifies_1 zz h17 h18;
  lemma_reveal_modifies_1 zzz h18 h19;
  lemma_reveal_modifies_1 zzz h19 h20;
  lemma_reveal_modifies_1 z2 h20 h21;
  let s = Set.union (Set.singleton (frameOf tmp)) (Set.singleton (frameOf ppx)) in
  let s' = Set.union (Set.singleton (frameOf ppx)) (Set.singleton (frameOf tmp)) in
  lemma_set_union s' (frameOf tmp);
  lemma_set_union s' (frameOf ppx);
  lemma_modifies_composition (Set.singleton (frameOf ppx)) (frameOf tmp) h16 h17 h18;
  lemma_modifies_composition s' (frameOf tmp) h16 h18 h19;
  lemma_modifies_composition s' (frameOf tmp) h16 h19 h20;
  lemma_modifies_composition s' (frameOf ppx) h16 h20 h21;
  cut (modifies (Set.union s' (Set.singleton (frameOf ppx))) h16 h21);
  Set.lemma_equal_intro s s'


[@"substitute"]
private val fmonty__1:
  tmp:buffer limb{length tmp = 40} ->
  ppx:felem -> ppz:felem -> ppqx:felem -> ppqz:felem ->
  px:felem -> pz:felem -> pqx:felem -> pqz:felem ->
  qx:felem -> Stack unit
    (requires (fun h ->
      live h ppx /\ live h ppz /\ live h ppqx /\ live h ppqz
      /\ live h px /\ live h pz /\ live h pqx /\ live h pqz
      /\ live h qx /\ live h tmp
      /\ red_513 (as_seq h px) /\ red_513 (as_seq h pz) /\ red_513 (as_seq h pqx) /\ red_513 (as_seq h pqz)
      /\ red_513 (as_seq h qx)
      /\ all_disjoint ppx ppz ppqx ppqz px pz pqx pqz qx
      /\ same_frame ppx ppz ppqx ppqz px pz pqx pqz
      /\ frameOf ppx <> frameOf tmp /\ frameOf ppx <> frameOf qx /\ frameOf qx <> frameOf tmp))
    (ensures (fun h0 _ h1 ->
      live h0 ppx /\ live h0 ppz /\ live h0 ppqx /\ live h0 ppqz
      /\ live h0 px /\ live h0 pz /\ live h0 pqx /\ live h0 pqz
      /\ live h0 qx /\ live h0 tmp
      /\ live h1 ppx /\ live h1 ppz /\ live h1 ppqx /\ live h1 ppqz
      /\ live h1 px /\ live h1 pz /\ live h1 pqx /\ live h1 pqz
      /\ live h1 tmp /\ live h1 qx
      /\ red_513 (as_seq h0 px) /\ red_513 (as_seq h0 pz) /\ red_513 (as_seq h0 pqx) /\ red_513 (as_seq h0 pqz)
      /\ red_513 (as_seq h0 qx)
      /\ all_disjoint ppx ppz ppqx ppqz px pz pqx pqz qx
      /\ red_53 (as_seq h1 px) /\ red_5413 (as_seq h1 pz)
      /\ red_513 (as_seq h1 (Buffer.sub tmp 25ul 5ul))
      /\ red_513 (as_seq h1 (Buffer.sub tmp 30ul 5ul))
      /\ (as_seq h1 px, as_seq h1 pz, as_seq h1 (Buffer.sub tmp 25ul 5ul), as_seq h1 (Buffer.sub tmp 30ul 5ul)) == fmonty_tot_1 (as_seq h0 px) (as_seq h0 pz) (as_seq h0 pqx) (as_seq h0 pqz) (as_seq h0 qx)
      /\ as_seq h1 qx == as_seq h0 qx
      /\ modifies (Set.union (Set.singleton (frameOf tmp)) (Set.singleton (frameOf ppx))) h0 h1
    ))
#reset-options "--initial_fuel 0 --max_fuel 0 --z3rlimit 200"
[@"substitute"]
private let fmonty__1 buf x2 z2 x3 z3 x z xprime zprime qx =
  let origx      = Buffer.sub buf 0ul  5ul in
  let origxprime = Buffer.sub buf 5ul  5ul in
  let zzz        = Buffer.sub buf 10ul 5ul in
  let xx         = Buffer.sub buf 15ul 5ul in
  let zz         = Buffer.sub buf 20ul 5ul in
  let xxprime    = Buffer.sub buf 25ul 5ul in
  let zzprime    = Buffer.sub buf 30ul 5ul in
  let zzzprime   = Buffer.sub buf 35ul 5ul in
  let h0 = ST.get() in
  blit x 0ul origx 0ul 5ul;
  let h1 = ST.get() in
  Hacl.Spec.Bignum.Fmul.lemma_whole_slice (as_seq h0 x);
  Hacl.Spec.Bignum.Fmul.lemma_whole_slice (as_seq h1 origx);
  Hacl.Spec.EC.AddAndDouble.fsum_513_is_53 (as_seq h1 x) (as_seq h1 z);
  fsum x z; // x < x + z
  let h2 = ST.get() in
  Hacl.Spec.EC.AddAndDouble.lemma_fdifference_unrolled'' (as_seq h2 z) (as_seq h2 origx);
  Hacl.Spec.EC.AddAndDouble.lemma_fdifference_unrolled''' (as_seq h2 z) (as_seq h2 origx);
  fdifference z origx; // z <- 8p + x - z
  let h3 = ST.get() in
  blit xprime 0ul origxprime 0ul 5ul;
  let h4 = ST.get() in
  Hacl.Spec.Bignum.Fmul.lemma_whole_slice (as_seq h3 xprime);
  Hacl.Spec.Bignum.Fmul.lemma_whole_slice (as_seq h4 origxprime);
  Hacl.Spec.EC.AddAndDouble.fsum_513_is_53 (as_seq h4 xprime) (as_seq h4 zprime);
  fsum xprime zprime; // xprime <- xprime + zprime
  let h5 = ST.get() in
  Hacl.Spec.EC.AddAndDouble.lemma_fdifference_unrolled'' (as_seq h5 zprime) (as_seq h5 origxprime);
  fdifference zprime origxprime; // zprime <- 8p + xprime - zprime
  let h6 = ST.get() in
  Hacl.Spec.EC.AddAndDouble.fmul_53_55_is_fine (as_seq h6 xprime) (as_seq h6 z);
  fmul xxprime xprime z; // xxprime <- sum * sub
  let h7 = ST.get() in
  Hacl.Spec.EC.AddAndDouble.fmul_53_55_is_fine (as_seq h7 x) (as_seq h7 zprime);
  fmul zzprime x zprime; // zzprime <- sum * sub
  let h8 = ST.get() in
  lemma_fmonty__1_modifies buf x2 z2 x3 z3 x z xprime zprime qx h0 h1 h2 h3 h4 h5 h6 h7 h8;
  ()


[@"substitute"]
private val fmonty__2:
  tmp:buffer limb{length tmp = 40} ->
  ppx:felem -> ppz:felem -> ppqx:felem -> ppqz:felem ->
  px:felem -> pz:felem -> pqx:felem -> pqz:felem ->
  qx:felem -> Stack unit
    (requires (fun h ->
      live h ppx /\ live h ppz /\ live h ppqx /\ live h ppqz
      /\ live h px /\ live h pz /\ live h pqx /\ live h pqz
      /\ live h qx /\ live h tmp
      /\ red_513 (as_seq h qx)
      /\ red_53 (as_seq h px) /\ red_5413 (as_seq h pz)
      /\ red_513 (as_seq h (Buffer.sub tmp 25ul 5ul))
      /\ red_513 (as_seq h (Buffer.sub tmp 30ul 5ul))
      /\ all_disjoint ppx ppz ppqx ppqz px pz pqx pqz qx
      /\ same_frame ppx ppz ppqx ppqz px pz pqx pqz
      /\ frameOf ppx <> frameOf tmp /\ frameOf ppx <> frameOf qx /\ frameOf qx <> frameOf tmp))
    (ensures (fun h0 _ h1 ->
      let xx         = Buffer.sub tmp 15ul 5ul in
      let zz         = Buffer.sub tmp 20ul 5ul in
      let xxprime    = Buffer.sub tmp 25ul 5ul in
      let zzprime    = Buffer.sub tmp 30ul 5ul in
      live h0 ppx /\ live h0 ppz /\ live h0 ppqx /\ live h0 ppqz
      /\ live h0 px /\ live h0 pz /\ live h0 pqx /\ live h0 pqz
      /\ live h0 qx /\ live h0 tmp
      /\ live h1 ppx /\ live h1 ppz /\ live h1 ppqx /\ live h1 ppqz
      /\ live h1 px /\ live h1 pz /\ live h1 pqx /\ live h1 pqz
      /\ live h1 tmp /\ live h1 qx
      /\ red_513 (as_seq h0 qx)
      /\ red_53 (as_seq h0 px) /\ red_5413 (as_seq h0 pz)
      /\ red_513 (as_seq h0 xxprime)
      /\ red_513 (as_seq h0 zzprime)
      /\ all_disjoint ppx ppz ppqx ppqz px pz pqx pqz qx
      /\ red_513 (as_seq h1 xx) /\ red_513 (as_seq h1 zz)
      /\ red_513 (as_seq h1 ppqx) /\ red_513 (as_seq h1 ppqz)
      /\ (as_seq h1 ppqx, as_seq h1 ppqz, as_seq h1 xx, as_seq h1 zz) ==
          fmonty_tot_2 (as_seq h0 px) (as_seq h0 pz) (as_seq h0 qx) (as_seq h0 xxprime)
                      (as_seq h0 zzprime)
      /\ as_seq h1 qx == as_seq h0 qx
      /\ modifies (Set.union (Set.singleton (frameOf tmp)) (Set.singleton (frameOf ppx))) h0 h1
    ))
#reset-options "--initial_fuel 0 --max_fuel 0 --z3rlimit 1500"
[@"substitute"]
private let fmonty__2 buf x2 z2 x3 z3 x z xprime zprime qx =
  let origx      = Buffer.sub buf 0ul  5ul in
  let origxprime = Buffer.sub buf 5ul  5ul in
  let zzz        = Buffer.sub buf 10ul 5ul in
  let xx         = Buffer.sub buf 15ul 5ul in
  let zz         = Buffer.sub buf 20ul 5ul in
  let xxprime    = Buffer.sub buf 25ul 5ul in
  let zzprime    = Buffer.sub buf 30ul 5ul in
  let zzzprime   = Buffer.sub buf 35ul 5ul in
  let h8 = ST.get() in
  blit xxprime 0ul origxprime 0ul 5ul;
  let h9 = ST.get() in
  Hacl.Spec.Bignum.Fmul.lemma_whole_slice (as_seq h8 xxprime);
  Hacl.Spec.Bignum.Fmul.lemma_whole_slice (as_seq h9 origxprime);
  no_upd_lemma_1 h8 h9 origxprime zzprime;
  no_upd_lemma_1 h8 h9 origxprime xxprime;
  Hacl.Spec.EC.AddAndDouble.fsum_513_is_53 (as_seq h9 xxprime) (as_seq h9 zzprime);
  fsum xxprime zzprime; // xxprime <- sum xxprime' = xxprime + zzprime
  let h10 = ST.get() in
  no_upd_lemma_1 h9 h10 xxprime zzprime;
  no_upd_lemma_1 h9 h10 xxprime origxprime;
  Hacl.Spec.EC.AddAndDouble.lemma_fdifference_unrolled''' (as_seq h10 zzprime) (as_seq h10 origxprime);
  fdifference zzprime origxprime; // zzprime <- sub zzprime' = xxprime - zzprime
  let h11 = ST.get() in
  no_upd_lemma_1 h10 h11 zzprime xxprime;
  lemma_53_is_5413 (as_seq h11 xxprime);
  Hacl.Spec.Bignum.Fsquare.fsquare_5413_is_fine (as_seq h11 xxprime);
  fsquare_times x3 xxprime 1ul; // sum sum x3 = xxprime' * xxprime'
  let h12 = ST.get() in
  no_upd_lemma_1 h11 h12 x3 zzprime;
  Hacl.Spec.Bignum.Fsquare.fsquare_5413_is_fine (as_seq h12 zzprime);
  fsquare_times zzzprime zzprime 1ul; // sub sub zzzprime = zzprime' * zzprime'
  let h13 = ST.get() in
  no_upd_lemma_1 h8 h9 origxprime qx;
  no_upd_lemma_1 h9 h10 xxprime qx;
  no_upd_lemma_1 h10 h11 zzprime qx;
  no_upd_lemma_1 h11 h12 x3 qx;
  no_upd_lemma_1 h12 h13 zzzprime qx;
  lemma_513_is_53 (as_seq h13 zzzprime);
  lemma_513_is_55 (as_seq h13 qx);
  Hacl.Spec.EC.AddAndDouble.fmul_53_55_is_fine (as_seq h13 zzzprime) (as_seq h13 qx);
  fmul z3 zzzprime qx; // z3 = zzzprime * qx
  let h14 = ST.get() in
  no_upd_lemma_1 h8 h9 origxprime x;
  no_upd_lemma_1 h9 h10 xxprime x;
  no_upd_lemma_1 h10 h11 zzprime x;
  no_upd_lemma_1 h11 h12 x3 x;
  no_upd_lemma_1 h12 h13 zzzprime x;
  no_upd_lemma_1 h13 h14 z3 x;
  lemma_53_is_5413 (as_seq h14 x);
  Hacl.Spec.Bignum.Fsquare.fsquare_5413_is_fine (as_seq h14 x);
  fsquare_times xx x 1ul; // sum red xx = x * x
  let h15 = ST.get() in
  no_upd_lemma_1 h8 h9 origxprime z;
  no_upd_lemma_1 h9 h10 xxprime z;
  no_upd_lemma_1 h10 h11 zzprime z;
  no_upd_lemma_1 h11 h12 x3 z;
  no_upd_lemma_1 h12 h13 zzzprime z;
  no_upd_lemma_1 h13 h14 z3 z;
  no_upd_lemma_1 h14 h15 xx z;
  Hacl.Spec.Bignum.Fsquare.fsquare_5413_is_fine (as_seq h15 z);
  fsquare_times zz z 1ul; // red sub zz = z * z
  let h16 = ST.get() in
  lemma_fmonty__2_modifies buf x2 z2 x3 z3 x z xprime zprime qx h8 h9 h10 h11 h12 h13 h14 h15 h16;
  ()


#reset-options "--initial_fuel 0 --max_fuel 0 --z3rlimit 100"

[@"substitute"]
private val fmonty__3:
  tmp:buffer limb{length tmp = 40} ->
  ppx:felem -> ppz:felem -> ppqx:felem -> ppqz:felem ->
  px:felem -> pz:felem -> pqx:felem -> pqz:felem ->
  qx:felem -> Stack unit
    (requires (fun h ->
      let xx         = Buffer.sub tmp 15ul 5ul in
      let zz         = Buffer.sub tmp 20ul 5ul in
      live h ppx /\ live h ppz /\ live h ppqx /\ live h ppqz
      /\ live h px /\ live h pz /\ live h pqx /\ live h pqz
      /\ live h qx /\ live h tmp
      /\ red_513 (as_seq h ppqx) /\ red_513 (as_seq h ppqz)
      /\ red_513 (as_seq h xx) /\ red_513 (as_seq h zz)
      /\ red_513 (as_seq h qx)
      /\ all_disjoint ppx ppz ppqx ppqz px pz pqx pqz qx
      /\ same_frame ppx ppz ppqx ppqz px pz pqx pqz
      /\ frameOf ppx <> frameOf tmp /\ frameOf ppx <> frameOf qx /\ frameOf qx <> frameOf tmp))
    (ensures (fun h0 _ h1 ->
      let xx         = Buffer.sub tmp 15ul 5ul in
      let zz         = Buffer.sub tmp 20ul 5ul in
      live h0 ppx /\ live h0 ppz /\ live h0 ppqx /\ live h0 ppqz
      /\ live h0 px /\ live h0 pz /\ live h0 pqx /\ live h0 pqz
      /\ live h0 qx /\ live h0 tmp
      /\ live h1 ppx /\ live h1 ppz /\ live h1 ppqx /\ live h1 ppqz
      /\ live h1 px /\ live h1 pz /\ live h1 pqx /\ live h1 pqz
      /\ live h1 tmp /\ live h1 qx
      /\ red_513 (as_seq h0 ppqx) /\ red_513 (as_seq h0 ppqz)
      /\ red_513 (as_seq h0 xx) /\ red_513 (as_seq h0 zz)
      /\ red_513 (as_seq h0 qx)
      /\ all_disjoint ppx ppz ppqx ppqz px pz pqx pqz qx
      /\ red_513 (as_seq h1 ppx) /\ red_513 (as_seq h1 ppz)
      /\ red_513 (as_seq h1 ppqx) /\ red_513 (as_seq h1 ppqz)
      /\ (as_seq h1 ppx, as_seq h1 ppz, as_seq h1 ppqx, as_seq h1 ppqz) ==
          fmonty_tot_3 (as_seq h0 ppqx) (as_seq h0 ppqz) (as_seq h0 xx) (as_seq h0 zz)
      /\ as_seq h1 qx == as_seq h0 qx
      /\ modifies (Set.union (Set.singleton (frameOf tmp)) (Set.singleton (frameOf ppx))) h0 h1
    ))


private let lemma_5413_is_55 (s:seqelem{red_5413 s}) : Lemma (Hacl.Spec.EC.AddAndDouble.red_55 s) = ()

#reset-options "--initial_fuel 0 --max_fuel 0 --z3rlimit 1500"
[@"substitute"]
private let fmonty__3 buf x2 z2 x3 z3 x z xprime zprime qx =
  let origx      = Buffer.sub buf 0ul  5ul in
  let origxprime = Buffer.sub buf 5ul  5ul in
  let zzz        = Buffer.sub buf 10ul 5ul in
  let xx         = Buffer.sub buf 15ul 5ul in
  let zz         = Buffer.sub buf 20ul 5ul in
  let xxprime    = Buffer.sub buf 25ul 5ul in
  let zzprime    = Buffer.sub buf 30ul 5ul in
  let zzzprime   = Buffer.sub buf 35ul 5ul in
  let h16 = ST.get() in
  lemma_513_is_53 (as_seq h16 xx);
  lemma_513_is_55 (as_seq h16 zz);
  Hacl.Spec.EC.AddAndDouble.fmul_53_55_is_fine (as_seq h16 xx)  (as_seq h16 zz);
  fmul x2 xx zz; // red red
  let h17 = ST.get() in
  no_upd_lemma_1 h16 h17 x2 zz;
  no_upd_lemma_1 h16 h17 x2 xx;
  Hacl.Spec.EC.AddAndDouble.lemma_fdifference_unrolled''' (as_seq h17 zz) (as_seq h17 xx);
  fdifference zz xx; // red red
  let h18 = ST.get() in
  let scalar = (uint64_to_limb Hacl.Bignum.Constants.a24) in
  Hacl.Spec.EC.AddAndDouble.fscalar_is_fine (as_seq h18 zz) scalar;
  fscalar zzz zz scalar;
  let h19 = ST.get() in
  lemma_513_is_52 (as_seq h19 xx);
  no_upd_lemma_1 h17 h18 zz xx;
  no_upd_lemma_1 h18 h19 zzz xx;
  Hacl.Spec.EC.AddAndDouble.fsum_52_is_53 (as_seq h19 zzz) (as_seq h19 xx);
  fsum zzz xx; // red red
  let h20 = ST.get() in
  no_upd_lemma_1 h18 h19 zzz zz;
  no_upd_lemma_1 h19 h20 zzz zz;
  lemma_5413_is_55 (as_seq h20 zz);
  Hacl.Spec.EC.AddAndDouble.fmul_53_55_is_fine (as_seq h20 zzz) (as_seq h20 zz);
  fmul z2 zzz zz;
  let h21 = ST.get() in
  lemma_fmonty__3_modifies buf x2 z2 x3 z3 x z xprime zprime qx h16 h17 h18 h19 h20 h21;
  ()



[@"substitute"]
private val fmonty__:
  tmp:buffer limb{length tmp = 40} ->
  ppx:felem -> ppz:felem -> ppqx:felem -> ppqz:felem ->
  px:felem -> pz:felem -> pqx:felem -> pqz:felem ->
  qx:felem -> Stack unit
    (requires (fun h ->
      live h ppx /\ live h ppz /\ live h ppqx /\ live h ppqz
      /\ live h px /\ live h pz /\ live h pqx /\ live h pqz
      /\ live h qx /\ live h tmp
      /\ red_513 (as_seq h px) /\ red_513 (as_seq h pz) /\ red_513 (as_seq h pqx) /\ red_513 (as_seq h pqz)
      /\ red_513 (as_seq h qx)
      /\ all_disjoint ppx ppz ppqx ppqz px pz pqx pqz qx
      /\ same_frame ppx ppz ppqx ppqz px pz pqx pqz
      /\ frameOf ppx <> frameOf tmp /\ frameOf ppx <> frameOf qx /\ frameOf qx <> frameOf tmp))
    (ensures (fun h0 _ h1 ->
      live h0 ppx /\ live h0 ppz /\ live h0 ppqx /\ live h0 ppqz
      /\ live h0 px /\ live h0 pz /\ live h0 pqx /\ live h0 pqz
      /\ live h0 qx /\ live h0 tmp
      /\ live h1 ppx /\ live h1 ppz /\ live h1 ppqx /\ live h1 ppqz
      /\ live h1 px /\ live h1 pz /\ live h1 pqx /\ live h1 pqz
      /\ live h1 tmp /\ live h1 qx
      /\ red_513 (as_seq h0 px) /\ red_513 (as_seq h0 pz) /\ red_513 (as_seq h0 pqx) /\ red_513 (as_seq h0 pqz)
      /\ red_513 (as_seq h0 qx)
      /\ all_disjoint ppx ppz ppqx ppqz px pz pqx pqz qx
      /\ red_513 (as_seq h1 ppx) /\ red_513 (as_seq h1 ppz)
      /\ red_513 (as_seq h1 ppqx) /\ red_513 (as_seq h1 ppqz)
      /\ (as_seq h1 ppx, as_seq h1 ppz, as_seq h1 ppqx, as_seq h1 ppqz) ==
          fmonty_tot (as_seq h0 px) (as_seq h0 pz) (as_seq h0 pqx) (as_seq h0 pqz) (as_seq h0 qx)
      /\ modifies (Set.union (Set.singleton (frameOf tmp)) (Set.singleton (frameOf ppx))) h0 h1
      /\ as_seq h1 qx == as_seq h0 qx
    ))
#reset-options "--initial_fuel 0 --max_fuel 0 --z3rlimit 150"
[@"substitute"]
private let fmonty__ buf x2 z2 x3 z3 x z xprime zprime qx =
  let origx      = Buffer.sub buf 0ul  5ul in
  let origxprime = Buffer.sub buf 5ul  5ul in
  let zzz        = Buffer.sub buf 10ul 5ul in
  let xx         = Buffer.sub buf 15ul 5ul in
  let zz         = Buffer.sub buf 20ul 5ul in
  let xxprime    = Buffer.sub buf 25ul 5ul in
  let zzprime    = Buffer.sub buf 30ul 5ul in
  let zzzprime   = Buffer.sub buf 35ul 5ul in
  let h0 = ST.get() in
  fmonty__1 buf x2 z2 x3 z3 x z xprime zprime qx;
  let h1 = ST.get() in
  fmonty__2 buf x2 z2 x3 z3 x z xprime zprime qx;
  let h2 = ST.get() in
  fmonty__3 buf x2 z2 x3 z3 x z xprime zprime qx;
  let h3 = ST.get() in
  lemma_fmonty_split (as_seq h0 x) (as_seq h0 z) (as_seq h0 xprime) (as_seq h0 zprime) (as_seq h0 qx);
  ()


#reset-options "--initial_fuel 0 --max_fuel 0 --z3rlimit 10"

open Hacl.EC.Point

let same_frame_p (p:point) (q:point) =
  frameOf (getx p) = frameOf (gety p)
  /\ frameOf (getx p) = frameOf (getz p)
  /\ frameOf (getx p) = frameOf (getx q)
  /\ frameOf (getx p) = frameOf (gety q)
  /\ frameOf (getx p) = frameOf (getz q)


let fmonty_pre h (pp:point) (ppq:point) (p:point) (pq:point) (q:point) : GTot Type0 =
  live h pp /\ live h ppq /\ live h p /\ live h pq /\ live h q
  /\ same_frame_p pp ppq /\ same_frame_p pp p /\ same_frame_p pp pq
  /\ frameOf (getx q) = frameOf(gety q) /\ frameOf (getx q) = frameOf (getz q) /\ frameOf (getx q) <> frameOf (getx pp)
  /\ all_disjoint (getx pp) (getz pp) (getx ppq) (getz ppq) (getx p) (getz p) (getx pq) (getz pq) (getx q)
  /\ red_513 (as_seq h (getx p)) /\ red_513 (as_seq h (getz p)) /\ red_513 (as_seq h (getx pq)) /\ red_513 (as_seq h (getz pq))
  /\ red_513 (as_seq h (getx q))


#reset-options "--initial_fuel 0 --max_fuel 0 --z3rlimit 100"

private val lemma_fmonty_modifies: h0:mem -> h1:mem -> h2:mem -> h3:mem -> h4:mem -> r:HS.rid -> Lemma
    (requires (
      fresh_frame h0 h1
      /\ modifies_0 h1 h2
      /\ modifies (Set.union (Set.singleton (HS.get_tip h1)) (Set.singleton r)) h2 h3
      /\ popped h3 h4))
    (ensures (modifies (Set.singleton r) h0 h4))
private let lemma_fmonty_modifies h0 h1 h2 h3 h4 r1 =
  lemma_reveal_modifies_0 h1 h2


val fmonty:
  pp:point ->
  ppq:point ->
  p:point ->
  pq:point ->
  q:point ->
  Stack unit
    (requires (fun h -> fmonty_pre h pp ppq p pq q
    ))
    (ensures (fun h0 _ h1 -> fmonty_pre h0 pp ppq p pq q
      /\ live h1 pp /\ live h1 ppq /\ live h1 p /\ live h1 pq /\ live h1 q
      /\ HyperStack.modifies_one (frameOf (getx pp)) h0 h1
      /\ red_513 (as_seq h1 (getx pp))
      /\ red_513 (as_seq h1 (getz pp))
      /\ red_513 (as_seq h1 (getx ppq))
      /\ red_513 (as_seq h1 (getz ppq))
      /\ (as_seq h1 (getx pp), as_seq h1 (getz pp), as_seq h1 (getx ppq), as_seq h1 (getz ppq)) ==
          fmonty_tot (as_seq h0 (getx p)) (as_seq h0 (getz p)) (as_seq h0 (getx pq)) (as_seq h0 (getz pq)) (as_seq h0 (getx q))
    ))
#reset-options "--initial_fuel 0 --max_fuel 0 --z3rlimit 100"
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
  let hinit = ST.get() in
  push_frame();
  let h0 = ST.get() in
  let buf = create limb_zero 40ul in
  let h1 = ST.get() in
  fmonty__ buf x2 z2 x3 z3 x z xprime zprime qx;
  let h2 = ST.get() in
  pop_frame();
  let hfin = ST.get() in
  lemma_fmonty_modifies hinit h0 h1 h2 hfin (frameOf x2);
  cut(live hfin pp /\ live hfin ppq /\ live hfin p /\ live hfin pq /\ live hfin qmqp);
  cut (HyperStack.modifies_one (frameOf (getx pp)) hinit hfin);
  cut (red_513 (as_seq hfin (getx pp)) /\ red_513 (as_seq hfin (getz pp))
      /\ red_513 (as_seq hfin (getx ppq)) /\ red_513 (as_seq hfin (getz ppq)) );
  cut ( (as_seq hfin (getx pp), as_seq hfin (getz pp), as_seq hfin (getx ppq), as_seq hfin (getz ppq)) ==
          fmonty_tot (as_seq hinit (getx p)) (as_seq hinit (getz p)) (as_seq hinit (getx pq)) (as_seq hinit (getz pq)) (as_seq hinit (getx qmqp)) )
