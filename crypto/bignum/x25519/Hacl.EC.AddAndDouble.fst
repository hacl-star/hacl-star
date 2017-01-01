module Hacl.EC.AddAndDouble

open FStar.HyperStack
open FStar.Buffer

open Hacl.Bignum.Constants
open Hacl.Bignum.Parameters
open Hacl.Bignum
open Hacl.Bignum.Fsquare
open Hacl.Spec.EC.AddAndDouble2


#set-options "--initial_fuel 0 --max_fuel 0"

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


inline_for_extraction let red_513 s = Hacl.Spec.EC.AddAndDouble.red_513 s
inline_for_extraction let red_53 s = Hacl.Spec.EC.AddAndDouble.red_53 s
inline_for_extraction let red_5413 s = Hacl.Spec.EC.AddAndDouble.red_5413 s


(* val fmonty_1: *)
(*   tmp:FStar.Buffer.buffer Hacl.UInt64.t{length tmp = 40} -> *)
(*   ppx:felem -> ppz:felem -> ppqx:felem -> ppqz:felem -> *)
(*   px:felem -> pz:felem -> pqx:felem -> pqz:felem -> *)
(*   qx:felem -> *)
(*   Stack unit *)
(*     (requires (fun h -> live h tmp *)
(*       /\ live h ppx /\ live h ppz /\ live h ppqx /\ live h ppqz *)
(*       /\ live h px /\ live h pz /\ live h pqx /\ live h pqz *)
(*       /\ live h qx *)
(*       /\ red_52 (as_seq h px) /\ red_52 (as_seq h pz) /\ red_52 (as_seq h pqx) /\ red_52 (as_seq h pqz) *)
(*       /\ red_52 (as_seq h qx) *)
(*       /\ all_disjoint ppx ppz ppqx ppqz px pz pqx pqz qx *)
(*       /\ disjoint tmp ppx /\ disjoint tmp ppz /\ disjoint tmp ppqx /\ disjoint tmp ppqz *)
(*       /\ disjoint tmp px /\ disjoint tmp pz /\ disjoint tmp pqx /\ disjoint tmp pqz *)
(*       /\ disjoint tmp qx *)
(*       )) *)
(*     (ensures (fun h0 _ h1 -> *)
(*       live h0 ppx /\ live h0 ppz /\ live h0 ppqx /\ live h0 ppqz *)
(*       /\ live h0 px /\ live h0 pz /\ live h0 pqx /\ live h0 pqz *)
(*       /\ live h0 qx /\ live h0 qz *)
(*       /\ live h1 ppx /\ live h1 ppz /\ live h1 ppqx /\ live h1 ppqz *)
(*       /\ red_52 (as_seq h0 px) /\ red_52 (as_seq h0 pz) /\ red_52 (as_seq h0 pqx) /\ red_52 (as_seq h0 pqz) *)
(*       /\ red_52 (as_seq h0 qx) /\ red_52 (as_seq h0 qz) *)
(*       /\ all_disjoint ppx ppz ppqx ppqz px pz pqx pqz qx qz *)
(*       /\ (as_seq h1 ppx, as_seq h1 ppz, as_seq h1 ppqx, as_seq h1 ppqz) == *)
(*           fmonty_tot (as_seq h0 px) (as_seq h0 pz) (as_seq h0 pqx) (as_seq h0 pqz) (as_seq h0 qx) (as_seq h0 qz) *)
(*     )) *)
(* #set-options "--initial_fuel 0 --max_fuel 0 --z3rlimit 100" *)
(* let fmonty_1 buf x2 z2 x3 z3 x z xprime zprime qx = *)
(*   let origx      = Buffer.sub buf 0ul  5ul in *)
(*   let origxprime = Buffer.sub buf 5ul  5ul in *)
(*   let zzz        = Buffer.sub buf 10ul 5ul in *)
(*   let xx         = Buffer.sub buf 15ul 5ul in *)
(*   let zz         = Buffer.sub buf 20ul 5ul in *)
(*   let xxprime    = Buffer.sub buf 25ul 5ul in *)
(*   let zzprime    = Buffer.sub buf 30ul 5ul in *)
(*   let zzzprime   = Buffer.sub buf 35ul 5ul in *)
(*   let h0 = ST.get() in *)
(*   blit x 0ul origx 0ul 5ul; *)
(*   let h1 = ST.get() in *)
(*   Hacl.Spec.Bignum.Fmul.lemma_whole_slice (as_seq h0 x); *)
(*   Hacl.Spec.Bignum.Fmul.lemma_whole_slice (as_seq h1 origx); *)
(*   Hacl.Spec.EC.AddAndDouble.fsum_52_is_53 (as_seq h1 x) (as_seq h1 z); *)
(*   fsum x z; // x < x + z *)
(*   let h2 = ST.get() in *)
(*   Hacl.Spec.EC.AddAndDouble.lemma_fdifference_unrolled' (as_seq h2 z) (as_seq h2 origx); *)
(*   fdifference z origx; // z <- 8p + x - z *)
(*   let h3 = ST.get() in *)
(*   blit xprime 0ul origxprime 0ul 5ul; *)
(*   let h4 = ST.get() in *)
(*   Hacl.Spec.Bignum.Fmul.lemma_whole_slice (as_seq h3 xprime); *)
(*   Hacl.Spec.Bignum.Fmul.lemma_whole_slice (as_seq h4 origxprime); *)
(*   Hacl.Spec.EC.AddAndDouble.fsum_52_is_53 (as_seq h4 xprime) (as_seq h4 zprime); *)
(*   fsum xprime zprime; // xprime <- xprime + zprime *)
(*   let h5 = ST.get() in *)
(*   Hacl.Spec.EC.AddAndDouble.lemma_fdifference_unrolled' (as_seq h5 zprime) (as_seq h5 origxprime); *)
(*   fdifference zprime origxprime; // zprime <- 8p + xprime - zprime *)
(*   let h6 = ST.get() in *)
(*   Hacl.Spec.EC.AddAndDouble.fmul_53_55_is_fine (as_seq h6 xprime) (as_seq h6 z); *)
(*   fmul xxprime xprime z; // xxprime <- sum * sub *)
(*   let h7 = ST.get() in *)
(*   Hacl.Spec.EC.AddAndDouble.fmul_53_55_is_fine (as_seq h7 x) (as_seq h7 zprime); *)
(*   fmul zzprime x zprime; // zzprime <- sum * sub *)
(*   () *)


(* val fmonty_1: *)
(*   tmp:FStar.Buffer.buffer Hacl.UInt64.t{length tmp = 40} -> *)
(*   ppx:felem -> ppz:felem -> ppqx:felem -> ppqz:felem -> *)
(*   px:felem -> pz:felem -> pqx:felem -> pqz:felem -> *)
(*   qx:felem -> *)
(*   Stack unit *)
(*     (requires (fun h -> *)
(*       live h ppx /\ live h ppz /\ live h ppqx /\ live h ppqz *)
(*       /\ live h px /\ live h pz /\ live h pqx /\ live h pqz *)
(*       /\ live h qx /\ live h tmp *)
(*       /\ red_52 (as_seq h px) /\ red_52 (as_seq h pz) /\ red_52 (as_seq h pqx) /\ red_52 (as_seq h pqz) *)
(*       /\ red_52 (as_seq h qx) *)
(*       /\ all_disjoint ppx ppz ppqx ppqz px pz pqx pqz qx *)
(*       /\ disjoint tmp ppx /\ disjoint tmp ppz /\ disjoint tmp ppqx /\ disjoint tmp ppqz *)
(*       /\ disjoint tmp px /\ disjoint tmp pz /\ disjoint tmp pqx /\ disjoint tmp pqz *)
(*       /\ disjoint tmp qx *)
(*       )) *)
(*     (ensures (fun h0 _ h1 -> true)) *)
(* let fmonty_2 buf ppx ppz ppqx ppqz p pz pqx pqz qx = *)
(*   let h8 = ST.get() in *)
(*   blit xxprime 0ul origxprime 0ul 5ul; *)
(*   let h9 = ST.get() in *)
(*   Hacl.Spec.Bignum.Fmul.lemma_whole_slice (as_seq h8 xxprime); *)
(*   Hacl.Spec.Bignum.Fmul.lemma_whole_slice (as_seq h9 origxprime); *)
(*   Hacl.Spec.EC.AddAndDouble.fsum_52_is_53 (as_seq h9 xxprime) (as_seq h9 zzprime); *)
(*   fsum xxprime zzprime; // xxprime <- sum *)
(*   let h10 = ST.get() in *)
(*   Hacl.Spec.EC.AddAndDouble.lemma_fdifference_unrolled' (as_seq h10 zzprime) (as_seq h10 origxprime); *)
(*   fdifference zzprime origxprime; // zzprime <- sub *)
(*   admit() *)
(*   let h11 = ST.get() in *)
(*   fsquare_times x3 xxprime 1ul; // sum sum *)
(*   let h12 = ST.get() in *)
(*   fsquare_times zzzprime zzprime 1ul; // sub sub *)
(*   let h13 = ST.get() in *)
(*   fmul z3 zzzprime qx; *)
(*   let h14 = ST.get() in *)
(*   fsquare_times xx x 1ul; // sum red *)
(*   let h15 = ST.get() in *)
(*   fsquare_times zz z 1ul; // red sub *)
(*   let h16 = ST.get() in *)
(*   fmul x2 xx zz; // red red *)
(*   let h17 = ST.get() in *)
(*   fdifference zz xx; // red red *)
(*   let h18 = ST.get() in *)
(*   fscalar zzz zz (uint64_to_limb Hacl.Bignum.Constants.a24); *)
(*   let h19 = ST.get() in *)
(*   fsum zzz xx; // red red *)
(*   let h20 = ST.get() in *)
(*   fmul z2 zz zzz; *)
(*   pop_frame() *)


(* ********************************************************************************* *)
(* ********************************************************************************* *)

#set-options "--initial_fuel 0 --max_fuel 0 --z3rlimit 10"


val fmonty__1:
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
    ))
#set-options "--initial_fuel 0 --max_fuel 0 --z3rlimit 100"
let fmonty__1 buf x2 z2 x3 z3 x z xprime zprime qx =
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
  ()


val fmonty__2:
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
    ))
#set-options "--initial_fuel 0 --max_fuel 0 --z3rlimit 500"
let fmonty__2 buf x2 z2 x3 z3 x z xprime zprime qx =
  let origx      = Buffer.sub buf 0ul  5ul in
  let origxprime = Buffer.sub buf 5ul  5ul in
  let zzz        = Buffer.sub buf 10ul 5ul in
  let xx         = Buffer.sub buf 15ul 5ul in
  let zz         = Buffer.sub buf 20ul 5ul in
  let xxprime    = Buffer.sub buf 25ul 5ul in
  let zzprime    = Buffer.sub buf 30ul 5ul in
  let zzzprime   = Buffer.sub buf 35ul 5ul in
  let h8 = ST.get() in
  (* cut (red_513 (as_seq h8 xxprime)); *)
  (* cut (red_513 (as_seq h8 zzprime)); *)
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
  (* lemma_53_is_5413 (as_seq h12 zzprime); *)
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
  ()


#set-options "--initial_fuel 0 --max_fuel 0 --z3rlimit 10"

val fmonty__3:
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
    ))

let lemma_5413_is_55 (s:seqelem{red_5413 s}) : Lemma (Hacl.Spec.EC.AddAndDouble.red_55 s) = ()

#set-options "--initial_fuel 0 --max_fuel 0 --z3rlimit 1000"
let fmonty__3 buf x2 z2 x3 z3 x z xprime zprime qx =
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
  fmul z2 zzz zz



val fmonty__:
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
      /\ red_513 (as_seq h0 px) /\ red_513 (as_seq h0 pz) /\ red_513 (as_seq h0 pqx) /\ red_513 (as_seq h0 pqz)
      /\ red_513 (as_seq h0 qx)
      /\ all_disjoint ppx ppz ppqx ppqz px pz pqx pqz qx
      /\ red_513 (as_seq h1 ppx) /\ red_513 (as_seq h1 ppz)
      /\ red_513 (as_seq h1 ppqx) /\ red_513 (as_seq h1 ppqz)
      /\ (as_seq h1 ppx, as_seq h1 ppz, as_seq h1 ppqx, as_seq h1 ppqz) ==
          fmonty_tot (as_seq h0 px) (as_seq h0 pz) (as_seq h0 pqx) (as_seq h0 pqz) (as_seq h0 qx)
    ))
#set-options "--initial_fuel 0 --max_fuel 0 --z3rlimit 10"
let fmonty__ buf x2 z2 x3 z3 x z xprime zprime qx =
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
  (* let h0 = ST.get() in *)
  (* blit x 0ul origx 0ul 5ul; *)
  (* let h1 = ST.get() in *)
  (* Hacl.Spec.Bignum.Fmul.lemma_whole_slice (as_seq h0 x); *)
  (* Hacl.Spec.Bignum.Fmul.lemma_whole_slice (as_seq h1 origx); *)
  (* Hacl.Spec.EC.AddAndDouble.fsum_513_is_53 (as_seq h1 x) (as_seq h1 z); *)
  (* fsum x z; // x < x + z *)
  (* let h2 = ST.get() in *)
  (* Hacl.Spec.EC.AddAndDouble.lemma_fdifference_unrolled'' (as_seq h2 z) (as_seq h2 origx); *)
  (* Hacl.Spec.EC.AddAndDouble.lemma_fdifference_unrolled''' (as_seq h2 z) (as_seq h2 origx); *)
  (* fdifference z origx; // z <- 8p + x - z *)
  (* let h3 = ST.get() in *)
  (* blit xprime 0ul origxprime 0ul 5ul; *)
  (* let h4 = ST.get() in *)
  (* Hacl.Spec.Bignum.Fmul.lemma_whole_slice (as_seq h3 xprime); *)
  (* Hacl.Spec.Bignum.Fmul.lemma_whole_slice (as_seq h4 origxprime); *)
  (* Hacl.Spec.EC.AddAndDouble.fsum_513_is_53 (as_seq h4 xprime) (as_seq h4 zprime); *)
  (* fsum xprime zprime; // xprime <- xprime + zprime *)
  (* let h5 = ST.get() in *)
  (* Hacl.Spec.EC.AddAndDouble.lemma_fdifference_unrolled'' (as_seq h5 zprime) (as_seq h5 origxprime); *)
  (* fdifference zprime origxprime; // zprime <- 8p + xprime - zprime *)
  (* let h6 = ST.get() in *)
  (* Hacl.Spec.EC.AddAndDouble.fmul_53_55_is_fine (as_seq h6 xprime) (as_seq h6 z); *)
  (* fmul xxprime xprime z; // xxprime <- sum * sub *)
  (* let h7 = ST.get() in *)
  (* Hacl.Spec.EC.AddAndDouble.fmul_53_55_is_fine (as_seq h7 x) (as_seq h7 zprime); *)
  (* fmul zzprime x zprime; // zzprime <- sum * sub *)
  (* let h8 = ST.get() in *)
  (* blit xxprime 0ul origxprime 0ul 5ul; *)
  (* let h9 = ST.get() in *)
  (* Hacl.Spec.Bignum.Fmul.lemma_whole_slice (as_seq h8 xxprime); *)
  (* Hacl.Spec.Bignum.Fmul.lemma_whole_slice (as_seq h9 origxprime); *)
  (* Hacl.Spec.EC.AddAndDouble.fsum_513_is_53 (as_seq h9 xxprime) (as_seq h9 zzprime); *)
  (* fsum xxprime zzprime; // xxprime <- sum *)
  (* let h10 = ST.get() in *)
  (* Hacl.Spec.EC.AddAndDouble.lemma_fdifference_unrolled''' (as_seq h10 zzprime) (as_seq h10 origxprime); *)
  (* fdifference zzprime origxprime; // zzprime <- sub *)
  (* let h11 = ST.get() in *)
  (* lemma_53_is_5413 (as_seq h11 xxprime); *)
  (* Hacl.Spec.Bignum.Fsquare.fsquare_5413_is_fine (as_seq h11 xxprime); *)
  (* fsquare_times x3 xxprime 1ul; // sum sum *)
  (* let h12 = ST.get() in *)
  (* lemma_53_is_5413 (as_seq h12 zzprime); *)
  (* Hacl.Spec.Bignum.Fsquare.fsquare_5413_is_fine (as_seq h12 zzprime); *)
  (* fsquare_times zzzprime zzprime 1ul; // sub sub *)
  (* let h13 = ST.get() in *)
  (* lemma_513_is_53 (as_seq h13 zzzprime); lemma_513_is_55 (as_seq h13 qx); *)
  (* fmul z3 zzzprime qx; *)
  (* let h14 = ST.get() in *)
  (* lemma_53_is_5413 (as_seq h14 x); *)
  (* Hacl.Spec.Bignum.Fsquare.fsquare_5413_is_fine (as_seq h14 x); *)
  (* fsquare_times xx x 1ul; // sum red *)
  (* let h15 = ST.get() in *)
  (* Hacl.Spec.Bignum.Fsquare.fsquare_5413_is_fine (as_seq h15 z); *)
  (* fsquare_times zz z 1ul; // red sub *)
  (* let h16 = ST.get() in *)
  (* lemma_513_is_53 (as_seq h16 xx); *)
  (* lemma_513_is_55 (as_seq h16 zz); *)
  (* Hacl.Spec.EC.AddAndDouble.fmul_53_55_is_fine (as_seq h16 xx)  (as_seq h16 zz); *)
  (* fmul x2 xx zz; // red red *)
  (* let h17 = ST.get() in *)
  (* Hacl.Spec.EC.AddAndDouble.lemma_fdifference_unrolled'' (as_seq h17 zz) (as_seq h17 xx); *)
  (* fdifference zz xx; // red red *)
  (* let h18 = ST.get() in *)
  (* let scalar = (uint64_to_limb Hacl.Bignum.Constants.a24) in *)
  (* Hacl.Spec.EC.AddAndDouble.fscalar_is_fine (as_seq h18 zz) scalar; *)
  (* fscalar zzz zz scalar; *)
  (* let h19 = ST.get() in *)
  (* lemma_513_is_52 (as_seq h19 xx); *)
  (* Hacl.Spec.EC.AddAndDouble.fsum_52_is_53 (as_seq h19 zzz) (as_seq h19 xx); *)
  (* fsum zzz xx; // red red *)
  (* let h20 = ST.get() in *)
  (* Hacl.Spec.EC.AddAndDouble.fmul_53_55_is_fine (as_seq h20 zzz) (as_seq h20 zz); *)
  (* fmul z2 zzz zz; *)
  (* pop_frame(); *)
  (* admit() *)


#set-options "--initial_fuel 0 --max_fuel 0 --z3rlimit 10"

val fmonty_:
  ppx:felem -> ppz:felem -> ppqx:felem -> ppqz:felem ->
  px:felem -> pz:felem -> pqx:felem -> pqz:felem ->
  qx:felem -> Stack unit
    (requires (fun h ->
      live h ppx /\ live h ppz /\ live h ppqx /\ live h ppqz
      /\ live h px /\ live h pz /\ live h pqx /\ live h pqz
      /\ live h qx
      /\ red_513 (as_seq h px) /\ red_513 (as_seq h pz) /\ red_513 (as_seq h pqx) /\ red_513 (as_seq h pqz)
      /\ red_513 (as_seq h qx)
      /\ all_disjoint ppx ppz ppqx ppqz px pz pqx pqz qx))
    (ensures (fun h0 _ h1 ->
      live h0 ppx /\ live h0 ppz /\ live h0 ppqx /\ live h0 ppqz
      /\ live h0 px /\ live h0 pz /\ live h0 pqx /\ live h0 pqz
      /\ live h0 qx
      /\ live h1 ppx /\ live h1 ppz /\ live h1 ppqx /\ live h1 ppqz
      /\ red_513 (as_seq h0 px) /\ red_513 (as_seq h0 pz) /\ red_513 (as_seq h0 pqx) /\ red_513 (as_seq h0 pqz)
      /\ red_513 (as_seq h0 qx)
      /\ all_disjoint ppx ppz ppqx ppqz px pz pqx pqz qx
      /\ red_513 (as_seq h1 ppx) /\ red_513 (as_seq h1 ppz)
      /\ red_513 (as_seq h1 ppqx) /\ red_513 (as_seq h1 ppqz)
      /\ (as_seq h1 ppx, as_seq h1 ppz, as_seq h1 ppqx, as_seq h1 ppqz) ==
          fmonty_tot (as_seq h0 px) (as_seq h0 pz) (as_seq h0 pqx) (as_seq h0 pqz) (as_seq h0 qx)
    ))
#set-options "--initial_fuel 0 --max_fuel 0 --z3rlimit 10"
let fmonty_ x2 z2 x3 z3 x z xprime zprime qx =
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
  blit xxprime 0ul origxprime 0ul 5ul;
  let h9 = ST.get() in
  Hacl.Spec.Bignum.Fmul.lemma_whole_slice (as_seq h8 xxprime);
  Hacl.Spec.Bignum.Fmul.lemma_whole_slice (as_seq h9 origxprime);
  Hacl.Spec.EC.AddAndDouble.fsum_513_is_53 (as_seq h9 xxprime) (as_seq h9 zzprime);
  fsum xxprime zzprime; // xxprime <- sum
  let h10 = ST.get() in
  Hacl.Spec.EC.AddAndDouble.lemma_fdifference_unrolled''' (as_seq h10 zzprime) (as_seq h10 origxprime);
  fdifference zzprime origxprime; // zzprime <- sub
  let h11 = ST.get() in
  lemma_53_is_5413 (as_seq h11 xxprime);
  Hacl.Spec.Bignum.Fsquare.fsquare_5413_is_fine (as_seq h11 xxprime);
  fsquare_times x3 xxprime 1ul; // sum sum
  let h12 = ST.get() in
  lemma_53_is_5413 (as_seq h12 zzprime);
  Hacl.Spec.Bignum.Fsquare.fsquare_5413_is_fine (as_seq h12 zzprime);  
  fsquare_times zzzprime zzprime 1ul; // sub sub
  let h13 = ST.get() in
  lemma_513_is_53 (as_seq h13 zzzprime); lemma_513_is_55 (as_seq h13 qx);
  fmul z3 zzzprime qx;
  let h14 = ST.get() in
  lemma_53_is_5413 (as_seq h14 x);
  Hacl.Spec.Bignum.Fsquare.fsquare_5413_is_fine (as_seq h14 x);
  fsquare_times xx x 1ul; // sum red
  let h15 = ST.get() in
  Hacl.Spec.Bignum.Fsquare.fsquare_5413_is_fine (as_seq h15 z);
  fsquare_times zz z 1ul; // red sub
  let h16 = ST.get() in
  lemma_513_is_53 (as_seq h16 xx);
  lemma_513_is_55 (as_seq h16 zz);
  Hacl.Spec.EC.AddAndDouble.fmul_53_55_is_fine (as_seq h16 xx)  (as_seq h16 zz);
  fmul x2 xx zz; // red red
  let h17 = ST.get() in
  Hacl.Spec.EC.AddAndDouble.lemma_fdifference_unrolled'' (as_seq h17 zz) (as_seq h17 xx);
  fdifference zz xx; // red red
  let h18 = ST.get() in
  let scalar = (uint64_to_limb Hacl.Bignum.Constants.a24) in
  Hacl.Spec.EC.AddAndDouble.fscalar_is_fine (as_seq h18 zz) scalar;
  fscalar zzz zz scalar;
  let h19 = ST.get() in
  lemma_513_is_52 (as_seq h19 xx);
  Hacl.Spec.EC.AddAndDouble.fsum_52_is_53 (as_seq h19 zzz) (as_seq h19 xx);
  fsum zzz xx; // red red
  let h20 = ST.get() in
  Hacl.Spec.EC.AddAndDouble.fmul_53_55_is_fine (as_seq h20 zzz) (as_seq h20 zz);
  fmul z2 zzz zz;
  pop_frame();
  admit()


open Hacl.EC.Point

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
