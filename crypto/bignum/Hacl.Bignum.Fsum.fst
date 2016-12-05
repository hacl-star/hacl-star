module Hacl.Bignum.Fsum

open FStar.HyperStack
open FStar.Buffer

open Hacl.Bignum.Parameters
open Hacl.Bignum.Bigint
open Hacl.Bignum.Limb
open Hacl.Bignum.Predicates


module U32 = FStar.UInt32


type seqelem = s:Seq.seq limb{Seq.length s = len}


let red (s:seqelem) (l:nat{l <= len}) = (forall (i:nat). (i < l) ==> v (Seq.index s i) < pow2 (n - 1))


val fsum_spec: s:seqelem -> s':seqelem -> ctr:nat{ctr <= len /\ red s ctr /\ red s' ctr} -> Tot seqelem
  (decreases ctr)
let rec fsum_spec a b ctr =
  if ctr = 0 then a
  else (
    let i = ctr - 1 in
    let ai = Seq.index a i in
    let bi = Seq.index b i in
    Math.Lemmas.pow2_double_sum (n-1);
    let a' = Seq.upd a i (ai +^ bi) in
    fsum_spec a' b i
  )


let red_c h (f:felem) ctr = live h f /\ red (as_seq h f) ctr


val fsum_:
  a:felem ->
  b:felem{disjoint a b} ->
  i:ctr{U32.v i <= len} ->
  Stack unit
    (requires (fun h -> red_c h a (U32.v i) /\ red_c h b (U32.v i)))
    (ensures (fun h0 _ h1 -> red_c h0 a (U32.v i) /\ red_c h0 b (U32.v i) /\ live h1 a
      /\ as_seq h1 a == fsum_spec (as_seq h0 a) (as_seq h0 b) (U32.v i)))
let rec fsum_ a b i =
  if U32 (i =^ 0ul) then ()
  else (
    let i = U32 (i -^ 1ul) in
    let ai = a.(i) in let bi = b.(i) in
    Math.Lemmas.pow2_double_sum n;
    a.(i) <- ai +^ bi;
    fsum_ a b i
  )
