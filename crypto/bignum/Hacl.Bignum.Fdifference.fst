module Hacl.Bignum.Fdifference

open FStar.HyperStack
open FStar.Buffer

open Hacl.Bignum.Parameters
open Hacl.Bignum.Bigint
open Hacl.Bignum.Limb


module U32 = FStar.UInt32

type seqelem = s:Seq.seq limb{Seq.length s = len}


let gte_limbs (a:seqelem) (b:seqelem) (l:nat{l <= len}) : GTot Type0 =
  (forall (i:nat). {:pattern (Seq.index a i) \/ (Seq.index b i)} i < l ==> v (Seq.index b i) >= v (Seq.index a i))


val fdifference_spec:
  a:seqelem -> b:seqelem ->
  ctr:nat{ctr <= len /\ gte_limbs a b ctr} ->
  Tot seqelem (decreases ctr)
let rec fdifference_spec a b ctr =
  if ctr = 0 then a
  else (
    let i = ctr - 1 in
    let ai = Seq.index a i in
    let bi = Seq.index b i in
    let a' = Seq.upd a i (bi -^ ai) in
    fdifference_spec a' b i
  )


let gte_limbs_c h (a:felem) h' (b:felem) (l:nat{l <= len}) : GTot Type0 =
  live h a /\ live h' b /\ gte_limbs (as_seq h a) (as_seq h' b) l


val fdifference_:
  a:felem ->
  b:felem{disjoint a b} ->
  i:ctr{U32.v i <= len} ->
  Stack unit
    (requires (fun h -> gte_limbs_c h a h b (U32.v i)))
    (ensures (fun h0 _ h1 -> gte_limbs_c h0 a h0 b (U32.v i) /\ live h1 a
      /\ as_seq h1 a == fdifference_spec (as_seq h0 a) (as_seq h0 b) (U32.v i)))
let rec fdifference_ a b i =
  if U32 (i =^ 0ul) then ()
  else (
    let i = U32 (i -^ 1ul) in
    let ai = a.(i) in let bi = b.(i) in
    a.(i) <- bi -^ ai;
    fdifference_ a b i
  )


(* val fdifference: *)
(*   a:felem -> *)
(*   b:felem -> *)
(*   Stack unit *)
(*     (requires (fun h -> gte_limbs_c h b h a len)) *)
(*     (ensures  (fun h0 _ h1 -> is_subtraction h1 a h0 b 0)) *)
(* let fdifference a b = *)
(*   fdifference_ a b clen *)
