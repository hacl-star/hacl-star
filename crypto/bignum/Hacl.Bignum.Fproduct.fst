module Hacl.Bignum.Fproduct


open FStar.HyperStack
open FStar.Buffer

open Hacl.Bignum.Parameters
open Hacl.Bignum.Bigint
open Hacl.Bignum.Limb
open Hacl.Bignum.Modulo

module U32 = FStar.UInt32


type seqelem = s:Seq.seq limb{Seq.length s = len}
type seqelem_wide = s:Seq.seq wide{Seq.length s = len}


let copy_from_wide_pre (s:seqelem_wide) : GTot Type0 =
  (forall (i:nat). {:pattern w (Seq.index s i)} i < len ==> w (Seq.index s i) < pow2 n)


val copy_from_wide_spec: s:seqelem_wide{copy_from_wide_pre s} -> i:nat{i <= len} ->
  tmp:seqelem{(forall (j:nat). (j >= i /\ j < len) ==> v (Seq.index tmp j) = w (Seq.index s j))} -> Tot seqelem
let rec copy_from_wide_spec s i tmp =
  if i = 0 then tmp
  else (
    let i = i - 1 in
    let si = Seq.index s i in
    let tmpi = wide_to_limb si in
    Math.Lemmas.modulo_lemma (w si) (pow2 n);
    let tmp' = Seq.upd tmp i tmpi in
    copy_from_wide_spec s i tmp'
  )


val copy_from_wide_:
  output:felem ->
  input:felem_wide ->
  ctr:U32.t{U32.v ctr <= len} ->
  Stack unit
    (requires (fun _ -> true))
    (ensures (fun _ _ _ -> true))
let rec copy_from_wide_ output input ctr =
  if U32 (ctr =^ 0ul) then ()
  else (
    let i = U32 (ctr -^ 1ul) in
    let inputi = input.(i) in
    output.(i) <- Wide.wide_to_limb inputi;
    copy_from_wide_ output input i
  )


val shift_:
  output:felem ->
  tmp:limb ->
  ctr:U32.t ->
  Stack unit
    (requires (fun _ -> true))
    (ensures (fun _ _ _ -> true))
let rec shift_ output tmp ctr =
  let open FStar.UInt32 in
  let tmp = if (ctr =^ clen) then output.(0ul) else tmp in
  if (ctr =^ 1ul) then output.(1ul) <- tmp
  else (
    let z = output.(ctr -^ 1ul) in
    output.((ctr %^ clen)) <- z;
    shift_ output tmp (ctr -^ 1ul)
  )


val sum_scalar_multiplication_:
  output:felem_wide ->
  input:felem ->
  s:limb ->
  ctr:U32.t ->
  Stack unit
    (requires (fun _ -> true))
    (ensures (fun _ _ _ -> true))
let rec sum_scalar_multiplication_ output input s ctr =
  if U32 (ctr =^ 0ul) then ()
  else (
    let i = U32 (ctr -^ 1ul) in
    let oi = output.(i) in let ii = input.(i) in
    let open Hacl.Bignum.Wide in
    output.(i) <- (oi +^ (ii *^ s));
    sum_scalar_multiplication_ output input s i
  )


val mul_shift_reduce_:
  output:felem_wide ->
  input:felem ->
  input2:felem ->
  ctr:U32.t ->
  Stack unit
    (requires (fun _ -> true))
    (ensures (fun _ _ _ -> true))
let rec mul_shift_reduce_ output input input2 ctr =
  let open FStar.UInt32 in
  if (ctr =^ 0ul) then ()
  else (
    let i = ctr -^ 1ul in
    let j = clen -^ 1ul -^ i in
    let input2i = input2.(j) in
    sum_scalar_multiplication_ output input input2i clen;
    if (ctr >^ 1ul) then shift_reduce input (ctemplate j);
    mul_shift_reduce_ output input input2 i
  )

val carry_wide_:
  t:felem_wide ->
  ctr:U32.t ->
  Stack unit
    (requires (fun _ -> true))
    (ensures (fun _ _ _ -> true))
let rec carry_wide_ t ctr =
  if U32 (ctr =^ clen -^ 1ul) then ()
  else (
    let tctr = t.(ctr) in
    let tctrp1 = t.(U32 (ctr+^1ul)) in
    let r0 = Hacl.Bignum.Wide.wide_to_limb (tctr) &^ ((one <<^ ctemplate ctr) -^ 1ul) in
    let open Hacl.Bignum.Wide in
    let c  = Hacl.Bignum.Wide.wide_to_limb (tctr >>^ ctemplate ctr) in
    t.(ctr) <- Hacl.Bignum.Wide.limb_to_wide r0;
    t.(U32 (ctr +^ 1ul)) <- tctrp1 +^ Hacl.Bignum.Wide.limb_to_wide c;
    carry_wide_ t (U32 (ctr +^ 1ul))
  )

  
val fmul:
  output:felem ->
  input:felem ->
  input2:felem ->
  Stack unit
    (requires (fun _ -> true))
    (ensures (fun _ _ _ -> true))
let fmul output input input2 =
  push_frame();
  let tmp = create Wide.zero clen in
  let t   = create Wide.zero clen in
  blit input 0ul tmp 0ul clen;
  mul_shift_reduce_ t tmp input2 clen;
  carry_wide_ t 0ul;
  reduce_wide t;
  (* let tnm1 = t.(U32 (len -^ 1ul)) in *)
  (* let t0   = t.(0ul) in   *)
  (* let c = Wide.wide_to_limb (Wide (tnm1 >>^ (ctemplate (U32 (clen -^ 1ul)))) in *)
  (* t.(U32 (clen -^ 1ul)) <- Wide (tnm1 &^ Wide.limb_to_wide ((one <<^ ctemplate (U32 (clen -^ 1ul))) &^ 1ul)); *)
  (* t.(0ul) <- Wide (t0 +^ (c *^ nineteen)); *)
  copy_from_wide_ output t clen;
  let output0 = output.(0ul) in
  let output1 = output.(1ul) in
  let c = output0 >>^ (ctemplate 0ul) in
  output.(0ul) <- output0 &^ (one <<^ ctemplate (U32 (clen -^ 1ul)) -^ 1uL);
  output.(1ul) <- output1 +^ c;
  pop_frame()

val fsquare_times_:
  input:felem ->
  count:U32.t ->
  Stack unit
    (requires (fun _ -> true))
    (ensures (fun _ _ _ -> true))
let rec fsquare_times_ tmp count =
  if U32 (count =^ 0ul) then ()
  else (
    fmul tmp tmp tmp;
    fsquare_times_ tmp (U32 (count -^ 1ul))
  )


val fsquare_times:
  output:felem ->
  input:felem ->
  count:U32.t ->
  Stack unit
    (requires (fun _ -> true))
    (ensures (fun _ _ _ -> true))
let fsquare_times output input count =
  push_frame();
  let tmp = create zero clen in
  blit input 0ul tmp 0ul clen;
  fsquare_times_ tmp count;
  blit tmp 0ul output 0ul clen;
  pop_frame()
