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


#set-options "--z3timeout 20"

val copy_from_wide_spec_: s:seqelem_wide{copy_from_wide_pre s} ->
  i:nat{i <= len} ->
  tmp:seqelem{(forall (j:nat). (j >= i /\ j < len) ==> v (Seq.index tmp j) = w (Seq.index s j))} ->
  Tot (s':seqelem{(forall (j:nat). j < len ==> v (Seq.index s' j) = w (Seq.index s j))})
let rec copy_from_wide_spec_ s i tmp =
  if i = 0 then tmp
  else (
    let i = i - 1 in
    let si = Seq.index s i in
    let tmpi = wide_to_limb si in
    Math.Lemmas.modulo_lemma (w si) (pow2 n);
    let tmp' = Seq.upd tmp i tmpi in
    copy_from_wide_spec_ s i tmp'
  )


#set-options "--z3timeout 5"

val copy_from_wide_spec: s:seqelem_wide{copy_from_wide_pre s} ->
  Tot (s':seqelem{(forall (j:nat). j < len ==> v (Seq.index s' j) = w (Seq.index s j))})
let rec copy_from_wide_spec s =
  let tmp = Seq.create len limb_zero in
  copy_from_wide_spec_ s len tmp


#set-options "--z3timeout 50"

val copy_from_wide_:
  output:felem ->
  input:felem_wide{disjoint output input} ->
  ctr:U32.t{U32.v ctr <= len} ->
  Stack unit
    (requires (fun h -> live h output /\ live h input /\ copy_from_wide_pre (as_seq h input)
      /\ (forall (i:nat). (i >= U32.v ctr /\ i < len) ==> v (get h output i) == w (get h input i))))
    (ensures (fun h0 _ h1 -> live h0 input /\ copy_from_wide_pre (as_seq h0 input) /\ live h1 output
      /\ modifies_1 output h0 h1
      /\ as_seq h1 output == copy_from_wide_spec (as_seq h0 input) ))
let rec copy_from_wide_ output input ctr =
  if U32 (ctr =^ 0ul) then (
    let h = ST.get() in
    assert(forall (i:nat). i < len ==> v (Seq.index (as_seq h output) i) = w (Seq.index (as_seq h input) i));
    Seq.lemma_eq_intro (as_seq h output) (copy_from_wide_spec (as_seq h input))
  )
  else (
    let i = U32 (ctr -^ 1ul) in
    let inputi = input.(i) in
    Math.Lemmas.modulo_lemma (w inputi) (pow2 n);
    output.(i) <- wide_to_limb inputi;
    copy_from_wide_ output input i
  )


#set-options "--z3timeout 5"

val shift_spec: seqelem -> Tot seqelem
let shift_spec s =
  let sfirst = Seq.slice s 0 (len - 1) in
  let slast = Seq.slice s (len-1) len in
  Seq.append slast sfirst

#set-options "--z3timeout 50"

val shift_:
  output:felem ->
  ctr:U32.t{U32.v ctr < len} ->
  Stack unit
    (requires (fun h -> live h output))
    (ensures (fun h0 _ h1 -> live h0 output /\ live h1 output /\ modifies_1 output h0 h1
      /\ (forall (i:nat). (i < U32.v ctr) ==> v (get h1 output (i+1)) = v (get h0 output i))
      /\ (forall (i:nat). (i > U32.v ctr /\ i < len) ==> get h1 output i == get h0 output i)))
let rec shift_ output ctr =
  let open FStar.UInt32 in
  if (ctr =^ 0ul) then ()
  else (
    let z = output.(ctr -^ 1ul) in
    output.(ctr) <- z;
    shift_ output (ctr -^ 1ul)
  )

#set-options "--z3timeout 50"


val shift:
  output:felem ->
  Stack unit
    (requires (fun h -> live h output))
    (ensures (fun h0 _ h1 -> live h0 output /\ live h1 output /\ modifies_1 output h0 h1
      /\ as_seq h1 output == shift_spec (as_seq h0 output)))
let rec shift output =
  let h0 = ST.get() in
  let open FStar.UInt32 in
  let tmp = output.(clen -^ 1ul) in
  shift_ output (clen -^ 1ul);
  output.(0ul) <- tmp;
  let h = ST.get() in
  Seq.lemma_eq_intro (as_seq h output) (shift_spec (as_seq h0 output))

#set-options "--z3timeout 20 --initial_fuel 1 --max_fuel 1"

open FStar.Mul

let sum_scalar_multiplication_pre_ (sw:seqelem_wide) (s:seqelem) (scalar:limb) (i:nat{i <= len}) : GTot Type0 =
  (forall (j:nat). j < i ==> w (Seq.index sw j) + (v (Seq.index s j) * v scalar) < pow2 wide_n)


val sum_scalar_multiplication_spec:
  sw:seqelem_wide ->
  s:seqelem ->
  scalar:limb ->
  i:nat{i <= len /\ sum_scalar_multiplication_pre_ sw s scalar i} ->
  Tot seqelem_wide
  (decreases i)
let rec sum_scalar_multiplication_spec sw s scalar i =
  if i = 0 then sw
  else (
    let j = i - 1 in
    let swi = Seq.index sw j in
    let si = Seq.index s j in
    let open Hacl.Bignum.Wide in
    let swi' = swi +^ (mul_wide si scalar) in
    let sw' = Seq.upd sw j swi' in
    sum_scalar_multiplication_spec sw' s scalar j
  )


#set-options "--z3timeout 20 --initial_fuel 1 --max_fuel 1"

val sum_scalar_multiplication_:
  output:felem_wide ->
  input:felem{disjoint output input} ->
  s:limb ->
  ctr:U32.t{U32.v ctr <= len} ->
  Stack unit
    (requires (fun h -> live h output /\ live h input /\ sum_scalar_multiplication_pre_ (as_seq h output) (as_seq h input) s (U32.v ctr)))
    (ensures (fun h0 _ h1 -> live h1 output /\ modifies_1 output h0 h1 /\ live h0 input /\ live h0 output
      /\ sum_scalar_multiplication_pre_ (as_seq h0 output) (as_seq h0 input) s (U32.v ctr)
      /\ (as_seq h1 output) == sum_scalar_multiplication_spec (as_seq h0 output) (as_seq h0 input) s (U32.v ctr)))
let rec sum_scalar_multiplication_ output input s ctr =
  if U32 (ctr =^ 0ul) then ()
  else (
    let i = U32 (ctr -^ 1ul) in
    let oi = output.(i) in let ii = input.(i) in
    let open Hacl.Bignum.Wide in
    output.(i) <- (oi +^ (ii *^ s));
    let h = ST.get() in
    sum_scalar_multiplication_ output input s i
  )


let shift_reduce_pre (s:seqelem) : GTot Type0 = reduce_pre (shift_spec s)

val shift_reduce_spec: s:seqelem{shift_reduce_pre s} -> Tot (s':seqelem)
let shift_reduce_spec s =
  reduce_spec (shift_spec s)


val shift_reduce: output:felem -> Stack unit
  (requires (fun h -> live h output /\ shift_reduce_pre (as_seq h output)))
  (ensures (fun h0 _ h1 -> live h0 output /\ live h1 output /\ modifies_1 output h0 h1
    /\ shift_reduce_pre (as_seq h0 output)
    /\ as_seq h1 output == shift_reduce_spec (as_seq h0 output)))
let shift_reduce output =
  shift output;
  reduce output



let rec mul_shift_reduce_pre (output:seqelem_wide) (input:seqelem) (input2:seqelem) (ctr:nat{ctr <= len}) : GTot Type0 (decreases ctr) =
  if ctr > 0 then (
    sum_scalar_multiplication_pre_ output input (Seq.index input2 (len-ctr)) len
    /\ (let output' = sum_scalar_multiplication_spec output input (Seq.index input2 (len-ctr)) len in
       (ctr > 1 ==> shift_reduce_pre input) /\
         (let input'  = if ctr > 1 then shift_reduce_spec input else input in
          mul_shift_reduce_pre output' input' input2 (ctr-1))))
          else true


val mul_shift_reduce_spec:
  output:seqelem_wide ->
  input:seqelem -> input2:seqelem ->
  ctr:nat{ctr <= len /\ mul_shift_reduce_pre output input input2 ctr} ->
  Tot seqelem_wide
  (decreases ctr)
let rec mul_shift_reduce_spec output input input2 ctr =
  if ctr = 0 then output
  else (
    let i = ctr - 1 in
    let j = len - i - 1 in
    let input2j = Seq.index input2 j in
    let output' = sum_scalar_multiplication_spec output input input2j len in
    let input'  = if ctr > 1 then shift_reduce_spec input else input in
    mul_shift_reduce_spec output' input' input2 i
  )

#set-options "--z3timeout 50 --initial_fuel 1 --max_fuel 1"

val mul_shift_reduce_:
  output:felem_wide ->
  input:felem{disjoint output input} ->
  input2:felem{disjoint output input2 /\ disjoint input input2}  ->
  ctr:U32.t{U32.v ctr <= len} ->
  Stack unit
    (requires (fun h -> live h output /\ live h input /\ live h input2
      /\ mul_shift_reduce_pre (as_seq h output) (as_seq h input) (as_seq h input2) (U32.v ctr)))
    (ensures (fun h0 _ h1 -> live h0 output /\ live h0 input /\ live h0 input2 /\ modifies_2 output input h0 h1
      /\ live h1 output /\ live h1 input
      /\ mul_shift_reduce_pre (as_seq h0 output) (as_seq h0 input) (as_seq h0 input2) (U32.v ctr)
      /\ as_seq h1 output == mul_shift_reduce_spec (as_seq h0 output) (as_seq h0 input) (as_seq h0 input2) (U32.v ctr)))
let rec mul_shift_reduce_ output input input2 ctr =
  let open FStar.UInt32 in
  if (ctr =^ 0ul) then ()
  else (
    let h0 = ST.get() in
    let i = ctr -^ 1ul in
    let j = clen -^ 1ul -^ i in
    let input2i = input2.(j) in
    sum_scalar_multiplication_ output input input2i clen;
    if (ctr >^ 1ul) then shift_reduce input;
    mul_shift_reduce_ output input input2 i
  )


#set-options "--z3timeout 10 --initial_fuel 1 --max_fuel 1"

let carry_wide_pre (s:seqelem_wide) (i:nat{i < len}) : GTot Type0 =
  w (Seq.index s i) < pow2 wide_n
  /\ (forall (j:nat). (j > i /\ j < len) ==> w (Seq.index s j) < pow2 (wide_n - 1))


#set-options "--lax"

val carry_wide_spec: s:seqelem_wide -> i:nat{i < len} -> Tot (s':seqelem_wide)
let rec carry_wide_spec s i =
  if i = len - 1 then s
  else (
    let si = Seq.index s i in
    let sip1 = Seq.index s (i+1) in
    let r0 = wide_to_limb si &^ ((limb_one <<^ climb_size) -^ limb_one) in
    let open Hacl.Bignum.Wide in
    let c = wide_to_limb (si >>^ climb_size) in
    let s' = Seq.upd s i (limb_to_wide r0) in
    let s'' = Seq.upd s (i+1) (sip1 +^ limb_to_wide c) in
    carry_wide_spec s'' (i+1)
  )


val carry_wide_:
  t:felem_wide ->
  ctr:U32.t ->
  Stack unit
    (requires (fun h -> live h t /\ carry_wide_pre (as_seq h t) (U32.v ctr)))
    (ensures (fun h0 _ h1 -> live h0 t /\ live h1 t /\ modifies_1 t h0 h1
      /\ carry_wide_pre (as_seq h0 t) (U32.v ctr)
      /\ as_seq h1 t == carry_wide_spec (as_seq h0 t) (U32.v ctr)))
let rec carry_wide_ t ctr =
  if U32 (ctr =^ clen -^ 1ul) then ()
  else (
    let tctr = t.(ctr) in
    let tctrp1 = t.(U32 (ctr+^1ul)) in
    let r0 = wide_to_limb (tctr) &^ ((limb_one <<^ climb_size) -^ limb_one) in
    let open Hacl.Bignum.Wide in
    let c  = wide_to_limb (tctr >>^ climb_size) in
    t.(ctr) <- limb_to_wide r0;
    t.(U32 (ctr +^ 1ul)) <- tctrp1 +^ limb_to_wide c;
    carry_wide_ t (U32 (ctr +^ 1ul))
  )

  
val fmul:
  output:felem ->
  input:felem{disjoint output input} ->
  input2:felem{disjoint output input2 /\ disjoint input input2} ->
  Stack unit
    (requires (fun h -> live h output /\ live h input /\ live h input2))
    (ensures (fun h0 _ h1 -> modifies_2 output input h0 h1 /\ live h1 output /\ live h1 input))
let fmul output input input2 =
  push_frame();
  let tmp = create limb_zero clen in
  let t   = create wide_zero clen in
  blit input 0ul tmp 0ul clen;
  mul_shift_reduce_ t tmp input2 clen;
  carry_wide_ t 0ul;
  reduce_wide t;
  copy_from_wide_ output t clen;
  let output0 = output.(0ul) in
  let output1 = output.(1ul) in
  let c = output0 >>^ climb_size in
  output.(0ul) <- output0 &^ ((limb_one <<^ climb_size) -^ limb_one);
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
  let tmp = create limb_zero clen in
  blit input 0ul tmp 0ul clen;
  fsquare_times_ tmp count;
  blit tmp 0ul output 0ul clen;
  pop_frame()
