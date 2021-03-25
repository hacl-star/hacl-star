module Hacl.Impl.EC.Masking

open FStar.HyperStack.All
open FStar.HyperStack
module ST = FStar.HyperStack.ST

open Lib.IntTypes
open Lib.Buffer

open Hacl.Spec.P256.Definition
open Lib.Loops

open Spec.ECC
open Spec.ECC.Curves
open Hacl.Lemmas.P256


val copy_conditional: #c: curve 
  -> out: felem c
  -> x: felem c
  -> mask: uint64{uint_v mask = 0 \/ uint_v mask = pow2 64 - 1} -> Stack unit 
  (requires fun h -> live h out /\ live h x)
  (ensures fun h0 _ h1 -> modifies (loc out) h0 h1 /\ (
    if uint_v mask = 0 then as_nat c h1 out == as_nat c h0 out else as_nat c h1 out == as_nat c h0 x)
  ) 


let copy_conditional #c out x mask = 
(*    let h0 = ST.get() in 
  let out_0 = index out (size 0) in 
  let out_1 = index out (size 1) in 
  let out_2 = index out (size 2) in 
  let out_3 = index out (size 3) in 

  let x_0 = index x (size 0) in 
  let x_1 = index x (size 1) in 
  let x_2 = index x (size 2) in 
  let x_3 = index x (size 3) in 

  let r_0 = logxor out_0 (logand mask (logxor out_0 x_0)) in 
  let r_1 = logxor out_1 (logand mask (logxor out_1 x_1)) in 
  let r_2 = logxor out_2 (logand mask (logxor out_2 x_2)) in 
  let r_3 = logxor out_3 (logand mask (logxor out_3 x_3)) in 


  lemma_xor_copy_cond out_0 x_0 mask;
  lemma_xor_copy_cond out_1 x_1 mask;
  lemma_xor_copy_cond out_2 x_2 mask;
  lemma_xor_copy_cond out_3 x_3 mask;

 
  upd out (size 0) r_0;
  upd out (size 1) r_1;
  upd out (size 2) r_2;
  upd out (size 3) r_3;
    let h1 = ST.get() in 

  lemma_eq_funct_ (as_seq h1 out) (as_seq h0 out);
  lemma_eq_funct_ (as_seq h1 out) (as_seq h0 x)
*)
  let h0 = ST.get() in
  
  let len = getCoordinateLenU64 c in 
  let inv h (i: nat { i <= uint_v (getCoordinateLenU64 c)}) = True in 
  for 0ul len inv (fun i -> 
    let h_ = ST.get() in 
    let x_i = index x i in 
    let out_i = index out i in 
    let r_i = logxor out_i (logand mask (logxor out_i x_i)) in 
    upd out i r_i
  )

  


val cmovznz4: #c: curve -> cin: uint64 -> x: felem c -> y: felem c -> result: felem c ->
  Stack unit
  (requires fun h -> live h x /\ live h y /\ live h result /\ disjoint x result /\ eq_or_disjoint y result)
  (ensures fun h0 _ h1 -> modifies1 result h0 h1 /\ (
    if uint_v cin = 0 then as_nat c h1 result == as_nat c h0 x 
    else as_nat c h1 result == as_nat c h0 y)
  )

let cmovznz4 #c  cin x y r =
  let h0 = ST.get() in
  let mask = neq_mask cin (u64 0) in
  
  let len = getCoordinateLenU64 c in 
  let inv h (i: nat { i <= uint_v (getCoordinateLenU64 c)}) = 
    live h x /\ live h y /\ modifies (loc r) h0 h /\ 
    (
      forall (j: nat {j >= i && j < v (getCoordinateLenU64 c)}).
      let y_i = Lib.Sequence.index (as_seq h y) j in 
      let y_0 = Lib.Sequence.index (as_seq h0 y) j in 
      uint_v y_i == uint_v y_0
    ) /\ (
      forall (j: nat {j < i}).
	let x_i = Lib.Sequence.index (as_seq h0 x) j in 
	let y_i = Lib.Sequence.index (as_seq h0 y) j in 
	let r_i = Lib.Sequence.index (as_seq h r) j in 
	if uint_v cin = 0 then 
	  uint_v r_i == uint_v x_i
	else
	  uint_v r_i == uint_v y_i
    ) in 
  for 0ul len inv (fun i -> 
    let h_ = ST.get() in 
    let x_i = index x i in 
    let y_i = index y i in 
    let r_i = logor (logand y_i mask) (logand x_i (lognot mask)) in 
    upd r i r_i;
    cmovznz4_lemma cin (Seq.index (as_seq h0 x) (v i)) (Seq.index (as_seq h0 y) (v i))
  )



val eq0_u64: a: uint64 -> Tot (r: uint64 {if uint_v a = 0 then uint_v r == pow2 64 - 1 else uint_v r == 0})


val eq1_u64: a: uint64 -> Tot (r: uint64 {if uint_v a = 0 then uint_v r == 0 else uint_v r == pow2 64 - 1})


let eq0_u64 a =
  eq_mask_lemma a (u64 0);
  eq_mask a (u64 0)


let eq1_u64 a =
  neq_mask_lemma a (u64 0);
  neq_mask a (u64 0)

