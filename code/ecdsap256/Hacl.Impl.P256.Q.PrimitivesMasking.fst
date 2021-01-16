module Hacl.Impl.P256.Q.PrimitivesMasking

open FStar.HyperStack.All
open FStar.HyperStack
module ST = FStar.HyperStack.ST

open Lib.IntTypes

open Lib.Buffer

open Spec.P256.Definitions
open Spec.P256.Lemmas



inline_for_extraction noextract
val copy_conditional: out: felem -> x: felem -> mask: uint64{uint_v mask = 0 \/ uint_v mask = pow2 64 - 1} -> Stack unit 
  (requires fun h -> live h out /\ live h x)
  (ensures fun h0 _ h1 -> modifies (loc out) h0 h1 /\ 
    (if uint_v mask = 0 then as_seq h1 out == as_seq h0 out else as_seq h1 out == as_seq h0 x) /\
    (if uint_v mask = 0 then as_nat h1 out == as_nat h0 out else as_nat h1 out == as_nat h0 x)
  ) 

let copy_conditional out x mask = 
    let h0 = ST.get() in 
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


val cmovznz4: out: felem -> x: felem -> y: felem -> mask: uint64 -> Stack unit
  (requires fun h -> live h out /\ live h x /\ live h y /\ (uint_v mask == 0 \/ uint_v mask = pow2 64 - 1))
  (ensures fun h0 _ h1 -> modifies (loc out) h0 h1 /\ (
    if v mask = 0 then as_nat h1 out == as_nat h0 x else as_nat h1 out == as_nat h0 y))

let cmovznz4 out x y mask = 
  let h0 = ST.get() in 
  
  let out_0 = index out (size 0) in 
  let out_1 = index out (size 1) in 
  let out_2 = index out (size 2) in 
  let out_3 = index out (size 3) in  

  let mask = eq_mask mask (u64 0) in 
  
  let r0 = logor (logand x.(size 0) mask) (logand y.(size 0) (lognot mask)) in 
  let r1 = logor (logand x.(size 1) mask) (logand y.(size 1) (lognot mask)) in 
  let r2 = logor (logand x.(size 2) mask) (logand y.(size 2) (lognot mask)) in 
  let r3 = logor (logand x.(size 3) mask) (logand y.(size 3) (lognot mask)) in 

  upd out (size 0) r0;
  upd out (size 1) r1;
  upd out (size 2) r2;
  upd out (size 3) r3;

  let x = as_seq h0 x in 
  let y = as_seq h0 y in 
  cmovznz4_lemma mask (Seq.index y 0) (Seq.index x 0);
  cmovznz4_lemma mask (Seq.index y 1) (Seq.index x 1);
  cmovznz4_lemma mask (Seq.index y 2) (Seq.index x 2);
  cmovznz4_lemma mask (Seq.index y 3) (Seq.index x 3)


inline_for_extraction noextract
val cmovznz2: uint64 -> uint64 -> mask: uint64 -> Tot (r: uint64)

let cmovznz2 a b mask = 
  logor (logand a mask) (logand b (lognot mask))



inline_for_extraction noextract
val cmovznz01: a: uint64 -> b: uint64 -> mask: uint64 {uint_v mask = 0 \/ uint_v mask = 1} -> 
  Tot (r: uint64 {if uint_v mask = 0 then uint_v r = uint_v a else uint_v r = uint_v b})

let cmovznz01 a b mask = 
  let mask = (u64 0) -. mask in 
  lemma_xor_copy_cond a b mask;
  logxor a (logand mask (logxor a b))


inline_for_extraction noextract
val cmovznz: a: uint64 -> b: uint64 -> mask: uint64 {uint_v mask = 0 \/ uint_v mask = pow2 64 - 1} -> 
  Tot (r: uint64 {if uint_v mask = 0 then uint_v r = uint_v a else uint_v r = uint_v b})

let cmovznz a b mask = 
  lemma_xor_copy_cond a b mask;
  logxor a (logand mask (logxor a b))




val cswap8:  x: widefelem -> y: widefelem -> mask: uint64 -> Stack unit 
  (requires fun h -> True)
  (ensures fun h0 _ h1 -> True)

let cswap8 p1 p2 bit = 
  let open Lib.Sequence in 
  let h0 = ST.get () in
  let mask = bit in

  [@ inline_let]
  let inv h1 (i:nat{i <= 8}) = 
    (forall (k:nat{k < i}).
      if v bit = 1
      then (as_seq h1 p1).[k] == (as_seq h0 p2).[k] /\ (as_seq h1 p2).[k] == (as_seq h0 p1).[k]
      else (as_seq h1 p1).[k] == (as_seq h0 p1).[k] /\ (as_seq h1 p2).[k] == (as_seq h0 p2).[k]) /\
    (forall (k:nat{i <= k /\ k < 12}).
      (as_seq h1 p1).[k] == (as_seq h0 p1).[k] /\ (as_seq h1 p2).[k] == (as_seq h0 p2).[k]) /\
    modifies (loc p1 |+| loc p2) h0 h1 in
 
  Lib.Loops.for 0ul 8ul inv
    (fun i ->
      let dummy = mask &. (p1.(i) ^. p2.(i)) in
      p1.(i) <- p1.(i) ^. dummy;
      p2.(i) <- p2.(i) ^. dummy;
      lemma_cswap2_step bit ((as_seq h0 p1).[v i]) ((as_seq h0 p2).[v i])
    );
  let h1 = ST.get () in
  Lib.Sequence.eq_intro (as_seq h1 p1) (if v bit = 1 then as_seq h0 p2 else as_seq h0 p1);
  Lib.Sequence.eq_intro (as_seq h1 p2) (if v bit = 1 then as_seq h0 p1 else as_seq h0 p2)
