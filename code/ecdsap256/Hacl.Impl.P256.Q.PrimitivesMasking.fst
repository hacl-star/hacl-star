module Hacl.Impl.P256.Q.PrimitivesMasking

open FStar.HyperStack.All
open FStar.HyperStack
module ST = FStar.HyperStack.ST

open Lib.IntTypes

open Lib.Buffer

open Spec.P256.Definitions
open Spec.P256.Lemmas


#set-options "--z3rlimit 300" 

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


val copy_point_conditional_mask_u64_2:  result: point 
  -> x: point -> mask: uint64 {uint_v mask == 0 \/ uint_v mask == pow2 64 - 1}  
  -> Stack unit
  (requires fun h -> live h result /\ live h x /\ disjoint result x)
  (ensures fun h0 _ h1 -> modifies (loc result) h0 h1  /\ (
    if uint_v mask = 0
    then 
      as_nat h1 (gsub result (size 0) (size 4)) == as_nat h0 (gsub result (size 0) (size 4)) /\
      as_nat h1 (gsub result (size 4) (size 4)) == as_nat h0 (gsub result (size 4) (size 4)) /\
      as_nat h1 (gsub result (size 8) (size 4)) == as_nat h0 (gsub result (size 8) (size 4)) 
    else
      as_nat h1 (gsub result (size 0) (size 4)) == as_nat h0 (gsub x (size 0) (size 4)) /\
      as_nat h1 (gsub result (size 4) (size 4)) == as_nat h0 (gsub x (size 4) (size 4)) /\
      as_nat h1 (gsub result (size 8) (size 4)) == as_nat h0 (gsub x (size 8) (size 4)))
  )



let copy_point_conditional_mask_u64_2  result x mask = 
  let h0 = ST.get() in 

  let x_x = sub x (size 0) (size 4) in 
  let x_y = sub x (size 4) (size 4) in 
  let x_z = sub x (size 8) (size 4) in 

  let result_x = sub result (size 0) (size 4) in 
  let result_y = sub result (size 4) (size 4) in 
  let result_z = sub result (size 8) (size 4) in 

  copy_conditional result_x x_x mask;
  copy_conditional result_y x_y mask;
  copy_conditional result_z x_z mask


val copy_point_conditional_mask_u64_3: #buf_type: buftype -> result: point 
  -> x: point -> y: point 
  -> mask: uint64 {uint_v mask == 0 \/ uint_v mask == pow2 64 - 1}  
  -> Stack unit
  (requires fun h -> live h result /\ live h x /\ live h y /\ disjoint result x /\ disjoint result y)
  (ensures fun h0 _ h1 -> modifies (loc result) h0 h1  /\ (
  
  if uint_v mask = 0
  then 
    as_nat h1 (gsub result (size 0) (size 4)) == as_nat h0 (gsub x (size 0) (size 4)) /\
    as_nat h1 (gsub result (size 4) (size 4)) == as_nat h0 (gsub x (size 4) (size 4)) /\
    as_nat h1 (gsub result (size 8) (size 4)) == as_nat h0 (gsub x (size 8) (size 4)) 
  else
    as_nat h1 (gsub result (size 0) (size 4)) == as_nat h0 (gsub y (size 0) (size 4)) /\
    as_nat h1 (gsub result (size 4) (size 4)) == as_nat h0 (gsub y (size 4) (size 4)) /\
    as_nat h1 (gsub result (size 8) (size 4)) == as_nat h0 (gsub y (size 8) (size 4)))
  )


let copy_point_conditional_mask_u64_3 #buf_type result x y mask = 
  let h0 = ST.get() in 

  let x_x = sub x (size 0) (size 4) in 
  let x_y = sub x (size 4) (size 4) in 
  let x_z = sub x (size 8) (size 4) in 

  let y_x = sub y (size 0) (size 4) in 
  let y_y = sub y (size 4) (size 4) in 
  let y_z = sub y (size 8) (size 4) in 

  let result_x = sub result (size 0) (size 4) in 
  let result_y = sub result (size 4) (size 4) in 
  let result_z = sub result (size 8) (size 4) in 

  cmovznz4 result_x x_x y_x mask;
  cmovznz4 result_y x_y y_y mask;
  cmovznz4 result_z x_z y_z mask


inline_for_extraction noextract
val cmovznz2: uint64 -> uint64 -> mask: uint64 -> Tot (r: uint64)

let cmovznz2 a b mask = 
  logor (logand a mask) (logand b (lognot mask))



inline_for_extraction noextract
val cmovznz01: #t:inttype{unsigned t} -> #l:secrecy_level -> a: uint_t t l 
  -> b: uint_t t l -> mask: uint_t t l {uint_v mask = 0 \/ uint_v mask = 1} -> 
  Tot (r: uint_t t l {if uint_v mask = 0 then uint_v r = v a else uint_v r = v b} )

let cmovznz01 a b mask = 
  admit();
  let mask = (u64 0) -. mask in 
  admit();
  lemma_xor_copy_cond a b mask;
  logxor a (logand mask (logxor a b))


inline_for_extraction noextract
val cmovznz: a: uint64 -> b: uint64 -> mask: uint64 {uint_v mask = 0 \/ uint_v mask = pow2 64 - 1} -> 
  Tot (r: uint64 {if uint_v mask = 0 then uint_v r = uint_v a else uint_v r = uint_v b})

let cmovznz a b mask = 
  lemma_xor_copy_cond a b mask;
  logxor a (logand mask (logxor a b))


val maskU8toU64: a: uint8 {v a = 0 \/ v a = pow2 8 - 1} ->
  Tot (b: uint64 {v b = 0 \/ v b = pow2 64 -1 /\ ((v a == 0) ==> (v b == 0)) /\ ((v a == pow2 8 - 1) ==> (v b == pow2 64 - 1))})

let maskU8toU64 a = 
  let a0 = to_u64 a in 
  let a1 = shift_right a0 (size 8) in 
  let a2 = shift_right a0 (size 16) in 
  let a3 = shift_right a0 (size 24) in 
  
  let a4 = shift_right a0 (size 32) in 
  let a5 = shift_right a0 (size 40) in 
  let a6 = shift_right a0 (size 48) in 
  let a7 = shift_right a0 (size 56) in 

  let a01 = logxor a0 a1 in 
  let a23 = logxor a2 a3 in 
  let a45 = logxor a4 a5 in 
  let a67 = logxor a6 a7 in 

  let a03 = logxor a01 a23 in 
  let a47 = logxor a45 a67 in 

  admit();
  logxor a03 a47
    


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
