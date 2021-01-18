module Hacl.Impl.P256.Q.Comparision

open FStar.HyperStack.All
open FStar.HyperStack
module ST = FStar.HyperStack.ST

open Lib.IntTypes
open Lib.Buffer

open Spec.P256.Definitions



#set-options " --z3rlimit 100"

type qualification = 
  |Public
  |Private

let invert_qualif (a: qualification): Lemma
  (requires True) 
  (ensures (inversion qualification))
  [SMTPat (qualification)] =
  allow_inversion (qualification) 


inline_for_extraction noextract
val unsafe_bool_of_u64 (x: uint64 { v x == 0 \/ v x == pow2 64 - 1 }):
  (b:bool { b <==> v x == 0 })

let unsafe_bool_of_u64 x = 
  let open Lib.RawIntTypes in
  FStar.UInt64.(u64_to_UInt64 x =^ 0uL)


val eq_u64_u64_u64: #q: qualification -> a: uint64 -> b: uint64 -> Tot uint64

let eq_u64_u64_u64 #q a b = 
  match q with 
  |Public -> begin
      let open Lib.RawIntTypes in
      let r = FStar.UInt64.(u64_to_UInt64 a =^ u64_to_UInt64 b) in 
      match r with 
      |true -> u64 0
      |false -> u64 (maxint U64) end
  |Private -> 
    eq_mask_lemma a b;
    eq_mask a b


val eq_u64_u64_bool: #q: qualification -> a: uint64 -> b: uint64 -> Tot bool

let eq_u64_u64_bool #q a b = 
  match q with 
  |Public -> 
    let open Lib.RawIntTypes in 
    FStar.UInt64.(u64_to_UInt64 a =^ u64_to_UInt64 b) 
  |Private -> 
    eq_mask_lemma a b;
    let r = eq_mask a b in 
    unsafe_bool_of_u64 r


val neq_u64_u64_u64: #q: qualification -> a: uint64 -> b: uint64 -> Tot uint64

let neq_u64_u64_u64 #q a b = 
  lognot_lemma (eq_u64_u64_u64 #q a b);
  lognot (eq_u64_u64_u64 #q a b)


val eq_u64_0_u64: #q: qualification -> a: uint64 -> Tot uint64

let eq_u64_0_u64 #q a = 
  eq_u64_u64_u64 #q a (u64 0) 


val neq_u64_0_u64: #q: qualification -> a: uint64 -> Tot uint64

let neq_u64_0_u64 #q a = 
  neq_u64_u64_u64 #q a (u64 0)



inline_for_extraction noextract
val eq_felem_0_u64: #q: qualification -> #buf_type: buftype -> f: lbuffer_t buf_type uint64 (size 4) -> Stack uint64
  (requires fun h -> live h f)
  (ensures fun h0 r h1 -> modifies0 h0 h1 /\ 
  (if as_nat h0 f = 0 then uint_v r == pow2 64 - 1 else uint_v r == 0))


let eq_felem_0_u64 #q f = 
  let a0 = index f (size 0) in 
  let a1 = index f (size 1) in 
  let a2 = index f (size 2) in 
  let a3 = index f (size 3) in 

  let r0 = eq_u64_0_u64 #q a0 in 
  let r1 = eq_u64_0_u64 #q a1 in 
  let r2 = eq_u64_0_u64 #q a2 in 
  let r3 = eq_u64_0_u64 #q a3 in 

  let r01 = logand r0 r1 in 
  let r23 = logand r2 r3 in 
  let r = logand r01 r23 in 

  logand_lemma r0 r1; 
  logand_lemma r2 r3;
  logand_lemma r01 r23;
  r


val global_to_comparable: glbuffer uint64 (size 4) -> Stack (lbuffer_t IMMUT uint64 (size 4))
  (requires fun h -> True)
  (ensures fun h0 _ h1 -> True)

let global_to_comparable f = (const_to_ilbuffer f) <: lbuffer_t IMMUT uint64 (size 4)


val global_to_comparable_scalar: glbuffer uint8 (size 32) -> Stack (lbuffer_t IMMUT uint8 (size 32))
  (requires fun h -> True)
  (ensures fun h0 _ h1 -> True)

let global_to_comparable_scalar f = (const_to_ilbuffer f) <: lbuffer_t IMMUT uint8 (size 32)




val cmp_felem_felem_u64: #q:qualification -> #buf_type0: buftype -> #buf_type1: buftype -> 
  a: lbuffer_t buf_type0 uint64 (size 4) -> b: lbuffer_t buf_type1 uint64 (size 4) -> Stack uint64
  (requires fun h -> True)
  (ensures fun h0 _ h1 -> True)


let cmp_felem_felem_u64 #q #b0 #b1 a b = 
  let a_0 = index a (size 0) in 
  let a_1 = index a (size 1) in 
  let a_2 = index a (size 2) in 
  let a_3 = index a (size 3) in 

  let b_0 = index b (size 0) in 
  let b_1 = index b (size 1) in 
  let b_2 = index b (size 2) in 
  let b_3 = index b (size 3) in 

  let r_0 = eq_u64_u64_u64 #q a_0 b_0 in 
  let r_1 = eq_u64_u64_u64 #q a_1 b_1 in
  let r_2 = eq_u64_u64_u64 #q a_2 b_2 in 
  let r_3 = eq_u64_u64_u64 #q a_3 b_3 in 

  let r01 = logand r_0 r_1 in 
  let r23 = logand r_2 r_3 in 
  let r = logand r01 r23 in 
  
  logand_lemma r_0 r_1;
  logand_lemma r_2 r_3;
  logand_lemma r01 r23;
  
  eq_mask_lemma a_0 b_0;
  eq_mask_lemma a_1 b_1;
  eq_mask_lemma a_2 b_2;
  eq_mask_lemma a_3 b_3;
  (* lemma_equality (a_0, a_1, a_2, a_3) (b_0, b_1, b_2, b_3); *)
  r


val cmp_felem_felem_bool: #q:qualification -> #buf_type0: buftype -> #buf_type1: buftype -> 
  a: lbuffer_t buf_type0 uint64 (size 4) -> b: lbuffer_t buf_type1 uint64 (size 4) -> Stack bool
  (requires fun h -> True)
  (ensures fun h0 _ h1 -> True)


let cmp_felem_felem_bool #q #b0 #b1 a b = 
  admit();
  let f = cmp_felem_felem_u64 #q #b0 #b1 a b in 
  unsafe_bool_of_u64 f
