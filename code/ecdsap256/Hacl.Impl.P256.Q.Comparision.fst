module Hacl.Impl.P256.Q.Comparision

open FStar.HyperStack.All
open FStar.HyperStack
module ST = FStar.HyperStack.ST

open Lib.IntTypes
open Lib.Buffer

open Spec.P256.Definitions



#set-options " --z3rlimit 100"


inline_for_extraction noextract
val unsafe_bool_of_u64: #t:inttype{unsigned t /\ ~(U128? t) /\ ~(S128? t) }  ->
  x: uint_t t SEC {uint_v x == 0 \/ uint_v x == maxint t} -> 
  Tot (b: bool {b <==> v x == 0})

let unsafe_bool_of_u64 #t x = 
  let open Lib.RawIntTypes in
  match t with 
  |U64 -> FStar.UInt64.(u64_to_UInt64 x =^ 0uL)
  |U8 -> FStar.UInt8.(u8_to_UInt8 x =^ 0uy)
  | _ -> admit(); false

(*
(x: uint64 { v x == 0 \/ v x == pow2 64 - 1 }):
  (b:bool { b <==> v x == 0 }) 

let unsafe_bool_of_u64 x = 

  FStar.UInt64.(u64_to_UInt64 x =^ 0uL)
*)

[@(strict_on_arguments [0])]
inline_for_extraction
val eq_int: #t:inttype{unsigned t /\ ~(U128? t) /\ ~(S128? t) } 
  -> #l:secrecy_level 
  -> a: uint_t t l -> b: uint_t t l 
  -> Tot (uint_t t l)

let eq_int #t #l a b = 
  match l with 
  |PUB -> begin
    let r = eq #t a b in 
      eq_lemma #t a b;
    match r with 
    |true -> uint #t #l 0
    |false -> uint #t #l (maxint t)
    end
  |SEC -> 
    neq_mask_lemma #t a b;
    neq_mask #t a b
    

(* [@(strict_on_arguments [0])]
inline_for_extraction *)
inline_for_extraction
val eq_bool: #t:inttype{unsigned t /\ ~(U128? t) /\ ~(S128? t) }  
  -> #l:secrecy_level 
  -> a: uint_t t l -> b: uint_t t l 
  -> Tot bool

let eq_bool #t #l a b = 
  match l with 
  |PUB -> 
    eq #t a b
  |SEC -> 
    neq_mask_lemma #t a b;
    let r = neq_mask a b in 
    unsafe_bool_of_u64 #t r


[@(strict_on_arguments [0])]
inline_for_extraction
val neq_int: #t:inttype{unsigned t /\ ~(U128? t) /\ ~(S128? t) } 
  -> #l:secrecy_level 
  -> a: uint_t t l -> b: uint_t t l 
  -> Tot (uint_t t l)
  
let neq_int #t #l a b = 
  lognot_lemma (eq_int a b);
  lognot (eq_int  a b)

inline_for_extraction
val eq0_int: #t:inttype{unsigned t /\ ~(U128? t) /\ ~(S128? t) } 
  -> #l:secrecy_level 
  -> a: uint_t t l 
  -> Tot (uint_t t l)

let eq0_int #t #l a = 
  eq_int a (uint #t #l 0) 

inline_for_extraction
val neq0_int:#t:inttype{unsigned t /\ ~(U128? t) /\ ~(S128? t) } 
  -> #l:secrecy_level 
  -> a: uint_t t l 
  -> Tot (uint_t t l)

let neq0_int #t #l a = 
  neq_int #t a (uint #t #l 0) 



inline_for_extraction noextract
val eq_felem_0_u64:  f: felem -> Stack uint64
  (requires fun h -> live h f)
  (ensures fun h0 r h1 -> modifies0 h0 h1 /\ 
  (if as_nat h0 f = 0 then uint_v r == pow2 64 - 1 else uint_v r == 0))


let eq_felem_0_u64  f = 
  let a0 = index f (size 0) in 
  let a1 = index f (size 1) in 
  let a2 = index f (size 2) in 
  let a3 = index f (size 3) in 

  let r0 = eq0_int a0 in 
  let r1 = eq0_int a1 in 
  let r2 = eq0_int a2 in 
  let r3 = eq0_int a3 in 

  let r01 = logand r0 r1 in 
  let r23 = logand r2 r3 in 
  let r = logand r01 r23 in 

  logand_lemma r0 r1; 
  logand_lemma r2 r3;
  logand_lemma r01 r23;
  r

inline_for_extraction
val global_to_comparable: glbuffer uint64 (size 4) -> Stack (lbuffer_t IMMUT uint64 (size 4))
  (requires fun h -> True)
  (ensures fun h0 _ h1 -> True)

let global_to_comparable f = (const_to_ilbuffer f) <: lbuffer_t IMMUT uint64 (size 4)

inline_for_extraction
val global_to_comparable_scalar: glbuffer uint8 (size 32) -> Stack (lbuffer_t IMMUT uint8 (size 32))
  (requires fun h -> True)
  (ensures fun h0 _ h1 -> True)

let global_to_comparable_scalar f = (const_to_ilbuffer f) <: lbuffer_t IMMUT uint8 (size 32)




val cmp_felem_felem_u64: #buf_type0: buftype -> #buf_type1: buftype -> 
  a: lbuffer_t buf_type0 uint64 (size 4) -> b: lbuffer_t buf_type1 uint64 (size 4) -> Stack uint64
  (requires fun h -> live h a /\ live h b)
  (ensures fun h0 _ h1 -> True)


let cmp_felem_felem_u64 #b0 #b1 a b = 
  let a_0 = index a (size 0) in 
  let a_1 = index a (size 1) in 
  let a_2 = index a (size 2) in 
  let a_3 = index a (size 3) in 

  let b_0 = index b (size 0) in 
  let b_1 = index b (size 1) in 
  let b_2 = index b (size 2) in 
  let b_3 = index b (size 3) in 

  let r_0 = eq_int #U64 a_0 b_0 in 
  let r_1 = eq_int #U64 a_1 b_1 in
  let r_2 = eq_int #U64 a_2 b_2 in 
  let r_3 = eq_int #U64 a_3 b_3 in 

  let r01 = logand r_0 r_1 in 
  let r23 = logand r_2 r_3 in 
  let r = logand r01 r23 in 

(*
  logand_lemma r_0 r_1;
  logand_lemma r_2 r_3;
  logand_lemma r01 r23;
  
  eq_mask_lemma a_0 b_0;
  eq_mask_lemma a_1 b_1;
  eq_mask_lemma a_2 b_2;
  eq_mask_lemma a_3 b_3; *)
  (* lemma_equality (a_0, a_1, a_2, a_3) (b_0, b_1, b_2, b_3); *)
  r


val cmp_felem_felem_bool: #buf_type0: buftype -> #buf_type1: buftype -> 
  a: lbuffer_t buf_type0 uint64 (size 4) -> b: lbuffer_t buf_type1 uint64 (size 4) -> Stack bool
  (requires fun h -> True)
  (ensures fun h0 _ h1 -> True)


let cmp_felem_felem_bool #b0 #b1 a b = 
  admit();
  let f = cmp_felem_felem_u64 #b0 #b1 a b in 
  unsafe_bool_of_u64 f
