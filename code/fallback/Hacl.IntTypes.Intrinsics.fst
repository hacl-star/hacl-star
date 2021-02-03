module Hacl.IntTypes.Intrinsics

open FStar.HyperStack.All
open FStar.HyperStack
module ST = FStar.HyperStack.ST

open Lib.IntTypes
open Lib.Buffer

open FStar.Mul

#set-options "--fuel 0 --ifuel 0 --z3rlimit 100"
(* 
val add_carry_u64: cin:uint64 -> x:uint64 -> y:uint64 -> r:lbuffer uint64 (size 1) ->
  Stack uint64
    (requires fun h -> live h r /\ v cin <= 1)
    (ensures  fun h0 c h1 ->
      modifies1 r h0 h1 /\ v c <= 1 /\
      (let r = Seq.index (as_seq h1 r) 0 in
       v r + v c * pow2 64 == v x + v y + v cin))


let add_carry_u64 cin x y result1 =
  let res = x +. cin +. y in 
  let c = logand (logor (lt_mask res x) (logand (eq_mask res x) cin)) (u64 1) in 
  result1.(0ul) <- res;
  logand_lemma (eq_mask res x) cin;
  logor_lemma (lt_mask res x) (logand (eq_mask res x) cin);
  logand_mask (logor (lt_mask res x) (logand (eq_mask res x) cin)) (u64 1) 1;
  c


val sub_borrow_u64: cin:uint64 -> x:uint64 -> y:uint64 -> r:lbuffer uint64 (size 1) ->
  Stack uint64
    (requires fun h -> live h r /\ v cin <= 1)
    (ensures  fun h0 c h1 ->
      modifies1 r h0 h1 /\
      (let r = Seq.index (as_seq h1 r) 0 in
       v r - v c * pow2 64 == v x - v y - v cin))

let sub_borrow_u64 cin x y result1 =
  let res = x -. y -. cin in 
  let eqlty = eq_mask res x in 
  let c1 = logand (logor (gt_mask res x) (logand eqlty cin)) (u64 1) in
    logand_lemma eqlty cin;
    logor_lemma (gt_mask res x) (logand eqlty cin);
    logand_mask (logor (gt_mask res x) (logand eqlty cin)) (u64 1) 1;
  result1.(0ul) <- res;
  c1

 *)
[@CInline]
val add_carry_u64: cin:uint64 -> x:uint64 -> y:uint64 -> r:lbuffer uint64 (size 1) ->
  Stack uint64
    (requires fun h -> live h r /\ v cin <= 1)
    (ensures  fun h0 c h1 ->
      modifies1 r h0 h1 /\ v c <= 1 /\
      (let r = Seq.index (as_seq h1 r) 0 in
       v r + v c * pow2 64 == v x + v y + v cin))


let add_carry_u64 cin x y r = 
  let x1 = to_u128 x +. to_u128 y +. to_u128 cin in 
  let x2 = logand x1 (u128 0xffffffffffffffff) in 
  let x3 = shift_right x1 (size 64) in 

  upd r (size 0) (to_u64 x2);
  
  to_u64 x3


[@CInline]
val add_carry_u64_void: cin:uint64 -> x:uint64 -> y:uint64 -> r:lbuffer uint64 (size 1) ->
  Stack unit
    (requires fun h -> live h r /\ v cin <= 1)
    (ensures  fun h0 _ h1 ->
      modifies1 r h0 h1 /\
      (let r = Seq.index (as_seq h1 r) 0 in
       v r  == v x + v y + v cin))


let add_carry_u64_void cin x y r = 
  let x1 = to_u128 x +. to_u128 y +. to_u128 cin in 
  let x2 = logand x1 (u128 0xffffffffffffffff) in 
  upd r (size 0) (to_u64 x2)


[@CInline]
val sub_borrow_u64: cin:uint64 -> x:uint64 -> y:uint64 -> r:lbuffer uint64 (size 1) ->
  Stack uint64
    (requires fun h -> live h r /\ v cin <= 1)
    (ensures  fun h0 c h1 ->
      modifies1 r h0 h1 /\
      (let r = Seq.index (as_seq h1 r) 0 in
       v r - v c * pow2 64 == v x - v y - v cin))

let sub_borrow_u64 cin x y r = 
  let x1 = to_u128 x -. to_u128 y -. to_u128 cin in 
  let x2 = logand x1 (u128 0xffffffffffffffff) in 
  let x3 = shift_right x1 (size 64) in 

  upd r (size 0) (to_u64 x2);
  (u64 0) -. (to_u64 x3)


[@CInline]
val sub_borrow_u64_void: cin:uint64 -> x:uint64 -> y:uint64 -> r:lbuffer uint64 (size 1) ->
  Stack unit
    (requires fun h -> live h r /\ v cin <= 1)
    (ensures  fun h0 _ h1 -> modifies1 r h0 h1 /\
    (let r = Seq.index (as_seq h1 r) 0 in v r == v x - v y - v cin))

let sub_borrow_u64_void cin x y r = 
  let x1 = to_u128 x -. to_u128 y -. to_u128 cin in 
  let x2 = logand x1 (u128 0xffffffffffffffff) in 
  upd r (size 0) (to_u64 x2)
    
