module Hacl.IntTypes.Intrinsics

open FStar.HyperStack.All
open FStar.HyperStack
module ST = FStar.HyperStack.ST

open Lib.IntTypes
open Lib.Buffer

open FStar.Mul

#set-options "--fuel 0 --ifuel 0 --z3rlimit 100"

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
