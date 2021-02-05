module Hacl.IntTypes.Intrinsics

open FStar.HyperStack.All
open FStar.HyperStack
module ST = FStar.HyperStack.ST

open Lib.IntTypes
open Lib.Buffer

open FStar.Mul

#set-options "--fuel 0 --ifuel 0 --z3rlimit 100"


inline_for_extraction noextract
let add_carry_st (t:inttype{t = U32 \/ t = U64}) =
    cin:uint_t t SEC
  -> x:uint_t t SEC
  -> y:uint_t t SEC
  -> r:lbuffer (uint_t t SEC) (size 1) ->
  Stack (uint_t t SEC)
  (requires fun h -> live h r /\ v cin <= 1)
  (ensures  fun h0 c h1 ->
    modifies1 r h0 h1 /\ v c <= 1 /\
    (let r = Seq.index (as_seq h1 r) 0 in
    v r + v c * pow2 (bits t) == v x + v y + v cin))


inline_for_extraction noextract
val add_carry: #t:inttype{t = U32 \/ t = U64} -> add_carry_st t
let add_carry #t cin x y r =
  let res = x +. cin +. y in
  let c = logand (logor (lt_mask res x) (logand (eq_mask res x) cin)) (uint #t 1) in
  r.(0ul) <- res;
  logand_lemma (eq_mask res x) cin;
  logor_lemma (lt_mask res x) (logand (eq_mask res x) cin);
  logand_mask (logor (lt_mask res x) (logand (eq_mask res x) cin)) (uint #t 1) 1;
  c


val add_carry_u32: add_carry_st U32
let add_carry_u32 cin x y r = add_carry #U32 cin x y r

val add_carry_u64: add_carry_st U64
let add_carry_u64 cin x y r = add_carry #U64 cin x y r


inline_for_extraction noextract
let sub_borrow_st (t:inttype{t = U32 \/ t = U64}) =
    cin:uint_t t SEC
  -> x:uint_t t SEC
  -> y:uint_t t SEC
  -> r:lbuffer (uint_t t SEC) (size 1) ->
  Stack (uint_t t SEC)
  (requires fun h -> live h r /\ v cin <= 1)
  (ensures  fun h0 c h1 ->
    modifies1 r h0 h1 /\ v c <= 1 /\
    (let r = Seq.index (as_seq h1 r) 0 in
    v r - v c * pow2 (bits t) == v x - v y - v cin))


inline_for_extraction noextract
val sub_borrow: #t:inttype{t = U32 \/ t = U64} -> sub_borrow_st t
let sub_borrow #t cin x y r =
  let res = x -. y -. cin in
  let c = logand (logor (gt_mask res x) (logand (eq_mask res x) cin)) (uint #t 1) in
  logand_lemma (eq_mask res x) cin;
  logor_lemma (gt_mask res x) (logand (eq_mask res x) cin);
  logand_mask (logor (gt_mask res x) (logand (eq_mask res x) cin)) (uint #t 1) 1;
  r.(0ul) <- res;
  c


val sub_borrow_u32: sub_borrow_st U32
let sub_borrow_u32 cin x y r = sub_borrow #U32 cin x y r

val sub_borrow_u64: sub_borrow_st U64
let sub_borrow_u64 cin x y r = sub_borrow #U64 cin x y r
