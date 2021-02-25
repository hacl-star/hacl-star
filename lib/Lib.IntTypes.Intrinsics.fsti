module Lib.IntTypes.Intrinsics

open FStar.HyperStack
open FStar.HyperStack.All

open Lib.IntTypes
open Lib.Buffer

open FStar.Mul

#set-options "--z3rlimit 50 --ifuel 0 --fuel 0"

inline_for_extraction
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


val add_carry_u32: add_carry_st U32

val add_carry_u64: add_carry_st U64


inline_for_extraction
let add_carry (#t:inttype{t = U32 \/ t = U64}) : add_carry_st t =
  match t with
  | U32 -> add_carry_u32
  | U64 -> add_carry_u64


inline_for_extraction
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


val sub_borrow_u32: sub_borrow_st U32

val sub_borrow_u64: sub_borrow_st U64


inline_for_extraction
let sub_borrow (#t:inttype{t = U32 \/ t = U64}) : sub_borrow_st t =
  match t with
  | U32 -> sub_borrow_u32
  | U64 -> sub_borrow_u64
