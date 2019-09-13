module Hacl.Impl.Addition

open FStar.HyperStack
open FStar.HyperStack.ST
open FStar.Mul

open LowStar.Buffer

open Lib.IntTypes
open Lib.Buffer

open Hacl.Impl.Lib

module ST = FStar.HyperStack.ST

inline_for_extraction noextract
val addcarry_u64:
    carry:uint64
  -> a:uint64
  -> b:uint64
  -> uint64 & uint64
let addcarry_u64 carry a b =
  let t1 = a +. carry in
  let carry = if lt_u64 t1 carry then u64 1 else u64 0 in
  let res = t1 +. b in
  let carry = if lt_u64 res t1 then carry +. u64 1 else carry in
  carry, res

inline_for_extraction noextract
val subborrow_u64:
    carry:uint64
  -> a:uint64
  -> b:uint64
  -> uint64 & uint64
let subborrow_u64 carry a b =
  let res = a -. b -. carry in
  let carry =
    if eq_u64 carry (u64 1) then
      (if le_u64 a b then u64 1 else u64 0)
    else
      (if lt_u64 a b then u64 1 else u64 0) in
  carry, res

inline_for_extraction noextract
val bn_sub_:
    aLen:size_t
  -> a:lbuffer uint64 (v aLen)
  -> bLen:size_t
  -> b:lbuffer uint64 (v bLen)
  -> carry:lbuffer uint64 1
  -> res:lbuffer uint64 (v aLen)
  -> Stack unit
    (requires fun h ->
      live h a /\ live h b /\ live h res /\ live h carry)
    (ensures  fun h0 _ h1 ->
      modifies (loc_union (loc_buffer carry) (loc_buffer res)) h0 h1)
let bn_sub_ aLen a bLen b carry res =
  let h0 = ST.get () in
  let inv h1 i = modifies (loc_union (loc_buffer carry) (loc_buffer res)) h0 h1 in
  Lib.Loops.for 0ul aLen inv
  (fun i ->
    let t1 = a.(i) in
    let t2 = bval bLen b i in
    let c, res_i = subborrow_u64 carry.(size 0) t1 t2 in
    carry.(size 0) <- c;
    res.(i) <- res_i
  )

val bn_sub:
    aLen:size_t
  -> a:lbuffer uint64 (v aLen)
  -> bLen:size_t{v bLen <= v aLen}
  -> b:lbuffer uint64 (v bLen)
  -> res:lbuffer uint64 (v aLen)
  -> Stack uint64
    (requires fun h -> live h a /\ live h b /\ live h res)
    (ensures  fun h0 _ h1 -> modifies (loc_buffer res) h0 h1)
[@"c_inline"]
let bn_sub aLen a bLen b res =
  push_frame ();
  let carry = create 1ul (u64 0) in
  bn_sub_ aLen a bLen b carry res;
  let res = carry.(0ul) in
  pop_frame ();
  res

inline_for_extraction noextract
val bn_add_:
    aLen:size_t
  -> a:lbuffer uint64 (v aLen)
  -> bLen:size_t
  -> b:lbuffer uint64 (v bLen)
  -> carry:lbuffer uint64 1
  -> res:lbuffer uint64 (v aLen)
  -> Stack unit
    (requires fun h -> live h a /\ live h b /\ live h res /\ live h carry)
    (ensures  fun h0 _ h1 -> modifies (loc_union (loc_buffer carry) (loc_buffer res)) h0 h1)
let bn_add_ aLen a bLen b carry res =
  let h0 = ST.get () in
  let inv h1 i = modifies (loc_union (loc_buffer carry) (loc_buffer res)) h0 h1 in
  Lib.Loops.for 0ul aLen inv
  (fun i ->
    let t1 = a.(i) in
    let t2 = bval bLen b i in
    let c, res_i = addcarry_u64 carry.(0ul) t1 t2 in
    carry.(0ul) <- c;
    res.(i) <- res_i
  )

val bn_add:
    aLen:size_t
  -> a:lbuffer uint64 (v aLen)
  -> bLen:size_t{v bLen <= v aLen}
  -> b:lbuffer uint64 (v bLen)
  -> res:lbuffer uint64 (v aLen)
  -> Stack uint64
    (requires fun h -> live h a /\ live h b /\ live h res)
    (ensures  fun h0 _ h1 -> modifies (loc_buffer res) h0 h1)
[@"c_inline"]
let bn_add aLen a bLen b res =
  push_frame ();
  let carry = create 1ul (u64 0) in
  bn_add_ aLen a bLen b carry res;
  let res = carry.(0ul) in
  pop_frame ();
  res
