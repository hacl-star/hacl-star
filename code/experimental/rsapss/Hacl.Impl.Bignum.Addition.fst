module Hacl.Impl.Bignum.Addition

open FStar.HyperStack
open FStar.HyperStack.ST
open FStar.Mul

open LowStar.Buffer

open Lib.IntTypes
open Lib.Buffer

open Hacl.Impl.Bignum.Core
open Hacl.Impl.Bignum.Convert

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
     #aLen:bn_len
  -> #bLen:bn_len
  -> a:lbignum aLen
  -> b:lbignum bLen
  -> carry:lbignum 1ul
  -> res:lbignum aLen
  -> Stack unit
    (requires fun h ->
      live h a /\ live h b /\ live h res /\ live h carry)
    (ensures  fun h0 _ h1 ->
      modifies (loc_union (loc carry) (loc res)) h0 h1)
let bn_sub_ #aLen #bLen a b carry res =
  let h0 = ST.get () in
  let inv h1 i = modifies (loc_union (loc carry) (loc res)) h0 h1 in
  Lib.Loops.for 0ul aLen inv
  (fun i ->
    let t1 = a.(i) in
    let t2 = bval bLen b i in
    let c, res_i = subborrow_u64 carry.(size 0) t1 t2 in
    carry.(size 0) <- c;
    res.(i) <- res_i
  )

val bn_sub:
     #aLen:bn_len
  -> #bLen:bn_len{v bLen <= v aLen}
  -> a:lbignum aLen
  -> b:lbignum bLen
  -> res:lbignum aLen
  -> Stack uint64
    (requires fun h -> live h a /\ live h b /\ live h res)
    (ensures  fun h0 _ h1 -> modifies (loc res) h0 h1)
[@"c_inline"]
let bn_sub #aLen #bLen a b res =
  push_frame ();
  let carry = create 1ul (u64 0) in
  bn_sub_ a b carry res;
  let res = carry.(0ul) in
  pop_frame ();
  res

inline_for_extraction noextract
val bn_add_:
     #aLen:bn_len
  -> #bLen:bn_len
  -> a:lbignum aLen
  -> b:lbignum bLen
  -> carry:lbignum 1ul
  -> res:lbignum aLen
  -> Stack unit
    (requires fun h -> live h a /\ live h b /\ live h res /\ live h carry)
    (ensures  fun h0 _ h1 -> modifies (loc_union (loc carry) (loc res)) h0 h1)
let bn_add_ #aLen #bLen a b carry res =
  let h0 = ST.get () in
  let inv h1 i = modifies (loc_union (loc carry) (loc res)) h0 h1 in
  Lib.Loops.for 0ul aLen inv
  (fun i ->
    let t1 = a.(i) in
    let t2 = bval bLen b i in
    let c, res_i = addcarry_u64 carry.(0ul) t1 t2 in
    carry.(0ul) <- c;
    res.(i) <- res_i
  )

val bn_add:
     #aLen:bn_len
  -> #bLen:bn_len{v bLen <= v aLen}
  -> a:lbignum aLen
  -> b:lbignum bLen
  -> res:lbignum aLen
  -> Stack uint64
    (requires fun h -> live h a /\ live h b /\ live h res)
    (ensures  fun h0 _ h1 ->
         modifies (loc res) h0 h1 /\
         as_snat h1 res = as_snat h0 a + as_snat h0 b)
[@"c_inline"]
let bn_add #aLen #bLen a b res =
  push_frame ();
  let carry = create 1ul (u64 0) in
  bn_add_ a b carry res;
  let res = carry.(0ul) in
  pop_frame ();
  admit();
  res

val bn_add_full:
     #aLen:bn_len{v aLen + 1 <= maxint U32}
  -> #bLen:bn_len{v bLen <= v aLen}
  -> a:lbignum aLen
  -> b:lbignum bLen
  -> res:lbignum (aLen +. 1ul)
  -> Stack unit
    (requires fun h -> live h a /\ live h b /\ live h res)
    (ensures  fun h0 _ h1 ->
         modifies (loc res) h0 h1 /\
         as_snat h1 res = as_snat h0 a + as_snat h0 b)
[@"c_inline"]
let bn_add_full #aLen #bLen a b res =
  push_frame ();
  let carry = sub res aLen 1ul in
  let res_prefix = sub res 0ul aLen in
  bn_add_ a b carry res_prefix;
  pop_frame ();
  admit()
