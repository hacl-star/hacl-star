module Hacl.Bignum.Addition

open FStar.HyperStack
open FStar.HyperStack.ST
open FStar.Mul

open Hacl.Bignum
open Hacl.Bignum.Base

open Lib.IntTypes
open Lib.Buffer

module ST = FStar.HyperStack.ST


#set-options "--z3rlimit 50 --max_fuel 0 --max_ifuel 0"

inline_for_extraction noextract
val bn_sub_:
    aLen:size_t
  -> a:lbignum aLen
  -> bLen:size_t
  -> b:lbignum bLen
  -> carry:lbuffer uint64 1ul
  -> res:lbignum aLen ->
  Stack unit
  (requires fun h ->
    live h a /\ live h b /\ live h res /\ live h carry)
  (ensures  fun h0 _ h1 ->
    modifies (loc carry |+| loc res) h0 h1)

let bn_sub_ aLen a bLen b carry res =
  let h0 = ST.get () in
  let inv h1 i = modifies (loc carry |+| loc res) h0 h1 in
  Lib.Loops.for 0ul aLen inv
  (fun i ->
    let t1 = a.(i) in
    let t2 = bval bLen b i in admit();
    let c, res_i = subborrow_u64 carry.(size 0) t1 t2 in
    carry.(size 0) <- c;
    res.(i) <- res_i
  )


val bn_sub:
    aLen:size_t
  -> a:lbignum aLen
  -> bLen:size_t{v bLen <= v aLen}
  -> b:lbignum bLen
  -> res:lbignum aLen ->
  Stack uint64
  (requires fun h -> live h a /\ live h b /\ live h res)
  (ensures  fun h0 c h1 -> modifies (loc res) h0 h1 /\
    bn_v h1 res - v c * pow2 (64 * v aLen) == bn_v h0 a - bn_v h0 b)

[@"c_inline"]
let bn_sub aLen a bLen b res =
  push_frame ();
  let carry = create 1ul (u64 0) in
  bn_sub_ aLen a bLen b carry res;
  let res = carry.(0ul) in
  pop_frame (); admit();
  res


inline_for_extraction noextract
val bn_add_:
    aLen:size_t
  -> a:lbignum aLen
  -> bLen:size_t
  -> b:lbignum bLen
  -> carry:lbuffer uint64 1ul
  -> res:lbignum aLen ->
  Stack unit
    (requires fun h -> live h a /\ live h b /\ live h res /\ live h carry)
    (ensures  fun h0 _ h1 -> modifies (loc carry |+| loc res) h0 h1)

let bn_add_ aLen a bLen b carry res =
  let h0 = ST.get () in
  let inv h1 i = modifies (loc carry |+| loc res) h0 h1 in
  Lib.Loops.for 0ul aLen inv
  (fun i ->
    let t1 = a.(i) in
    let t2 = bval bLen b i in
    admit();
    let c, res_i = addcarry_u64 carry.(0ul) t1 t2 in
    carry.(0ul) <- c;
    res.(i) <- res_i
  )


val bn_add:
    aLen:size_t
  -> a:lbignum aLen
  -> bLen:size_t{v bLen <= v aLen}
  -> b:lbignum bLen
  -> res:lbignum aLen ->
  Stack uint64
  (requires fun h -> live h a /\ live h b /\ live h res)
  (ensures  fun h0 c h1 -> modifies (loc res) h0 h1 /\
    bn_v h1 res + v c * pow2 (64 * v aLen) == bn_v h0 a + bn_v h0 b)

[@"c_inline"]
let bn_add aLen a bLen b res =
  push_frame ();
  let carry = create 1ul (u64 0) in
  bn_add_ aLen a bLen b carry res;
  let res = carry.(0ul) in admit();
  pop_frame ();
  res
