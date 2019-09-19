module Hacl.Bignum.Multiplication

open FStar.HyperStack
open FStar.HyperStack.ST
open FStar.Mul

open Lib.IntTypes
open Lib.Buffer

open Hacl.Bignum
open Hacl.Bignum.Base
open Hacl.Bignum.Comparison
open Hacl.Bignum.Addition

module ST = FStar.HyperStack.ST


#reset-options "--z3rlimit 50 --max_fuel 0 --max_ifuel 0"

inline_for_extraction noextract
val bn_mul_by_limb_addj_f: a_i:uint64 -> l:uint64 -> c:uint64 -> r_ij:uint64 -> uint64 & uint64
let bn_mul_by_limb_addj_f a_i l c r_ij =
  mul_carry_add_u64 a_i l c r_ij

//res = res + limb * bn * beta_j
inline_for_extraction noextract
val bn_mult_by_limb_addj_add:
    aLen:size_t
  -> a:lbignum aLen
  -> l:uint64
  -> j:size_t
  -> resLen:size_t{v aLen + v j < v resLen}
  -> res:lbignum resLen
  -> carry:lbignum 1ul ->
  Stack uint64
  (requires fun h ->
    live h a /\ live h res /\ live h carry /\
    disjoint res a /\ disjoint res carry)
  (ensures  fun h0 _ h1 -> modifies (loc carry |+| loc res) h0 h1)

let bn_mult_by_limb_addj_add aLen a l j resLen res carry =
  let h0 = ST.get () in
  let inv h1 i = modifies (loc carry |+| loc res) h0 h1 in
  Lib.Loops.for 0ul aLen inv
  (fun i ->
    let ij = i +. j in
    let res_ij = res.(ij) in
    let c, res_ij = bn_mul_by_limb_addj_f a.(i) l carry.(0ul) res_ij in
    carry.(0ul) <- c;
    res.(ij) <- res_ij
  );
  let res1Len = resLen -. (aLen +. j) in
  let res1 = sub res (aLen +. j) res1Len in
  bn_add res1Len res1 1ul carry res1


inline_for_extraction noextract
val bn_mult_by_limb_addj:
    aLen:size_t
  -> a:lbignum aLen
  -> l:uint64
  -> j:size_t
  -> resLen:size_t{v aLen + v j < v resLen}
  -> res:lbignum resLen
  -> carry:lbignum 1ul ->
  Stack unit
  (requires fun h -> live h a /\ live h res /\ live h carry /\ disjoint res a)
  (ensures  fun h0 _ h1 -> modifies (loc carry |+| loc res) h0 h1)

let bn_mult_by_limb_addj aLen a l j resLen res carry =
  let h0 = ST.get() in
  let inv h1 i = modifies (loc carry |+| loc res) h0 h1 in
  Lib.Loops.for 0ul aLen inv
  (fun i ->
    let ij = i +. j in
    let res_ij = res.(ij) in
    let c, res_ij = bn_mul_by_limb_addj_f a.(i) l carry.(0ul) res_ij in
    carry.(0ul) <- c;
    res.(ij) <- res_ij
  );
  res.(aLen +. j) <- carry.(0ul)


inline_for_extraction noextract
val bn_mult_:
    aLen:size_t
  -> a:lbignum aLen
  -> bLen:size_t
  -> b:lbignum bLen
  -> resLen:size_t{v resLen = v aLen + v bLen}
  -> res:lbignum resLen
  -> carry:lbignum 1ul ->
  Stack unit
  (requires fun h ->
    live h a /\ live h b /\ live h res /\ live h carry /\
    disjoint res a /\ disjoint res b)
  (ensures  fun h0 _ h1 -> modifies (loc carry |+| loc res) h0 h1)

let bn_mult_ aLen a bLen b resLen res carry =
  let h0 = ST.get() in
  let inv h1 j = modifies (loc carry |+| loc res) h0 h1 in
  Lib.Loops.for 0ul bLen inv
  (fun j ->
    carry.(0ul) <- u64 0;
    bn_mult_by_limb_addj aLen a b.(j) j resLen res carry
  )


val bn_mul:
    aLen:size_t
  -> a:lbignum aLen
  -> bLen:size_t{v aLen + v bLen <= max_size_t}
  -> b:lbignum bLen
  -> res:lbignum (aLen +! bLen) ->
  Stack unit
  (requires fun h ->
    live h a /\ live h b /\ live h res /\
    disjoint res a /\ disjoint res b)
  (ensures  fun h0 _ h1 -> modifies (loc res) h0 h1 /\
    bn_v h1 res == bn_v h0 a * bn_v h0 b)

[@"c_inline"]
let bn_mul aLen a bLen b res =
  push_frame ();
  let resLen = aLen +! bLen in
  memset res (u64 0) resLen;
  let carry = create 1ul (u64 0) in
  bn_mult_ aLen a bLen b resLen res carry;
  admit();
  pop_frame ()
