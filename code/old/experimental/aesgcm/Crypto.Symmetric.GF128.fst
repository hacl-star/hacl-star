module Crypto.Symmetric.GF128

module ST = FStar.HyperStack.ST

open FStar.HyperStack.All

module U8   = FStar.UInt8
module U32  = FStar.UInt32
module H8   = Hacl.UInt8
module H128 = Hacl.UInt128
module Spec = Spec.GF128
module BV   = FStar.BitVector

open Spec
open Spec.GaloisField

open FStar.Mul
open FStar.Ghost
open FStar.Seq
open FStar.Buffer
open FStar.UInt
open FStar.BitVector
open Hacl.Cast
open Hacl.Endianness

type elem = Spec.elem
type elemB = b:buffer H128.t{length b = 1}

noextract let sel_elem h (b:elemB{live h b}): GTot elem = to_felem #gf128 (H128.v (Seq.index (as_seq h b) 0))

#set-options "--z3rlimit 20 --max_fuel 0 --initial_fuel 0"

val load128_be: b:buffer U8.t{length b = 16} -> Stack H128.t
  (requires (fun h -> live h b))
  (ensures (fun h0 n h1 -> h0 == h1 /\ live h1 b /\ to_felem #gf128 (H128.v n) = encode (as_seq h1 b)))
let load128_be b = let v = load128_be b in uint128_to_sint128 v

#reset-options "--z3rlimit 20 --max_fuel 1 --initial_fuel 1"

val store128_be: b:buffer H8.t{length b = 16} -> n:H128.t -> Stack unit
  (requires (fun h -> live h b))
  (ensures (fun h0 _ h1 -> modifies_1 b h0 h1 /\ live h1 b /\ Seq.equal (decode (to_felem #gf128 (H128.v n))) (as_seq h1 b)))
let store128_be b n =
  hstore128_be b n;
  let h1 = ST.get() in
  FStar.Old.Endianness.lemma_big_endian_inj (decode (to_felem #gf128 (H128.v n))) (as_seq h1 b)

(* * Every block of message is regarded as an element in Galois field GF(2^128), **)
(* * The following several functions are basic operations in this field.         **)
(* * gf128_add: addition. Equivalent to bitxor.                                  **)
(* * gf128_shift_reduce: shift right by 1 bit then add. Used in multiplication.  **)
(* * gf128_mul: multiplication. Achieved by combining 128 additions.             **)

(* In place addition. Calculate "a + b" and store the result in a. *)
val gf128_add: a:elemB -> b:elemB {disjoint a b} -> Stack unit
  (requires (fun h -> live h a /\ live h b))
  (ensures (fun h0 _ h1 -> 
    live h0 a /\ live h0 b /\ live h1 a /\ modifies_1 a h0 h1 /\
    sel_elem h1 a = sel_elem h0 a +@ sel_elem h0 b))
let gf128_add a b = 
  let av = a.(0ul) in
  let bv = b.(0ul) in
  let r = H128.(av ^^ bv) in
  a.(0ul) <- r

inline_for_extraction let zero_128 : H128.t = uint64_to_sint128 0uL
inline_for_extraction let one_128  : H128.t = uint64_to_sint128 1uL
inline_for_extraction let ones_128 : H128.t =
  H128.(((uint64_to_sint128 0xffffffffffffffffuL) <<^ 64ul) +^ (uint64_to_sint128 0xffffffffffffffffuL))
inline_for_extraction private let r_mul : H128.t = H128.(uint64_to_sint128(225uL) <<^ 120ul)

val fzero_lemma: v:H128.t -> Lemma
  (requires v == zero_128)
  (ensures to_felem #gf128 (H128.v v) = Spec.GaloisField.zero #gf128)
let fzero_lemma v =
  assert(H128.v v = UInt.zero 128);
  lemma_eq_intro (to_felem #gf128 (H128.v v)) (Spec.GaloisField.zero #gf128)

val r_mul_lemma: v:H128.t -> Lemma
  (requires v == r_mul)
  (ensures to_felem #gf128 (H128.v v) = Spec.irr)
let r_mul_lemma v = assert_norm((225 * pow2 120) % pow2 128 = 0xe1000000000000000000000000000000)

private val elem_vec_logand_lemma: a:BV.bv_t 128 -> i:nat{i < 128} ->
  Lemma (Seq.equal (BV.logand_vec a (BV.elem_vec #128 i))
    (if Seq.index a i then (BV.elem_vec #128 i) else (BV.zero_vec #128)))
let elem_vec_logand_lemma a i = ()


#reset-options "--max_fuel 0 --z3rlimit 50 --admit_smt_queries true"

(* * ith_bit_mask return a mask corresponding to the i-th bit of num.            **)
(* * This function should be in constant time.                                   **)

private inline_for_extraction 
val ith_bit_mask: num:H128.t -> i:U32.t{U32.v i < 128} ->
  Tot (r:H128.t {(nth (H128.v num) (U32.v i) = true  ==> r == ones_128) /\
                 (nth (H128.v num) (U32.v i) = false ==> r == zero_128)})
let ith_bit_mask num i =
  let mi = U32.(127ul -^ i) in
  let proj = H128.(one_128 <<^ mi) in
  FStar.Math.Lemmas.pow2_lt_compat 128 (U32.v mi);
  FStar.Math.Lemmas.small_modulo_lemma_1 (pow2 (U32.v mi)) (pow2 128);
  assert(H128.v proj = (FStar.UInt.pow2_n #128 (127 - U32.v i)));
  assert(Seq.equal (FStar.UInt.to_vec #128 (H128.v proj)) (BV.elem_vec #128 (U32.v i)));
  let res = H128.(num &^ proj) in
  elem_vec_logand_lemma (FStar.UInt.to_vec #128 (H128.v num)) (U32.v i);
  H128.eq_mask res proj

#reset-options "--max_fuel 0 --z3rlimit 50 --admit_smt_queries true"

private
val gf128_shift_reduce: a:elemB -> Stack unit
  (requires (fun h -> live h a))
  (ensures (fun h0 _ h1 -> 
    live h0 a /\ live h1 a /\ modifies_1 a h0 h1 /\
    sel_elem h1 a = shift_reduce (sel_elem h0 a)))
let gf128_shift_reduce a =
  let av = a.(0ul) in
  let msk0 = ith_bit_mask av 127ul in
  let msk_r_mul = H128.(r_mul &^ msk0) in
  FStar.UInt.logand_lemma_1 (H128.v r_mul);
  FStar.UInt.logand_lemma_2 (H128.v r_mul);
  let av = H128.(av >>^ 1ul) in
  r_mul_lemma r_mul;
  FStar.UInt.logxor_lemma_1 (H128.v av);
  a.(0ul) <- H128.(av ^^ msk_r_mul)

#reset-options "--max_fuel 0 --z3rlimit 50"

private
val gf128_cond_fadd:
  x:elemB ->
  y:elemB {disjoint x y} ->
  z:elemB {disjoint x z /\ disjoint y z} ->
  i:U32.t {U32.v i < 128} ->
  Stack unit
  (requires (fun h -> live h x /\ live h y /\ live h z))
  (ensures (fun h0 _ h1 -> live h0 x /\ live h0 y /\ live h0 z /\
    live h1 x /\ live h1 y /\ live h1 z /\ modifies_1 z h0 h1 /\
    sel_elem h1 z = cond_fadd (sel_elem h0 x) (sel_elem h0 y) (sel_elem h0 z) (U32.v i)))
let gf128_cond_fadd x y z i =
  let xv = x.(0ul) in
  let yv = y.(0ul) in
  let zv = z.(0ul) in
  let mski = ith_bit_mask yv i in
  let msk_x = H128.(xv &^ mski) in
  FStar.UInt.logand_lemma_1 (H128.v xv);
  FStar.UInt.logand_lemma_2 (H128.v xv);
  FStar.UInt.logxor_lemma_1 (H128.v zv);
  z.(0ul) <- H128.(zv ^^ msk_x)

#reset-options "--z3rlimit 40 --max_fuel 1 --initial_fuel 1"

private val fmul_loop_lemma: #f:field -> a:felem f -> b:felem f -> n:nat{n < f.bits} -> Lemma
  (requires True)
  (ensures fmul_loop a b n = cond_fadd a b (fmul_loop (shift_reduce #f a) b (n + 1)) n)
let fmul_loop_lemma #f a b n = ()

private val gf128_mul_loop: 
  x:elemB -> 
  y:elemB {disjoint x y} -> 
  z:elemB {disjoint x z /\ disjoint y z} ->
  ctr:U32.t{U32.v ctr <= 128} -> 
  Stack unit
  (requires (fun h -> live h x /\ live h y /\ live h z))
  (ensures (fun h0 _ h1 -> live h0 x /\ live h0 y /\ live h0 z /\
    live h1 x /\ live h1 y /\ live h1 z /\ modifies_2 x z h0 h1 /\
    sel_elem h1 z = fmul_loop (sel_elem h0 x) (sel_elem h0 y) (U32.v ctr) +@ sel_elem h0 z))
let rec gf128_mul_loop x y z ctr =
  if ctr = 128ul then begin
    let h0 = ST.get() in
    add_comm (fmul_loop (sel_elem h0 x) (sel_elem h0 y) (U32.v ctr)) (sel_elem h0 z);
    add_zero (sel_elem h0 z) (fmul_loop (sel_elem h0 x) (sel_elem h0 y) (U32.v ctr))
  end else begin
    let h0 = ST.get() in
    gf128_cond_fadd x y z ctr;
    gf128_shift_reduce x;
    gf128_mul_loop x y z (U32.(ctr +^ 1ul));
    
    fmul_loop_lemma (sel_elem h0 x) (sel_elem h0 y) (U32.v ctr);
    cond_fadd_lemma (sel_elem h0 x) (sel_elem h0 y) (fmul_loop (shift_reduce (sel_elem h0 x)) (sel_elem h0 y) (U32.v ctr + 1)) (sel_elem h0 z) (U32.v ctr)
  end

#reset-options "--z3rlimit 20 --max_fuel 0 --initial_fuel 0"

(* In place multiplication. Calculate "a * b" and store the result in a.    *)
(* WARNING: may have issues with constant time. *)
val gf128_mul: x:elemB -> y:elemB {disjoint x y} -> Stack unit
  (requires (fun h -> live h x /\ live h y))
  (ensures (fun h0 _ h1 -> live h0 x /\ live h0 y /\ live h1 x /\ live h1 y /\ modifies_1 x h0 h1 /\
    sel_elem h1 x = sel_elem h0 x *@ sel_elem h0 y))
let gf128_mul x y =
  push_frame();
  let z = create zero_128 1ul in
  let h0 = ST.get() in
  gf128_mul_loop x y z 0ul;
  x.(0ul) <- z.(0ul);
  fzero_lemma zero_128;
  add_zero #gf128 (fmul_loop (sel_elem h0 x) (sel_elem h0 y) 0) (sel_elem h0 z);
  pop_frame()


val add_and_multiply: acc:elemB -> block:elemB{disjoint acc block}
  -> k:elemB{disjoint acc k /\ disjoint block k} -> Stack unit
  (requires (fun h -> live h acc /\ live h block /\ live h k))
  (ensures (fun h0 _ h1 -> live h0 acc /\ live h0 block /\ live h0 k
    /\ live h1 acc /\ live h1 k
    /\ modifies_1 acc h0 h1
    /\ sel_elem h1 acc = (sel_elem h0 acc +@ sel_elem h0 block) *@ sel_elem h0 k))
let add_and_multiply acc block k =
  gf128_add acc block;
  gf128_mul acc k

val finish: acc:elemB -> s:buffer U8.t{length s = 16} -> Stack unit
  (requires (fun h -> live h acc /\ live h s /\ disjoint acc s))
  (ensures  (fun h0 _ h1 -> live h0 acc /\ live h0 s
    /\ modifies_1 acc h0 h1 /\ live h1 acc
    /\ decode (sel_elem h1 acc) = finish (sel_elem h0 acc) (as_seq h0 s)))
let finish a s = 
  let sf = load128_be s in
  a.(0ul) <- H128.(a.(0ul) ^^ sf)

(*
//16-09-23 Instead of the code below, we should re-use existing AEAD encodings
//16-09-23 and share their injectivity proofs and crypto model.

#reset-options "--initial_fuel 0 --max_fuel 0 --z3rlimit 20"

private val ghash_loop_:
  tag:elemB ->
  auth_key:elemB {disjoint tag auth_key} ->
  str:buffer UInt8.t{disjoint tag str /\ disjoint auth_key tag} ->
  tmp:buffer UInt128.t{disjoint tag tmp /\ disjoint auth_key tmp /\ disjoint str tmp} ->
  len:U32.t{length str = U32.v len} ->
  dep:U32.t{U32.v dep <= U32.v len} -> Stack unit
  (requires (fun h -> U32.v len - U32.v dep <= 16 /\ live h tag /\ live h auth_key /\ live h str))
  (ensures (fun h0 _ h1 -> live h1 tag /\ live h1 auth_key /\ live h1 str /\ modifies_1 tag h0 h1))
let ghash_loop_ tag auth_key str tmp len dep =
  let t = sub str dep (U32.(len -^ dep)) in
  tmp.(0ul) <- load128_be t;
  add_and_multiply tag tmp auth_key

(* WARNING: may have issues with constant time. *)
private val ghash_loop: 
  tag:elemB ->
  auth_key:elemB {disjoint tag auth_key} ->
  str:buffer UInt8.t{disjoint tag str /\ disjoint auth_key str} ->
  tmp:buffer UInt128.t{disjoint tag tmp /\ disjoint auth_key tmp /\ disjoint str tmp} ->
  len:U32.t{length str = U32.v len} ->
  dep:U32.t{U32.v dep <= U32.v len} -> Stack unit
  (requires (fun h -> live h tag /\ live h auth_key /\ live h str /\ live h tmp))
  (ensures (fun h0 _ h1 -> live h1 tag /\ live h1 auth_key /\ live h1 str /\ live h1 tmp /\ modifies_2 tag tmp h0 h1))
let rec ghash_loop tag auth_key str tmp len dep =
  (* Appending zeros if the last block is not complete *)
  let rest = U32.(len -^ dep) in 
  if rest <> 0ul then 
  if U32.(16ul >=^ rest) then ghash_loop_ tag auth_key str tmp len dep
  else 
  begin
    let next = U32.add dep 16ul in
    let si = sub str dep 16ul in
    tmp.(0ul) <- load128_be si;
    add_and_multiply tag tmp auth_key;
    ghash_loop tag auth_key str tmp len next
  end
 
(* During authentication, the length information should also be included. *)
(* This function will generate an element in GF128 by:                    *)
(* 1. express len of additional data and len of ciphertext as 64-bit int; *)
(* 2. concatenate the two integers to get a 128-bit block.                *)
private val mk_len_info: len_info:elemB ->
    len_1:U32.t -> len_2:U32.t -> Stack unit
    (requires (fun h -> live h len_info))
    (ensures (fun h0 _ h1 -> live h1 len_info /\ modifies_1 len_info h0 h1))
let mk_len_info len_info len_1 len_2 =
  let l1 = FStar.UInt128.uint64_to_uint128(uint32_to_uint64 len_1) in
  let l2 = FStar.UInt128.uint64_to_uint128(uint32_to_uint64 len_2) in
  let u = U128.((l1 <<^ 64ul) +^ l2) in
  len_info.(0ul) <- u

#reset-options "--initial_fuel 0 --max_fuel 0 --z3rlimit 20"

(* A hash function used in authentication. It will authenticate additional data first, *)
(* then ciphertext and at last length information. The result is stored in tag.        *)
val ghash:
  k:elemB ->
  ad:buffer UInt8.t{disjoint k ad} ->
  adlen:U32.t{U32.v adlen = length ad} ->
  ciphertext:buffer UInt8.t{disjoint k ciphertext /\ disjoint ad ciphertext} ->
  len:U32.t{U32.v len = length ciphertext} ->
  tag:elemB{disjoint k tag /\ disjoint ad tag /\ disjoint ciphertext tag} ->
  Stack unit
  (requires (fun h -> live h k /\ live h ad /\ live h ciphertext /\ live h tag))
  (ensures (fun h0 _ h1 -> live h1 tag /\ modifies_1 tag h0 h1))

let ghash k ad adlen ciphertext len tag =
  push_frame();
  let h0 = ST.get() in
  let len_info = create zero_128 1ul in
  mk_len_info len_info adlen len;
  let h1 = ST.get() in
  assert(modifies_0 h0 h1);
  tag.(0ul) <- zero_128;
  let tmp = create zero_128 1ul in
  ghash_loop tag k ad tmp adlen 0ul;
  ghash_loop tag k ciphertext tmp len 0ul;
  add_and_multiply tag len_info k;
  //gf128_add tag len_info;
  //gf128_mul tag k;
  let h2 = ST.get() in
  assert(modifies_1 tag h1 h2);
  pop_frame()
*)
