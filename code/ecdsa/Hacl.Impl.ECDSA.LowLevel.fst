module Hacl.Impl.ECDSA.LowLevel

open FStar.HyperStack.All
open FStar.HyperStack
module ST = FStar.HyperStack.ST

open Lib.IntTypes
open Lib.Buffer

open FStar.Math.Lemmas
open Hacl.Impl.EC.LowLevel 

open Hacl.Impl.EC.Masking
open FStar.Mul
open Lib.IntTypes.Intrinsics


#reset-options "--z3rlimit 300"

val lemma_reduction_prime_2prime_with_carry_cin: 
  c: curve ->
  cin: nat {cin <= 1} ->
  x: nat {x + cin * pow2 (getPower c) < 2 * getOrder #c /\ x < pow2 (getPower c)} -> 
  carry0 : nat {carry0 <= 1 /\ (if carry0 = 0 then x >= getOrder #c else x < getOrder #c)} -> 
  result: nat {if cin < carry0 then result = x else result = x - getOrder #c + carry0 * pow2 (getPower c)} -> 
  Lemma (result = (x + cin * pow2 (getPower c)) % getOrder #c)

let lemma_reduction_prime_2prime_with_carry_cin c cin x carry0 result = 
  let n = x + cin * pow2 (getPower c) in 
  let prime = getOrder #c in 

  if cin = 0 && carry0 = 1 then begin
    small_mod x prime;
    assert(result = (x + cin * pow2 (getPower c)) % prime)
    end
  else if cin = 0 && carry0 = 0 then begin
    small_modulo_lemma_1 (x - prime) prime;
    lemma_mod_sub x prime 1;
    assert(result = (x + cin * pow2 (getPower c)) % prime)
    end
  else if cin = 1 && carry0 = 0 then 
    assert(result = (x + cin * pow2 (getPower c)) % prime)
  else
    begin 
      lemma_mod_sub (x + cin * pow2 (getPower c)) prime 1;
      small_mod result prime;
      assert(result = (x + cin * pow2 (getPower c)) % prime)
    end

inline_for_extraction noextract
val reduction_prime_2prime_with_carry_cin: #c: curve -> cin: uint64 -> x: felem c -> result: felem c ->
  Stack unit
  (requires fun h -> live h x /\ live h result /\ eq_or_disjoint x result /\ (
    as_nat c h x + uint_v cin * pow2 (getPower c) < 2 * getOrder #c))
  (ensures fun h0 _ h1 -> modifies (loc result) h0 h1 /\
    as_nat c h1 result = (as_nat c h0 x + uint_v cin * pow2 (getPower c)) % getOrder #c)

let reduction_prime_2prime_with_carry_cin #c cin x result =
  push_frame();

  let h0 = ST.get() in 

  let len = getCoordinateLenU64 c in

  let tempBuffer = create len (u64 0) in
  let tempBufferForSubborrow = create (size 1) (u64 0) in
 
  let carry0 = sub_bn_order x tempBuffer in
  let carry = sub_borrow_u64 carry0 cin (u64 0) tempBufferForSubborrow in
  cmovznz4 carry tempBuffer x result;
  pop_frame();
  
  let h2 = ST.get() in 
  lseq_upperbound #(v (getCoordinateLenU64 c)) (as_seq h0 x); 
  lemma_reduction_prime_2prime_with_carry_cin c (v cin) (as_nat c h0 x) (uint_v carry0) (as_nat c h2 result)


let reduction_prime_2prime_with_carry #c x result  = 
  let len = getCoordinateLenU64 c in
  
  let cin = Lib.Buffer.index x len in
  let x_ = Lib.Buffer.sub x (size 0) len in
  let x__ = Lib.Buffer.sub x len len in 

  let h0 = ST.get() in 
  FStar.Math.Lemmas.pow2_plus 64 (v (getCoordinateLenU64 c) * 64);
  lseq_upperbound1 (as_seq h0 x) (v (getCoordinateLenU64 c) + 1) (2 * v (getCoordinateLenU64 c) - v (getCoordinateLenU64 c) - 1);
  lseq_as_nat_definiton (as_seq h0 x) (v (getCoordinateLenU64 c) + 1);

  lemma_lseq_as_seq_extension (as_seq h0 (gsub x (size 0) (getCoordinateLenU64 c))) (as_seq h0 x) (v (getCoordinateLenU64 c));
  reduction_prime_2prime_with_carry_cin cin x_ result


inline_for_extraction noextract
val reduction_prime_2prime_order_: #c: curve -> x: felem c -> result: felem c -> 
  Stack unit 
  (requires fun h -> live h x /\ live h result /\ eq_or_disjoint x result)
  (ensures fun h0 _ h1 -> modifies (loc result) h0 h1 /\ as_nat c h1 result == as_nat c h0 x % getOrder #c)  


let reduction_prime_2prime_order_ #c x result  =
   push_frame();
  let len = getCoordinateLenU64 c in
  let tempBuffer = create len (u64 0) in
    let h0 = ST.get() in
  let r = sub_bn_order x tempBuffer in
    let h1 = ST.get() in 
  lemma_mod_plus (as_nat c h0 x) (-1) (getOrder #c);
  lseq_upperbound #(v (getCoordinateLenU64 c)) (as_seq h0 x); 
  cmovznz4 r tempBuffer x result;
    let h2 = ST.get() in 
  pop_frame()


[@CInline]
let reduction_prime_2prime_order_p256 = reduction_prime_2prime_order_ #P256

[@CInline]
let reduction_prime_2prime_order_p384 = reduction_prime_2prime_order_ #P384

(* [@CInline]
let reduction_prime_2prime_order_generic = reduction_prime_2prime_order_ #Default *)


let reduction_prime_2prime_order #c x result = 
  match c with 
  |P256 -> reduction_prime_2prime_order_p256 x result
  |P384 -> reduction_prime_2prime_order_p384 x result
  (* |Default -> reduction_prime_2prime_order_generic x result *)


inline_for_extraction noextract
val felem_add_ecdsa_: #c: curve -> a: felem c -> b: felem c -> out: felem c ->
  Stack unit
  (requires (fun h0 ->
    live h0 a /\ live h0 b /\ live h0 out /\ eq_or_disjoint a out /\ eq_or_disjoint b out /\ eq_or_disjoint a b /\
    as_nat c h0 a < getOrder #c /\ as_nat c h0 b < getOrder #c))
  (ensures (fun h0 _ h1 -> modifies (loc out) h0 h1 /\
    as_nat c h1 out == (as_nat c h0 a + as_nat c h0 b) % getOrder #c /\
    as_nat c h1 out == toDomain_ #c #DSA ((fromDomain_ #c #DSA (as_nat c h0 a) + fromDomain_ #c #DSA (as_nat c h0 b)) % getOrder #c)))

let felem_add_ecdsa_ #c arg1 arg2 out =
  let h0 = ST.get() in
  let t = add_bn arg1 arg2 out in
  reduction_prime_2prime_with_carry_cin t out out;
  
  additionInDomain #c #DSA (as_nat c h0 arg1) (as_nat c h0 arg2);
  inDomain_mod_is_not_mod #c #DSA (fromDomain_ #c #DSA (as_nat c h0 arg1) + fromDomain_ #c #DSA (as_nat c h0 arg2))

[@CInline]
let felem_add_ecdsa_P256 = felem_add_ecdsa_ #P256
[@CInline]
let felem_add_ecdsa_P384 = felem_add_ecdsa_ #P384
(* [@CInline]
let felem_add_ecdsa_generic = felem_add_ecdsa_ #Default
 *)
let felem_add_ecdsa #c a b o = 
  match c with
  | P256 -> felem_add_ecdsa_P256 a b o
  | P384 -> felem_add_ecdsa_P384 a b o
  (* | Default -> felem_add_ecdsa_generic a b o  *)


let upload_one_montg_form #c b = 
  match c with 
  |P256 -> 
    upd b (size 0) (u64 884452912994769583);
    upd b (size 1) (u64 4834901526196019579);
    upd b (size 2) (u64 0);
    upd b (size 3) (u64 4294967295);
    lemmaToDomain #P256 #DSA 1;
      let h1 = ST.get() in 
    Hacl.Impl.P256.LowLevel.lemma_lseq_nat_instant_4 (as_seq h1 b); 
    assert_norm(884452912994769583 + 4834901526196019579 * pow2 64 + 0 * pow2 (2 * 64) + 4294967295 * pow2 (3 * 64) == pow2 256 % getOrder #P256)
  |_ -> 
    uploadZeroImpl b; 
    reduction_prime_2prime_with_carry_cin #c (u64 1) b b;
    lemmaToDomain #c #DSA 1
