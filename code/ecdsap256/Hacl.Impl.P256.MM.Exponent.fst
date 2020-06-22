module Hacl.Impl.P256.MM.Exponent

open FStar.HyperStack.All
open FStar.HyperStack
module ST = FStar.HyperStack.ST

open Lib.Sequence
open Lib.IntTypes
open Lib.Buffer

open FStar.Math.Lemmas

open Hacl.Impl.P256.LowLevel 

open FStar.Mul

open Lib.Loops

open Hacl.Impl.P256.MontgomeryMultiplication
open Hacl.Spec.P256.MontgomeryMultiplication

open Hacl.Impl.P256.LowLevel.PrimeSpecific
open Hacl.Impl.P256.Core

open Hacl.Spec.P256.Definition
open Hacl.Lemmas.P256
open Spec.ECDSA.Lemmas
open Spec.P256
open Hacl.Spec.P256.MontgomeryMultiplication

friend Hacl.Spec.P256.MontgomeryMultiplication

#set-options "--fuel 0 --ifuel 0 --z3rlimit 100"


[@ CInline]
val cswap: bit:uint64{v bit <= 1} -> p:felem -> q:felem
  -> Stack unit
    (requires fun h ->
      as_nat h p < prime /\ as_nat h q < prime /\ 
      live h p /\ live h q /\ eq_or_disjoint p q)
    (ensures  fun h0 _ h1 ->
      modifies (loc p |+| loc q) h0 h1 /\
	(
	  let (r0, r1) = conditional_swap_pow bit (as_nat h0 p) (as_nat h0 q) in 
	  let pBefore = as_seq h0 p in let qBefore = as_seq h0 q in 
	  let pAfter = as_seq h1 p in let qAfter = as_seq h1 q in 
	  as_nat h1 p < prime /\ as_nat h1 q < prime /\
      (v bit == 1 ==> as_seq h1 p == as_seq h0 q /\ as_seq h1 q == as_seq h0 p) /\
      (v bit == 0 ==> as_seq h1 p == as_seq h0 p /\ as_seq h1 q == as_seq h0 q)))


let cswap bit p1 p2 =
  let h0 = ST.get () in
  let mask = u64 0 -. bit in
  let open Lib.Sequence in 
  [@ inline_let]
  let inv h1 (i:nat{i <= 4}) =
    (forall (k:nat{k < i}).
      if v bit = 1
      then (as_seq h1 p1).[k] == (as_seq h0 p2).[k] /\ (as_seq h1 p2).[k] == (as_seq h0 p1).[k]
      else (as_seq h1 p1).[k] == (as_seq h0 p1).[k] /\ (as_seq h1 p2).[k] == (as_seq h0 p2).[k]) /\
    (forall (k:nat{i <= k /\ k < 4}).
      (as_seq h1 p1).[k] == (as_seq h0 p1).[k] /\ (as_seq h1 p2).[k] == (as_seq h0 p2).[k]) /\
    modifies (loc p1 |+| loc p2) h0 h1 in
 
  Lib.Loops.for 0ul 4ul inv
    (fun i ->
      let dummy = mask &. (p1.(i) ^. p2.(i)) in
      p1.(i) <- p1.(i) ^. dummy;
      p2.(i) <- p2.(i) ^. dummy;
      lemma_cswap2_step bit ((as_seq h0 p1).[v i]) ((as_seq h0 p2).[v i])
    );
  let h1 = ST.get () in 
  Lib.Sequence.eq_intro (as_seq h1 p1) (if v bit = 1 then as_seq h0 p2 else as_seq h0 p1);
  Lib.Sequence.eq_intro (as_seq h1 p2) (if v bit = 1 then as_seq h0 p1 else as_seq h0 p2)


inline_for_extraction noextract 
val upload_one_montg_form: b: felem -> Stack unit
  (requires fun h -> live h b)
  (ensures fun h0 _ h1 -> modifies (loc b) h0 h1 /\ as_nat h1 b == toDomain_ (1) /\ as_nat h1 b < prime)

let upload_one_montg_form b =
  upd b (size 0) (u64 1);
  upd b (size 1) (u64 18446744069414584320);
  upd b (size 2) (u64 18446744073709551615);
  upd b (size 3) (u64 4294967294);
  
  assert_norm (1 + 18446744069414584320 * pow2 64 + 18446744073709551615 * pow2 64 * pow2 64 + 4294967294 * pow2 64 * pow2 64 * pow2 64  == pow2 256 % prime256);
  lemmaToDomain 1


inline_for_extraction noextract
val montgomery_ladder_power_step0: a: felem -> b: felem -> Stack unit
  (requires fun h -> live h a /\ live h b /\ as_nat h a < prime /\ 
    as_nat h b < prime /\ disjoint a b )
  (ensures fun h0 _ h1 -> modifies (loc a |+| loc b) h0 h1 /\ 
    as_nat h1 a < prime /\ as_nat h1 b < prime /\
    (
      let (r0D, r1D) = _pow_step0 (fromDomain_ (as_nat h0 a)) (fromDomain_ (as_nat h0 b)) in 
      r0D == fromDomain_ (as_nat h1 a) /\ r1D == fromDomain_ (as_nat h1 b)
    )
)

let montgomery_ladder_power_step0 a b = 
  let h0 = ST.get() in 
    montgomery_multiplication_buffer a b b;
      lemmaToDomainAndBackIsTheSame (fromDomain_ (as_nat h0 a) * fromDomain_ (as_nat h0 b) % prime);
    montgomery_square_buffer a a ;
      lemmaToDomainAndBackIsTheSame (fromDomain_ (as_nat h0 a) * fromDomain_ (as_nat h0 a) % prime)


inline_for_extraction noextract
val montgomery_ladder_power_step: a: felem -> b: felem -> scalar: glbuffer uint8 (size 32) ->   i:size_t{v i < 256} ->  Stack unit
  (requires fun h -> live h a  /\ live h b /\ live h scalar /\ as_nat h a < prime /\ as_nat h b < prime /\ disjoint a b)
  (ensures fun h0 _ h1 -> modifies (loc a |+| loc b) h0 h1  /\
    (
      let a_ = fromDomain_ (as_nat h0 a) in 
      let b_ = fromDomain_ (as_nat h0 b) in 
      let (r0D, r1D) = _pow_step (as_seq h0 scalar) (uint_v i) (a_, b_) in 
      r0D == fromDomain_ (as_nat h1 a) /\ r1D == fromDomain_ (as_nat h1 b) /\ 
      as_nat h1 a < prime /\ as_nat h1 b < prime 
    ) 
  )  

let montgomery_ladder_power_step a b scalar i = 
    let h0 = ST.get() in 
  let bit0 = (size 255) -. i in 
  let bit = scalar_bit scalar bit0 in 
  cswap bit a b;
  montgomery_ladder_power_step0 a b;
  cswap bit a b;
  lemma_swaped_steps (fromDomain_ (as_nat h0 a)) (fromDomain_ (as_nat h0 b))


inline_for_extraction noextract 
val _montgomery_ladder_power: a: felem -> b: felem -> scalar: glbuffer uint8 (size 32) -> Stack unit
  (requires fun h -> live h a /\ live h b /\ live h scalar /\ as_nat h a < prime /\ 
    as_nat h b < prime /\ disjoint a b /\ disjoint a scalar /\ disjoint b scalar)
  (ensures fun h0 _ h1 -> modifies (loc a |+| loc b) h0 h1 /\ 
    (
      let a_ = fromDomain_ (as_nat h0 a) in 
      let b_ = fromDomain_ (as_nat h0 b) in 
      let (r0D, r1D) = Lib.LoopCombinators.repeati 256 (_pow_step (as_seq h0 scalar)) (a_, b_) in 
      r0D == fromDomain_ (as_nat h1 a) /\ r1D == fromDomain_ (as_nat h1 b) /\
      as_nat h1 a < prime /\ as_nat h1 b < prime)
  )

  
let _montgomery_ladder_power a b scalar = 
  let h0 = ST.get() in 
  [@inline_let]
  let spec_exp h0  = _pow_step (as_seq h0 scalar) in 
  [@inline_let]
  let acc (h: mem) : GTot (tuple2 nat_prime nat_prime) = (fromDomain_ (as_nat h a), fromDomain_ (as_nat h b)) in 
  Lib.LoopCombinators.eq_repeati0 256 (spec_exp h0) (acc h0);
  [@inline_let]
  let inv h (i: nat {i <= 256}) = 
    live h a /\ live h b /\ live h scalar /\ modifies (loc a |+| loc b) h0 h /\ as_nat h a < prime /\ as_nat h b < prime /\
    acc h == Lib.LoopCombinators.repeati i (spec_exp h0) (acc h0) in 
  for 0ul 256ul inv (
    fun i -> 
	  montgomery_ladder_power_step a b scalar i;
	  Lib.LoopCombinators.unfold_repeati 256 (spec_exp h0) (acc h0) (uint_v i))


val montgomery_ladder_power: a: felem -> scalar: glbuffer uint8 (size 32) -> result: felem -> 
  Stack unit 
    (requires fun h -> live h a /\ live h scalar /\ live h result /\ as_nat h a < prime /\ disjoint a scalar)
    (ensures fun h0 _ h1 -> modifies (loc a |+| loc result) h0 h1 /\
      as_nat h1 result < prime /\ 
      (
	assert_norm (1 < prime256);
	let r0D = pow_spec (as_seq h0 scalar) (fromDomain_ (as_nat h0 a)) in 
	r0D == fromDomain_ (as_nat h1 result)
      )
    )


let montgomery_ladder_power a scalar result = 
  assert_norm (1 < prime256);
  push_frame(); 
      let p = create (size 4) (u64 0) in 
      upload_one_montg_form p; 
      _montgomery_ladder_power p a scalar;
     lemmaToDomainAndBackIsTheSame 1;  
    copy result p;
  pop_frame()  


unfold let sqPower_list: list uint8 =
 [
   u8 0;  u8 0;  u8 0;  u8 0;   u8 0;   u8 0;   u8 0;   u8 0;
   u8 0;  u8 0;  u8 0;  u8 64;  u8 0;   u8 0;   u8 0;   u8 0;
   u8 0;  u8 0;  u8 0;  u8 0;   u8 0;   u8 0;   u8 0;   u8 64;
   u8 0;  u8 0;  u8 0;  u8 192; u8 255; u8 255; u8 255; u8 63
 ]


let sqPower_seq: s: lseq uint8 32{Lib.ByteSequence.nat_from_intseq_le s == (prime256 + 1) / 4} =
  let open Lib.ByteSequence in 
  assert_norm (List.Tot.length sqPower_list  == 32);
  nat_from_intlist_seq_le 32 sqPower_list;
  assert_norm (nat_from_intlist_le sqPower_list == (prime256 + 1) / 4);
  of_list sqPower_list


inline_for_extraction
let sqPower_buffer: x: glbuffer uint8 32ul {witnessed x sqPower_seq /\ recallable x} = 
  createL_global sqPower_list


let square_root a result = 
  recall_contents sqPower_buffer sqPower_seq;
  montgomery_ladder_power a sqPower_buffer result
