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
val cswap: #c : curve ->  bit:uint64{v bit <= 1} -> p:felem c -> q:felem c
  -> Stack unit
    (requires fun h ->
      as_nat c h p < getPrime c /\ as_nat c h q < getPrime c /\ 
      live h p /\ live h q /\ eq_or_disjoint p q)
    (ensures  fun h0 _ h1 ->
      modifies (loc p |+| loc q) h0 h1 /\
	(
	  let (r0, r1) = conditional_swap_pow #c bit (as_nat c h0 p) (as_nat c h0 q) in 
	  let pBefore = as_seq h0 p in let qBefore = as_seq h0 q in 
	  let pAfter = as_seq h1 p in let qAfter = as_seq h1 q in 
	  as_nat c h1 p < getPrime c /\ as_nat c h1 q < getPrime c /\
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
val upload_one_montg_form: #c: curve -> b: felem c -> Stack unit
  (requires fun h -> live h b)
  (ensures fun h0 _ h1 -> modifies (loc b) h0 h1 /\ as_nat c h1 b == toDomain_ #c 1 /\ as_nat c h1 b < getPrime c)

let upload_one_montg_form #c b =
  upd b (size 0) (u64 1);
  upd b (size 1) (u64 18446744069414584320);
  upd b (size 2) (u64 18446744073709551615);
  upd b (size 3) (u64 4294967294);
  
  assert_norm (1 + 18446744069414584320 * pow2 64 + 18446744073709551615 * pow2 64 * pow2 64 + 4294967294 * pow2 64 * pow2 64 * pow2 64  == pow2 256 % prime256);
  lemmaToDomain #c 1


inline_for_extraction noextract
val montgomery_ladder_power_step0: #c: curve -> a: felem c -> b: felem c -> Stack unit
  (requires fun h -> live h a /\ live h b /\ as_nat c h a < getPrime c /\ 
    as_nat c h b < getPrime c /\ disjoint a b )
  (ensures fun h0 _ h1 -> modifies (loc a |+| loc b) h0 h1 /\ 
    as_nat c h1 a < getPrime c /\ as_nat c h1 b < getPrime c /\
    (
      let (r0D, r1D) = _pow_step0 #c (fromDomain_ #c (as_nat c h0 a)) (fromDomain_ #c (as_nat c h0 b)) in 
      r0D == fromDomain_ #c (as_nat c h1 a) /\ r1D == fromDomain_ #c (as_nat c h1 b)
    )
)

let montgomery_ladder_power_step0 #c a b = 
  let h0 = ST.get() in 
    montgomery_multiplication_buffer a b b;
      lemmaToDomainAndBackIsTheSame #c (fromDomain_ #c (as_nat c h0 a) * fromDomain_ #c (as_nat c h0 b) % getPrime c);
    montgomery_square_buffer a a ;
      lemmaToDomainAndBackIsTheSame #c (fromDomain_ #c (as_nat c h0 a) * fromDomain_ #c (as_nat c h0 a) % getPrime c)


inline_for_extraction noextract
val montgomery_ladder_power_step: #c: curve -> a: felem c -> b: felem c -> scalar: glbuffer uint8 (size 32) ->   i:size_t{v i < 256} ->  Stack unit
  (requires fun h -> live h a  /\ live h b /\ live h scalar /\ as_nat c h a < getPrime c 
    /\ as_nat c h b < getPrime c /\ disjoint a b)
  (ensures fun h0 _ h1 -> modifies (loc a |+| loc b) h0 h1  /\
    (
      let a_ = fromDomain_ #c (as_nat c h0 a) in 
      let b_ = fromDomain_ #c (as_nat c h0 b) in 
      let (r0D, r1D) = _pow_step #c (as_seq h0 scalar) (uint_v i) (a_, b_) in 
      r0D == fromDomain_ #c (as_nat c h1 a) /\ r1D == fromDomain_ #c (as_nat c h1 b) /\ 
      as_nat c h1 a < getPrime c /\ as_nat c h1 b < getPrime c 
    ) 
  )  

let montgomery_ladder_power_step #c a b scalar i = 
    let h0 = ST.get() in 
  let bit0 = (size 255) -. i in 
  let bit = scalar_bit scalar bit0 in 
  cswap bit a b;
  montgomery_ladder_power_step0 a b;
  cswap bit a b;
  lemma_swaped_steps #c (fromDomain_ #c (as_nat c h0 a)) (fromDomain_ #c (as_nat c h0 b))


val _montgomery_ladder_power: #c: curve -> a: felem c -> b: felem c -> scalar: glbuffer uint8 (size 32) -> Stack unit
  (requires fun h -> live h a /\ live h b /\ live h scalar /\ as_nat c h a < getPrime c /\ 
    as_nat c h b < getPrime c /\ disjoint a b /\ disjoint a scalar /\ disjoint b scalar)
  (ensures fun h0 _ h1 -> modifies (loc a |+| loc b) h0 h1 /\ 
    (
      let a_ = fromDomain_ #c (as_nat c h0 a) in 
      let b_ = fromDomain_ #c (as_nat c h0 b) in 
      let (r0D, r1D) = Lib.LoopCombinators.repeati 256 (_pow_step (as_seq h0 scalar)) (a_, b_) in 
      r0D == fromDomain_ #c (as_nat c h1 a) /\ r1D == fromDomain_ #c (as_nat c h1 b) /\
      as_nat c h1 a < getPrime c /\ as_nat c h1 b < getPrime c)
  )

  
let _montgomery_ladder_power #c a b scalar = 
  let h0 = ST.get() in 
  [@inline_let]
  let spec_exp h0  = _pow_step (as_seq h0 scalar) in 
  [@inline_let]
  let acc (h: mem) : GTot (tuple2 nat_prime nat_prime) = (fromDomain_ #c (as_nat c h a), fromDomain_ #c (as_nat c h b)) in 
  Lib.LoopCombinators.eq_repeati0 256 (spec_exp h0) (acc h0);
  [@inline_let]
  let inv h (i: nat {i <= 256}) = 
    live h a /\ live h b /\ live h scalar /\ modifies (loc a |+| loc b) h0 h /\ as_nat c h a < getPrime c /\ as_nat c h b < getPrime c /\
    acc h == Lib.LoopCombinators.repeati i (spec_exp h0) (acc h0) in 
  for 0ul 256ul inv (
    fun i -> 
	  montgomery_ladder_power_step a b scalar i;
	  Lib.LoopCombinators.unfold_repeati 256 (spec_exp h0) (acc h0) (uint_v i))


val montgomery_ladder_power: #c: curve -> a: felem c -> scalar: glbuffer uint8 (size 32) -> result: felem c -> 
  Stack unit 
    (requires fun h -> live h a /\ live h scalar /\ live h result /\ as_nat c h a < getPrime c /\ disjoint a scalar)
    (ensures fun h0 _ h1 -> modifies (loc a |+| loc result) h0 h1 (*/\
      as_nat c h1 result < getPrime c /\ 
      (
	assert_norm (1 < prime256);
	let r0D = pow_spec (as_seq h0 scalar) (fromDomain_ #c (as_nat c h0 a)) in 
	r0D == fromDomain_ #c (as_nat c h1 result)
      ) *)
    )


let montgomery_ladder_power #c a scalar result = 
  assert_norm (1 < prime256);
  push_frame(); 
  let p = create (getCoordinateLenU64 c) (u64 0) in  
    upload_one_montg_form #c p; 
      _montgomery_ladder_power #c p a scalar;
     lemmaToDomainAndBackIsTheSame #c 1;  
    copy result p;
    admit(); 
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
