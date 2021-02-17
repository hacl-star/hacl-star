module Hacl.Impl.P256.MM.Exponent

open FStar.HyperStack.All
open FStar.HyperStack
module ST = FStar.HyperStack.ST

open Lib.Sequence
open Lib.IntTypes
open Lib.Buffer

open FStar.Math.Lemmas

open Hacl.Impl.EC.LowLevel 

open FStar.Mul

open Lib.Loops

open Hacl.Impl.P256.MontgomeryMultiplication
open Hacl.Spec.P.MontgomeryMultiplication

open Hacl.Spec.P256.Definition
open Hacl.Lemmas.P256
open Spec.ECDSA.Lemmas
open Spec.P256
open Hacl.Spec.P.MontgomeryMultiplication

friend Hacl.Spec.P.MontgomeryMultiplication

open Hacl.Impl.P256.MontgomeryMultiplication.Exponent

#set-options "--fuel 0 --ifuel 0 --z3rlimit 100"

(* For p256 curve there is a special implementation of multiplication by prime - 2 *)

[@ CInline]
val cswap: #c: curve -> bit:uint64{v bit <= 1} -> p: felem c -> q: felem c
  -> Stack unit
    (requires fun h ->  as_nat c h p < getPrime c /\ as_nat c h q < getPrime c /\ 
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


let cswap #c bit p1 p2 =
  
  let h0 = ST.get () in
  let mask = u64 0 -. bit in

  let len = getCoordinateLenU64 c in 

  let open Lib.Sequence in 
  [@ inline_let]
  let inv h1 (i:nat{i <= uint_v len}) =
    (forall (k:nat{k < i}).
      if v bit = 1
      then (as_seq h1 p1).[k] == (as_seq h0 p2).[k] /\ (as_seq h1 p2).[k] == (as_seq h0 p1).[k]
      else (as_seq h1 p1).[k] == (as_seq h0 p1).[k] /\ (as_seq h1 p2).[k] == (as_seq h0 p2).[k]) /\
    (forall (k:nat{i <= k /\ k < v len}).
      (as_seq h1 p1).[k] == (as_seq h0 p1).[k] /\ (as_seq h1 p2).[k] == (as_seq h0 p2).[k]) /\
    modifies (loc p1 |+| loc p2) h0 h1 in

  Lib.Loops.for 0ul len inv
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
val montgomery_ladder_power_step0: #c: curve -> a: felem c -> b: felem c -> Stack unit
  (requires fun h -> live h a /\ live h b /\ as_nat c h a < getPrime c /\ 
    as_nat c h b < getPrime c /\ disjoint a b )
  (ensures fun h0 _ h1 -> modifies (loc a |+| loc b) h0 h1 /\ 
    as_nat c h1 a < getPrime c /\ as_nat c h1 b < getPrime c /\
    (
      let (r0D, r1D) = _pow_step0 #c (fromDomain_ #c (as_nat c h0 a)) (fromDomain_ #c (as_nat c h0 b)) in 
      r0D == fromDomain_ #c (as_nat c h1 a) /\ r1D == fromDomain_ #c (as_nat c h1 b)))

let montgomery_ladder_power_step0 #c a b = 
  let h0 = ST.get() in 
    montgomery_multiplication_buffer a b b;
      lemmaToDomainAndBackIsTheSame #c (fromDomain_ #c (as_nat c h0 a) * fromDomain_ #c (as_nat c h0 b) % getPrime c);
    montgomery_square_buffer a a ;
      lemmaToDomainAndBackIsTheSame #c (fromDomain_ #c (as_nat c h0 a) * fromDomain_ #c (as_nat c h0 a) % getPrime c)


val montgomery_ladder_power_step: #c: curve -> a: felem c -> b: felem c 
  -> scalar: glbuffer uint8 (getScalarLen c) 
  -> i:size_t{v i < getScalarLenNat c} ->  Stack unit
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
  let bit0 = getScalarLenU64 c -. 1ul -. i in  
  let bit = scalar_bit scalar bit0 in 
  cswap bit a b;
  montgomery_ladder_power_step0 a b;
  cswap bit a b;
  lemma_swaped_steps #c (fromDomain_ #c (as_nat c h0 a)) (fromDomain_ #c (as_nat c h0 b))
  

val _montgomery_ladder_power: #c: curve -> a: felem c -> b: felem c 
  -> scalar: glbuffer uint8 (getScalarLen c) -> Stack unit
  (requires fun h -> live h a /\ live h b /\ live h scalar /\ as_nat c h a < getPrime c /\ 
    as_nat c h b < getPrime c /\ disjoint a b /\ disjoint a scalar /\ disjoint b scalar)
  (ensures fun h0 _ h1 -> modifies (loc a |+| loc b) h0 h1 /\ 
    (
      let a_ = fromDomain_ #c (as_nat c h0 a) in 
      let b_ = fromDomain_ #c (as_nat c h0 b) in 
      let (r0D, r1D) = Lib.LoopCombinators.repeati (getScalarLenNat c) (_pow_step #c (as_seq h0 scalar)) (a_, b_) in 
      r0D == fromDomain_ #c (as_nat c h1 a) /\ r1D == fromDomain_ #c (as_nat c h1 b) /\
      as_nat c h1 a < getPrime c /\ as_nat c h1 b < getPrime c))

  
let _montgomery_ladder_power #c a b scalar = 
  let scalarLen = getScalarLenU64 c in 
  let h0 = ST.get() in 
  [@inline_let]
  let spec_exp h0  = _pow_step #c (as_seq h0 scalar) in 
  [@inline_let]
  let acc (h: mem) : GTot (tuple2 nat_prime nat_prime) = (fromDomain_ #c (as_nat c h a), fromDomain_ #c (as_nat c h b)) in 
  Lib.LoopCombinators.eq_repeati0 (getScalarLenNat c) (spec_exp h0) (acc h0);
  [@inline_let]
  let inv h (i: nat {i <= (getScalarLenNat c)}) = 
    live h a /\ live h b /\ live h scalar /\ modifies (loc a |+| loc b) h0 h /\ as_nat c h a < getPrime c /\ as_nat c h b < getPrime c /\
    acc h == Lib.LoopCombinators.repeati i (spec_exp h0) (acc h0) in 
  for 0ul scalarLen inv (
    fun i -> 
	  montgomery_ladder_power_step a b scalar i;
	  Lib.LoopCombinators.unfold_repeati (getScalarLenNat c) (spec_exp h0) (acc h0) (uint_v i))


val montgomery_ladder_power: #c: curve -> a: felem c 
  -> scalar: glbuffer uint8 (getScalarLen c) -> result: felem c -> 
  Stack unit 
    (requires fun h -> live h a /\ live h scalar /\ live h result /\ as_nat c h a < getPrime c /\ disjoint a scalar)
    (ensures fun h0 _ h1 -> modifies (loc a |+| loc result) h0 h1 /\
      as_nat c h1 result < getPrime c /\ 
      (
	let r0D = pow_spec #c (as_seq h0 scalar) (fromDomain_ #c (as_nat c h0 a)) in 
	r0D == fromDomain_ #c (as_nat c h1 result)
      ) /\

      (
      let k = fromDomain_ #c (as_nat c h0 a) in 
      let scalar = as_seq h0 scalar in 
      let prime = getPrime c in 
      as_nat c h1 result = toDomain_ #c ((pow k (Lib.ByteSequence.nat_from_bytes_le scalar) % getPrime c
      ))))


let montgomery_ladder_power #c a scalar result = 
  push_frame(); 
    let h0 = ST.get() in 
  let len = getCoordinateLenU64 c in 
  let p = create len (u64 0) in  
    upload_one_montg_form #c p; 
    _montgomery_ladder_power #c p a scalar;
    lemmaToDomainAndBackIsTheSame #c 1;  
    copy result p;
  let h1 = ST.get() in 
 
  assert(
    let k = as_seq h0 scalar in 
    let a = fromDomain_ #c (as_nat c h0 a) in 
    let r0D = pow_spec #c k a in 
    
    r0D == pow a (Lib.ByteSequence.nat_from_bytes_le k) % getPrime c /\
    r0D == fromDomain_ #c (as_nat c h1 result));

  lemmaFromDomainToDomain #c (as_nat c h1 result); 
  pop_frame()  


let exponent #c a result tempBuffer = 
  match c with 
  |P384 ->
    recall_contents (prime_inverse_buffer #c) (prime_inverse_seq #c);
    montgomery_ladder_power #c a prime_inverse_buffer result
  |P256 -> 
    exponent_p256 a result tempBuffer


inline_for_extraction noextract
let sqPower_list_p256 : list uint8 =
  [
      u8 0;  u8 0;  u8 0;  u8 0;   u8 0;   u8 0;   u8 0;   u8 0;
      u8 0;  u8 0;  u8 0;  u8 64;  u8 0;   u8 0;   u8 0;   u8 0;
      u8 0;  u8 0;  u8 0;  u8 0;   u8 0;   u8 0;   u8 0;   u8 64;
      u8 0;  u8 0;  u8 0;  u8 192; u8 255; u8 255; u8 255; u8 63
  ]


inline_for_extraction noextract
let sqPower_list_p384 : list uint8 =
    [ 
      u8 0;   u8 0;   u8 0;   u8 64;  u8 0;   u8 0;   u8 0;   u8 0; 
      u8 0;   u8 0;   u8 0;   u8 192; u8 255; u8 255; u8 255; u8 191;
      u8 255; u8 255; u8 255; u8 255; u8 255; u8 255; u8 255; u8 255; 
      u8 255; u8 255; u8 255; u8 255; u8 255; u8 255; u8 255; u8 255; 
      u8 255; u8 255; u8 255; u8 255; u8 255; u8 255; u8 255; u8 255;
      u8 255; u8 255; u8 255; u8 255; u8 255; u8 255; u8 255; u8 63
   ]


inline_for_extraction noextract
let sqPower_list (#c: curve) : list uint8 = 
  match c with 
  |P256 -> sqPower_list_p256
  |P384 -> sqPower_list_p384


let sqPower_seq (#c: curve) : s: lseq uint8 (getScalarLenNat c)
  {
    Lib.ByteSequence.nat_from_intseq_le s == (getPrime c + 1) / 4 /\
    Lib.ByteSequence.nat_from_intseq_le s < getPrime c
  } =
  let open Lib.ByteSequence in 
  assert_norm (List.Tot.length (sqPower_list #P256) == 32);
  assert_norm (List.Tot.length (sqPower_list #P384) == 48);
  
  nat_from_intlist_seq_le 32 (sqPower_list #P256);
  nat_from_intlist_seq_le 48 (sqPower_list #P384); 
  
  assert_norm (nat_from_intlist_le (sqPower_list #P256)  == (getPrime P256 + 1) / 4);
  assert_norm (nat_from_intlist_le (sqPower_list #P384)  == (getPrime P384 + 1) / 4);
  
  of_list (sqPower_list #c)


inline_for_extraction
let sqPower_buffer_p256 : x: glbuffer uint8 (getScalarLen P256) {witnessed x sqPower_seq /\ recallable x} = 
  createL_global sqPower_list_p256


inline_for_extraction
let sqPower_buffer_p384 : x: glbuffer uint8 (getScalarLen P384) {witnessed x sqPower_seq /\ recallable x} = 
  createL_global sqPower_list_p384

inline_for_extraction
let sqPower_buffer (#c: curve): (x: glbuffer uint8 (getScalarLen c)) = 
  match c with
  |P256 -> sqPower_buffer_p256 
  |P384 -> sqPower_buffer_p384 


let square_root #c a result = 
  recall_contents (sqPower_buffer #c) (sqPower_seq #c);
  montgomery_ladder_power a sqPower_buffer result
