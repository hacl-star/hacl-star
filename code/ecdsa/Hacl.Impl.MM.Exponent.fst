module Hacl.Impl.MM.Exponent

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

open Hacl.Impl.EC.MontgomeryMultiplication
open Hacl.Spec.MontgomeryMultiplication

open Hacl.Spec.EC.Definition
open Hacl.Lemmas.P256
open Spec.ECDSA.Lemmas
open Spec.ECC
open Spec.ECC.Curves
open Hacl.Spec.MontgomeryMultiplication


#set-options "--z3rlimit 100"

(* For p256 curve there is a special implementation of multiplication by prime - 2 *)

[@ CInline]
val cswap: #c: curve -> #m: mode -> bit:uint64{v bit <= 1} -> p: felem c -> q: felem c -> 
  Stack unit
  (requires fun h -> as_nat c h p < getModePrime m c /\ as_nat c h q < getModePrime m c /\ 
    live h p /\ live h q /\ eq_or_disjoint p q)
  (ensures  fun h0 _ h1 -> modifies (loc p |+| loc q) h0 h1 /\ (
    let (r0, r1) = conditional_swap_pow #c bit (as_nat c h0 p) (as_nat c h0 q) in 
    let pBefore = as_seq h0 p in let qBefore = as_seq h0 q in 
    let pAfter = as_seq h1 p in let qAfter = as_seq h1 q in 
    as_nat c h1 p < getModePrime m c /\ as_nat c h1 q < getModePrime m c /\
    (v bit == 1 ==> as_seq h1 p == as_seq h0 q /\ as_seq h1 q == as_seq h0 p) /\
    (v bit == 0 ==> as_seq h1 p == as_seq h0 p /\ as_seq h1 q == as_seq h0 q)))


let cswap #c #m bit p1 p2 =
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
val montgomery_ladder_power_step0: #c: curve -> #m: mode -> a: felem c -> b: felem c -> Stack unit
  (requires fun h -> live h a /\ live h b /\ as_nat c h a < getModePrime m c /\ as_nat c h b < getModePrime m c /\ disjoint a b)
  (ensures fun h0 _ h1 -> modifies (loc a |+| loc b) h0 h1 /\ 
    as_nat c h1 a < getModePrime m c /\ as_nat c h1 b < getModePrime m c /\ (
    let (r0D, r1D) = _pow_step0 #c #m (fromDomain_ #c #m (as_nat c h0 a)) (fromDomain_ #c #m (as_nat c h0 b)) in 
    r0D == fromDomain_ #c #m (as_nat c h1 a) /\ r1D == fromDomain_ #c #m (as_nat c h1 b)))

let montgomery_ladder_power_step0 #c #m a b = 
  let h0 = ST.get() in 
  montgomery_multiplication_buffer #c m a b b;
  montgomery_square_buffer #c m a a;
  let h1 = ST.get() in 
    let aD = fromDomain_ #c #m (as_nat c h0 a) in 
    let bD = fromDomain_ #c #m (as_nat c h0 b) in 
    lemmaToDomainFromDomain #c #m (aD * bD % getModePrime m c);
    lemmaToDomainFromDomain #c #m (aD * aD % getModePrime m c)


val montgomery_ladder_power_step: #c: curve -> #m: mode -> a: felem c -> b: felem c 
  -> scalar: glbuffer uint8 (getScalarLenBytes c) 
  -> i:size_t{v i < v (getScalarLen c)} -> 
  Stack unit
  (requires fun h -> live h a /\ live h b /\ live h scalar /\ as_nat c h a < getModePrime m c /\ 
    as_nat c h b < getModePrime m c /\ disjoint a b)
  (ensures fun h0 _ h1 -> modifies (loc a |+| loc b) h0 h1 /\ (
    let a_ = fromDomain_ #c #m (as_nat c h0 a) in 
    let b_ = fromDomain_ #c #m (as_nat c h0 b) in 
    let (r0D, r1D) = _pow_step #c #m (as_seq h0 scalar) (uint_v i) (a_, b_) in 
    r0D == fromDomain_ #c #m (as_nat c h1 a) /\ r1D == fromDomain_ #c #m (as_nat c h1 b) /\ 
    as_nat c h1 a < getModePrime m c /\ as_nat c h1 b < getModePrime m c))  

let montgomery_ladder_power_step #c #m a b scalar i = 
    let h0 = ST.get() in 
  let bit0 = getScalarLen c -. 1ul -. i in  
  let bit = scalar_bit #c scalar bit0 in 
  cswap #c #m bit a b;
  montgomery_ladder_power_step0 #c #m a b;
  cswap #c #m bit a b;
  lemma_swaped_steps #c #m (fromDomain_ #c #m (as_nat c h0 a)) (fromDomain_ #c #m (as_nat c h0 b))
  

val _montgomery_ladder_power: #c: curve -> #m: mode -> a: felem c -> b: felem c 
  -> scalar: glbuffer uint8 (getScalarLenBytes c) -> Stack unit
  (requires fun h -> live h a /\ live h b /\ live h scalar /\ as_nat c h a < getModePrime m c /\ 
    as_nat c h b < getModePrime m c /\ disjoint a b /\ disjoint a scalar /\ disjoint b scalar)
  (ensures fun h0 _ h1 -> modifies (loc a |+| loc b) h0 h1 /\ (
    let a_ = fromDomain_ #c #m (as_nat c h0 a) in 
    let b_ = fromDomain_ #c #m (as_nat c h0 b) in 
    let (r0D, r1D) = Lib.LoopCombinators.repeati (v (getScalarLen c)) (_pow_step #c #m (as_seq h0 scalar)) (a_, b_) in 
    r0D == fromDomain #c (as_nat c h1 a) /\ r1D == fromDomain #c (as_nat c h1 b) /\
    as_nat c h1 a < getModePrime m c /\ as_nat c h1 b < getModePrime m c))

let _montgomery_ladder_power #c #m a b scalar = 
  let scalarLen = getScalarLen c in 
  let h0 = ST.get() in 
    [@inline_let]
    let spec_exp h0 = _pow_step #c #m (as_seq h0 scalar) in 
    [@inline_let]
    let acc (h: mem) : GTot (tuple2 (elem (getModePrime m c)) (elem (getModePrime m c))) = fromDomain_ #c #m (as_nat c h a), fromDomain_ #c #m (as_nat c h b) in

  Lib.LoopCombinators.eq_repeati0 (v (getScalarLen c)) (spec_exp h0) (acc h0);
  [@inline_let]
  let inv h (i: nat {i <= v (getScalarLen c)}) = live h a /\ live h b /\ live h scalar /\ modifies (loc a |+| loc b) h0 h /\ 
    as_nat c h a < getModePrime m c /\ as_nat c h b < getModePrime m c /\
    acc h == Lib.LoopCombinators.repeati i (spec_exp h0) (acc h0) in 
  admit();
  for 0ul scalarLen inv (fun i -> 
    montgomery_ladder_power_step #c #m a b scalar i;
    Lib.LoopCombinators.unfold_repeati (v (getScalarLen c)) (spec_exp h0) (acc h0) (uint_v i)
    );
    
  admit()


val montgomery_ladder_power: #c: curve -> #m: mode -> a: felem c 
  -> scalar: glbuffer uint8 (getScalarLenBytes c) -> result: felem c -> 
  Stack unit 
  (requires fun h -> live h a /\ live h scalar /\ live h result /\ as_nat c h a < getPrime c /\ disjoint a scalar)
  (ensures fun h0 _ h1 -> modifies (loc a |+| loc result) h0 h1 /\ as_nat c h1 result < getPrime c /\ (
    let r0D = pow_spec #c #m (as_seq h0 scalar) (fromDomain #c (as_nat c h0 a)) in 
    let k = fromDomain #c (as_nat c h0 a) in 
    let scalar = as_seq h0 scalar in 
    let prime = getPrime c in 
    as_nat c h1 result = toDomain #c ((pow k (Lib.ByteSequence.nat_from_bytes_le scalar)) % getPrime c) /\
    r0D == fromDomain #c (as_nat c h1 result)))

let montgomery_ladder_power #c #m a scalar result = 
  push_frame(); 
  let len = getCoordinateLenU64 c in 
  let p = create len (u64 0) in  
    lemma_create_zero_buffer (v (getCoordinateLenU64 c)) c;
  upload_one_montg_form #c p; 
    lemmaToDomain #c #m 1;
    let h0 = ST.get() in 
  _montgomery_ladder_power #c #m p a scalar;
    lemmaToDomainFromDomain #c #m 1;  
  copy result p;
  let h1 = ST.get() in admit();
  assert(
    let k = as_seq h0 scalar in 
    let a = fromDomain #c (as_nat c h0 a) in 
    let r0D = pow_spec #c #m k a in 
    
    r0D == pow a (Lib.ByteSequence.nat_from_bytes_le k) % getPrime c /\
    r0D == fromDomain #c (as_nat c h1 result));

  lemmaFromDomainToDomain #c #m (as_nat c h1 result); 
  pop_frame()  

