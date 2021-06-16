module Hacl.Impl.EC.MM.Exponent

open FStar.HyperStack.All
open FStar.HyperStack
module ST = FStar.HyperStack.ST

open Lib.IntTypes
open Lib.Buffer

open Hacl.Impl.EC.LowLevel 
open FStar.Mul
open Lib.Loops

open Hacl.Spec.EC.Definition
open Hacl.EC.Lemmas
open Spec.ECDSA.Lemmas
open Spec.ECC.Curves

open Hacl.Impl.EC.MontgomeryMultiplication
friend Hacl.Spec.MontgomeryMultiplication

#set-options "--z3rlimit 100"

inline_for_extraction noextract
val cswap: #c: curve -> #m: mode -> bit:uint64{v bit <= 1} -> p: felem c -> q: felem c -> 
  Stack unit
  (requires fun h -> as_nat c h p < getModePrime m c /\ as_nat c h q < getModePrime m c /\ 
    live h p /\ live h q /\ eq_or_disjoint p q)
  (ensures  fun h0 _ h1 -> modifies (loc p |+| loc q) h0 h1 /\ (
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


#set-options "--z3rlimit 300"

inline_for_extraction noextract
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
    as_nat c h1 a < getModePrime m c /\ as_nat c h1 b < getModePrime m c ))  

let montgomery_ladder_power_step #c #m p q scalar i = 
    let h0 = ST.get() in 
  let bit0 = getScalarLen c -! 1ul -! i in  
  let bit = scalar_bit #c scalar bit0 in 
  cswap #c #m bit p q;
    let h1 = ST.get() in 
  montgomery_ladder_power_step0 #c #m p q;
    let h2 = ST.get() in 
  cswap #c #m bit p q;
    let h3 = ST.get() in 

  let p0D, q0D = (fromDomain_ #c #m (as_nat c h0 p)), (fromDomain_ #c #m (as_nat c h0 q)) in 
  lemma_swaped_steps #c #m p0D q0D



let _montgomery_ladder_power #c #m a b scalar = 
  let scalarLen = getScalarLen c in 
  let h0 = ST.get() in 
    [@inline_let]
    let spec_exp h0 = _pow_step #c #m (as_seq h0 scalar) in 
    [@inline_let]
    let acc (h: mem) : GTot (tuple2 (elem (getModePrime m c)) (elem (getModePrime m c))) = 
      fromDomain_ #c #m (as_nat c h a), fromDomain_ #c #m (as_nat c h b) in

    [@inline_let]
    let inv h (i: nat {i <= v (getScalarLen c)}) = live h a /\ live h b /\ live h scalar /\ modifies (loc a |+| loc b) h0 h /\ 
      as_nat c h a < getModePrime m c /\ as_nat c h b < getModePrime m c /\
      acc h == Lib.LoopCombinators.repeati i (spec_exp h0) (acc h0) in 
 
  Lib.LoopCombinators.eq_repeati0 (v (getScalarLen c)) (spec_exp h0) (acc h0);
  for 0ul scalarLen inv (fun i -> 
    montgomery_ladder_power_step #c #m a b scalar i;
    Lib.LoopCombinators.unfold_repeati (v (getScalarLen c)) (spec_exp h0) (acc h0) (uint_v i))


inline_for_extraction noextract 
val upload_one_montg_form: #c: curve -> #m: mode -> b: felem c -> Stack unit
  (requires fun h -> live h b)
  (ensures fun h0 _ h1 -> modifies (loc b) h0 h1 /\ as_nat c h1 b == toDomain_ #c #m 1)

let upload_one_montg_form #c #m b = 
  match m with 
  |DH -> Hacl.Impl.EC.LowLevel.upload_one_montg_form b
  |DSA -> Hacl.Impl.ECDSA.LowLevel.upload_one_montg_form b


inline_for_extraction noextract
val montgomery_ladder_power_: #c: curve -> #m: mode -> a: felem c 
  -> scalar: glbuffer uint8 (getCoordinateLenU c) -> result: felem c -> 
  Stack unit 
  (requires fun h -> live h a /\ live h scalar /\ live h result /\ as_nat c h a < getModePrime m c /\
    disjoint a scalar)
  (ensures fun h0 _ h1 -> modifies (loc a |+| loc result) h0 h1 /\ 
    as_nat c h1 result < getModePrime m c /\ (
    let r0D = pow_spec #c #m (as_seq h0 scalar) (fromDomain_ #c #m (as_nat c h0 a)) in 
    let k = fromDomain_ #c #m (as_nat c h0 a) in 
    let scalar = as_seq h0 scalar in 
    let prime = getModePrime m c in 
    as_nat c h1 result = toDomain_ #c #m ((pow k (Lib.ByteSequence.nat_from_bytes_le scalar)) % prime) /\ 
    r0D == fromDomain_ #c #m (as_nat c h1 result)))

let montgomery_ladder_power_ #c #m a scalar result = 
  push_frame(); 
  let len = getCoordinateLenU64 c in 
  let p = create len (u64 0) in  
    lemma_create_zero_buffer #U64 (v (getCoordinateLenU64 c)) c;
  upload_one_montg_form #c #m p; 
  
  copy a result;
    lemmaToDomain #c #m 1;
    let h0 = ST.get() in 
  _montgomery_ladder_power #c #m p a scalar;
    let h1 = ST.get() in 
  copy result p;
  
  assert( 
    let b_ = fromDomain_ #c #m (as_nat c h0 a) in 
    let r0D = pow_spec #c #m (as_seq h0 scalar) (fromDomain_ #c #m (as_nat c h0 a)) in 
    r0D == fromDomain_ #c #m (as_nat c h1 p));

  lemmaFromDomainToDomain #c #m (as_nat c h1 p); 

  pop_frame()  



val montgomery_ladder_power_p256: a: felem P256
  -> scalar: glbuffer uint8 (getCoordinateLenU P256) -> result: felem P256 -> 
  Stack unit 
  (requires fun h -> live h a /\ live h scalar /\ live h result /\ as_nat P256 h a < getModePrime DH P256 /\
    disjoint a scalar)
  (ensures fun h0 _ h1 -> modifies (loc a |+| loc result) h0 h1 /\ 
    as_nat P256 h1 result < getModePrime DH P256 /\ (
    let r0D = pow_spec #P256 #DH (as_seq h0 scalar) (fromDomain_ #P256 #DH (as_nat P256 h0 a)) in 
    let k = fromDomain_ #P256 #DH (as_nat P256 h0 a) in 
    let scalar = as_seq h0 scalar in 
    let prime = getModePrime DH P256 in 
    as_nat P256 h1 result = toDomain_ #P256 #DH ((pow k (Lib.ByteSequence.nat_from_bytes_le scalar)) % prime) /\ 
    r0D == fromDomain_ #P256 #DH (as_nat P256 h1 result)))


let montgomery_ladder_power_p256 a scalar result = montgomery_ladder_power_ #P256 #DH a scalar result


val montgomery_ladder_power_p384: a: felem P384
  -> scalar: glbuffer uint8 (getCoordinateLenU P384) -> result: felem P384 -> 
  Stack unit 
  (requires fun h -> live h a /\ live h scalar /\ live h result /\ as_nat P384 h a < getModePrime DH P384 /\
    disjoint a scalar)
  (ensures fun h0 _ h1 -> modifies (loc a |+| loc result) h0 h1 /\ 
    as_nat P384 h1 result < getModePrime DH P384 /\ (
    let r0D = pow_spec #P384 #DH (as_seq h0 scalar) (fromDomain_ #P384 #DH (as_nat P384 h0 a)) in 
    let k = fromDomain_ #P384 #DH (as_nat P384 h0 a) in 
    let scalar = as_seq h0 scalar in 
    let prime = getModePrime DH P384 in 
    as_nat P384 h1 result = toDomain_ #P384 #DH ((pow k (Lib.ByteSequence.nat_from_bytes_le scalar)) % prime) /\ 
    r0D == fromDomain_ #P384 #DH (as_nat P384 h1 result)))


let montgomery_ladder_power_p384 a scalar result = montgomery_ladder_power_ #P384 #DH a scalar result


val montgomery_ladder_power_generic: a: felem Default
  -> scalar: glbuffer uint8 (getCoordinateLenU Default) -> result: felem Default -> 
  Stack unit 
  (requires fun h -> live h a /\ live h scalar /\ live h result /\ as_nat Default h a < getModePrime DH Default /\
    disjoint a scalar)
  (ensures fun h0 _ h1 -> modifies (loc a |+| loc result) h0 h1 /\ 
    as_nat Default h1 result < getModePrime DH Default /\ (
    let r0D = pow_spec #Default #DH (as_seq h0 scalar) (fromDomain_ #Default #DH (as_nat Default h0 a)) in 
    let k = fromDomain_ #Default #DH (as_nat Default h0 a) in 
    let scalar = as_seq h0 scalar in 
    let prime = getModePrime DH Default in 
    as_nat Default h1 result = toDomain_ #Default #DH ((pow k (Lib.ByteSequence.nat_from_bytes_le scalar)) % prime) /\ 
    r0D == fromDomain_ #Default #DH (as_nat Default h1 result)))


let montgomery_ladder_power_generic a scalar result = montgomery_ladder_power_ #Default #DH a scalar result

let montgomery_ladder_power #c a scalar result = 
  match c with 
  |P256 -> montgomery_ladder_power_p256 a scalar result
  |P384 -> montgomery_ladder_power_p384 a scalar result
  |Default -> montgomery_ladder_power_generic a scalar result
