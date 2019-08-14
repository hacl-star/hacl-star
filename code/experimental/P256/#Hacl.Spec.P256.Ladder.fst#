module Hacl.Spec.P256.Ladder

open FStar.HyperStack.All
open FStar.HyperStack
module ST = FStar.HyperStack.ST

open Lib.IntTypes
open Lib.Buffer

open Hacl.Spec.P256.Definitions
open Hacl.Spec.P256.MontgomeryMultiplication
open Hacl.Spec.P256.MontgomeryMultiplication.PointAdd 
open Hacl.Spec.P256.MontgomeryMultiplication.PointDouble
open Hacl.Spec.P256


open FStar.Math.Lemmas
open Lib.Sequence
open Lib.ByteSequence


val point_prime_to_coordinates: p: point_seq -> Tot (r: tuple3 nat nat nat {
  let x2, y2, z2 = r in 
  let x1, y1, z1 = felem_seq_as_nat (sub p 0 4), felem_seq_as_nat (sub p 4 4), felem_seq_as_nat (sub p 8 4) in
  x1 == x2 /\ y1 == y2 /\ z1 == z2})

let point_prime_to_coordinates p  =  
   felem_seq_as_nat (sub p 0 4), felem_seq_as_nat (sub p 4 4), felem_seq_as_nat (sub p 8 4) 
   

val montgomery_ladder_step0: p: point_prime -> q: point_prime -> 
  Tot (r: tuple2 point_prime point_prime 
    {
      let r0, r1 = r in 

      let r0_coordinates = point_prime_to_coordinates r0 in 
      let r1_coordinates = point_prime_to_coordinates r1 in 
      let p = point_prime_to_coordinates p in 
      let q = point_prime_to_coordinates q in 
    
      let r0N, r1N = _ml_step0 (fromDomainPoint p) (fromDomainPoint q) in 
      r0N == fromDomainPoint r0_coordinates /\ r1N == fromDomainPoint r1_coordinates
    } 
 )   
    

let montgomery_ladder_step0 r0 r1 = 
  let r0 = point_add_seq r1 r0 in 
  let r1 = point_double_seq r1 in 
  (r0, r1)


#reset-options "--z3refresh --z3rlimit  100"


val montgomery_ladder_step1_seq: p: point_prime -> q: point_prime -> 
  Tot (r: tuple2 point_prime point_prime 
    {
      let r0, r1 = r in

      let r0_coordinates = point_prime_to_coordinates r0 in 
      let r1_coordinates = point_prime_to_coordinates r1 in 
      let p = point_prime_to_coordinates p in 
      let q = point_prime_to_coordinates q in 
    
      let r0N, r1N = _ml_step1 (fromDomainPoint p) (fromDomainPoint q) in 
      r0N == fromDomainPoint r0_coordinates /\ r1N == fromDomainPoint r1_coordinates
    }
 )    


let montgomery_ladder_step1_seq r0 r1 = 
  let r1 = point_add_seq r0 r1 in 
  let r0 = point_double_seq r0 in  
  (r0, r1)


val swap: p: point_prime -> q: point_prime -> Tot (r: tuple2 point_prime point_prime {let pNew, qNew = r in 
  pNew == q /\ qNew == p})

let swap p q = (q, p)


val conditional_swap: i: uint64 -> p: point_prime -> q: point_prime -> Tot (r: tuple2 point_prime point_prime
  {
    let pNew, qNew = r in 
    if uint_v i = 0 then pNew == p /\ qNew == q
    else
      let p1, q1 = swap p q in 
      p1 == pNew /\ q1 == qNew
 }
)

#reset-options "--z3refresh --z3rlimit  100"

let conditional_swap i p q = 
  if uint_v i = 0 then 
    (p, q)
  else
    (q, p)


(*This code is taken from Curve25519, written by Polubelova M *)
val lemma_cswap2_step:
    bit:uint64{v bit <= 1}
  -> p1:uint64
  -> p2:uint64
  -> Lemma (
      let mask = u64 0 -. bit in
      let dummy = mask &. (p1 ^. p2) in
      let p1' = p1 ^. dummy in
      let p2' = p2 ^. dummy in
      if v bit = 1 then p1' == p2 /\ p2' == p1 else p1' == p1 /\ p2' == p2)
let lemma_cswap2_step bit p1 p2 =
  let mask = u64 0 -. bit in
  assert (v bit == 0 ==> v mask == 0);
  assert (v bit == 1 ==> v mask == pow2 64 - 1);
  let dummy = mask &. (p1 ^. p2) in
  logand_lemma mask (p1 ^. p2);
  assert (v bit == 1 ==> v dummy == v (p1 ^. p2));
  assert (v bit == 0 ==> v dummy == 0);
  let p1' = p1 ^. dummy in
  uintv_extensionality dummy (if v bit = 1 then (p1 ^. p2) else u64 0);
  logxor_lemma p1 p2;
  let p2' = p2 ^. dummy in
  logxor_lemma p2 p1

[@ CInline]
val cswap: bit:uint64{v bit <= 1} -> p:point -> q:point
  -> Stack unit
    (requires fun h ->
      live h p /\ live h q /\ (disjoint p q \/ p == q) /\
           
      as_nat h (gsub p (size 0) (size 4)) < prime /\ 
      as_nat h (gsub p (size 4) (size 4)) < prime /\
      as_nat h (gsub p (size 8) (size 4)) < prime /\
	     
      as_nat h (gsub q (size 0) (size 4)) < prime /\  
      as_nat h (gsub q (size 4) (size 4)) < prime /\
      as_nat h (gsub q (size 8) (size 4)) < prime
)
    (ensures  fun h0 _ h1 ->
      modifies (loc p |+| loc q) h0 h1 /\
      (let pBefore = as_seq h0 p in let qBefore = as_seq h0 q in 
	let pAfter = as_seq h1 p in let qAfter = as_seq h1 q in 
	let condP0, condP1 = conditional_swap bit pBefore qBefore  in 
	condP0 == pAfter /\ condP1 == qAfter) /\ 

      (v bit == 1 ==> as_seq h1 p == as_seq h0 q /\ as_seq h1 q == as_seq h0 p) /\
      (v bit == 0 ==> as_seq h1 p == as_seq h0 p /\ as_seq h1 q == as_seq h0 q))


let cswap bit p1 p2 =
  let h0 = ST.get () in
  let mask = u64 0 -. bit in

  [@ inline_let]
  let inv h1 (i:nat{i <= 12}) =
    (forall (k:nat{k < i}).
      if v bit = 1
      then (as_seq h1 p1).[k] == (as_seq h0 p2).[k] /\ (as_seq h1 p2).[k] == (as_seq h0 p1).[k]
      else (as_seq h1 p1).[k] == (as_seq h0 p1).[k] /\ (as_seq h1 p2).[k] == (as_seq h0 p2).[k]) /\
    (forall (k:nat{i <= k /\ k < 12}).
      (as_seq h1 p1).[k] == (as_seq h0 p1).[k] /\ (as_seq h1 p2).[k] == (as_seq h0 p2).[k]) /\
    modifies (loc p1 |+| loc p2) h0 h1 in
 
  Lib.Loops.for 0ul 12ul inv
    (fun i ->
      let dummy = mask &. (p1.(i) ^. p2.(i)) in
      p1.(i) <- p1.(i) ^. dummy;
      p2.(i) <- p2.(i) ^. dummy;
      lemma_cswap2_step bit ((as_seq h0 p1).[v i]) ((as_seq h0 p2).[v i])
    );
  let h1 = ST.get () in
  Lib.Sequence.eq_intro (as_seq h1 p1) (if v bit = 1 then as_seq h0 p2 else as_seq h0 p1);
  Lib.Sequence.eq_intro (as_seq h1 p2) (if v bit = 1 then as_seq h0 p1 else as_seq h0 p2)



#reset-options "--z3refresh --z3rlimit 100"

val lemma_swaped_steps: p: point_prime -> q: point_prime -> 
  Lemma (
    let (afterSwapP, afterSwapQ) = swap p q in 
    let p1, q1 = montgomery_ladder_step1_seq afterSwapP afterSwapQ in 
    let p2, q2 = swap p1 q1 in 
    let r0, r1 = montgomery_ladder_step0 p q in 
    p2 == r0 /\ q2 == r1)

let lemma_swaped_steps p q = 
  let p0, q0 = montgomery_ladder_step0 p q in 
    assert(p0 == point_add_seq q p);
    assert(q0 == point_double_seq q);
  
  let afterSwapP, afterSwapQ = swap p q in 
    assert(afterSwapP == q /\ afterSwapQ == p);
  let (p1, q1) = montgomery_ladder_step1_seq afterSwapP afterSwapQ in 
    assert(q1 == point_add_seq q p);
    assert(p1 == point_double_seq q);
  let (p2, q2) = swap p1 q1 in 
    assert(p2 == point_add_seq q p);
    assert(q2 == point_double_seq q);
    assert(p2 == p0);
    assert(q2 == q0)


val montgomery_ladder_step_swap: p: point_prime -> q: point_prime -> k: scalar -> i: nat {i < 256} -> 
  Tot (r: tuple2 point_prime point_prime 
  {
    let r0, r1 = r in 
    let r0_coordinates = fromDomainPoint(point_prime_to_coordinates r0) in 
    let r1_coordinates = fromDomainPoint(point_prime_to_coordinates r1) in 
    let p = fromDomainPoint(point_prime_to_coordinates p) in 
    let q = fromDomainPoint(point_prime_to_coordinates q) in 

    let r0N, r1N = _ml_step k i (p, q) in 
    r0N == r0_coordinates /\ r1N ==  r1_coordinates
  }
)
    


let montgomery_ladder_step_swap p q k i = 
  let bit = 255 - i in 
  let bit = ith_bit k bit in 
  let p0, q0 = conditional_swap bit p q in 
  let p1, q1 = montgomery_ladder_step1_seq p0 q0 in 
  let p2, q2 = conditional_swap bit p1 q1 in

  lemma_swaped_steps p q;

  assert(if uint_v bit = 0 then p0 == p /\ q0 == q else p0 == q /\ q0 == p);
  assert(if uint_v bit = 0 
    then 
      let r0, r1 = montgomery_ladder_step1_seq p q in 
      p2 == r0 /\ q2 == r1 
    else 
     let r0, r1 = montgomery_ladder_step0 p q in p2 == r0 /\ q2 == r1);

  assert(
     let pD = fromDomainPoint (point_prime_to_coordinates p) in 
     let qD = fromDomainPoint (point_prime_to_coordinates q) in 

     let p2D = fromDomainPoint (point_prime_to_coordinates p2) in 
     let q2D = fromDomainPoint (point_prime_to_coordinates q2) in 

     let r0Step1, r1Step1 = _ml_step1 pD qD in 
     let r0Step0, r1Step0 = _ml_step0 pD qD in 

     if uint_v bit = 0 then 
       r0Step1 == p2D /\ r1Step1 == q2D
     else 
       r0Step0 == p2D /\ r1Step0 == q2D
 
    );

  let open Lib.RawIntTypes in  

  
  assert(
    let pD = fromDomainPoint (point_prime_to_coordinates p) in 
    let qD = fromDomainPoint (point_prime_to_coordinates q) in 

    let p2D = fromDomainPoint (point_prime_to_coordinates p2) in 
    let q2D = fromDomainPoint (point_prime_to_coordinates q2) in 
    
    let rf, qf = _ml_step k i (pD, qD) in 

    let r0Step1, r1Step1 = _ml_step1 pD qD in 
    let r0Step0, r1Step0 = _ml_step0 pD qD  in 

    if uint_to_nat bit = 0 then 
       rf == r0Step1 /\ qf == r1Step1
    else 
       rf == r0Step0 /\ qf == r1Step0);


    assert(
    let pD = fromDomainPoint (point_prime_to_coordinates p) in 
    let qD = fromDomainPoint (point_prime_to_coordinates q) in 

    let p2D = fromDomainPoint (point_prime_to_coordinates p2) in 
    let q2D = fromDomainPoint (point_prime_to_coordinates q2) in 
    
    let rf, qf = _ml_step k i (pD, qD) in 

    let r0Step1, r1Step1 = _ml_step1 pD qD in 
    let r0Step0, r1Step0 = _ml_step0 pD qD  in 

    if uint_to_nat bit = 0 then 
       rf == p2D /\ qf == q2D
    else 
       rf == p2D /\ qf == q2D);


   (p2, q2)  
 
    
  


