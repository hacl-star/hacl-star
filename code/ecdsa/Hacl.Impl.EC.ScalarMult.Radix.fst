module Hacl.Impl.EC.ScalarMult.Radix

open FStar.HyperStack.All
open FStar.HyperStack
module ST = FStar.HyperStack.ST

open Lib.IntTypes
open Lib.Buffer
open Lib.Loops

open Spec.ECC
open Spec.ECC.Curves
open Hacl.Impl.EC.Masking

open Hacl.Spec.EC.Definition

open Hacl.Impl.EC.PointAdd
open Hacl.Impl.EC.PointDouble

open Hacl.Spec.MontgomeryMultiplication

open Hacl.Impl.EC.Masking.ScalarAccess
open Hacl.Impl.EC.Precomputed

open FStar.Mul

open Lib.LoopCombinators
open Hacl.Spec.EC.ScalarMult.Radix


#set-options "--z3rlimit 200 --max_ifuel 0 --max_fuel 0 "


inline_for_extraction noextract
val getPointDoubleNTimes: #c: curve -> p: point c -> tempBuffer: lbuffer uint64 (size 17 *! getCoordinateLenU64 c) ->
  Stack unit 
  (requires fun h -> live h p /\ live h tempBuffer /\ disjoint p tempBuffer /\ point_eval c h p)
  (ensures fun h0 _ h1 -> modifies (loc p |+| loc tempBuffer) h0 h1 /\ point_eval c h1 p /\
    fromDomainPoint #c #DH (point_as_nat c h1 p) == Spec.ECC.Radix.getPointDoubleNTimes #c
      (fromDomainPoint #c #DH(point_as_nat c h0 p)) 4)

let getPointDoubleNTimes #c p tempBuffer = 
  let h0 = ST.get() in 
  let inv h (k: nat) = live h p /\ live h tempBuffer /\ disjoint p tempBuffer /\ point_eval c h p /\ 
    modifies (loc p |+| loc tempBuffer) h0 h /\
    fromDomainPoint #c #DH (point_as_nat c h p) ==
      Lib.LoopCombinators.repeat k (_point_double #c) (fromDomainPoint #c #DH (point_as_nat c h0 p)) in 
  Lib.LoopCombinators.eq_repeat0 (_point_double #c) (fromDomainPoint #c #DH (point_as_nat c h0 p));  
  for 0ul 4ul inv (fun i -> 
    point_double p p tempBuffer; 
    unfold_repeat 4 (_point_double #c) (fromDomainPoint #c #DH (point_as_nat c h0 p)) (v i))


inline_for_extraction noextract  
val scalar_mult_step_radix_precomputed: #c: curve -> #buf_type: buftype 
  -> p: point c -> tempBuffer: lbuffer uint64 (size 17 *! getCoordinateLenU64 c) 
  -> scalar: scalar_t #buf_type #c 
  -> i: size_t{v i >= 1 /\ v i < v (getScalarLenBytes c) * 2 - 1} -> 
  Stack unit
  (requires fun h -> live h p /\ live h tempBuffer /\ live h scalar /\ point_eval c h p /\
    LowStar.Monotonic.Buffer.all_disjoint [loc p; loc tempBuffer; loc scalar])
  (ensures fun h0 _ h1 -> modifies (loc p |+| loc tempBuffer) h0 h1 /\ point_eval c h1 p /\ (
    pointEqual (fromDomainPoint #c #DH (point_as_nat c h1 p)) 
      (Spec.ECC.Radix._ml_step #c #Affine (as_seq h0 scalar) (basePoint #c) (v i - 1) (fromDomainPoint #c #DH (point_as_nat c h0 p)))))


val lemma_test: #c: curve -> si: nat {si < 16} -> p: point_nat_prime #c -> p0: point_nat_prime #c 
  -> pA: point_nat_prime #c 
  -> Lemma (requires (
    let pRadixed = Spec.ECC.Radix.getPointDoubleNTimes #c p 4 in 
    let pointPrecomputed = Spec.ECC.Radix.getPrecomputedPoint_Affine #c p0 si in 
    let pD = fromDomainPoint #c #DH pA in 
    not (pointEqual (Spec.ECC.Radix.getPointDoubleNTimes #c p 4) (Spec.ECC.Radix.getPrecomputedPoint_Affine #c p0 si)) /\ pointEqual pD pointPrecomputed))
  (ensures (
    let pRadixed = Spec.ECC.Radix.getPointDoubleNTimes #c p 4 in 
    let pointPrecomputed = Spec.ECC.Radix.getPrecomputedPoint_Affine #c p0 si in 
    let pD = fromDomainPoint #c #DH pA in 
    pointEqual (_point_add_mixed #c pRadixed pD) (_point_add_mixed #c pRadixed pointPrecomputed)))


let lemma_test #c si p p0 pA = 
  let pRadixed = Spec.ECC.Radix.getPointDoubleNTimes #c p 4 in 
  let pointPrecomputed = Spec.ECC.Radix.getPrecomputedPoint_Affine #c p0 si in 
  let pD = fromDomainPoint #c #DH pA in  
  if (si = 0) then
    begin 
      lemma_point_add_mixed_b_is_infinity pD pointPrecomputed pRadixed
    end 
  else begin 
    lemma_not_affine_equality pD pointPrecomputed; 
    lemma_point_add_mixed_two_points #c pD pointPrecomputed pRadixed
    end



let scalar_mult_step_radix_precomputed #c p tempBuffer scalar i = 
  let h0 = ST.get() in 
  push_frame(); 
    let pointToAdd = create (size 2 *! getCoordinateLenU64 c) (u64 0) in 
    getPointPrecomputedMixed #c scalar i pointToAdd;      
      let h1 = ST.get() in
    Hacl.Impl.P.PointAdd.Aux.lemma_coord_eval c h0 h1 p;
    getPointDoubleNTimes #c p tempBuffer;
      let h2 = ST.get() in
    Hacl.Impl.EC.PointAddMixed.point_add_mixed #c p pointToAdd p tempBuffer;
    
    let h3 = ST.get() in
    pop_frame();
   
    let si = 
      let scalar = scalar_as_nat (as_seq h0 scalar) in 
      Math.Lib.arithmetic_shift_right scalar  (v (getScalarLen c) - ((v i - 1) + 2) * 4) % pow2 4 in 

    let p = fromDomainPoint #c #DH (point_as_nat c h0 p) in 

    assume (not 
      (pointEqual (Spec.ECC.Radix.getPointDoubleNTimes #c p 4) 
      (Spec.ECC.Radix.getPrecomputedPoint_Affine #c (basePoint #c) si))); 


    lemma_test #c si p (basePoint #c) (toJacobianCoordinates (point_affine_as_nat c h1 pointToAdd))



inline_for_extraction noextract
val montgomery_ladder_2_precomputed: #c: curve -> #buf_type: buftype -> p: point c -> 
  scalar: lbuffer_t buf_type uint8 (size 32) -> 
  tempBuffer:  lbuffer uint64 (size 88)  -> 
  Stack unit
  (requires fun h -> True )
  (ensures fun h0 _ h1 -> modifies (loc p |+| loc tempBuffer) h0 h1)

let montgomery_ladder_2_precomputed #c #a p scalar tempBuffer =  
 let h0 = ST.get() in 
  let inv h (i: nat {i <= 64}) = True in 

  recall_contents (points_radix_16 #c) (Lib.Sequence.of_list (points_radix_16_list c));
  let bits = getScalar_4_byBit #c scalar 0 in 
  let pointToStart = sub (points_radix_16 #c) (bits *. size 8) (size 8) in 

  copy (sub p (size 0) (size 8)) pointToStart;

  upd p (size 8) (u64 1);
  upd p (size 9) (u64 0);
  upd p (size 10) (u64 0);
  upd p (size 11) (u64 0);


  for 1ul 64ul inv 
    (fun i -> let h2 = ST.get() in
      scalar_mult_step_radix_precomputed p tempBuffer scalar i
    )


[@ CInline]
inline_for_extraction noextract  
val montgomery_ladder_step_radix: 
   #c: curve ->
  p: point P256 -> tempBuffer: lbuffer uint64 (size 88) -> 
  precomputedTable: lbuffer uint64 (size 192) ->
  scalar:  lbuffer uint8 (size 32) -> 
  i:size_t{v i < 256} -> 
  Stack unit
  (requires fun h -> live h p /\live h tempBuffer /\ live h scalar /\
    LowStar.Monotonic.Buffer.all_disjoint [loc p;loc tempBuffer; loc scalar])
  (ensures fun h0 _ h1 -> True)



let montgomery_ladder_step_radix #c p tempBuffer precomputedTable scalar i =  
  let bits = getScalar_4_byBit #c scalar i in 

  let pointToAdd = create (size 12) (u64 0) in 

  let invK h (k: nat) = True in 
  Lib.Loops.for 0ul 16ul invK
  (fun k -> 
      let mask = eq_mask (to_u64 bits) (to_u64 k) in 
      (* eq_mask_lemma d (to_u64 k);  *)
  
      let lut_cmb_x = sub precomputedTable (k *! 12) (size 4) in 
      let lut_cmb_y = sub precomputedTable (k *! 12 +! (size 4)) (size 4) in
      let lut_cmb_z = sub precomputedTable (k *! 12 +! (size 8)) (size 4) in 

      copy_conditional #c (sub pointToAdd (size 0) (size 4)) lut_cmb_x mask;
      copy_conditional #c (sub pointToAdd (size 4) (size 4)) lut_cmb_y mask;
      copy_conditional #c (sub pointToAdd (size 8) (size 4)) lut_cmb_z mask
      
      
      ); 
      
  
  point_double p p tempBuffer;
  point_double p p tempBuffer;
  point_double p p tempBuffer;
  point_double p p tempBuffer;

  point_add pointToAdd p p tempBuffer


[@ CInline]
val generatePrecomputedTable: #c: curve -> b: lbuffer uint64 (size 192) -> publicKey: point c ->
  tempBuffer: lbuffer uint64 (size 88) -> Stack unit  
  (requires fun h -> True)
  (ensures fun h0 _ h1 -> True)

let generatePrecomputedTable #c b publicKey tempBuffer = 
  let point0 = sub b (size 0) (size 12) in 
  let point1 = sub b (size 12) (size 12) in 
  let point2 = sub b (size 24) (size 12) in 
  let point3 = sub b (size 36) (size 12) in 
  let point4 = sub b (size 48) (size 12) in 
  let point5 = sub b (size 60) (size 12) in 
  let point6 = sub b (size 72) (size 12) in 
  let point7 = sub b (size 84) (size 12) in 
  let point8 = sub b (size 96) (size 12) in 
  let point9 = sub b (size 108) (size 12) in 
  let point10 = sub b (size 120) (size 12) in 
  let point11 = sub b (size 132) (size 12) in 
  let point12 = sub b (size 144) (size 12) in 
  let point13 = sub b (size 156) (size 12) in 
  let point14 = sub b (size 168) (size 12) in 
  let point15 = sub b (size 180) (size 12) in 

  Hacl.Impl.EC.LowLevel.uploadZeroPoint #c point0;
  Hacl.Impl.EC.LowLevel.copy_point #c publicKey point1;
  point_double #c publicKey point2 tempBuffer;
  point_add #c point2 point1 point3 tempBuffer;
  point_double #c point2 point4 tempBuffer;
  point_add #c point4 point1 point5 tempBuffer;
  point_double #c point3 point6 tempBuffer;
  point_add #c point6 point1 point7 tempBuffer;
  point_double #c point4 point8 tempBuffer;
  point_add #c point8 point1 point9 tempBuffer;
  point_double #c point5 point10 tempBuffer;
  point_add #c point10 point1 point11 tempBuffer;
  point_double #c point6 point12 tempBuffer;
  point_add #c point12 point1 point13 tempBuffer;
  point_double #c point7 point14 tempBuffer;
  point_add #c point14 point1 point15 tempBuffer



inline_for_extraction noextract
val montgomery_ladder_2: #buf_type: buftype -> #c: curve -> p: point c -> 
  scalar: lbuffer_t buf_type uint8 (size 32) -> 
  tempBuffer:  lbuffer uint64 (size 88)  -> 
  precomputedTable: lbuffer uint64 (size 192) ->
  Stack unit
  (requires fun h -> True )
  (ensures fun h0 _ h1 -> modifies (loc p |+| loc tempBuffer) h0 h1)

let montgomery_ladder_2 #a #c p scalar tempBuffer precomputedTable =  
 let h0 = ST.get() in 
   push_frame();

     [@inline_let]
     let spec_ml h0 = _ml_step #c (as_seq h0 scalar) in 


     [@inline_let]
     let inv h (i: nat {i <= 64}) = True in 


  let bits =  getScalar_4_byBit #c  scalar (u64 0) in 
  let pointToStart = sub precomputedTable  (bits *. size 12) (size 12) in 

  copy (sub p (size 0) (size 12)) pointToStart;
  
     for 1ul 64ul inv 
       (fun i -> let h2 = ST.get() in
   montgomery_ladder_step_radix #c p tempBuffer precomputedTable scalar i
       );
   pop_frame()





inline_for_extraction noextract
val scalar_multiplication_t_0: #c: curve -> #t:buftype ->  p: point c -> result: point c -> 
  scalar: scalar_t #t #c -> 
  tempBuffer: lbuffer uint64 (size 17 *! getCoordinateLenU64 c) ->
  Stack unit 
  (requires fun h -> True (* live h q /\ live h p /\ live h result /\ live h scalar /\ live h tempBuffer /\
    LowStar.Monotonic.Buffer.all_disjoint [loc p; loc q; loc tempBuffer; loc scalar] /\
    disjoint q result /\ eq_or_disjoint p result /\ disjoint result tempBuffer /\ disjoint result scalar /\
    point_eval c h p /\ ~ (isPointAtInfinity (point_as_nat c h p)) *))
  (ensures fun h0 _ h1 -> True (* modifies (loc q |+| loc result |+| loc tempBuffer) h0 h1 /\ point_eval c h1 q /\ (
    let i1 = point_as_nat c h0 p in point_mult_0 i1 0; 
    let pD = fromDomainPoint #c #DH (point_as_nat c h1 q) in
    let r0, r1 = montgomery_ladder_spec_left (as_seq h0 scalar) (pointAtInfinity, i1) in 
    pD == r0 *))


let scalar_multiplication_t_0 #c p result scalar tempBuffer = 
(*     let len = getCoordinateLenU64 c in 
  let q = sub tempBuffer (size 0) (size 3 *! len) in 
  uploadStartPoints q p result; 
  montgomery_ladder q result scalar tempBuffer;
  copy q result *)
  let bufferPrecomputed = create (size 192) (u64 0) in 
  generatePrecomputedTable bufferPrecomputed result tempBuffer;
  montgomery_ladder_2 result scalar tempBuffer bufferPrecomputed


inline_for_extraction noextract
val secretToPublic_0: #c: curve -> #t: buftype -> q: point c -> result: point c -> 
  scalar: lbuffer_t t uint8 (getScalarLenBytes c) -> 
  tempBuffer: lbuffer uint64 (size 17 *! getCoordinateLenU64 c) ->
  Stack unit 
  (requires fun h -> live h q /\ live h result /\ live h scalar /\ live h tempBuffer /\
    LowStar.Monotonic.Buffer.all_disjoint [loc q; loc tempBuffer; loc scalar] /\
    disjoint q result /\ disjoint result tempBuffer /\ disjoint result scalar)
  (ensures fun h0 _ h1 -> modifies (loc q |+| loc result |+| loc tempBuffer) h0 h1 /\ point_eval c h1 q /\ (
    let i1 = basePoint #c in 
    point_mult_0 i1 0; 
    let pD = fromDomainPoint #c #DH (point_as_nat c h1 q) in
    let r0, _ = montgomery_ladder_spec_left (as_seq h0 scalar) (pointAtInfinity , i1) in pD == r0))


let secretToPublic_0 #c q result scalar tempBuffer = 
(*   uploadStartPointsS2P q result; 
  montgomery_ladder q result scalar tempBuffer
 *)  montgomery_ladder_2_precomputed result scalar tempBuffer;
  copy q result
