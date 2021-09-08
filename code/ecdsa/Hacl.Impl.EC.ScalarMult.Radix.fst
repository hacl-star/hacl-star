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
open Hacl.Impl.EC.PointDouble


open Hacl.Spec.MontgomeryMultiplication

#set-options " --z3rlimit 200"

open Hacl.Impl.EC.Masking.ScalarAccess
open Hacl.Impl.EC.Precomputed





[@ CInline]
inline_for_extraction noextract  
val montgomery_ladder_step_radix_precomputed: #c: curve ->
  p: point c -> tempBuffer: lbuffer uint64 (size 88) -> 
  scalar:  lbuffer uint8 (size 32)-> 
  i:size_t{v i < 256} -> 
  Stack unit
  (requires fun h -> live h p /\live h tempBuffer /\ live h scalar /\
    LowStar.Monotonic.Buffer.all_disjoint [loc p;loc tempBuffer; loc scalar])
  (ensures fun h0 _ h1 -> True)


let montgomery_ladder_step_radix_precomputed #c p tempBuffer scalar i =  
  let bits = getScalar_4_byBit #c scalar i in 

  let pointToAdd = create (size 8) (u64 0) in 
  getPointPrecomputedMixed #c scalar i pointToAdd;
  
  point_double p p tempBuffer;
  point_double p p tempBuffer;
  point_double p p tempBuffer;
  point_double p p tempBuffer;

  
  Hacl.Impl.EC.PointAddMixed.point_add_mixed p pointToAdd p tempBuffer



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

  recall_contents points_radix_p256_16 (Lib.Sequence.of_list points_radix_16_list_p256);
  let bits = getScalar_4_byBit #c scalar 0 in 
  let pointToStart = sub (points_radix_p256_16) (bits *. size 8) (size 8) in 

  copy (sub p (size 0) (size 8)) pointToStart;

  upd p (size 8) (u64 1);
  upd p (size 9) (u64 0);
  upd p (size 10) (u64 0);
  upd p (size 11) (u64 0);


  for 1ul 64ul inv 
    (fun i -> let h2 = ST.get() in
      montgomery_ladder_step_radix_precomputed p tempBuffer scalar i
    )


inline_for_extraction noextract
val scalar_multiplication_t_0: #c: curve -> #t:buftype -> q: point c -> p: point c -> result: point c -> 
  scalar: scalar_t #t #c -> 
  tempBuffer: lbuffer uint64 (size 17 *! getCoordinateLenU64 c) ->
  Stack unit 
  (requires fun h -> live h q /\ live h p /\ live h result /\ live h scalar /\ live h tempBuffer /\
    LowStar.Monotonic.Buffer.all_disjoint [loc p; loc q; loc tempBuffer; loc scalar] /\
    disjoint q result /\ eq_or_disjoint p result /\ disjoint result tempBuffer /\ disjoint result scalar /\
    point_eval c h p /\ ~ (isPointAtInfinity (point_as_nat c h p)))
  (ensures fun h0 _ h1 -> modifies (loc q |+| loc result |+| loc tempBuffer) h0 h1 /\ point_eval c h1 q /\ (
    let i1 = point_as_nat c h0 p in point_mult_0 i1 0; 
    let pD = fromDomainPoint #c #DH (point_as_nat c h1 q) in
    let r0, r1 = montgomery_ladder_spec_left (as_seq h0 scalar) (pointAtInfinity, i1) in 
    pD == r0))


let scalar_multiplication_t_0 #c q p result scalar tempBuffer = ()
  (* uploadStartPoints q p result;  *)
  (* montgomery_ladder q result scalar tempBuffer *)


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
  (* uploadStartPointsS2P q result;  *)
(*   montgomery_ladder q result scalar tempBuffer *)
  montgomery_ladder_2_precomputed result scalar tempBuffer;
  copy q result
