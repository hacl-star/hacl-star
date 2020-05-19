module Hacl.Impl.P256.PointDouble

open FStar.HyperStack.All
open FStar.HyperStack
module ST = FStar.HyperStack.ST

open Lib.IntTypes
open Hacl.Impl.P256.Arithmetics

open Lib.Buffer

open Spec.P256.Lemmas
open Spec.P256.Definitions
open Hacl.Impl.SolinasReduction
open Spec.P256.MontgomeryMultiplication
open Spec.P256.MontgomeryMultiplication.PointDouble
open Spec.P256.MontgomeryMultiplication.PointAdd
open Hacl.Impl.P256.LowLevel 
open Hacl.Impl.P256.LowLevel.PrimeSpecific
open Hacl.Impl.P256.MontgomeryMultiplication
open Spec.P256
open Hacl.Impl.P256.Math 

open FStar.Tactics 
open FStar.Tactics.Canon

open FStar.Math.Lemmas

friend Spec.P256.MontgomeryMultiplication
open FStar.Mul

#reset-options "--z3rlimit 300" 


inline_for_extraction noextract
val point_double_compute_s_m: p: point -> s: felem -> m: felem 
  -> tempBuffer:lbuffer uint64 (size 20) 
  -> yy : felem 
  -> Stack unit
  (requires fun h -> live h p /\ live h s /\ live h m /\ live h tempBuffer /\
    LowStar.Monotonic.Buffer.all_disjoint [loc p; loc s; loc m; loc tempBuffer] /\
    as_nat h (gsub p (size 8) (size 4)) < prime256 /\ 
    as_nat h (gsub p (size 0) (size 4)) < prime256 /\ 
    as_nat h (gsub p (size 4) (size 4)) < prime256 
  )
  (ensures fun h0 _ h1 -> 
    modifies (loc tempBuffer |+| loc s |+| loc m) h0 h1 /\ (
      let x = as_nat h0 (gsub p (size 0) (size 4)) in 
      let y = as_nat h0 (gsub p (size 4) (size 4)) in 
      let z = as_nat h0 (gsub p (size 8) (size 4)) in 

      let pxD = fromDomain_ x in 
      let pyD = fromDomain_ y in 
      let pzD = fromDomain_ z in 

      as_nat h1 s == toDomain_(4 * pxD * pyD * pyD % prime256) /\
      as_nat h1 m == toDomain_(((-3) * pzD * pzD * pzD * pzD + 3 * pxD * pxD) % prime))
)


let point_double_compute_s_m p s m tempBuffer yy =
    let px = sub p (size 0) (size 4) in 
    let py = sub p (size 4) (size 4) in 
    let pz = sub p (size 8) (size 4) in 

    let xyy = sub tempBuffer (size 0) (size 4) in 
    let zzzz = sub tempBuffer (size 4) (size 4) in 
    let minThreeZzzz = sub tempBuffer (size 8) (size 4) in 
    let xx = sub tempBuffer (size 12) (size 4) in 
    let threeXx = sub tempBuffer (size 16) (size 4) in 

      let h0 = ST.get() in 
    montgomery_square_buffer py yy; 
    montgomery_multiplication_buffer px yy xyy;

    quatre pz zzzz; 
    multByMinusThree zzzz minThreeZzzz;
      let h1 = ST.get() in 
    montgomery_square_buffer px xx;
    multByThree xx threeXx;
    p256_add minThreeZzzz threeXx m;
    multByFour xyy s;

      lemmaToDomainAndBackIsTheSame (fromDomain_ (as_nat h0 py) * fromDomain_ (as_nat h0 py) % prime256);
      lemma_mod_mul_distr_r (fromDomain_ (as_nat h0 px)) (fromDomain_ (as_nat h0 py) * fromDomain_ (as_nat h0 py)) prime256; 
      lemma_brackets (fromDomain_ (as_nat h0 px)) (fromDomain_ (as_nat h0 py)) (fromDomain_ (as_nat h0 py));
    
      lemma_mod_mul_distr_r 4 (fromDomain_ (as_nat h0 px) * fromDomain_ (as_nat h0 py) * fromDomain_ (as_nat h0 py)) prime256;
      lemma_brackets4 4 (fromDomain_ (as_nat h0 px)) (fromDomain_ (as_nat h0 py)) (fromDomain_ (as_nat h0 py));
      lemma_mod_mul_distr_r (-3) (fromDomain_ (as_nat h0 pz) * fromDomain_ (as_nat h0 pz) * fromDomain_ (as_nat h0 pz) * fromDomain_ (as_nat h0 pz)) prime256;
      
      lemma_brackets5_0 (-3) (fromDomain_ (as_nat h0 pz)) (fromDomain_ (as_nat h0 pz))  (fromDomain_ (as_nat h0 pz))  (fromDomain_ (as_nat h0 pz));
      lemma_mod_mul_distr_r 3 (fromDomain_ (as_nat h1 px) * fromDomain_ (as_nat h1 px)) prime256;
      lemma_brackets 3 (fromDomain_ (as_nat h1 px)) (fromDomain_ (as_nat h1 px));

      lemma_mod_add_distr ((-3) * fromDomain_ (as_nat h0 pz) * fromDomain_ (as_nat h0 pz) * fromDomain_ (as_nat h0 pz) * fromDomain_ (as_nat h0 pz) % prime256)  (3 * fromDomain_ (as_nat h1 px) * fromDomain_ (as_nat h1 px)) prime256;
      lemma_mod_add_distr (3 * fromDomain_ (as_nat h1 px) * fromDomain_ (as_nat h1 px)) ((-3) * fromDomain_ (as_nat h0 pz) * fromDomain_ (as_nat h0 pz) * fromDomain_ (as_nat h0 pz) * fromDomain_ (as_nat h0 pz)) prime256


inline_for_extraction noextract 
val point_double_compute_x3: x3: felem -> 
  s: felem -> m: felem -> tempBuffer: lbuffer uint64 (size 8) -> Stack unit 
  (requires fun h -> live h x3 /\ live h s /\ live h m /\ live h tempBuffer /\
    LowStar.Monotonic.Buffer.all_disjoint [loc x3; loc s; loc m; loc tempBuffer] /\
    as_nat h s < prime /\ as_nat h m < prime 
  )
  (ensures fun h0 _ h1 -> modifies (loc x3 |+| loc tempBuffer) h0 h1 /\ (
    let mD = fromDomain_ (as_nat h0 m) in 
    let sD = fromDomain_ (as_nat h0 s) in 
    as_nat h1 x3 = toDomain_ ((mD * mD - 2 * sD) % prime256) /\ 
    as_nat h1 x3 < prime
   )
)


let point_double_compute_x3 x3 s m tempBuffer = 
   let twoS = sub tempBuffer (size 0) (size 4) in 
   let mm = sub tempBuffer (size 4) (size 4) in 
     let h0 = ST.get() in 
   multByTwo s twoS;
   montgomery_square_buffer m mm;
   p256_sub mm twoS x3; 
     lemma_mod_add_distr (-((2 * fromDomain_ (as_nat h0 s) % prime256))) (fromDomain_ (as_nat h0 m) * fromDomain_ (as_nat h0 m))
     prime256;
     lemma_mod_sub_distr (fromDomain_ (as_nat h0 m) * fromDomain_ (as_nat h0 m)) (2 * fromDomain_ (as_nat h0 s)) prime256
 
inline_for_extraction noextract
val point_double_compute_y3: pY: felem ->  y3: felem ->  x3: felem -> 
  s: felem -> m: felem -> tempBuffer: lbuffer uint64 (size 16) -> yy: felem -> Stack unit 
  (requires fun h -> live h pY /\ live h y3 /\ live h x3 /\ live h s /\ live h m /\ live h tempBuffer
    /\ LowStar.Monotonic.Buffer.all_disjoint [loc pY; loc y3; loc x3; loc s; loc m; loc tempBuffer]
    /\ as_nat h x3 < prime /\ as_nat h s < prime /\ as_nat h m < prime /\ as_nat h pY < prime)
  (ensures fun h0 _ h1 -> modifies (loc y3 |+| loc tempBuffer) h0 h1 /\ 
    (
      let mD = fromDomain_ (as_nat h0 m) in 
      let sD = fromDomain_ (as_nat h0 s) in 
      let x3D = fromDomain_ (as_nat h0 x3) in 
      let pyD = fromDomain_ (as_nat h0 pY) in 
      as_nat h1 y3 = toDomain_ ((mD * (sD - x3D) - (8 * pyD * pyD * pyD * pyD)) % prime256) /\ 
      as_nat h1 y3 < prime
   )
 )

let point_double_compute_y3 pY y3 x3 s m tempBuffer yy = 
    let yyyy = sub tempBuffer (size 0) (size 4) in 
    let eightYyyy = sub tempBuffer (size 4) (size 4) in 
    let sx3 = sub tempBuffer (size 8) (size 4) in 
    let msx3 = sub tempBuffer (size 12) (size 4) in 
      let h0 = ST.get() in 
    montgomery_square_buffer yy yyyy;
    multByEight yyyy eightYyyy;
    p256_sub s x3 sx3;
      let h1 = ST.get() in 
    montgomery_multiplication_buffer m sx3 msx3; 
      let h2 = ST.get() in   
    p256_sub msx3 eightYyyy y3;  

	lemma_mod_mul_distr_r 8 (fromDomain_ (as_nat h0 pY) * fromDomain_ (as_nat h0 pY) * 
	fromDomain_ (as_nat h0 pY) * fromDomain_ (as_nat h0 pY)) prime256;
	assert_by_tactic (8 * (fromDomain_ (as_nat h0 pY) * fromDomain_ (as_nat h0 pY) * fromDomain_ (as_nat h0 pY) * fromDomain_ (as_nat h0 pY)) ==  8 * fromDomain_ (as_nat h0 pY) * fromDomain_ (as_nat h0 pY) * fromDomain_ (as_nat h0 pY) * fromDomain_ (as_nat h0 pY)) canon; 

	lemma_mod_mul_distr_r (fromDomain_ (as_nat h1 m)) (fromDomain_ (as_nat h0 s) - fromDomain_ (as_nat h0 x3)) prime256;
	lemma_mod_add_distr (-fromDomain_ (as_nat h2 eightYyyy)) (fromDomain_ (as_nat h1 m) * ((fromDomain_ (as_nat h0 s) - fromDomain_ (as_nat h0 x3)))) prime256;
	lemma_mod_sub_distr (fromDomain_ (as_nat h1 m) * (fromDomain_ (as_nat h0 s) - fromDomain_ (as_nat h0 x3))) (8 * fromDomain_ (as_nat h0 pY) * fromDomain_ (as_nat h0 pY) * fromDomain_ (as_nat h0 pY) * fromDomain_ (as_nat h0 pY)) prime256


let point_double p result tempBuffer = 
	let h0 = ST.get() in   
    let s = sub tempBuffer (size 0) (size 4) in 
    let m = sub tempBuffer (size 4) (size 4) in 
    let yy = sub tempBuffer (size 8) (size 4) in 

    let buffer_for_s_m = sub tempBuffer (size 12) (size 24) in 

    let buffer_for_x3 = sub tempBuffer (size 32) (size 8) in 
    let buffer_for_y3 = sub tempBuffer (size 40) (size 16) in 

    let pypz = sub tempBuffer (size 56) (size 4) in 

    let x3 = sub tempBuffer (size 60) (size 4) in 
    let y3 = sub tempBuffer (size 64) (size 4) in 
    let z3 = sub tempBuffer (size 68) (size 4) in 

    let pX = sub p (size 0) (size 4) in 
    let pY = sub p (size 4) (size 4) in 
    let pZ = sub p (size 8) (size 4) in 

   point_double_compute_s_m p s m buffer_for_s_m yy; 
   point_double_compute_x3 x3 s m buffer_for_x3;
   point_double_compute_y3 pY y3 x3 s m buffer_for_y3 yy;
   
   montgomery_multiplication_buffer pY pZ pypz;
   multByTwo pypz z3;
   
     lemma_mod_mul_distr_r 2 (fromDomain_ (as_nat h0 pY) * fromDomain_ (as_nat h0 pZ)) prime256;
     assert_by_tactic (2 * fromDomain_ (as_nat h0 pY) * fromDomain_ (as_nat h0 pZ) == 2 * (fromDomain_ (as_nat h0 pY) * fromDomain_ (as_nat h0 pZ))) canon;
     
   concat3 (size 4) x3 (size 4) y3 (size 4) z3 result ; 

   let hEnd = ST.get() in 
   
   let pxD = fromDomain_ (as_nat h0 pX) in 
   let pyD = fromDomain_ (as_nat h0 pY) in 
   let pzD = fromDomain_ (as_nat h0 pZ) in 
   
     Spec.P256.MontgomeryMultiplication.PointDouble.lemma_xToSpecification pxD pyD pzD (as_nat hEnd s) (as_nat hEnd m) (as_nat hEnd (gsub result (size 0) (size 4)));
     Spec.P256.MontgomeryMultiplication.PointDouble.lemma_yToSpecification pxD pyD pzD (as_nat hEnd s) (as_nat hEnd m) (as_nat hEnd x3) (as_nat hEnd (gsub result (size 4) (size 4)));
     Spec.P256.MontgomeryMultiplication.PointDouble.lemma_zToSpecification pxD pyD pzD (as_nat hEnd (gsub result (size 8) (size 4)))

