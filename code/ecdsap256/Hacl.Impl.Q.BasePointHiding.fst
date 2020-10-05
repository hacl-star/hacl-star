module Hacl.Impl.Q.BasePointHiding


open FStar.HyperStack.All
open FStar.HyperStack
module ST = FStar.HyperStack.ST

open Lib.IntTypes
open Lib.Buffer

open Hacl.Impl.P256.LowLevel

open Spec.P256
open Spec.P256.Definitions

open FStar.Mul


open Hacl.Impl.P256.LowLevel.PrimeSpecific
open Lib.Loops

open Lib.IntTypes.Intrinsics

open Spec.P256.MontgomeryMultiplication
open Hacl.Impl.P256.Core
open Hacl.Impl.P256.MontgomeryMultiplication


#set-options "--z3rlimit 200 --max_fuel 0 --max_ifuel 0" 


(* usually p -> toDomain -> ... -> fromDomain -> r *)

val basePointRandomisation: resultPoint: point -> r: felem ->
  Stack unit 
    (requires fun h -> live h resultPoint /\ live h r /\ as_nat h r < prime256 /\ disjoint resultPoint r)
    (ensures fun h0 _ h1 -> 
      let resultPoint = point_prime_to_coordinates (as_seq h1 resultPoint) in 
      let resultFromDomain = fromDomainPoint resultPoint in 
      let resultNormalized = _norm resultFromDomain in 
      basePoint == resultNormalized)


(* or this, depends *)
      
(*
val basePointRandomisation: p: point -> resultPoint: point -> 
  Stack unit 
    (requires fun h -> live h p /\ live h resultPoint)
    (ensures fun h0 _ h1 -> 
      let resultPoint = point_prime_to_coordinates (as_seq h1 resultPoint) in 
      let pointOriginal = point_prime_to_coordinates (as_seq h0 p) in 
      let resultNormalized = _norm resultPoint in 
      pointOriginal == resultNormalized)
*)


(* prime = 2**256 - 2**224 + 2**192 + 2**96 -1

r = getrandbits(256)
x = getrandbits(256)

z = getrandbits(256)
z_ = (z * r) % prime

xn = (x * power_mod(z * z, prime - 2, prime)) % prime
xn_ = (x * power_mod(z_ * z_, prime - 2, prime)  * r * r) % prime

xn == xn_ *)


let basePointRandomisation result r = 
  push_frame(); 
    let tempBuffer = create (size 88) (u64 0) in 
    let rTemp = create (size 4) (u64 0) in 
    let h0 = ST.get() in 
 
    
  uploadBasePoint result;

  let zCoordinate = sub result (size 8) (size 4) in 
  let xCoordinate = sub result (size 0) (size 4) in 
  let yCoordinate = sub result (size 4) (size 4) in 

  let h1 = ST.get() in 
  montgomery_multiplication_buffer zCoordinate r zCoordinate;
  let h2 = ST.get() in 

  (*montgomery_square_buffer zCoordinate zCoordinate;
  let h3 = ST.get() in 
  exponent zCoordinate zCoordinate tempBuffer; *)
  let h4 = ST.get() in 
  assume (as_nat h4 xCoordinate < prime256);
  assume (as_nat h4 zCoordinate < prime256);
  let h5 = ST.get() in 
  montgomery_square_buffer r rTemp;
  let h6 = ST.get() in 
  montgomery_multiplication_buffer xCoordinate rTemp xCoordinate;
  let h7 = ST.get() in 
  montgomery_multiplication_buffer rTemp r rTemp;

  montgomery_multiplication_buffer yCoordinate rTemp yCoordinate;


  norm result result tempBuffer;


  (*montgomery_multiplication_buffer xCoordinate zCoordinate xCoordinate; 
  let h8 = ST.get() in


  let bpX, bpY, bpZ = basePoint in 
  lemmaFromDomainToDomain (as_nat h1 (gsub result (size 8) (size 4)));
  (*assert(fromDomain_ (as_nat h1 (gsub result (size 8) (size 4))) == bpZ);
  assert(as_nat h1 (gsub result (size 8) (size 4)) == toDomain_ bpZ); *)
  assert(as_nat h2 zCoordinate = toDomain_ (bpZ * fromDomain_ (as_nat h1 r) % prime256));

  assert(as_nat h3 zCoordinate = toDomain_ ((bpZ * fromDomain_ (as_nat h1 r) % prime256) * (bpZ * fromDomain_ (as_nat h1 r) % prime256) % prime256));

  assert(as_nat h4 zCoordinate = toDomain_ (Spec.P256.Lemmas.pow ( ((bpZ * fromDomain_ (as_nat h1 r) % prime256) * (bpZ * fromDomain_ (as_nat h1 r) % prime256) % prime256)) (prime256 - 2) % prime256));
 
  assert(as_nat h7 xCoordinate = toDomain_ (fromDomain_ (as_nat h6 xCoordinate) * (fromDomain_ (as_nat h0 r) * fromDomain_ (as_nat h0 r) % prime256) % prime256));
admit();

  assert(as_nat h8 xCoordinate = toDomain_ ( (fromDomain_ (as_nat h6 xCoordinate) * ((fromDomain_ (as_nat h1 r) * fromDomain_ (as_nat h1 r) % prime256)) * (Spec.P256.Lemmas.pow ( ((bpZ * fromDomain_ (as_nat h1 r) % prime256) * (bpZ * fromDomain_ (as_nat h1 r) % prime256) % prime256)) (prime256 - 2) % prime256) % prime256)));


*)


  admit()
