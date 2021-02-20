module Hacl.Impl.P384.Exponent

open FStar.HyperStack.All
open FStar.HyperStack
module ST = FStar.HyperStack.ST

open Hacl.Impl.P256.Math 

open Lib.IntTypes
open Lib.Buffer

open FStar.Math.Lemmas
open FStar.Mul

open Hacl.Spec.P256.Definition
open Hacl.Lemmas.P256
open Hacl.Impl.P256.LowLevel 
open Spec.P256
open Lib.Loops

open Hacl.Impl.P256.MM.Lemmas

open Hacl.Impl.EC.MontgomeryMultiplication
open Hacl.Spec.P.MontgomeryMultiplication


#set-options "--z3rlimit 100 --ifuel 0 --fuel 0"

(* 
(* Changing argument order *)
inline_for_extraction noextract
val montgomery_multiplication_buffer: result: felem P384 -> a: felem P384 -> b: felem P384 -> Stack unit
  (requires (fun h -> live h a /\  as_nat P384 h a < prime256 /\ live h b /\ live h result /\ as_nat P384 h b < prime256)) 
  (ensures (fun h0 _ h1 -> modifies (loc result) h0 h1) (*/\  
    as_nat h1 result < prime256 /\
    as_nat h1 result = (as_nat h0 a * as_nat h0 b * modp_inv2_prime (pow2 256) prime256) % prime256 /\
    as_nat h1 result = toDomain_ (fromDomain_ (as_nat h0 a) * fromDomain_ (as_nat h0 b) % prime256) /\
    as_nat h1 result = toDomain_ (fromDomain_ (as_nat h0 a) * fromDomain_ (as_nat h0 b))) *)
  )


let montgomery_multiplication_buffer result a b = 
  montgomery_multiplication_buffer #P384 a b result


inline_for_extraction noextract
val montgomery_square_buffer: result: felem P256 -> a: felem P256 -> Stack unit
  (requires (fun h -> live h a /\ as_nat P256 h a < prime256 /\ live h result)) 
  (ensures (fun h0 _ h1 -> modifies (loc result) h0 h1 (* /\  
    as_nat h1 result < prime256 /\ 
    as_nat h1 result = (as_nat h0 a * as_nat h0 a * modp_inv2_prime (pow2 256) prime256) % prime256 /\
    as_nat h1 result = toDomain_ (fromDomain_ (as_nat h0 a) * fromDomain_ (as_nat h0 a) % prime256) /\
    as_nat h1 result = toDomain_ (fromDomain_ (as_nat h0 a) * fromDomain_ (as_nat h0 a))*) )
  )


let montgomery_square_buffer result a = montgomery_square_buffer #P384 a result


 *)


[@ CInline]
val exponent_p384: a: felem P384 -> result: felem P384 -> 
  tempBuffer: lbuffer uint64 (getCoordinateLenU P384 *. 8ul) -> Stack unit
  (requires fun h -> live h a /\ live h tempBuffer /\ live h result /\ disjoint tempBuffer result /\ 
    disjoint a tempBuffer /\ as_nat P384 h a < prime256)
  (ensures fun h0 _ h1 -> modifies2 result tempBuffer h0 h1 /\ (
    let k = fromDomain_ #P384 (as_nat P384 h0 a) in 
    as_nat P384 h1 result =  toDomain_ #P384 (pow k (prime384 - 2) % prime256)))


let exponent_p384 t result tempBuffer = 
  let h0 = ST.get () in 

  let x15 = sub tempBuffer (size 0) (size 6) in 

  let x2 = sub tempBuffer (size 6) (size 6) in 
  let x3 = sub tempBuffer (size 12) (size 6) in 
  let x6 = sub tempBuffer (size 18) (size 6) in 
  let x12 = sub tempBuffer (size 24) (size 6) in 
  let x30 = sub tempBuffer (size 30) (size 6) in 
  let x60 = sub tempBuffer (size 36) (size 6) in 
  let x120 = sub tempBuffer (size 42) (size 6) in 

  (* x2   = (nth double 1  `andThen` add x1  ) x1 *)
  montgomery_square_buffer #P384 t x2;
  montgomery_multiplication_buffer #P384 x2 t x2;

  (* x3   = (nth double 1  `andThen` add x1  ) x2 *)
  montgomery_square_buffer #P384 x2 x3; 
  montgomery_multiplication_buffer #P384 x3 t x3;


(* x6   = (nth double        3  `andThen` add x3  ) x3 *)
  montgomery_square_buffer #P384 x3 x6;
  montgomery_square_buffer #P384 x6 x6;
  montgomery_square_buffer #P384 x6 x6;
  montgomery_multiplication_buffer #P384 x6 x3 x6;

(* x12  = (nth double        6  `andThen` add x6  ) x6 *)
  montgomery_square_buffer #P384 x6 x12;
  fsquarePowN #P384 (size 5) x12;
  montgomery_multiplication_buffer #P384 x12 x6 x12;

 (* x15  = (nth double        3  `andThen` add x3  ) x12 *)
  montgomery_square_buffer #P384 x12 x15;
  montgomery_square_buffer #P384 x15 x15;
  montgomery_square_buffer #P384 x15 x15;
  montgomery_multiplication_buffer #P384 x15 x3 x15;

    (* x30  = (nth double       15  `andThen` add x15 ) x15 *)
  montgomery_square_buffer #P384 x15 x30;
  fsquarePowN #P384 (size 14) x30;
  montgomery_multiplication_buffer #P384 x30 x15 x30;

(* x60  = (nth double       30  `andThen` add x30 ) x30 *)
  montgomery_square_buffer #P384 x30 x60;
  fsquarePowN #P384 (size 29) x60;
  montgomery_multiplication_buffer #P384 x60 x30 x60;

(* x120 = (nth double       60  `andThen` add x60 ) x60 *)
  montgomery_square_buffer #P384 x60 x120;
  fsquarePowN #P384 (size 59) x120;
  montgomery_multiplication_buffer #P384 x120 x60 x120;

  montgomery_square_buffer x120 result;
  fsquarePowN #P384 (size 119) result;
  montgomery_multiplication_buffer #P384 result x120 result;
  fsquarePowN #P384 (size 15) result;
  montgomery_multiplication_buffer #P384 result x15 result;
  fsquarePowN #P384 (size 31) result;
  montgomery_multiplication_buffer #P384 result x30 result;
  fsquarePowN #P384 (size 2) result;
  montgomery_multiplication_buffer  #P384 result x2 result;
  fsquarePowN #P384 (size 94) result;
  montgomery_multiplication_buffer #P384 result x30 result;
  fsquarePowN #P384 (size 2) result;
  montgomery_multiplication_buffer result t result