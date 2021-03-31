module Hacl.Impl.P384.Exponent

open FStar.HyperStack.All
open FStar.HyperStack
module ST = FStar.HyperStack.ST

open Lib.IntTypes
open Lib.Buffer

open FStar.Mul

open Hacl.Spec.EC.Definition
open Spec.ECC
open Spec.ECC.Curves
open Hacl.Impl.EC.MontgomeryMultiplication
open Hacl.Impl.EC.LowLevel

#set-options "--z3rlimit 100 --ifuel 0 --fuel 0"


[@ CInline]
val exponent_p384: a: felem P384 -> result: felem P384 -> 
  tempBuffer: lbuffer uint64 (getCoordinateLenU P384 *. 8ul) -> Stack unit
  (requires fun h -> live h a /\ live h tempBuffer /\ live h result /\ disjoint tempBuffer result /\ 
    disjoint a tempBuffer /\ as_nat P384 h a < prime256)
  (ensures fun h0 _ h1 -> modifies2 result tempBuffer h0 h1 /\ (
    let k = fromDomain #P384 (as_nat P384 h0 a) in 
    as_nat P384 h1 result =  toDomain #P384 (pow k (prime384 - 2) % prime256)))


let exponent_p384 t result tempBuffer = 
  let h0 = ST.get () in 

  let t0 = sub tempBuffer (size 0) (size 6) in 

  let t1 = sub tempBuffer (size 6) (size 6) in 
  let t2 = sub tempBuffer (size 12) (size 6) in 
  let t3 = sub tempBuffer (size 18) (size 6) in 
  let t4 = sub tempBuffer (size 24) (size 6) in 
  let t5 = sub tempBuffer (size 30) (size 6) in (* 
  let t6 = sub tempBuffer (size 24) (size 4) in 
  let t7 = sub tempBuffer (size 28) (size 4) in 
 *)

(* _10     = sq(t) *)
(* t0 = _10  *)
  montgomery_square_buffer_dh #P384 t t0;

(* _11     = m(t, _10) *)
  montgomery_multiplication_buffer_dh #P384 t t0 t0;
(* t0 = _11*)

(* _110    = sq(_11) *)
  montgomery_square_buffer_dh #P384 t0 t0;
(* t0 = _110 *)  

(* _111    = m(t, _110) *)
  montgomery_multiplication_buffer_dh #P384 t t0 t0;
(* t0 = _111 *)  

(* _111000 (t1) = n_sq(_111, 3) *)
  montgomery_square_buffer_dh #P384 t0 t1;
  fsquarePowN_dh #P384 (size 2) t1;
(* t1 = sq _111 *)
(* t1 = n_sq _111 3  *)
(* t1 = _111000 *)


(* _111111 = m(_111,  _111000) *)
  montgomery_multiplication_buffer_dh #P384 t0 t1 t1;  
(* t1 = t0 * t1 *)
(* t1 = _111 * _111000 *)
(* t1 = _111111 *)



(* x12     = m(n_sq(_111111, 6), _111111) *)
  montgomery_square_buffer_dh #P384 t1 t2;
  fsquarePowN_dh #P384 (size 5) t2 ;
  montgomery_multiplication_buffer_dh #P384 t2 t1 t2;
(* t2 = x12 *)



(* x24     = m(n_sq(x12 , 12), x12) *)
  montgomery_square_buffer_dh #P384 t2 t3;
  fsquarePowN_dh #P384 (size 11) t3 ;
  montgomery_multiplication_buffer_dh #P384 t2 t3 t2;
(* t2 = x24*) 

(* x30     = m(n_sq(x24 , 6) , _111111) *)
  fsquarePowN_dh #P384 (size 6) t2 ;
  montgomery_multiplication_buffer_dh #P384 t2 t1 t1;  
(* t1 = x30 *)


(* x31     = m(sq(x30), t) *)
  montgomery_square_buffer_dh #P384 t1 t2;
  (* fsquarePowN_dh #P384 (size 29) t2 ; *)
  montgomery_multiplication_buffer_dh #P384 t2 t t2;
(* t2 = x31 *)


 (* x32     = m(sq(x31), t)  *)
  montgomery_square_buffer_dh #P384 t2 t3;
  (* fsquarePowN_dh #P384 (size 30) t3 ; *)
  montgomery_multiplication_buffer_dh #P384 t t3 t3;
(* t3 = x32*)




(* x63     = m(n_sq(x32, 31) , x31) *)
  montgomery_square_buffer_dh #P384 t3 t4;
  fsquarePowN_dh #P384 (size 30) t4 ;
  montgomery_multiplication_buffer_dh #P384 t4 t2 t4;
(* t4 = x63 *)



(* x126    = m(n_sq(x63, 63) , x63) *)
  montgomery_square_buffer_dh #P384 t4 t5;
  fsquarePowN_dh #P384 (size 62) t5 ;
  montgomery_multiplication_buffer_dh #P384 t4 t5 t4;  
(* t4 = x126*)


(* x252    = m(n_sq(x126, 126) , x126) *)
  montgomery_square_buffer_dh #P384 t4 t5;
  fsquarePowN_dh #P384 (size 125) t5 ;
  montgomery_multiplication_buffer_dh #P384 t4 t5 t4;
(* t4 = x252 *)


(* x255    = m(n_sq(x252, 3) , _111) *)
  fsquarePowN_dh #P384 (size 3) t4 ;
  montgomery_multiplication_buffer_dh #P384 t4 t0 t4;
(* t4 = x255 *)


(* i0 = m(n_sq(x255, 33), x32) *)
  fsquarePowN_dh #P384 (size 33) t4 ;
  montgomery_multiplication_buffer_dh #P384 t4 t3 t4;
(*t4 = i0 *)


(* i1 = m(n_sq(i0, 94), x30) *)
  fsquarePowN_dh #P384 (size 94) t4 ;
  montgomery_multiplication_buffer_dh #P384 t4 t1 t4;
(* t4 = i1 *)

(* i397    = n_sq(i1, 2) *)
  fsquarePowN_dh #P384  (size 2) t4;

(* r = m(t, i397) *)
  montgomery_multiplication_buffer_dh #P384 t4 t result
