module Hacl.Impl.EC.MontgomeryMultiplication

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
open Spec.P256
open Spec.ECDSA.Lemmas

open Hacl.Impl.EC.LowLevel

open Lib.Loops
open Hacl.Spec.P.MontgomeryMultiplication

(* open Hacl.Impl.P256.MontgomeryMultiplication.Exponent *)
open Hacl.Impl.P256.MontgomeryMultiplication
(* open Hacl.Impl.P256.MM.Exponent *)


let montgomery_multiplication_buffer_by_one #c a result = 
  match c with 
  |P256 -> 
    assume ((getPrime c + 1) % pow2 64 == 0);
    montgomery_multiplication_buffer_by_one_w_ko a result
  |P384 -> montgomery_multiplication_buffer_by_one_ko a result



let montgomery_multiplication_buffer #c a b result = 
  match c with 
  |P256 ->
    assume ((getPrime c + 1) % pow2 64 == 0);
    montgomery_multiplication_buffer_w_k0 a b result
  |P384 -> montgomery_multiplication_buffer_k0 a b result



let montgomery_square_buffer #c a result = 
  match c with 
  |P256 ->
     assume ((getPrime c + 1) % pow2 64 == 0);
     montgomery_square_buffer_w_k0 a result
  |P384 -> montgomery_square_buffer_k0 a result




let fsquarePowN #c n a = 
  let h0 = ST.get() in  
  (* lemmaFromDomainToDomain #P256 (as_nat P256 h0 a); *)
  assert_norm (pow2 0 == 1); 
  let inv (h0: HyperStack.mem) (h1: HyperStack.mem) (i: nat) : Type0 = True (*
    let k = fromDomain_ #P256 (as_nat P256 h0 a) in 
    as_nat P256 h1 a = toDomain_ #P256 (pow k (pow2 i)) /\
    as_nat P256 h1 a < prime256 /\ live h1 a /\ modifies1 a h0 h1  *) in 

 (* power_one_2 (fromDomain_ #P256 (as_nat P256 h0 a)); *)

  for (size 0) n (inv h0) (fun x -> 
    let h0_ = ST.get() in 
     montgomery_square_buffer #c a a
     (* ; 
     let k = fromDomain_ #P256 (as_nat P256 h0 a) in  
     inDomain_mod_is_not_mod #P256 (fromDomain_ #P256 (as_nat P256 h0_ a) * fromDomain_ #P256 (as_nat P256 h0_ a)); 
     lemmaFromDomainToDomainModuloPrime #P256 (let k = fromDomain_ #P256 (as_nat P256 h0 a) in pow k (pow2 (v x)));

     (*modulo_distributivity_mult (pow k (pow2 (v x))) (pow k (pow2 (v x))) prime256; 
     pow_plus k  (pow2 (v x)) (pow2 (v x )); 
     pow2_double_sum (v x); *)
     inDomain_mod_is_not_mod #P256 (pow k (pow2 (v x + 1)))
 *)
   )
