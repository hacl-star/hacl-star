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

