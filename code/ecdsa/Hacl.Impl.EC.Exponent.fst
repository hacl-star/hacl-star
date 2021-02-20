module Hacl.Impl.EC.Exponent

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

open Hacl.Impl.EC.MontgomeryMultiplication
open Hacl.Impl.P256.Exponent
open Hacl.Impl.P384.Exponent
open Hacl.Impl.MM.Exponent



let exponent #c a result tempBuffer = 
  match c with 
  |P384 ->
      exponent_p384 a result tempBuffer
    (* 
    recall_contents (prime_inverse_buffer #c) (prime_inverse_seq #c);
    montgomery_ladder_power #c a prime_inverse_buffer result *)
  |P256 -> 
    exponent_p256 a result tempBuffer


inline_for_extraction
let sqPower_buffer_p256 : x: glbuffer uint8 (getScalarLen P256) {witnessed x sqPower_seq /\ recallable x} = 
  createL_global sqPower_list_p256


inline_for_extraction
let sqPower_buffer_p384 : x: glbuffer uint8 (getScalarLen P384) {witnessed x sqPower_seq /\ recallable x} = 
  createL_global sqPower_list_p384

inline_for_extraction
let sqPower_buffer (#c: curve): (x: glbuffer uint8 (getScalarLen c)) = 
  match c with
  |P256 -> sqPower_buffer_p256 
  |P384 -> sqPower_buffer_p384 


let square_root #c a result = 
  recall_contents (sqPower_buffer #c) (sqPower_seq #c);
  montgomery_ladder_power a sqPower_buffer result
