module Hacl.Impl.EC.Exponent

open FStar.HyperStack.All
open FStar.HyperStack
module ST = FStar.HyperStack.ST

open Hacl.Impl.EC.Math 

open Lib.IntTypes
open Lib.Buffer

open FStar.Math.Lemmas
open FStar.Mul

open Hacl.Spec.EC.Definition
open Hacl.Lemmas.P256
open Spec.ECC
open Spec.ECDSA.Lemmas

open Hacl.Impl.EC.LowLevel

open Lib.Loops
open Hacl.Spec.MontgomeryMultiplication

open Hacl.Impl.EC.MontgomeryMultiplication

open Hacl.Impl.P256.Exponent
open Hacl.Impl.P384.Exponent
open Hacl.Impl.P521.Exponent

open Hacl.Impl.EC.Setup

open Hacl.Impl.MM.Exponent


let exponent #c a result tempBuffer = 
  match c with 
  |P256 -> 
    exponent_p256 a result tempBuffer
  |P384 ->
    exponent_p384 a result tempBuffer
  |Default -> 
    recall_contents (prime_inverse_buffer #c) (Lib.Sequence.of_list (prime_inverse_list c));
    montgomery_ladder_power #c #DH a (prime_inverse_buffer #c) result


let square_root #c a result = 
  recall_contents (sqPower_buffer #c) (Lib.Sequence.of_list (sqPower_list #c));
  montgomery_ladder_power #c #DH a (sqPower_buffer #c) result
