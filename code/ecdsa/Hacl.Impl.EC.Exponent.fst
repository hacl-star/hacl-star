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
open Hacl.EC.Lemmas
open Spec.ECC
open Spec.ECDSA.Lemmas

open Hacl.Impl.EC.LowLevel

open Lib.Loops
open Hacl.Spec.MontgomeryMultiplication

open Hacl.Impl.EC.MontgomeryMultiplication

open Hacl.Impl.P256.Exponent
open Hacl.Impl.P384.Exponent
(* open Hacl.Impl.P521.Exponent *)

open Hacl.Impl.EC.Setup

open Hacl.Impl.EC.MM.Exponent
open Lib.ByteSequence 

#set-options "--z3rlimit 100 --ifuel 0 --fuel 0"


val lemma_list_nat_from_bytes: a: list uint8 { List.Tot.length a <= max_size_t} -> 
  i: nat {i > 0 /\ i <= List.Tot.length a} ->
  Lemma (Lib.ByteSequence.nat_from_intseq_le (Lib.Sequence.slice (Lib.Sequence.of_list a) 0 i) == lst_as_nat_ a i)

let rec lemma_list_nat_from_bytes a i = 
  let l = List.Tot.length a in 
  let al = (Lib.Sequence.of_list a) in 
  let sl = (Lib.Sequence.slice al 0 i) in 
  match i with 
  |1 -> nat_from_intseq_le_lemma0 sl; lst_as_nat_first a
  |_ -> lemma_list_nat_from_bytes a (i - 1);
    let i1 = i - 1 in 
    nat_from_intseq_le_slice_lemma al i1;
    nat_from_intseq_le_slice_lemma sl (i - 1);
    nat_from_intseq_le_lemma0 (Lib.Sequence.slice sl i1 i); 
    lst_as_nat_definiton a i



let exponent #c a result tempBuffer = 
  match c with 
  |P256 -> exponent_p256 a result tempBuffer
  |P384 -> exponent_p384 a result tempBuffer
  |_ -> 
    recall_contents (prime_inverse_buffer #c) (Lib.Sequence.of_list (prime_inverse_list c));
    montgomery_ladder_power_dh #c a (prime_inverse_buffer #c) result;
    lemma_list_nat_from_bytes (prime_inverse_list c) (List.Tot.length (prime_inverse_list c))


(* val square_root_: #c: curve -> a: felem c -> result: felem c -> Stack unit 
  (requires fun h -> live h a /\ live h result /\ as_nat c h a < getPrime c)
  (ensures fun h0 _ h1 -> modifies (loc a |+| loc result) h0 h1 /\
    as_nat c h1 result < getPrime c /\
    fromDomain #c (as_nat c h1 result) = sq_root_spec #c #DH (fromDomain #c (as_nat c h0 a)) /\
    fromDomain #c (as_nat c h1 result) = pow (fromDomain #c (as_nat c h0 a)) ((getPrime c + 1) / 4) % getPrime c)
 *)
let square_root #c a result = 
  recall_contents (sqPower_buffer #c) (Lib.Sequence.of_list (sqPower_list #c));
  montgomery_ladder_power_dh #c a (sqPower_buffer #c) result;
  lemma_list_nat_from_bytes (sqPower_list #c) (List.Tot.length (sqPower_list #c))
(* 

val square_root_p256: a: felem P256 -> result: felem P256 -> Stack unit 
  (requires fun h -> live h a /\ live h result /\ as_nat P256 h a < getPrime P256)
  (ensures fun h0 _ h1 -> modifies (loc a |+| loc result) h0 h1)

let square_root_p256 = square_root_ #P256 

let square_root_p384 = square_root_ #P384

 *)
(* let square_root #c a result = 
  match c with 
  |P256 -> square_root_p256 a result
  |P384 -> square_root_p384 a result *)