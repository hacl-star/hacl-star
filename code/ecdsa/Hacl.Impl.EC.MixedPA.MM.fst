module Hacl.Impl.EC.MixedPA.MM

open FStar.HyperStack.All
open FStar.HyperStack
module ST = FStar.HyperStack.ST

open Lib.IntTypes

open FStar.Math.Lemmas
open FStar.Mul

open Hacl.Impl.EC.LowLevel
open Hacl.Impl.EC.MontgomeryMultiplication.Lemmas

open Lib.Loops
open Hacl.Impl.EC.Setup

open Lib.Sequence 
open Lib.Buffer

open Hacl.Spec.MontgomeryMultiplication
open Hacl.Spec.EC.Definition
open Spec.ECC
open Spec.ECC.Curves

open FStar.Mul

open Hacl.Impl.EC.MontgomeryMultiplication



#set-options "--z3rlimit 300 --ifuel 0 --fuel 0"  


inline_for_extraction noextract
val montgomery_multiplication_buffer_by_one_mixed_: #c: curve -> result: felem c -> 
  Stack unit
  (requires (fun h -> live h result)) 
  (ensures (fun h0 _ h1 -> modifies (loc result) h0 h1 /\ (
    let prime = getModePrime DH c in  
    as_nat c h1 result = modp_inv2_prime (pow2 (getPower c)) prime % prime /\
    as_nat c h1 result = fromDomain_ #c #DH 1)))

let montgomery_multiplication_buffer_by_one_mixed_ #c result = 
  push_frame();
  let len = getCoordinateLenU64 c in 
  let t = create (size 2 *! len) (u64 0) in 
    let t_low = sub t (size 0) len in 
    let t_high = sub t len len in 

    let h0 = ST.get() in 
  uploadOneImpl #c t_low;
    let h1 = ST.get() in 
  
    lemma_create_zero_buffer #U64 (2 * v len) c; 
    lemma_test (as_seq h0 t) (v len);
    lemma_test (as_seq h1 t) (v len);
  montgomery_multiplication_reduction_dh #c t result;
  pop_frame();
  
    lemmaFromDomain #c #DH 1


let montgomery_multiplication_buffer_by_one_mixed_p256 = montgomery_multiplication_buffer_by_one_mixed_ #P256

let montgomery_multiplication_buffer_by_one_mixed_p384 = montgomery_multiplication_buffer_by_one_mixed_ #P384

(* let montgomery_multiplication_buffer_by_one_mixed_general = montgomery_multiplication_buffer_by_one_mixed_ #Default

 *)
let montgomery_multiplication_buffer_by_one_mixed #c result = 
  match c with 
  |P256 -> montgomery_multiplication_buffer_by_one_mixed_p256 result
  |P384 -> montgomery_multiplication_buffer_by_one_mixed_p384 result
  (* |Default -> montgomery_multiplication_buffer_by_one_mixed_general result *)
  
