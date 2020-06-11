module Hacl.Impl.SCA.S


open FStar.HyperStack.All
open FStar.HyperStack
module ST = FStar.HyperStack.ST

open Lib.IntTypes
open Lib.Buffer

open Hacl.Impl.P256.LowLevel
open Hacl.Impl.ECDSA.MontgomeryMultiplication
open Hacl.Impl.ECDSA.MM.Exponent
open Hacl.Impl.ECDSA.MontgomeryMultiplication

open Spec.P256.Definitions

open Spec.ECDSAP256.Definition

open FStar.Mul

open Spec.P256.Lemmas

(* 
  The step 6 of the signature could be replaced by any f the methos below.
  They do the same computations by in different order
*)



(* (r + fa) * k_inv *)

inline_for_extraction
val ecdsa_signature_step6_0: result: felem 
  -> kFelem: felem
  -> z: felem 
  -> r: felem
  -> da: felem 
  -> Stack unit
    (requires fun h -> 
      live h result /\ live h kFelem /\ live h z /\ live h r /\ live h da /\
      as_nat h kFelem < prime_p256_order /\ 
      as_nat h z < prime_p256_order /\ 
      as_nat h r < prime_p256_order /\ 
      as_nat h da < prime_p256_order
    )
    (ensures fun h0 _ h1 -> 
      modifies (loc result) h0 h1 /\
      as_nat h1 result = (as_nat h0 z + as_nat h0 r * as_nat h0 da) * pow (as_nat h0 kFelem) (prime_p256_order - 2) % prime_p256_order
    )

let ecdsa_signature_step6_0 result kFelem z r da = 
  admit();
  let open FStar.Tactics in 
  let open FStar.Tactics.Canon in 
  push_frame();
    let rda = create (size 4) (u64 0) in 
    let zBuffer = create (size 4) (u64 0) in 
    let kInv = create (size 4) (u64 0) in 
  let h0 = ST.get() in 
    montgomery_multiplication_ecdsa_module r da rda;
    fromDomainImpl z zBuffer;
    felem_add rda zBuffer zBuffer;  
    copy kInv kFelem;
    montgomery_ladder_exponent kInv;
    montgomery_multiplication_ecdsa_module zBuffer kInv result;
  pop_frame()


(* k ^ -1 * z + (k ^ -1 * da) * r *)
val ecdsa_signature_step6_1: result: felem 
  -> kFelem: felem
  -> z: felem 
  -> r: felem
  -> da: felem 
  -> Stack unit
    (requires fun h -> 
      live h result /\ live h kFelem /\ live h z /\ live h r /\ live h da /\
      as_nat h kFelem < prime_p256_order /\ 
      as_nat h z < prime_p256_order /\ 
      as_nat h r < prime_p256_order /\ 
      as_nat h da < prime_p256_order
    )
    (ensures fun h0 _ h1 -> 
      modifies (loc result) h0 h1 /\
      as_nat h1 result = (as_nat h0 z + as_nat h0 r * as_nat h0 da) * pow (as_nat h0 kFelem) (prime_p256_order - 2) % prime_p256_order
    )


let ecdsa_signature_step6_1 result kFelen z r da = 
    admit();
  let open FStar.Tactics in 
  let open FStar.Tactics.Canon in 
  push_frame();
    let rda = create (size 4) (u64 0) in 
    let zBuffer = create (size 4) (u64 0) in 
    let kInv = create (size 4) (u64 0) in 
    montgomery_ladder_exponent kInv;
    montgomery_multiplication_ecdsa_module kInv z zBuffer;
    montgomery_multiplication_ecdsa_module kInv da rda;
    montgomery_multiplication_ecdsa_module rda r rda;
    felem_add rda zBuffer result;
  pop_frame()
    

(* k ^ -1 * z + (k ^ -1 * r) * da *)
val ecdsa_signature_step6_2: result: felem 
  -> kFelem: felem
  -> z: felem 
  -> r: felem
  -> da: felem 
  -> Stack unit
    (requires fun h -> 
      live h result /\ live h kFelem /\ live h z /\ live h r /\ live h da /\
      as_nat h kFelem < prime_p256_order /\ 
      as_nat h z < prime_p256_order /\ 
      as_nat h r < prime_p256_order /\ 
      as_nat h da < prime_p256_order
    )
    (ensures fun h0 _ h1 -> 
      modifies (loc result) h0 h1 /\
      as_nat h1 result = (as_nat h0 z + as_nat h0 r * as_nat h0 da) * pow (as_nat h0 kFelem) (prime_p256_order - 2) % prime_p256_order
    )

let ecdsa_signature_step6_2 result kFelen z r da = 
    admit();
  let open FStar.Tactics in 
  let open FStar.Tactics.Canon in 
  push_frame();
    let rda = create (size 4) (u64 0) in 
    let zBuffer = create (size 4) (u64 0) in 
    let kInv = create (size 4) (u64 0) in 
    montgomery_ladder_exponent kInv;
    montgomery_multiplication_ecdsa_module kInv z zBuffer;
    montgomery_multiplication_ecdsa_module kInv r rda;
    montgomery_multiplication_ecdsa_module rda da rda;
    felem_add rda zBuffer result;
  pop_frame()


assume val montgomery_ladder_exponent_minus_one: a: felem -> Stack unit 
  (requires fun h -> live h a /\ as_nat h a < prime)
  (ensures fun h0 _ h1 -> modifies (loc a) h0 h1 /\ 
    (
      let b_ = fromDomain_ (as_nat h0 a) in 
      fromDomain_ (as_nat h1 a) ==  pow (as_nat h0 a) (prime_p256_order - 3) % prime_p256_order
    )
)


(* k ^ -1 * z + k ^ -2 * r * k * da *)
val ecdsa_signature_step6_3: result: felem 
  -> kFelem: felem
  -> z: felem 
  -> r: felem
  -> da: felem 
  -> Stack unit
    (requires fun h -> 
      live h result /\ live h kFelem /\ live h z /\ live h r /\ live h da /\
      as_nat h kFelem < prime_p256_order /\ 
      as_nat h z < prime_p256_order /\ 
      as_nat h r < prime_p256_order /\ 
      as_nat h da < prime_p256_order
    )
    (ensures fun h0 _ h1 -> 
      modifies (loc result) h0 h1 /\
      as_nat h1 result = (as_nat h0 z + as_nat h0 r * as_nat h0 da) * pow (as_nat h0 kFelem) (prime_p256_order - 2) % prime_p256_order
    )    
