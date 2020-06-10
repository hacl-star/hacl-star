module Hacl.Impl.SCA.ScalarBlinding


open FStar.HyperStack.All
open FStar.HyperStack
module ST = FStar.HyperStack.ST

open Lib.IntTypes
open Lib.Buffer

open Hacl.Impl.P256.LowLevel
open Hacl.Impl.ECDSA.MontgomeryMultiplication

open Spec.P256.Definitions

open Spec.ECDSAP256.Definition

open FStar.Mul


#set-options "--fuel 1 --ifuel 1 --z3rlimit 100"

val orderMultiplicationGeneral: a: felem -> b: felem -> out: widefelem -> 
  Stack unit 
    (requires fun h -> live h a /\ live h b /\ live h out /\ disjoint b out)
    (ensures fun h0 _ h1 -> modifies (loc out) h0 h1 /\
      wide_as_nat h1 out = as_nat h0 a * as_nat h0 b
    )

let orderMultiplicationGeneral a b out = 
  mul a b out


assume val mul1_add_il: u2: uint64 -> f3: felem -> result: felem -> 
  Stack uint64 
  (requires fun h -> live h f3 /\ live h result /\ eq_or_disjoint f3 result)
  (ensures fun h0 c h1 -> modifies (loc result) h0 h1  /\
    as_nat h1 result + uint_v c * pow2 256 == prime_p256_order * uint_v u2 + as_nat h0 f3)


#push-options "--z3rlimit 300"

val orderMultiplicationECDSAP256Order: a: felem -> out: widefelem -> 
  Stack unit 
    (requires fun h -> live h a /\ live h out /\ disjoint a out)
    (ensures fun h0 _ h1 -> modifies (loc out) h0 h1 /\
      wide_as_nat h1 out = as_nat h0 a * prime_p256_order)

let orderMultiplicationECDSAP256Order f out = 
	admit();
	  recall_contents prime256order_buffer (Lib.Sequence.of_list p256_order_prime_list);

	  lemma_powers ();

	  let f0 = f.(0ul) in
	  let f1 = f.(1ul) in
	  let f2 = f.(2ul) in
	  let f3 = f.(3ul) in

	    let h0 = ST.get() in 
	  let b0 = sub out (size 0) (size 4) in 
	  let c0 = mul1_il prime256order_buffer f0 b0 in 
	    upd out (size 4) c0;

	    let h1 = ST.get() in 
	    let bk0 = sub out (size 0) (size 1) in 
	    
	    assert(prime_p256_order * uint_v f0 = uint_v (Lib.Sequence.index (as_seq h1 out) 4) * pow2 64 * pow2 64 * pow2 64 * pow2 64 + as_nat h1 b0); 

	  let b1 = sub out (size 1) (size 4) in  
	  let c1 = mul1_add_il f1 b1 b1 in 
	      upd out (size 5) c1; 
	    let h2 = ST.get() in 
	    assert(as_nat h2 b1 + uint_v (Lib.Sequence.index (as_seq h2 out) 5) * pow2 64 * pow2 64 * pow2 64 * pow2 64 == prime_p256_order * uint_v f1 + as_nat h1 b1);

	      let bk1 = sub out (size 0) (size 2) in 
	  let b2 = sub out (size 2) (size 4) in 
	  let c2 = mul1_add_il f2 b2 b2 in 
	    upd out (size 6) c2;
	    let h3 = ST.get() in 
	   
	    assert(as_nat h3 b2 + uint_v (Lib.Sequence.index (as_seq h3 out) 6) * pow2 64 * pow2 64 * pow2 64 * pow2 64 == prime_p256_order * uint_v f2 + as_nat h2 b2);

	     let bk2 = sub out (size 0) (size 3) in 
	  let b3 = sub out (size 3) (size 4) in 
	  let c3 = mul1_add_il f3 b3 b3 in 
	    upd out (size 7) c3


assume val blindingFactorAddition: a: felem -> k: felem -> out: widefelem -> 
  Stack unit 
    (requires fun h -> live h a /\ live h k /\ live h out)
    (ensures fun h0 _ h1 -> modifies (loc out) h0 h1 /\ 
      wide_as_nat h1 out = as_nat h0 a + as_nat h0 k * prime_p256_order /\
      as_nat h0 a == (wide_as_nat h1 out) % prime_p256_order)

