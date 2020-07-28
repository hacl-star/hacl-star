module Hacl.Impl.ECDSA.Reduction

open FStar.HyperStack.All
open FStar.HyperStack
module ST = FStar.HyperStack.ST

open Lib.IntTypes
open Lib.Buffer

open Hacl.Spec.P256.Definition
open Hacl.Spec.ECDSA.Definition

open Hacl.Impl.ECDSA.MontgomeryMultiplication
open Hacl.Impl.P256.LowLevel 

open Hacl.Lemmas.P256
open Lib.ByteSequence

open Spec.P256

#set-options "--z3rlimit 100 --ifuel 0 --fuel 0"

inline_for_extraction
val reduction_8_32: #c: curve -> x: lbuffer uint8 (size 32) -> result: lbuffer uint8 (size 32) -> 
  Stack unit 
    (requires fun h -> live h x /\ live h result /\ eq_or_disjoint x result)
    (ensures fun h0 _ h1 -> modifies (loc result) h0 h1 /\ 
      nat_from_bytes_be (as_seq h1 result) == nat_from_bytes_be (as_seq h0 x) % prime_p256_order /\
      nat_from_bytes_be (as_seq h1 result) < prime_p256_order
    )

let reduction_8_32 #c x result = 
  push_frame();
    let h0 = ST.get() in 
      let xAsFelem = create (size 4) (u64 0) in 
      toUint64ChangeEndian #c x xAsFelem;
    let h1 = ST.get() in   
      lemma_core_0 c xAsFelem h1;
      changeEndianLemma (uints_from_bytes_be (as_seq h0 x));
      uints_from_bytes_be_nat_lemma #U64 #_ #4 (as_seq h1 x); 
    reduction_prime_2prime_order #c xAsFelem xAsFelem;
    let h2 = ST.get() in 
    changeEndian #c xAsFelem;
    toUint8 xAsFelem result;
      lemma_core_0 c xAsFelem h2;
      lemma_nat_from_to_intseq_le_preserves_value 4 (as_seq h2 xAsFelem);
      changeEndian_le_be (as_nat c h2 xAsFelem);
      lemma_nat_to_from_bytes_be_preserves_value (as_seq h0 x) 32 (nat_from_bytes_be (as_seq h0 x) % prime_p256_order);
  pop_frame()
