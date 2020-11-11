module Hacl.Impl.P256.Primitives

open FStar.HyperStack.All
open FStar.HyperStack
module ST = FStar.HyperStack.ST

open Lib.IntTypes
open Lib.Buffer
open Lib.ByteSequence

open Spec.P256
open Spec.ECDSA
open Spec.P256.Definitions
open Spec.DH
open Spec.ECDSAP256.Definition
open Spec.P256.Lemmas

open Hacl.Impl.P256.LowLevel 
open Hacl.Impl.P256.Core
open Hacl.Impl.P256.Signature.Common

#set-options "--fuel 0 --ifuel 0 --z3rlimit 200"


inline_for_extraction noextract
val secretToPublic:
    result:lbuffer uint8 (size 64)
  -> scalar:lbuffer uint8 (size 32)
  -> Stack bool
  (requires fun h ->
    live h result /\ live h scalar /\ 
    disjoint result scalar)
  (ensures fun h0 r h1 ->
    let pointX, pointY, flag = ecp256_dh_i (as_seq h0 scalar) in
    modifies (loc result) h0 h1 /\
    r == flag /\
    as_seq h1 (gsub result (size 0) (size 32)) == pointX /\
    as_seq h1 (gsub result (size 32) (size 32)) == pointY)

let secretToPublic result scalar = 
    push_frame();
  let tempBuffer = create (size 100) (u64 0) in
  let resultBuffer = create (size 12) (u64 0) in
  let resultBufferX = sub resultBuffer (size 0) (size 4) in
  let resultBufferY = sub resultBuffer (size 4) (size 4) in
  let resultX = sub result (size 0) (size 32) in
  let resultY = sub result (size 32) (size 32) in

  secretToPublic resultBuffer scalar tempBuffer;
  let flag = isPointAtInfinityPrivate resultBuffer in

  let h0 = ST.get() in
  changeEndian resultBufferX;
  changeEndian resultBufferY;

  toUint8 resultBufferX resultX;
  toUint8 resultBufferY resultY;

  lemma_core_0 resultBufferX h0;
  lemma_nat_from_to_intseq_le_preserves_value 4 (as_seq h0 resultBufferX);
  changeEndian_le_be (as_nat h0 resultBufferX);

  lemma_core_0 resultBufferY h0;
  lemma_nat_from_to_intseq_le_preserves_value 4 (as_seq h0 resultBufferY);
  changeEndian_le_be (as_nat h0 resultBufferY); 
  pop_frame();

  let open Hacl.Impl.P256.LowLevel.RawCmp in 
  unsafe_bool_of_u64  flag



(*
  This function provides a raw implementation of the secrettopublic function. 
  It doesnot provide the verification that the point gotten at the result doesnot belong to infinity.
  We strongly encourage you to use this function only if you understand what you´re doing.
*)

inline_for_extraction noextract
val secretToPublicRaw:
    result:lbuffer uint8 (size 64)
  -> scalar:lbuffer uint8 (size 32)
  -> Stack unit
  (requires fun h ->
    live h result /\ live h scalar /\ 
    disjoint result scalar)
  (ensures fun h0 r h1 ->
    let pointX, pointY, flag = ecp256_dh_i (as_seq h0 scalar) in
    modifies (loc result) h0 h1 /\
    as_seq h1 (gsub result (size 0) (size 32)) == pointX /\
    as_seq h1 (gsub result (size 32) (size 32)) == pointY)


let secretToPublicRaw result scalar =
  push_frame();
  let tempBuffer = create (size 100) (u64 0) in
  let resultBuffer = create (size 12) (u64 0) in
  let resultBufferX = sub resultBuffer (size 0) (size 4) in
  let resultBufferY = sub resultBuffer (size 4) (size 4) in
  let resultX = sub result (size 0) (size 32) in
  let resultY = sub result (size 32) (size 32) in

  Hacl.Impl.P256.Core.secretToPublic resultBuffer scalar tempBuffer;
  let h0 = ST.get() in
  changeEndian resultBufferX;
  changeEndian resultBufferY;

  toUint8 resultBufferX resultX;
  toUint8 resultBufferY resultY;

  lemma_core_0 resultBufferX h0;
  lemma_nat_from_to_intseq_le_preserves_value 4 (as_seq h0 resultBufferX);
  changeEndian_le_be (as_nat h0 resultBufferX);

  lemma_core_0 resultBufferY h0;
  lemma_nat_from_to_intseq_le_preserves_value 4 (as_seq h0 resultBufferY);
  changeEndian_le_be (as_nat h0 resultBufferY); 
  pop_frame();
  admit()
  
