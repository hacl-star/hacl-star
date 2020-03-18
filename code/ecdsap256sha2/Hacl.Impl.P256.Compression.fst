module Hacl.Impl.P256.Compression

open FStar.HyperStack.All
open FStar.HyperStack
module ST = FStar.HyperStack.ST

open Lib.IntTypes
open Lib.Buffer

open Spec.P256.Definitions


val eq_u8_nCT: a:uint8 -> b:uint8 -> (r:bool{r == (uint_v a = uint_v b)})

let eq_u8_nCT a b =
  let open Lib.RawIntTypes in
  FStar.UInt8.(u8_to_UInt8 a =^ u8_to_UInt8 b)

val copy_conditional_u8: out: lbuffer uint8 (size 64) -> x: lbuffer uint8 (size 64) -> mask: uint8{uint_v mask = 0 \/ uint_v mask = pow2 8 - 1} -> Stack unit 
  (requires fun h -> live h out /\ live h x)
  (ensures fun h0 _ h1 -> modifies (loc out) h0 h1) 

let copy_conditional_u8 out x mask = 
  ()


let decompressionNotCompressed b result = 
  let compressionIdentifier = index b (size 0) in
  let correctIdentifier = eq_u8_nCT (u8 4) compressionIdentifier in 
  if correctIdentifier then 
    copy (sub b (size 1) (size 64)) result;
  admit();  
  correctIdentifier


let decompressionNotCompressed2 b result = 
  let compressionIdentifier = index b (size 0) in 
  let correctIdentifier = eq_mask (u8 4) compressionIdentifier in 
    eq_mask_lemma (u8 4) compressionIdentifier;
  copy_conditional_u8 result (sub b (size 1) (size 64)) correctIdentifier;
  correctIdentifier



let decompressionCompressed b result = 
  (u64 0)
