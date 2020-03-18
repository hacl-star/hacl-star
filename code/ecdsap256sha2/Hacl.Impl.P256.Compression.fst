module Hacl.Impl.P256.Compression

open FStar.HyperStack.All
open FStar.HyperStack
module ST = FStar.HyperStack.ST

open Lib.IntTypes
open Lib.Buffer

open Hacl.Impl.P256
open Hacl.Impl.P256.MM.Exponent

open Spec.P256.Definitions


val eq_u8_nCT: a:uint8 -> b:uint8 -> (r:bool{r == (uint_v a = uint_v b)})

let eq_u8_nCT a b =
  let open Lib.RawIntTypes in
  FStar.UInt8.(u8_to_UInt8 a =^ u8_to_UInt8 b)

[@ CInline]
val copy_conditional_u8: out: lbuffer uint8 (size 64) -> x: lbuffer uint8 (size 64) -> mask: uint8{uint_v mask = 0 \/ uint_v mask = pow2 8 - 1} -> Stack unit 
  (requires fun h -> live h out /\ live h x)
  (ensures fun h0 _ h1 -> modifies (loc out) h0 h1) 

let copy_conditional_u8 out x mask = 
  [@inline_let]
  let inv h1 (i: nat {i <= 64}) = True in
  Lib.Loops.for 0ul 64ul inv 
    (fun i -> 
      let out_i = index out i in 
      let x_i = index x i in 
      let r_i = logxor out_i (logand mask (logxor out_i x_i)) in 
      upd out i r_i
    )
      


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
  let compressedIdentifier = index b (size 0) in 
  let correctIdentifier2 = eq_u8_nCT (u8 2) compressedIdentifier in 
  let correctIdentifier3 = eq_u8_nCT (u8 3) compressedIdentifier in 
  if correctIdentifier2 || correctIdentifier3 then 
    begin
      let x = sub b (size 1) (size 32) in 
      copy x result;
      (* to domain *)
      computeYFromX x (sub result (size 32) (size 32)) correctIdentifier2;
      (* from Domain *)
      true
    end
  else 
    false
  
