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
      




val uploadA: a: felem -> Stack unit
  (requires fun h -> live h a)
  (ensures fun h0 _ h1 -> modifies (loc a) h0 h1 /\ as_nat h1 a == aCoordinateP256 % prime256)

let uploadA a = 
  upd a (size 0) (u64 18446744073709551612);
  upd a (size 1) (u64 4294967295);
  upd a (size 2) (u64 0);
  upd a (size 3) (u64 18446744069414584321);
  assert_norm(18446744073709551612 + 4294967295 * pow2 64 + 18446744069414584321 * pow2 64 * pow2 64 * pow2 64 = aCoordinateP256 % prime256)
  

val uploadB: b: felem -> Stack unit 
  (requires fun h -> live h b)
  (ensures fun h0 _ h1 -> modifies (loc b) h0 h1 /\ as_nat h1 b == bCoordinateP256)

let uploadB b = 
  upd b (size 0) (u64 4309448131093880907);
  upd b (size 1) (u64 7285987128567378166);
  upd b (size 2) (u64 12964664127075681980);
  upd b (size 3) (u64 6540974713487397863);
  assert_norm (4309448131093880907 + 7285987128567378166 * pow2 64 + 12964664127075681980 * pow2 64 * pow2 64 + 6540974713487397863 * pow2 64 * pow2 64 * pow2 64 == 41058363725152142129326129780047268409114441015993725554835256314039467401291)



val computeYFromX: x: felem ->  result: felem -> sign: uint64 -> Stack unit 
  (requires fun h -> live h x /\ live h result /\ as_nat h x < prime)
  (ensures fun h0 _ h1 -> True)


let computeYFromX x result sign = 
  push_frame();
    let aCoordinateBuffer = create (size 4) (u64 0) in 
    let bCoordinateBuffer = create (size 4) (u64 0) in 
   
    uploadA aCoordinateBuffer;
    uploadB bCoordinateBuffer;

    montgomery_multiplication_buffer aCoordinateBuffer x aCoordinateBuffer;

    cube x result;
    p256_add result aCoordinateBuffer result;
    p256_add result bCoordinateBuffer result;

    uploadZeroImpl aCoordinateBuffer;
    p256_sub aCoordinateBuffer result bCoordinateBuffer;

    cmovznz4 sign bCoordinateBuffer result result;

    square_root result;


    admit();
    


 pop_frame()   
    
    


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
  
