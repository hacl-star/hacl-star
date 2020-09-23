module Hacl.Impl.ECDSA.DER

open FStar.HyperStack.All
open FStar.HyperStack
module ST = FStar.HyperStack.ST

open Lib.IntTypes
open Lib.Buffer

open Hacl.Impl.P256.LowLevel.RawCmp
open Lib.RawIntTypes

let lenCoor = 32ul
let integerIdentificator = 2 


val decode: sigLen: size_t -> signature: lbuffer uint8 sigLen 
  -> bufferForR: lbuffer uint8 lenCoor
  -> bufferForS: lbuffer uint8 lenCoor -> 
  Stack bool
    (requires fun h -> live h signature /\ live h bufferForR /\ live h bufferForS)
    (ensures fun h0 flag h1 -> 
      let open Lib.Sequence in 

      if v sigLen < 3 then flag = false else (
      
      let lengthIdentificator = index (as_seq h0 signature) 1 in 
      let integerFirstIdentifier = index (as_seq h0 signature) 2 in 

      if v sigLen >= 256 then flag = false else (* well *)
      if v lengthIdentificator + 1 <> v sigLen then flag = false else 
      if v integerFirstIdentifier = integerIdentificator then flag = false else True
  
  )
)



let decode sigLen signature bufferForR bufferS = 
  if sigLen <. 3ul then false else
  let zeroByte = index signature (size 0) in 
  if unsafe_bool_of_u8 (neq_mask #U8 zeroByte (u8 30)) then false else
  
  let firstByte = index signature (size 1) in
  if unsafe_bool_of_u8 (neq_mask #U8 firstByte (u8 255)) then false else begin
    eq_mask_lemma firstByte (u8 255);
  
  let lengthFullSignature = to_u32 (incr firstByte) in 
    incr_lemma firstByte;
  let sizeAsUInt32 = size_to_uint32 sigLen in 
    eq_mask_lemma lengthFullSignature sizeAsUInt32;
  if unsafe_bool_of_u32 (eq_mask #U32 lengthFullSignature sizeAsUInt32) then false else
  let secondByte = index signature (size 2) in 

  if unsafe_bool_of_u8 (neq_mask #U8 secondByte (u8 integerIdentificator)) then false else 

  

    true
  end
