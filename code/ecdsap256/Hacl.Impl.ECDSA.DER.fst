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

      if v sigLen < 6 then flag = false else (
      
      let lengthIdentificator = index (as_seq h0 signature) 1 in 
      let integerFirstIdentifier = index (as_seq h0 signature) 2 in 

      if v sigLen >= 256 then flag = false else (* well *)
      if v lengthIdentificator + 1 <> v sigLen then flag = false else 
      if v integerFirstIdentifier = integerIdentificator then flag = false else True
  
  )
)


assume val checkBorders: byte: uint8 -> Tot (flag: bool { flag <==> v byte = 0 || v byte > v lenCoor + 1})

assume val notCorrectFormalStartSignature: len: uint8 -> byteZero: uint8 -> byteOne: uint8 -> 
  Tot (flag: bool 
    {
      if (v len = 0x33 &&  v byteZero = 0  && v byteOne > 0x7F) then not flag
      else if v len <> 33 then not flag
      else flag   
    })


assume val copyBuffer: len: size_t -> from: lbuffer uint8 len -> to: lbuffer uint8 lenCoor ->
  Stack unit 
    (requires fun h -> live h from /\ live h to)
    (ensures fun h0 _ h1 -> True)





(* Note that the r and s value must be prepended with 0x00 if their first byte is greater than 0x7F.  *)

let decode sigLen signature bufferForR bufferForS = 
  if sigLen <. 6ul then false else
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
  let startofRIndex = index signature (size 2) in 

  if unsafe_bool_of_u8 (neq_mask #U8 startofRIndex (u8 integerIdentificator)) then false else 

  let expectedLenR = index signature (size 3) in 

  let lengthAfterThirdByte = firstByte -. (u8 3) in 

  if checkBorders expectedLenR || unsafe_bool_of_u8 (gt_mask expectedLenR lengthAfterThirdByte) then false else 

  let forthByteR = index signature (size 4) in 
  let fifthByteR = index signature (size 5) in 

  if notCorrectFormalStartSignature expectedLenR forthByteR fifthByteR  then false else 
    let r = sub signature (size 4) expectedLenR in 
    copyBuffer expectedLenR r bufferForR;
    
  
  let startOfSIndex = size 3 +. expectedLenR +. 1 in 
  if unsafe_bool_of_u8 (neq_mask #U8 startOfSIndex (u8 integerIdentificator)) then false else begin
  let expectedLenS = incr startOfSIndex in 

  
  let lengthAfterR = lengthAfterThirdByte -. (u8 2) -. expectedLenS in 
  
  let expectedLenS = index signature (startOfSIndex +. 1) in 
  if checkBorders expectedLenS || unsafe_bool_of_u8 (eq_mask expectedLenS lengthAfterR) then false else

  let firstByteIndexS = incr expectedLenS in
  let secondByteIndexS = incr firstByteIndexS in 

  let zeroByteS = index signature firstByteIndexS in 
  let firstByteS = index signature secondByteIndexS in 
  

  if notCorrectFormalStartSignature expectedLenS zeroByteS firstByteS  then false else 
  let s = sub signature firstByteIndexS expectedLenS in 
  copyBuffer expectedLenS s bufferForS;
  


    true
  end

  end
