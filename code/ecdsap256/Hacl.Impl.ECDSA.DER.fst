module Hacl.Impl.ECDSA.DER

open FStar.HyperStack.All
open FStar.HyperStack
module ST = FStar.HyperStack.ST

open Lib.IntTypes
open Lib.Buffer

open Hacl.Impl.P256.LowLevel.RawCmp
open Lib.RawIntTypes

let lenCoor = 32ul
let integerIdentificator = 2ul


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
      if v integerFirstIdentifier = v integerIdentificator then flag = false else True
  
  )
)


assume val checkBorders: b: uint8 -> Tot (flag: bool { flag <==> v b = 0 || v b > v lenCoor + 1})

assume val notCorrectFormalStartSignature: len: uint8 -> byteZero: uint8 -> byteOne: uint8 -> 
  Tot (flag: bool 
    {
      if (v len = 0x33 &&  v byteZero = 0  && v byteOne > 0x7F) 
	then flag = false
      else if v len <> 33 then 
	flag = false
      else 
	flag = true
    })


assume val copyBuffer: len: size_t -> from: lbuffer uint8 len -> to: lbuffer uint8 lenCoor ->
  Stack unit 
    (requires fun h -> live h from /\ live h to)
    (ensures fun h0 _ h1 -> True)





(* Note that the r and s value must be prepended with 0x00 if their first byte is greater than 0x7F.  *)

let decode sigLen signature bufferForR bufferForS = 
  (* |0x30|SigLen|0x02|RLen|R|0x02|SLen|S *)

  if sigLen <. 6ul then false else

  (* |->0x30|SigLen|0x02|RLen|R|0x02|SLen|S  *)
  let pointer = size 0 in 
  let zeroByte = index signature pointer in 
  (* the only allowed value is 0x30 *)
  if unsafe_bool_of_u8 (neq_mask #U8 zeroByte (u8 30)) then false else

  (* |0x30| -> SigLen| 0x02| RLen| R | 0x02| SLen| S *)
  (* now pointer references the first byte (i.e. the sigLen byte) *)
  let pointer = incr pointer in 
  (* firstByte = sigLen *)
  let firstByte = index signature pointer in
  
  (* the buffer is uint8, so we ask of the values we compare to be both in the uint8 range *)
  if unsafe_bool_of_u8 (neq_mask #U8 firstByte (u8 255)) then false else begin
    eq_mask_lemma firstByte (u8 255);

  (*lengthFullsignature = sigLen + 1 -> to take into account the first byte *)
  let lengthFullSignature = to_u32 (incr firstByte) in 
    incr_lemma firstByte;
  let sizeAsUInt32 = size_to_uint32 sigLen in 
    eq_mask_lemma lengthFullSignature sizeAsUInt32;
  (* we compare the sigLen + 1 with the length of signature  *)
  if unsafe_bool_of_u32 (eq_mask #U32 lengthFullSignature sizeAsUInt32) then false else

  let pointer = incr pointer in
  (* now pointer references the 2nd byte =  the type indentifier of r *)
  (* |0x30|SigLen| -> 0x02|RLen|R|0x02|SLen|S  *)

  let startofRIndex = index signature pointer in 
  (* the only allowed value here is 0x2 *)
  if unsafe_bool_of_u8 (neq_mask #U8 startofRIndex (u8 2)) then false else 

  let pointer = incr pointer in 
  (* now pointer references the 3rd byte = the length of r  *)
  (* |0x30|SigLen|0x02| -> RLen|R|0x02|SLen|S  *)
  let expectedLenR = index signature pointer in 

  let lengthAfterThirdByte = sigLen -. pointer in 
  (* the lengthAfterThirdByte has the length of the full signature - 3, meaning the shifted by the number of bytes we already looked at *)

  
  let sc = unsafe_bool_of_u8 (gt_mask expectedLenR lengthAfterThirdByte) in 
  (* we compare the length of r with the length of the rest of the signature.
     It should be more than the length of the rest of the signature.   *)

  if sc then false else

  (* the second check of the length of the coordinates.
   we expect the length of the coordinate to be unconditionally more than 0 and less than 34. 33 is still a possible value in some cases. *)
  let checkedBordersResult = checkBorders expectedLenR  in 
  if checkedBordersResult then false else 

  let pointer = incr pointer in 
  (* now the pointer references the forth byte of the signature *)
  (* |0x30|SigLen|0x02|RLen| -> R|0x02|SLen|S  *)

  let rZeroByte = index signature pointer in 
  (* rZeroByte stands for the 0th byte of signature *)
  let rFirstByte = index signature (incr pointer) in 
  (* rFirstByte stands for the 1th byte of signature *)

  (* signature might be the size of 33 if and only if the 0th byte is 0 and the first byte is more or equal than 0x7f. In all the other cases the length is 32 and less *)
  if notCorrectFormalStartSignature expectedLenR rZeroByte rFirstByte then false else 

  (* if everything is fine, we copy the data  *)
  let r = sub signature pointer expectedLenR in 

  (* The function copies from the last type till the first/zero/length one (depending on the length) *)
  copyBuffer expectedLenR r bufferForR;
    
  
  let startOfSIndex = size 3 +. expectedLenR +. (size 1) in 
  if unsafe_bool_of_u8 (neq_mask #U8 startOfSIndex (u8 2)) then false else begin
  let expectedLenS = incr startOfSIndex in 

  
  let lengthAfterR = lengthAfterThirdByte -. (u8 2) -. expectedLenS in 
  
  let expectedLenS = index signature (startOfSIndex +. (size 1)) in 

  let sc = unsafe_bool_of_u8 (eq_mask expectedLenS lengthAfterR) in 
  if checkBorders expectedLenS || sc then false else

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
