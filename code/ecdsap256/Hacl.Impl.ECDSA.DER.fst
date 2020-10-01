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


val checkBorders: b: uint8 -> Tot (flag: bool {(not flag) <==> v b <> 0 && v b <= v lenCoor + 1})

let checkBorders b = 
  let zero = eq_mask b (u8 0) in 
  let moreThan33 = gt_mask b (u8 (FStar.UInt32.v lenCoor + 1)) in 
  let both = lognot (logor zero moreThan33) in 
    logor_lemma zero moreThan33;
    lognot_lemma (logor zero moreThan33);
  
  unsafe_bool_of_u8 both


val notCorrectFormatStartSignature: len: uint8 -> byteZero: uint8 -> byteOne: uint8 -> 
  Tot (flag: bool 
    {
      if (v byteZero = 0 && v len = 33 && v byteOne >= 0x7F) ||  (v len <> 33 && v byteZero <> 0)
      then 
	flag == false 
      else 
	flag == true
    })

let notCorrectFormatStartSignature len byteZero byteOne = 
  let zero = eq_mask byteZero (u8 0) in 
  let len33 = eq_mask len (u8 33) in 
  let byteOneMore7f = gte_mask byteOne (u8 0x7f) in 

  let firstBranch = logand (logand zero len33) byteOneMore7f in 
    logand_lemma zero len33;
    logand_lemma (logand zero len33) byteOneMore7f;

  let secondBranch = lognot (logor zero len33) in 
    logor_lemma zero len33;
    lognot_lemma (logor zero len33);

  let twoBranched = logor firstBranch secondBranch in 
  logor_lemma firstBranch secondBranch;

  unsafe_bool_of_u8 twoBranched


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
  let identificationByte = index signature pointer in 
  (* the only allowed value is 0x30 *)
  if unsafe_bool_of_u8 (neq_mask #U8 identificationByte (u8 30)) then false else

  (* |0x30| -> SigLen| 0x02| RLen| R | 0x02| SLen| S *)
  (* now pointer references the first byte (i.e. the sigLen byte) *)
  let pointer = incr pointer in 
  (* firstByte = sigLen *)
  let signatureLengthByte = index signature pointer in
  
  (* the buffer is uint8, so we ask of the values we compare to be both in the uint8 range *)
  if unsafe_bool_of_u8 (neq_mask #U8 signatureLengthByte (u8 255)) then false else begin
    eq_mask_lemma signatureLengthByte (u8 255);

  (*lengthFullsignature = sigLen + 1 -> to take into account the first byte *)
  let lengthFullSignature = to_u32 (incr signatureLengthByte) in 
    incr_lemma signatureLengthByte;
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
  let checkedBordersResultR = checkBorders expectedLenR  in 
  if checkedBordersResultR then false else 

  let pointer = incr pointer in 
  (* now the pointer references the forth byte of the signature *)
  (* |0x30|SigLen|0x02|RLen| -> R|0x02|SLen|S  *)

  let rZeroByte = index signature pointer in 
  (* rZeroByte stands for the 0th byte of signature *)
  let rFirstByte = index signature (incr pointer) in 
  (* rFirstByte stands for the 1th byte of signature *)

  (* signature might be the size of 33 if and only if the 0th byte is 0 and the first byte is more or equal than 0x7f. In all the other cases the length is 32 and less *)
  if notCorrectFormatStartSignature expectedLenR rZeroByte rFirstByte then false else 

  (* if everything is fine, we copy the data  *)
  let r = sub signature pointer expectedLenR in 

  (* The function copies from the last type till the first/zero/length one (depending on the length) *)
  copyBuffer expectedLenR r bufferForR;
    
  let pointer = pointer +. expectedLenR in 
  (* now the pointer references the start of the type identifier for S *)
    (* |0x30|SigLen|0x02|RLen|R| -> 0x02|SLen|S  *)

  let startOfSByte = index signature pointer in 

  (* the only allowed value is 0x02 *)
  if unsafe_bool_of_u8 (neq_mask #U8 startOfSByte (u8 2)) then false else begin

  let pointer = incr pointer in
  (* now the pointer references the start of the length for S *)
  (* |0x30|SigLen|0x02|RLen|R|0x02| -> SLen|S  *)

  let lengthSByte = index signature pointer in 
  let expectedLengthS = sigLen -. pointer -. 1ul in 
  (*  *)

  let sc = unsafe_bool_of_u8 (eq_mask expectedLengthS lengthSByte) in 
  (* if the length of the signature left is not equal to our computed length till this moment *)
  if sc then false else

  let checkedBordersResultS = checkBorders expectedLengthS  in 
  (* the second check of the length of the coordinates.
   we expect the length of the coordinate to be unconditionally more than 0 and less than 34. 33 is still a possible value in some cases. *)
  if checkedBordersResultS then false else

  let pointer = incr pointer in 
  (* now pointer references the start of the S *)

  let zeroByteS = index signature pointer in
  let firstByteS = index signature (incr pointer) in 

  (* signature might be the size of 33 if and only if the 0th byte is 0 and the first byte is more or equal than 0x7f. In all the other cases the length is 32 and less *)
  if notCorrectFormatStartSignature expectedLengthS zeroByteS firstByteS  then false else 
  let s = sub signature pointer expectedLengthS in 
  copyBuffer expectedLengthS s bufferForS;
  
  true
  end

  end
