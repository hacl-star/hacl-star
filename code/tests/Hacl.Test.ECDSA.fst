module Hacl.Test.ECDSA

open FStar.HyperStack.All
open FStar.Mul

open LowStar.Buffer

open Lib.IntTypes
open Lib.Buffer
open Lib.PrintBuffer

open Hacl.Impl.ECDSA


val test_ecdsa_signature: 
     mLen: size_t 
  -> m: ilbuffer uint8 mLen {uint_v mLen < Spec.Hash.Definitions.max_input_length (Spec.Hash.Definitions.SHA2_256)} 
  -> privKey: lbuffer uint8 (size 32) 
  -> k: lbuffer uint8 (size 32)
  -> expectedR: ilbuffer uint8 32ul 
  -> expectedS: ilbuffer uint8 32ul 
  -> expectedResult: uint64 -> 
  
  Stack unit 
    (requires fun h -> live h m /\ live h privKey /\ live h k /\ live h expectedR /\ live h expectedS)
    (ensures fun h0 r h1 -> True)


(* quick fix, work in progress *)
let test_ecdsa mLen m privKey k expectedR expectedS expectedResult = 
  admit();
  push_frame();
  
  let m' = create mLen (u8 0) in 
  let privKey' = create 32ul (u8 0) in 
  let k' = create 32ul (u8 0) in 
  
  copy m' m;
  copy privKey' privKey;
  copy k' k;

  let signed = create 64ul (u8 0) in 
  let flag = ecdsa_p256_sha2_sign signed mLen m privKey k in 

  let rSigned = sub signed (size 0) (size 32) in 
  let sSigned = sub signed (size 32) (size 32) in 
  
  if not (result_compare_display 32ul rSigned expectedR) then C.exit 255l;
  if not (result_compare_display 32ul sSigned expectedS) then C.exit 255l;
  if not (Lib.IntTypes.eq expectedResult flag) then C.exit 255l;
  
  pop_frame()
