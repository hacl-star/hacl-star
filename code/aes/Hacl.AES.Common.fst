module Hacl.AES.Common

open Lib.IntTypes
open Lib.Sequence

open Spec.AES

unfold noextract
let u8_16_to_le (x:lseq uint8 16): lseq uint8 16 =
  create16 x.[15] x.[14] x.[13] x.[12] x.[11] x.[10] x.[9] 
    x.[8] x.[7] x.[6] x.[5] x.[4] x.[3] x.[2] x.[1] x.[0]

unfold noextract
let u8_16_2_to_le (x:lseq uint8 32): lseq uint8 32 =
  concat (u8_16_to_le (sub x 0 16)) (u8_16_to_le (sub x 16 16))
