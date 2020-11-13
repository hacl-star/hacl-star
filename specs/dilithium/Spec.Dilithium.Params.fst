module Spec.Dilithium.Params

open FStar.Mul
open Lib.IntTypes

// security mode 3
// changes may need to be made to the code if eta is changed to be <= 3

(* names based on the variables used in the ref code
  N -> param_n, since we can't have capitals, and I don't want to have single letter consts *)

inline_for_extraction
let seedbytes = 32
inline_for_extraction
let crhbytes = 48
inline_for_extraction
let param_n = 256
inline_for_extraction
let param_q = 8380417
inline_for_extraction
let root_of_unity = 1753
inline_for_extraction
let param_d = 14
inline_for_extraction
let gamma1 = 523776   // ((Q - 1)/16)
inline_for_extraction
let gamma2 = 261888   // (GAMMA1/2)
inline_for_extraction
let alpha = 523776    // (2*GAMMA2)
inline_for_extraction
let param_k = 5
inline_for_extraction
let param_l = 4
inline_for_extraction
let eta = 5
inline_for_extraction
let beta = 275
inline_for_extraction
let omega = 96
inline_for_extraction
let polyt1_packedbytes = 288
inline_for_extraction
let polyt0_packedbytes = 448
inline_for_extraction
let polyz_packedbytes = 640
inline_for_extraction
let polyw1_packedbytes = 128
inline_for_extraction
let polyeta_packedbytes = 128
inline_for_extraction
let pkbytes = 1472
inline_for_extraction
let skbytes = 3504
inline_for_extraction
let crypto_bytes = 2701
inline_for_extraction
let keccak_suffix = byte 0x1F

// rates in bytes, not bits
inline_for_extraction
let shake128_rate = 168
inline_for_extraction
let shake256_rate = 136
inline_for_extraction
let sha3_256_rate = 136
inline_for_extraction
let sha3_512_rate = 72

inline_for_extraction
let iter_cap = 99