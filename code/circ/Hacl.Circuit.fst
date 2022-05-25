module Hacl.Circuit

open Lib.Sliceable
open Lib.Bitmap
open Lib.IntTypes

inline_for_extraction noextract
let m = 1

inline_for_extraction noextract
let m' = 4

inline_for_extraction noextract
let circ : circuit 1 4 = fun (i:nat{i<4}) -> match i with
| 0 -> Input 0
| i -> Xor (i-1) (i-1)

let impl = circuit_lowstar #m #m' circ #8 #(uN U8 PUB 8)
