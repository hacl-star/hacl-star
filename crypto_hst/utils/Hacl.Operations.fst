module Hacl.Operations

open FStar.UInt32


(* Define base types *)
let u32 = FStar.UInt32.t
let s32 = Hacl.UInt32.t


(* Define word functions *)
let rotate_right (a:s32) (b:u32{v b <= 32}) : Tot s32 =
  Hacl.UInt32.logor (Hacl.UInt32.shift_right a b) (Hacl.UInt32.shift_left a (FStar.UInt32.sub 32ul b))

