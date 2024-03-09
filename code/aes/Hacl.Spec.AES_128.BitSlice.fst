module Hacl.Spec.AES_128.BitSlice

open Lib.IntTypes

inline_for_extraction noextract
let shift_row64 (u:uint64) =
  let u = (u &. u64 0x1111111111111111) |.
          ((u &. u64 0x2220222022202220) >>. size 4) |.
          ((u &. u64 0x0002000200020002) <<. size 12) |.
          ((u &. u64 0x4400440044004400) >>. size 8) |.
          ((u &. u64 0x0044004400440044) <<. size 8) |.
          ((u &. u64 0x8000800080008000) >>. size 12) |.
          ((u &. u64 0x0888088808880888) <<. size 4) in
  u
