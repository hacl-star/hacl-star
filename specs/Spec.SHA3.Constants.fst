module Spec.SHA3.Constants

open Lib.IntTypes

#reset-options "--z3rlimit 50 --max_fuel 0 --max_ifuel 0"

let rotc_t = x:size_t{0 < uint_v x && uint_v x < 64}

unfold let rotc_list: list rotc_t =
  [size 1; size 3; size 6; size 10; size 15; size 21; size 28; size 36;
   size 45; size 55; size 2; size 14; size 27; size 41; size 56; size 8;
   size 25; size 43; size 62; size 18; size 39; size 61; size 20; size 44]

let piln_t = x:size_t{size_v x < 25}

unfold let piln_list: list piln_t =
  [size 10; size 7; size 11; size 17; size 18; size 3; size 5; size 16;
   size 8; size 21; size 24; size 4; size 15; size 23; size 19; size 13;
   size 12; size 2; size 20; size 14; size 22; size 9; size 6; size 1]

unfold let rndc_list: list uint64 =
  [u64 0x0000000000000001; u64 0x0000000000008082; u64 0x800000000000808a; u64 0x8000000080008000;
   u64 0x000000000000808b; u64 0x0000000080000001; u64 0x8000000080008081; u64 0x8000000000008009;
   u64 0x000000000000008a; u64 0x0000000000000088; u64 0x0000000080008009; u64 0x000000008000000a;
   u64 0x000000008000808b; u64 0x800000000000008b; u64 0x8000000000008089; u64 0x8000000000008003;
   u64 0x8000000000008002; u64 0x8000000000000080; u64 0x000000000000800a; u64 0x800000008000000a;
   u64 0x8000000080008081; u64 0x8000000000008080; u64 0x0000000080000001; u64 0x8000000080008008]
