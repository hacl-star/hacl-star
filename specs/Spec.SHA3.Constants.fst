module Spec.SHA3.Constants

open Lib.IntTypes

#reset-options "--z3rlimit 50 --max_fuel 0 --max_ifuel 0"
let rotc_t = rotval U64

unfold let rotc_list:  list rotc_t =
  [1ul; 3ul; 6ul; 10ul; 15ul; 21ul; 28ul; 36ul;
   45ul; 55ul; 2ul; 14ul; 27ul; 41ul; 56ul; 8ul;
   25ul; 43ul; 62ul; 18ul; 39ul; 61ul; 20ul; 44ul]

let piln_t = x:size_t{size_v x < 25}

unfold let piln_list: list piln_t =
  [10ul; 7ul; 11ul; 17ul; 18ul; 3ul; 5ul; 16ul;
   8ul; 21ul; 24ul; 4ul; 15ul; 23ul; 19ul; 13ul;
   12ul; 2ul; 20ul; 14ul; 22ul; 9ul; 6ul; 1ul]

unfold let rndc_list: list (uint_t U64 PUB) =
  [0x0000000000000001uL; 0x0000000000008082uL; 0x800000000000808auL; 0x8000000080008000uL;
   0x000000000000808buL; 0x0000000080000001uL; 0x8000000080008081uL; 0x8000000000008009uL;
   0x000000000000008auL; 0x0000000000000088uL; 0x0000000080008009uL; 0x000000008000000auL;
   0x000000008000808buL; 0x800000000000008buL; 0x8000000000008089uL; 0x8000000000008003uL;
   0x8000000000008002uL; 0x8000000000000080uL; 0x000000000000800auL; 0x800000008000000auL;
   0x8000000080008081uL; 0x8000000000008080uL; 0x0000000080000001uL; 0x8000000080008008uL]
