module Lib.IntTypes.Compatibility

open Lib.IntTypes

val pow2_values: n:nat ->  Lemma (
    pow2 0 == 1 /\
    pow2 1 == 2 /\
    pow2 2 == 4 /\
    pow2 3 == 8 /\
    pow2 4 == 16 /\
    pow2 8 == 0x100 /\
    pow2 16 == 0x10000 /\
    pow2 32 == 0x100000000 /\
    pow2 64 == 0x10000000000000000 /\
    pow2 128 == 0x100000000000000000000000000000000
    )
    [SMTPat (pow2 n)]

val uint_v_size_lemma: s:size_nat ->
  Lemma
  (ensures (uint_v (size s) == s))
  [SMTPat (uint_v (size s))]
let uint_v_size_lemma s = ()

unfold
let inttype = t:inttype{unsigned t}

val uintv_extensionality:
   #t:inttype
 -> #l:secrecy_level
 -> a:uint_t t l
 -> b:uint_t t l
 -> Lemma
  (requires uint_v a == uint_v b)
  (ensures  a == b)
let uintv_extensionality #t #l a b = ()

let nat_to_uint (#t:inttype) (#l:secrecy_level) (n:nat{n <= maxint t}) : u:uint_t t l{uint_v u == n} = uint #t #l n

let zeroes t l = zeros t l
