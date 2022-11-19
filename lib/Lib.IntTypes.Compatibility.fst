module Lib.IntTypes.Compatibility

open Lib.IntTypes

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
