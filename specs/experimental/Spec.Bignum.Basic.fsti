module Spec.Bignum.Basic

open FStar.Mul
open Spec.Lib.IntTypes
open Spec.Lib.IntSeq
open Spec.Lib.RawIntTypes

(*
val bignum:Type0
val bn_v:bignum -> GTot nat
val bn: n:nat -> b:bignum{bn_v b == n}
val bn_add: a:bignum -> b:bignum -> c:bignum{bn_v c == bn_v a + bn_v b}
val bn_mul: a:bignum -> b:bignum -> c:bignum{bn_v c == bn_v a * bn_v b}
val bn_sub: a:bignum -> b:bignum{bn_v a > bn_v b} -> c:bignum{bn_v c == bn_v a - bn_v b}

val bn_get_bit: b:bignum -> i:size_nat -> c:nat{c == 0 \/ c == 1}
val bn_get_bits: b:bignum -> i:size_nat{i % 64 == 0} -> j:size_nat{i <= j /\ j % 64 == 0} -> c:bignum{bn_v c < pow2 (j - i) /\ bn_v c == (bn_v b / pow2 i) % pow2 (j - i) }
val bn_rshift:b:bignum -> i:size_nat{i % 64 == 0} -> c:bignum{bn_v c == bn_v b / pow2 i}

val bn_is_less:a:bignum -> b:bignum -> c:bool{c == true ==> a < b}

val bn_lshift_mul_add:x:bignum -> i:size_nat -> y:bignum{bn_v y < pow2 64} -> z:bignum -> c:bignum{bn_v c == bn_v x * (pow2 i) * bn_v y + bn_v z}
*)


val bignum:bits:size_nat -> Type0

val bn_v:#n:size_nat -> bignum n -> GTot (r:nat{r < pow2 n})
val bn:#n:size_nat -> a:nat{a < pow2 n} -> b:bignum n{bn_v b == a}

val bn_cast:#n:size_nat -> m:size_nat -> b:bignum n{bn_v b < pow2 m} -> c:bignum m{bn_v c == bn_v b}

val bn_add:#n:size_nat{n + 1< max_size_t} -> #m:size_nat{n >= m} -> a:bignum n -> b:bignum m -> c:bignum (n + 1){bn_v c == bn_v a + bn_v b}
val bn_mul:#n:size_nat -> #m:size_nat{n + m < max_size_t} -> a:bignum n -> b:bignum m -> c:bignum (n + m){bn_v c == bn_v a * bn_v b}
val bn_sub:#n:size_nat -> #m:size_nat{n >= m} -> a:bignum n -> b:bignum m {bn_v a >= bn_v b} -> c:bignum n{bn_v c == bn_v a - bn_v b}

val bn_get_bit:#n:size_nat -> b:bignum n -> i:size_nat{i < n} -> c:nat{c == 0 \/ c == 1}
val bn_get_bits:#n:size_nat -> b:bignum n -> i:size_nat{i < n /\ i % 64 == 0} -> j:size_nat{i <= j /\ j % 64 == 0 /\ j <= n} -> c:bignum (j - i){bn_v c == (bn_v b / pow2 i) % pow2 (j - i) }
val bn_rshift:#n:size_nat -> b:bignum n -> i:size_nat{i < n /\ i % 64 == 0} -> c:bignum (n - i){bn_v c == bn_v b / pow2 i}

val bn_to_u64:b:bignum 64 -> c:uint64{uint_v c == bn_v b}
val bn_from_u64:c:uint64 -> b:bignum 64{uint_v c == bn_v b}

val bn_is_less:#n:size_nat -> a:bignum n -> b:bignum n-> c:bool{c == true ==> bn_v a < bn_v b}

val bn_lshift_mul_add:#n:size_nat -> #m:size_nat{m >= n /\ m + 1 < max_size_t} -> x:bignum n -> i:size_nat -> y:bignum 64 -> z:bignum m -> c:bignum (m + 1){bn_v c == bn_v x * (pow2 i) * bn_v y + bn_v z}

//val blocks: x:size_nat{x > 0} ->  -> Tot (r:size_nat{r > 0 /\ x <= m * r})
#reset-options "--z3rlimit 150 --max_fuel 0"
let blocks (x:size_nat) (m:size_nat{m > 0}): (r:size_nat{x <= m * r}) = 
  if x < 1 then 0
  else (x - 1) / m + 1

val bn_from_bytes_be: #bBytes:size_nat{8 * bBytes < max_size_t} -> b:lbytes bBytes -> Tot (n:bignum (8*bBytes){bn_v n == nat_from_bytes_be b})

val bn_to_bytes_be: #bBits:size_nat -> n:bignum bBits ->  Tot (b:lbytes (blocks bBits 8) {bn_v n == nat_from_bytes_be b})

val bn_pow2_r_mod:#nBits:size_nat -> n:bignum nBits{bn_v n > 0} -> r:size_nat -> c:bignum nBits{bn_v c == (pow2 r) % (bn_v n)}

let (+^) #n #m = bn_add #n #m
let ( *^) #n #m = bn_mul #n #m
let (-^) #n #m = bn_sub #n #m
let (<^) #n = bn_is_less #n
