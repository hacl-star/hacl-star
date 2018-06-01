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

#reset-options "--z3rlimit 50 --max_fuel 0"
let blocks (x:size_nat) (m:size_nat{m > 0}): (r:size_nat{x <= m * r}) =
  if x < 1 then 0
  else (x - 1) / m + 1

let size_pos = x:size_nat{x > 0}
let carry = x:uint8{uint_v x == 0 \/ uint_v x == 1}

val bignum:bits:size_pos -> Type0

val bn_v:#bits:size_pos -> bignum bits -> GTot (r:nat{r < pow2 bits})
val bn_const_1:#bits:size_pos -> r:bignum bits{bn_v r == 1}

val bn_cast_le:#n:size_pos -> m:size_pos{m <= n} -> b:bignum n{bn_v b < pow2 m} -> c:bignum m{bn_v c == bn_v b}
val bn_cast_gt:#n:size_pos -> m:size_pos{m > n} -> b:bignum n{bn_v b < pow2 m} -> c:bignum m{bn_v c == bn_v b}

val bn_add:#n:size_pos -> #m:size_pos{m <= n} -> a:bignum n -> b:bignum m -> Pure (tuple2 carry (bignum n))
  (requires (True))
  (ensures (fun (c, res) -> bn_v res + uint_v c * pow2 n == bn_v a + bn_v b))

val bn_sub:#n:size_pos -> #m:size_pos{m <= n} -> a:bignum n -> b:bignum m {bn_v a >= bn_v b} -> c:bignum n{bn_v c == bn_v a - bn_v b}

val bn_mul:#n:size_pos -> #m:size_pos{n + m < max_size_t} -> a:bignum n -> b:bignum m -> c:bignum (n + m){bn_v c == bn_v a * bn_v b}

val bn_get_bit:#n:size_pos -> b:bignum n -> i:size_pos{i < n} -> c:nat{c == 0 \/ c == 1}
val bn_get_bits:#n:size_pos -> b:bignum n -> i:size_pos{i < n /\ i % 64 == 0} -> j:size_pos{i < j /\ j % 64 == 0 /\ j <= n} -> c:bignum (j - i){bn_v c == (bn_v b / pow2 i) % pow2 (j - i)}
val bn_rshift:#n:size_pos -> b:bignum n -> i:size_pos{i < n /\ i % 64 == 0} -> c:bignum (n - i){bn_v c == bn_v b / pow2 i}

val bn_to_u64:b:bignum 64 -> c:uint64{uint_v c == bn_v b}
val bn_from_u64:c:uint64 -> b:bignum 64{uint_v c == bn_v b}

val bn_is_less:#n:size_pos -> a:bignum n -> b:bignum n-> c:bool{c == true ==> bn_v a < bn_v b}

val bn_lshift_mul_add:#n:size_pos -> #m:size_pos{n <= m} -> x:bignum n -> i:size_pos{n + 1 + i <= m} -> y:bignum 64 -> z:bignum m -> Pure (tuple2 carry (bignum m))
  (requires (True))
  (ensures (fun (c, res) -> bn_v res + uint_v c * pow2 m == bn_v x * (pow2 i) * bn_v y + bn_v z))

val bn_from_bytes_be:#bBytes:size_pos{8 * bBytes < max_size_t} -> b:lbytes bBytes -> Tot (n:bignum (8 * bBytes){bn_v n == nat_from_bytes_be b})

val bn_to_bytes_be: #bBits:size_pos -> n:bignum bBits ->  Tot (b:lbytes (blocks bBits 8) {bn_v n == nat_from_bytes_be b})

val bn_pow2_r_mod:#nBits:size_pos -> n:bignum nBits{bn_v n > 0} -> r:size_pos -> c:bignum nBits{bn_v c == (pow2 r) % (bn_v n)}

//let (+^) #n = bn_add #n
//let ( *^) #n #m = bn_mul #n #m
//let (-^) #n #m = bn_sub #n #m
//let (<^) #n = bn_is_less #n
