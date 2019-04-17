module Spec.Powtwo.Lemmas

open FStar.Math.Lemmas

val pow2_values: n:nat ->  Lemma (
    pow2 0 == 1 /\
    pow2 1 == 2 /\
    pow2 2 == 4 /\
    pow2 3 == 8 /\
    pow2 4 == 16 /\
    pow2 5 == 32 /\
    pow2 6 == 64 /\
    pow2 7 == 128 /\
    pow2 8 == 0x100 /\
    pow2 9 == 512 /\
    pow2 10 == 1024 /\
    pow2 11 == 2048 /\
    pow2 12 == 4096 /\
    pow2 13 == 8192 /\
    pow2 14 == 16384 /\
    pow2 15 == 32768 /\
    pow2 16 == 0x10000 /\
    pow2 17 == 131072 /\
    pow2 18 == 262144 /\
    pow2 19 == 524288 /\
    pow2 20 == 1048576 /\
    pow2 21 == 2097152 /\
    pow2 22 == 4194304 /\
    pow2 23 == 8388608 /\
    pow2 24 == 16777216 /\
    pow2 25 == 33554432 /\
    pow2 26 == 67108864 /\
    pow2 27 == 134217728 /\
    pow2 28 == 268435456 /\
    pow2 29 == 536870912 /\
    pow2 30 == 1073741824 /\
    pow2 31 == 2147483648 /\
    pow2 32 == 0x100000000
    )
    [SMTPat (pow2 n)]

let pow2_values n =
    assert_norm (pow2 0 = 1);
    assert_norm (pow2 1 = 2);
    assert_norm (pow2 2 = 4);
    assert_norm (pow2 3 = 8);
    assert_norm (pow2 4 = 16);
    assert_norm (pow2 5 = 32);
    assert_norm (pow2 6 = 64);
    assert_norm (pow2 7 = 128);
    assert_norm (pow2 8 = 0x100);
    assert_norm (pow2 9 = 512);
    assert_norm (pow2 10 = 1024);
    assert_norm (pow2 11 = 2048);
    assert_norm (pow2 12 = 4096);
    assert_norm (pow2 13 = 8192);
    assert_norm (pow2 14 = 16384);
    assert_norm (pow2 15 = 32768);
    assert_norm (pow2 16 = 0x10000);
    assert_norm (pow2 17 = 131072);
    assert_norm (pow2 18 = 262144);
    assert_norm (pow2 19 = 524288);
    assert_norm (pow2 20 = 1048576);
    assert_norm (pow2 21 = 2097152);
    assert_norm (pow2 22 = 4194304);
    assert_norm (pow2 23 = 8388608);
    assert_norm (pow2 24 = 16777216);
    assert_norm (pow2 25 = 33554432);
    assert_norm (pow2 26 = 67108864);
    assert_norm (pow2 27 = 134217728);
    assert_norm (pow2 28 = 268435456);
    assert_norm (pow2 29 = 536870912);
    assert_norm (pow2 30 = 1073741824);
    assert_norm (pow2 31 = 2147483648);
    assert_norm (pow2 32 = 0x100000000)

val pow2_eq_compat: n:nat -> m:nat -> Lemma
  (requires (m == n))
  (ensures  (pow2 m == pow2 n))
let pow2_eq_compat n m = pow2_le_compat n m; pow2_le_compat m n 
