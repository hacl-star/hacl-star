module Hacl.Impl.QTesla.Lemmas.Sal

module U32 = FStar.UInt32
module I32 = FStar.Int32
module U64 = FStar.UInt64
module I64 = FStar.Int64

open FStar.Mul

#set-options "--max_fuel 0 --max_ifuel 0 --z3rlimit 40"

let op_At_Percent = Int.op_At_Percent

// Generalizes FStar.Math.Lemmas.pow2_multiplication_modulo_lemma_2
val pow2_multiplication_modulo_lemma_2: a:int -> b:nat -> c:nat{c <= b} ->
  Lemma ( (a * pow2 c) % pow2 b = (a % pow2 (b - c)) * pow2 c ) 
let pow2_multiplication_modulo_lemma_2 a b c =
  let open FStar.Math.Lemmas in
  euclidean_division_definition a (pow2 (b - c));
  let q = pow2 (b - c) in
  let r = a % pow2 (b - c) in
  assert(a = q * (a / q) + a % q);
  pow2_plus (b - c) c;
  paren_mul_right (a / pow2 (b - c)) (pow2 (b - c)) (pow2 c);
  paren_mul_left (a / pow2 (b - c)) (pow2 (b - c)) (pow2 c);
  modulo_addition_lemma ((a % pow2 (b - c)) * pow2 c) (pow2 b) (a / pow2 (b - c));
  multiplication_order_lemma (pow2 (b - c)) (a % pow2 (b - c)) (pow2 c);
  small_modulo_lemma_1 ((a % pow2 (b - c)) * pow2 c) (pow2 b)

// Generalizes FStar.Math.Lemmas.pow2_modulo_modulo_lemma_1
val pow2_modulo_modulo_lemma_1: a:int -> b:nat -> c:nat{c >= b} ->
  Lemma ( (a % pow2 c) % pow2 b = a % pow2 b )
let pow2_modulo_modulo_lemma_1 a b c =
  Math.Lemmas.pow2_plus (c - b) b;
  Math.Lemmas.modulo_modulo_lemma a (pow2 b) (pow2 (c - b))

val pow2_mod: a:pos -> Lemma (pow2 a % 2 = 0)
let pow2_mod a = Math.Lemmas.pow2_double_mult (a - 1)

val mod_op_At_Percent: v:int -> s:nat -> p:pos
  -> Lemma (pow2_mod p; (v % pow2 (p + s)) @% pow2 p == v @% pow2 p)
let mod_op_At_Percent v s p = 
  pow2_mod p;
  assert ((v % (pow2 (p + s))) @% pow2 p ==
    (let m = (v % pow2 (p + s)) % pow2 p in if m >= pow2 p / 2 then m - pow2 p else m));
  Math.Lemmas.pow2_le_compat (p + s) p;
  pow2_modulo_modulo_lemma_1 v p (p + s)

inline_for_extraction noextract
val shift_arithmetic_left_i32:
    x : I32.t
  -> s : U32.t{U32.v s < I32.n}// /\ shift_arithmetic_left_value_check x s}
  -> Tot I32.t // (r:I32.t{I32.v r == I32.v x * pow2 (UI32.v s)})

#reset-options "--z3rlimit 100 --max_fuel 2 --max_ifuel 2"

let shift_arithmetic_left_i32 x s =
    let open FStar.Int.Cast in
    uint32_to_int32 ((int32_to_uint32 x) `U32.shift_left` s)

val shift_arithmetic_left_i32_value_lemma:
    a:I32.t
  -> s:U32.t{U32.v s < U32.n /\ Int.fits (I32.v a * pow2 (U32.v s)) I32.n}
  -> Lemma (I32.v (shift_arithmetic_left_i32 a s) = (I32.v a * pow2 (U32.v s)) @% pow2 I32.n)

let shift_arithmetic_left_value_lemma a s =
  let open FStar.Int.Cast in
  calc (==) {
    I32.v (shift_arithmetic_left_i32 a s);
    == { } // shift_arithmetic_left definition
    I32.v (uint32_to_int32 U32.(int32_to_uint32 a <<^ s));
    == { } // U32.shift_left definition; U32.uint_to_t definition
    I32.v (uint32_to_int32 (U32.uint_to_t
      (UInt.shift_left (U32.v (int32_to_uint32 a)) (U32.v s))));
    == { UInt.shift_left_value_lemma (U32.v (int32_to_uint32 a)) (U32.v s) }
    I32.v (uint32_to_int32 (U32.uint_to_t
      ((U32.v (int32_to_uint32 a) * pow2 (U32.v s)) % pow2 U32.n)));
    == { } // Int.Cast.int32_to_uint32 definition
    I32.v (uint32_to_int32 (U32.uint_to_t
      (((I32.v a % pow2 U32.n) * pow2 (U32.v s)) % pow2 U32.n)));
    == { } // Int.Cast.uint32_to_int32 definition
    U32.v ((U32.uint_to_t
      (((I32.v a % pow2 32) * pow2 (U32.v s)) % pow2 U32.n))) @% pow2 U32.n;
    == { UInt32.vu_inv (((I32.v a @% pow2 32) * pow2 (U32.v s)) % pow2 U32.n) }
    (((I32.v a % pow2 32) * pow2 (U32.v s)) % pow2 U32.n) @% pow2 U32.n;
    == { mod_op_At_Percent (I32.v a * pow2 (U32.v s)) 0 (pow2 U32.n) }
    ((I32.v a % pow2 32) * pow2 (U32.v s)) @% pow2 U32.n;
    == { pow2_multiplication_modulo_lemma_2 (I32.v a) (U32.n + U32.v s) (U32.v s) }
    ((I32.v a * pow2 (U32.v s)) % pow2 (U32.n + U32.v s)) @% pow2 U32.n;
    == { mod_op_At_Percent (I32.v a * pow2 (U32.v s)) (U32.v s) U32.n }
    (I32.v a * pow2 (U32.v s)) @% pow2 U32.n;
  }

// Second first, same as the first. A little bit louder and a little bit worse.
inline_for_extraction noextract
val shift_arithmetic_left_i64:
    x : I64.t
  -> s : U32.t{U32.v s < I64.n}// /\ shift_arithmetic_left_value_check x s}
  -> Tot I64.t // (r:I32.t{I32.v r == I32.v x * pow2 (UI32.v s)})

#reset-options "--z3rlimit 100 --max_fuel 2 --max_ifuel 2"

let shift_arithmetic_left_i64 x s =
    let open FStar.Int.Cast in
    uint64_to_int64 ((int64_to_uint64 x) `U64.shift_left` s)

(*val shift_arithmetic_left_i64_value_lemma:
    a:I64.t
  -> s:U32.t{U32.v s < U32.n /\ Int.fits (I64.v a * pow2 (U32.v s)) I64.n}
  -> Lemma (I64.v (shift_arithmetic_left_i64 a s) = (I64.v a * pow2 (U32.v s)) @% pow2 I64.n)

let shift_arithmetic_left_i64_value_lemma a s =
  let open FStar.Int.Cast in
  calc (==) {
    I64.v (shift_arithmetic_left_i64 a s);
    == { } // shift_arithmetic_left definition
    I64.v (uint64_to_int64 U64.(int64_to_uint64 a <<^ s));
    == { } // U32.shift_left definition; U32.uint_to_t definition
    I64.v (uint64_to_int64 (U32.uint_to_t
      (UInt.shift_left (U32.v (int64_to_uint64 a)) (U32.v s))));
    == { UInt.shift_left_value_lemma (U32.v (int64_to_uint64 a)) (U32.v s) }
    I64.v (uint64_to_int64 (U32.uint_to_t
      ((U32.v (int64_to_uint64 a) * pow2 (U32.v s)) % pow2 U64.n)));
    == { } // Int.Cast.int32_to_uint32 definition
    I64.v (uint64_to_int64 (U32.uint_to_t
      (((I64.v a % pow2 U64.n) * pow2 (U32.v s)) % pow2 U64.n)));
    == { } // Int.Cast.uint32_to_int32 definition
    U32.v ((U32.uint_to_t
      (((I64.v a % pow2 32) * pow2 (U32.v s)) % pow2 U64.n))) @% pow2 U64.n;
    == { UInt32.vu_inv (((I64.v a @% pow2 32) * pow2 (U32.v s)) % pow2 U64.n) }
    (((I64.v a % pow2 32) * pow2 (U32.v s)) % pow2 U64.n) @% pow2 U64.n;
    == { mod_op_At_Percent (I64.v a * pow2 (U32.v s)) 0 (pow2 U64.n) }
    ((I64.v a % pow2 32) * pow2 (U32.v s)) @% pow2 U64.n;
    == { pow2_multiplication_modulo_lemma_2 (I64.v a) (U64.n + U32.v s) (U32.v s) }
    ((I64.v a * pow2 (U32.v s)) % pow2 (U64.n + U32.v s)) @% pow2 U64.n;
    == { mod_op_At_Percent (I64.v a * pow2 (U32.v s)) (U32.v s) U64.n }
    (I64.v a * pow2 (U32.v s)) @% pow2 U64.n;
  }
*)
