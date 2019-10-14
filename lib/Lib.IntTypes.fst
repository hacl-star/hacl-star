module Lib.IntTypes

open FStar.Math.Lemmas

#push-options "--max_fuel 0 --max_ifuel 1 --z3rlimit 100"

let pow2_2 _   = assert_norm (pow2 2 = 4)
let pow2_3 _   = assert_norm (pow2 3 = 8)
let pow2_4 _   = assert_norm (pow2 4 = 16)
let pow2_127 _ = assert_norm (pow2 127 = 0x80000000000000000000000000000000)

let bits_numbytes t = ()

let sec_int_t t = pub_int_t t

let sec_int_v #t u = pub_int_v u

let secret #t x = x

[@(strict_on_arguments [0])]
let mk_int #t #l x =
  match t with
  | U1 -> UInt8.uint_to_t x
  | U8 -> UInt8.uint_to_t x
  | U16 -> UInt16.uint_to_t x
  | U32 -> UInt32.uint_to_t x
  | U64 -> UInt64.uint_to_t x
  | U128 -> UInt128.uint_to_t x
  | S8 -> Int8.int_to_t x
  | S16 -> Int16.int_to_t x
  | S32 -> Int32.int_to_t x
  | S64 -> Int64.int_to_t x
  | S128 -> Int128.int_to_t x

val v_extensionality:
   #t:inttype
 -> #l:secrecy_level
 -> a:int_t t l
 -> b:int_t t l
 -> Lemma
  (requires v a == v b)
  (ensures  a == b)
let v_extensionality #t #l a b =
  match t with
  | U1   -> ()
  | U8   -> UInt8.v_inj a b
  | U16  -> UInt16.v_inj a b
  | U32  -> UInt32.v_inj a b
  | U64  -> UInt64.v_inj a b
  | U128 -> UInt128.v_inj a b
  | S8   -> Int8.v_inj a b
  | S16  -> Int16.v_inj a b
  | S32  -> Int32.v_inj a b
  | S64  -> Int64.v_inj a b
  | S128 -> Int128.v_inj a b

let v_injective #t #l a =
  v_extensionality a (mk_int (v a))

let v_mk_int #t #l n = ()

let u128 n = FStar.UInt128.uint64_to_uint128 (u64 n)

// KreMLin will extract this to FStar_Int128_int_to_t, which isn't provided
// We'll need to have FStar.Int128.int64_to_int128 to support int128_t literals
let i128 n =
  assert_norm (pow2 (bits S64 - 1) <= pow2 (bits S128 - 1));
  sint #S128 #SEC n

let size_to_uint32 x = x

let size_to_uint64 x = Int.Cast.uint32_to_uint64 x

let byte_to_uint8 x = x

let byte_to_int8 x = Int.Cast.uint8_to_int8 x

let op_At_Percent = Int.op_At_Percent

// FStar.UInt128 gets special treatment in KreMLin. There is no
// equivalent for FStar.Int128 at the moment, so we use the three
// assumed cast operators below.
//
// Using them will fail at runtime with an informative message.
// The commented-out implementations show that they are realizable.
//
// When support for `FStar.Int128` is added KreMLin, these casts must
// be added as special cases. When using builtin compiler support for
// `int128_t`, they can be implemented directly as C casts without
// undefined or implementation-defined behaviour.

assume
val uint128_to_int128: a:UInt128.t{v a <= maxint S128} -> b:Int128.t{Int128.v b == UInt128.v a}
//let uint128_to_int128 a = Int128.int_to_t (v a)

assume
val int128_to_uint128: a:Int128.t -> b:UInt128.t{UInt128.v b == Int128.v a % pow2 128}
//let int128_to_uint128 a = mk_int (v a % pow2 128)

assume
val int64_to_int128: a:Int64.t -> b:Int128.t{Int128.v b == Int64.v a}
//let int64_to_int128 a = Int128.int_to_t (v a)

val uint64_to_int128: a:UInt64.t -> b:Int128.t{Int128.v b == UInt64.v a}
let uint64_to_int128 a = uint128_to_int128 (Int.Cast.Full.uint64_to_uint128 a)

val int64_to_uint128: a:Int64.t -> b:UInt128.t{UInt128.v b == Int64.v a % pow2 128}
let int64_to_uint128 a = int128_to_uint128 (int64_to_int128 a)

val int128_to_uint64: a:Int128.t -> b:UInt64.t{UInt64.v b == Int128.v a % pow2 64}
let int128_to_uint64 a = Int.Cast.Full.uint128_to_uint64 (int128_to_uint128 a)

#push-options "--z3rlimit 700"

[@(strict_on_arguments [0;2])]
let cast #t #l t' l' u =
  assert_norm (pow2 8 = 2 * pow2 7);
  assert_norm (pow2 16 = 2 * pow2 15);
  assert_norm (pow2 64 * pow2 64 = pow2 128);
  assert_norm (pow2 16 * pow2 48 = pow2 64);
  assert_norm (pow2 8 * pow2 56 = pow2 64);
  assert_norm (pow2 32 * pow2 32 = pow2 64);
  modulo_modulo_lemma (v u) (pow2 32) (pow2 32);
  modulo_modulo_lemma (v u) (pow2 64) (pow2 64);
  modulo_modulo_lemma (v u) (pow2 128) (pow2 64);
  modulo_modulo_lemma (v u) (pow2 16) (pow2 48);
  modulo_modulo_lemma (v u) (pow2 8) (pow2 56);
  let open FStar.Int.Cast in
  let open FStar.Int.Cast.Full in
  match t, t' with
  | U1, U1     -> u
  | U1, U8     -> u
  | U1, U16    -> uint8_to_uint16 u
  | U1, U32    -> uint8_to_uint32 u
  | U1, U64    -> uint8_to_uint64 u
  | U1, U128   -> UInt128.uint64_to_uint128 (uint8_to_uint64 u)
  | U1, S8     -> uint8_to_int8 u
  | U1, S16    -> uint8_to_int16 u
  | U1, S32    -> uint8_to_int32 u
  | U1, S64    -> uint8_to_int64 u
  | U1, S128   -> uint64_to_int128 (uint8_to_uint64 u)

  | U8, U1     -> UInt8.rem u 2uy
  | U8, U8     -> u
  | U8, U16    -> uint8_to_uint16 u
  | U8, U32    -> uint8_to_uint32 u
  | U8, U64    -> uint8_to_uint64 u
  | U8, U128   -> UInt128.uint64_to_uint128 (uint8_to_uint64 u)
  | U8, S8     -> uint8_to_int8 u
  | U8, S16    -> uint8_to_int16 u
  | U8, S32    -> uint8_to_int32 u
  | U8, S64    -> uint8_to_int64 u
  | U8, S128   -> uint64_to_int128 (uint8_to_uint64 u)

  | U16, U1    -> UInt8.rem (uint16_to_uint8 u) 2uy
  | U16, U8    -> uint16_to_uint8 u
  | U16, U16   -> u
  | U16, U32   -> uint16_to_uint32 u
  | U16, U64   -> uint16_to_uint64 u
  | U16, U128  -> UInt128.uint64_to_uint128 (uint16_to_uint64 u)
  | U16, S8    -> uint16_to_int8 u
  | U16, S16   -> uint16_to_int16 u
  | U16, S32   -> uint16_to_int32 u
  | U16, S64   -> uint16_to_int64 u
  | U16, S128  -> uint64_to_int128 (uint16_to_uint64 u)

  | U32, U1    -> UInt8.rem (uint32_to_uint8 u) 2uy
  | U32, U8    -> uint32_to_uint8 u
  | U32, U16   -> uint32_to_uint16 u
  | U32, U32   -> u
  | U32, U64   -> uint32_to_uint64 u
  | U32, U128  -> UInt128.uint64_to_uint128 (uint32_to_uint64 u)
  | U32, S8    -> uint32_to_int8 u
  | U32, S16   -> uint32_to_int16 u
  | U32, S32   -> uint32_to_int32 u
  | U32, S64   -> uint32_to_int64 u
  | U32, S128  -> uint64_to_int128 (uint32_to_uint64 u)

  | U64, U1    -> UInt8.rem (uint64_to_uint8 u) 2uy
  | U64, U8    -> uint64_to_uint8 u
  | U64, U16   -> uint64_to_uint16 u
  | U64, U32   -> uint64_to_uint32 u
  | U64, U64   -> u
  | U64, U128  -> UInt128.uint64_to_uint128 u
  | U64, S8    -> uint64_to_int8 u
  | U64, S16   -> uint64_to_int16 u
  | U64, S32   -> uint64_to_int32 u
  | U64, S64   -> uint64_to_int64 u
  | U64, S128  -> uint64_to_int128 u

  | U128, U1   -> UInt8.rem (uint64_to_uint8 (uint128_to_uint64 u)) 2uy
  | U128, U8   -> uint64_to_uint8 (UInt128.uint128_to_uint64 u)
  | U128, U16  -> uint64_to_uint16 (UInt128.uint128_to_uint64 u)
  | U128, U32  -> uint64_to_uint32 (UInt128.uint128_to_uint64 u)
  | U128, U64  -> UInt128.uint128_to_uint64 u
  | U128, U128 -> u
  | U128, S8   -> uint64_to_int8 (UInt128.uint128_to_uint64 u)
  | U128, S16  -> uint64_to_int16 (UInt128.uint128_to_uint64 u)
  | U128, S32  -> uint64_to_int32 (UInt128.uint128_to_uint64 u)
  | U128, S64  -> uint64_to_int64 (UInt128.uint128_to_uint64 u)
  | U128, S128 -> uint128_to_int128 u

  | S8, U1     -> UInt8.rem (int8_to_uint8 u) 2uy
  | S8, U8     -> int8_to_uint8 u
  | S8, U16    -> int8_to_uint16 u
  | S8, U32    -> int8_to_uint32 u
  | S8, U64    -> int8_to_uint64 u
  | S8, U128   -> int64_to_uint128 (int8_to_int64 u)
  | S8, S8     -> u
  | S8, S16    -> int8_to_int16 u
  | S8, S32    -> int8_to_int32 u
  | S8, S64    -> int8_to_int64 u
  | S8, S128   -> int64_to_int128 (int8_to_int64 u)

  | S16, U1    -> UInt8.rem (int16_to_uint8 u) 2uy
  | S16, U8    -> int16_to_uint8 u
  | S16, U16   -> int16_to_uint16 u
  | S16, U32   -> int16_to_uint32 u
  | S16, U64   -> int16_to_uint64 u
  | S16, U128  -> int64_to_uint128 (int16_to_int64 u)
  | S16, S8    -> int16_to_int8 u
  | S16, S16   -> u
  | S16, S32   -> int16_to_int32 u
  | S16, S64   -> int16_to_int64 u
  | S16, S128  -> int64_to_int128 (int16_to_int64 u)

  | S32, U1    -> UInt8.rem (int32_to_uint8 u) 2uy
  | S32, U8    -> int32_to_uint8 u
  | S32, U16   -> int32_to_uint16 u
  | S32, U32   -> int32_to_uint32 u
  | S32, U64   -> int32_to_uint64 u
  | S32, U128  -> int64_to_uint128 (int32_to_int64 u)
  | S32, S8    -> int32_to_int8 u
  | S32, S16   -> int32_to_int16 u
  | S32, S32   -> u
  | S32, S64   -> int32_to_int64 u
  | S32, S128  -> int64_to_int128 (int32_to_int64 u)

  | S64, U1    -> UInt8.rem (int64_to_uint8 u) 2uy
  | S64, U8    -> int64_to_uint8 u
  | S64, U16   -> int64_to_uint16 u
  | S64, U32   -> int64_to_uint32 u
  | S64, U64   -> int64_to_uint64 u
  | S64, U128  -> int64_to_uint128 u
  | S64, S8    -> int64_to_int8 u
  | S64, S16   -> int64_to_int16 u
  | S64, S32   -> int64_to_int32 u
  | S64, S64   -> u
  | S64, S128  -> int64_to_int128 u

  | S128, U1    -> UInt8.rem (uint64_to_uint8 (int128_to_uint64 u)) 2uy
  | S128, U8    -> uint64_to_uint8 (int128_to_uint64 u)
  | S128, U16   -> uint64_to_uint16 (int128_to_uint64 u)
  | S128, U32   -> uint64_to_uint32 (int128_to_uint64 u)
  | S128, U64   -> int128_to_uint64 u
  | S128, U128  -> int128_to_uint128 u
  | S128, S8    -> uint64_to_int8  (int128_to_uint64 u)
  | S128, S16   -> uint64_to_int16 (int128_to_uint64 u)
  | S128, S32   -> uint64_to_int32 (int128_to_uint64 u)
  | S128, S64   -> uint64_to_int64 (int128_to_uint64 u)
  | S128, S128  -> u

#pop-options

[@(strict_on_arguments [0])]
let ones t l =
  match t with
  | U1  -> 0x1uy
  | U8  -> 0xFFuy
  | U16 -> 0xFFFFus
  | U32 -> 0xFFFFFFFFul
  | U64 -> 0xFFFFFFFFFFFFFFFFuL
  | U128 ->
    let x = UInt128.uint64_to_uint128 0xFFFFFFFFFFFFFFFFuL in
    let y = (UInt128.shift_left x 64ul) `UInt128.add` x in
    assert_norm (UInt128.v y == pow2 128 - 1);
    y
  | _ -> mk_int (-1)

let zeros t l = mk_int 0

[@(strict_on_arguments [0])]
let add_mod #t #l a b =
  match t with
  | U1   -> UInt8.rem (UInt8.add_mod a b) 2uy
  | U8   -> UInt8.add_mod a b
  | U16  -> UInt16.add_mod a b
  | U32  -> UInt32.add_mod a b
  | U64  -> UInt64.add_mod a b
  | U128 -> UInt128.add_mod a b

let add_mod_lemma #t #l a b = ()

[@(strict_on_arguments [0])]
let add #t #l a b =
  match t with
  | U1   -> UInt8.add a b
  | U8   -> UInt8.add a b
  | U16  -> UInt16.add a b
  | U32  -> UInt32.add a b
  | U64  -> UInt64.add a b
  | U128 -> UInt128.add a b
  | S8   -> Int8.add a b
  | S16  -> Int16.add a b
  | S32  -> Int32.add a b
  | S64  -> Int64.add a b
  | S128 -> Int128.add a b

let add_lemma #t #l a b = ()

#push-options "--max_fuel 1"

[@(strict_on_arguments [0])]
let incr #t #l a =
  match t with
  | U1   -> UInt8.add a 1uy
  | U8   -> UInt8.add a 1uy
  | U16  -> UInt16.add a 1us
  | U32  -> UInt32.add a 1ul
  | U64  -> UInt64.add a 1uL
  | U128 -> UInt128.add a (UInt128.uint_to_t 1)
  | S8   -> Int8.add a 1y
  | S16  -> Int16.add a 1s
  | S32  -> Int32.add a 1l
  | S64  -> Int64.add a 1L
  | S128 -> Int128.add a (Int128.int_to_t 1)

let incr_lemma #t #l a = ()

#pop-options

[@(strict_on_arguments [0])]
let mul_mod #t #l a b =
  match t with
  | U1  -> UInt8.mul_mod a b
  | U8  -> UInt8.mul_mod a b
  | U16 -> UInt16.mul_mod a b
  | U32 -> UInt32.mul_mod a b
  | U64 -> UInt64.mul_mod a b

let mul_mod_lemma #t #l a b = ()

[@(strict_on_arguments [0])]
let mul #t #l a b =
  match t with
  | U1  -> UInt8.mul a b
  | U8  -> UInt8.mul a b
  | U16 -> UInt16.mul a b
  | U32 -> UInt32.mul a b
  | U64 -> UInt64.mul a b
  | S8  -> Int8.mul a b
  | S16 -> Int16.mul a b
  | S32 -> Int32.mul a b
  | S64 -> Int64.mul a b

let mul_lemma #t #l a b = ()

let mul64_wide a b = UInt128.mul_wide a b

let mul64_wide_lemma a b = ()

let mul_s64_wide a b = Int128.mul_wide a b

let mul_s64_wide_lemma a b = ()

[@(strict_on_arguments [0])]
let sub_mod #t #l a b =
  match t with
  | U1   -> UInt8.rem (UInt8.sub_mod a b) 2uy
  | U8   -> UInt8.sub_mod a b
  | U16  -> UInt16.sub_mod a b
  | U32  -> UInt32.sub_mod a b
  | U64  -> UInt64.sub_mod a b
  | U128 -> UInt128.sub_mod a b

let sub_mod_lemma #t #l a b = ()

[@(strict_on_arguments [0])]
let sub #t #l a b =
  match t with
  | U1   -> UInt8.sub a b
  | U8   -> UInt8.sub a b
  | U16  -> UInt16.sub a b
  | U32  -> UInt32.sub a b
  | U64  -> UInt64.sub a b
  | U128 -> UInt128.sub a b
  | S8   -> Int8.sub a b
  | S16  -> Int16.sub a b
  | S32  -> Int32.sub a b
  | S64  -> Int64.sub a b
  | S128 -> Int128.sub a b

let sub_lemma #t #l a b = ()

#push-options "--max_fuel 1"

[@(strict_on_arguments [0])]
let decr #t #l a =
  match t with
  | U1   -> UInt8.sub a 1uy
  | U8   -> UInt8.sub a 1uy
  | U16  -> UInt16.sub a 1us
  | U32  -> UInt32.sub a 1ul
  | U64  -> UInt64.sub a 1uL
  | U128 -> UInt128.sub a (UInt128.uint_to_t 1)
  | S8   -> Int8.sub a 1y
  | S16  -> Int16.sub a 1s
  | S32  -> Int32.sub a 1l
  | S64  -> Int64.sub a 1L
  | S128 -> Int128.sub a (Int128.int_to_t 1)

let decr_lemma #t #l a = ()

#pop-options

[@(strict_on_arguments [0])]
let logxor #t #l a b =
  match t with
  | U1   ->
    assert_norm (UInt8.logxor 0uy 0uy == 0uy);
    assert_norm (UInt8.logxor 0uy 1uy == 1uy);
    assert_norm (UInt8.logxor 1uy 0uy == 1uy);
    assert_norm (UInt8.logxor 1uy 1uy == 0uy);
    UInt8.logxor a b
  | U8   -> UInt8.logxor a b
  | U16  -> UInt16.logxor a b
  | U32  -> UInt32.logxor a b
  | U64  -> UInt64.logxor a b
  | U128 -> UInt128.logxor a b
  | S8   -> Int8.logxor a b
  | S16  -> Int16.logxor a b
  | S32  -> Int32.logxor a b
  | S64  -> Int64.logxor a b
  | S128 -> Int128.logxor a b

#push-options "--max_fuel 1"

val logxor_lemma_: #t:inttype -> #l:secrecy_level -> a:int_t t l -> b:int_t t l -> Lemma
  (v (a `logxor` (a `logxor` b)) == v b)
let logxor_lemma_ #t #l a b =
  match t with
  | U1 | U8 | U16 | U32 | U64 | U128 ->
    UInt.logxor_associative #(bits t) (v a) (v a) (v b);
    UInt.logxor_self #(bits t) (v a);
    UInt.logxor_commutative #(bits t) 0 (v b);
    UInt.logxor_lemma_1 #(bits t) (v b)
  | S8 | S16 | S32 | S64 | S128 ->
    Int.logxor_associative #(bits t) (v a) (v a) (v b);
    Int.logxor_self #(bits t) (v a);
    Int.logxor_commutative #(bits t) 0 (v b);
    Int.logxor_lemma_1 #(bits t) (v b)

let logxor_lemma #t #l a b =
  logxor_lemma_ #t a b;
  v_extensionality (logxor a (logxor a b)) b;
  begin
  match t with
  | U1 | U8 | U16 | U32 | U64 | U128 -> UInt.logxor_commutative #(bits t) (v a) (v b)
  | S8 | S16 | S32 | S64 | S128      -> Int.logxor_commutative #(bits t) (v a) (v b)
  end;
  v_extensionality (logxor a (logxor b a)) b;
  begin
  match t with
  | U1 | U8 | U16 | U32 | U64 | U128 -> UInt.logxor_lemma_1 #(bits t) (v a)
  | S8 | S16 | S32 | S64 | S128      -> Int.logxor_lemma_1 #(bits t) (v a)
  end;
  v_extensionality (logxor a (mk_int #t #l 0)) a

let logxor_lemma1 #t #l a b =
  match v a, v b with
  | _, 0 ->
    UInt.logxor_lemma_1 #(bits t) (v a)
  | 0, _ ->
    UInt.logxor_commutative #(bits t) (v a) (v b);
    UInt.logxor_lemma_1 #(bits t) (v b)
  | 1, 1 ->
    v_extensionality a b;
    UInt.logxor_self #(bits t) (v a)

#pop-options

[@(strict_on_arguments [0])]
let logand #t #l a b =
  match t with
  | U1   ->
    assert_norm (UInt8.logand 0uy 0uy == 0uy);
    assert_norm (UInt8.logand 0uy 1uy == 0uy);
    assert_norm (UInt8.logand 1uy 0uy == 0uy);
    assert_norm (UInt8.logand 1uy 1uy == 1uy);
    UInt8.logand a b
  | U8   -> UInt8.logand a b
  | U16  -> UInt16.logand a b
  | U32  -> UInt32.logand a b
  | U64  -> UInt64.logand a b
  | U128 -> UInt128.logand a b
  | S8   -> Int8.logand a b
  | S16  -> Int16.logand a b
  | S32  -> Int32.logand a b
  | S64  -> Int64.logand a b
  | S128 -> Int128.logand a b

let logand_zeros #t #l a =
  match t with
  | U1 -> assert_norm (u1 0 `logand` zeros U1 l == u1 0 /\ u1 1 `logand` zeros U1 l == u1 0)
  | U8 | U16 | U32 | U64 | U128 -> UInt.logand_lemma_1 #(bits t) (v a)
  | S8 | S16 | S32 | S64 | S128 -> Int.logand_lemma_1 #(bits t) (v a)

let logand_ones #t #l a =
  match t with
  | U1 -> assert_norm (u1 0 `logand` ones U1 l == u1 0 /\ u1 1 `logand` ones U1 l == u1 1)
  | U8 | U16 | U32 | U64 | U128 -> UInt.logand_lemma_2 #(bits t) (v a)
  | S8 | S16 | S32 | S64 | S128 -> Int.logand_lemma_2 #(bits t) (v a)

let logand_lemma #t #l a b =
  logand_zeros #t #l b;
  logand_ones #t #l b;
  match t with
  | U1 ->
    assert_norm (u1 0 `logand` zeros U1 l == u1 0 /\ u1 1 `logand` zeros U1 l == u1 0);
    assert_norm (u1 0 `logand` ones U1 l == u1 0 /\ u1 1 `logand` ones U1 l == u1 1)
  | U8 | U16 | U32 | U64 | U128 -> UInt.logand_commutative #(bits t) (v a) (v b)
  | S8 | S16 | S32 | S64 | S128 -> Int.logand_commutative #(bits t) (v a) (v b)

let logand_spec #t #l a b =
  match t with
  | U1 ->
    assert_norm (u1 0 `logand` u1 0 == u1 0 /\ u1 0 `logand` u1 1 == u1 0);
    assert_norm (u1 1 `logand` u1 0 == u1 0 /\ u1 1 `logand` u1 1 == u1 1);
    assert_norm (0 `logand_v #U1` 0 == 0 /\ 0 `logand_v #U1` 1 == 0);
    assert_norm (1 `logand_v #U1` 0 == 0 /\ 1 `logand_v #U1` 1 == 1)
  | _ -> ()

let logand_le #t #l a b =
  match t with
  | U1 ->
    assert_norm (UInt8.logand 0uy 0uy == 0uy);
    assert_norm (UInt8.logand 0uy 1uy == 0uy);
    assert_norm (UInt8.logand 1uy 0uy == 0uy);
    assert_norm (UInt8.logand 1uy 1uy == 1uy)
  | U8 -> UInt.logand_le (UInt.to_uint_t 8 (v a)) (UInt.to_uint_t 8 (v b))
  | U16 -> UInt.logand_le (UInt.to_uint_t 16 (v a)) (UInt.to_uint_t 16 (v b))
  | U32 -> UInt.logand_le (UInt.to_uint_t 32 (v a)) (UInt.to_uint_t 32 (v b))
  | U64 -> UInt.logand_le (UInt.to_uint_t 64 (v a)) (UInt.to_uint_t 64 (v b))
  | U128 -> UInt.logand_le (UInt.to_uint_t 128 (v a)) (UInt.to_uint_t 128 (v b))

let logand_mask #t #l a b m =
  match t with
  | U1 ->
    assert_norm (UInt8.logand 0uy 0uy == 0uy);
    assert_norm (UInt8.logand 0uy 1uy == 0uy);
    assert_norm (UInt8.logand 1uy 0uy == 0uy);
    assert_norm (UInt8.logand 1uy 1uy == 1uy)
  | U8 -> UInt.logand_mask (UInt.to_uint_t 8 (v a)) m
  | U16 -> UInt.logand_mask (UInt.to_uint_t 16 (v a)) m
  | U32 -> UInt.logand_mask (UInt.to_uint_t 32 (v a)) m
  | U64 -> UInt.logand_mask (UInt.to_uint_t 64 (v a)) m
  | U128 -> UInt.logand_mask (UInt.to_uint_t 128 (v a)) m


[@(strict_on_arguments [0])]
let logor #t #l a b =
  match t with
  | U1   ->
    assert_norm (UInt8.logor 0uy 0uy == 0uy);
    assert_norm (UInt8.logor 0uy 1uy == 1uy);
    assert_norm (UInt8.logor 1uy 0uy == 1uy);
    assert_norm (UInt8.logor 1uy 1uy == 1uy);
    UInt8.logor a b
  | U8   -> UInt8.logor a b
  | U16  -> UInt16.logor a b
  | U32  -> UInt32.logor a b
  | U64  -> UInt64.logor a b
  | U128 -> UInt128.logor a b
  | S8   -> Int8.logor a b
  | S16  -> Int16.logor a b
  | S32  -> Int32.logor a b
  | S64  -> Int64.logor a b
  | S128 -> Int128.logor a b

#push-options "--max_fuel 1"

let logor_disjoint #t #l a b m =
  if m > 0 then
  begin
    UInt.logor_disjoint #(bits t) (v b) (v a) m;
    UInt.logor_commutative #(bits t) (v b) (v a)
  end
  else
  begin
    UInt.logor_commutative #(bits t) (v a) (v b);
    UInt.logor_lemma_1 #(bits t) (v b)
  end

#pop-options

let logor_zeros #t #l a = 
  match t with 
  |U1 -> assert_norm(u1 0 `logor` zeros U1 l == u1 0 /\ u1 1 `logor` zeros U1 l == u1 1)
  | U8 | U16 | U32 | U64 | U128 -> UInt.logor_lemma_1 #(bits t) (v a)
  | S8 | S16 | S32 | S64 | S128 -> Int.nth_lemma #(bits t) (Int.logor #(bits t) (v a) (Int.zero (bits t))) (v a)


let logor_ones #t #l a = 
  match t with 
  |U1 -> assert_norm(u1 0 `logor` ones U1 l == u1 1 /\ u1 1 `logor` ones U1 l == u1 1)
  | U8 | U16 | U32 | U64 | U128 -> UInt.logor_lemma_2 #(bits t) (v a)
  | S8 | S16 | S32 | S64 | S128 -> Int.nth_lemma (Int.logor #(bits t) (v a) (Int.ones (bits t))) (Int.ones (bits t))

let logor_lemma #t #l a b = 
  logor_zeros #t #l b;
  logor_ones #t #l b;
  match t with 
  | U1 -> 
    assert_norm(u1 0 `logor` ones U1 l == u1 1 /\ u1 1 `logor` ones U1 l == u1 1);
    assert_norm(u1 0 `logor` zeros U1 l == u1 0 /\ u1 1 `logor` zeros U1 l == u1 1)
  | U8 | U16 | U32 | U64 | U128 -> UInt.logor_commutative #(bits t) (v a) (v b)
  | S8 | S16 | S32 | S64 | S128 -> Int.nth_lemma #(bits t) (Int.logor #(bits t) (v a) (v b)) (Int.logor #(bits t) (v b) (v a))

let logor_spec #t #l a b =
  match t with
  | U1 ->
    assert_norm(u1 0 `logor` ones U1 l == u1 1 /\ u1 1 `logor` ones U1 l == u1 1);
    assert_norm(u1 0 `logor` zeros U1 l == u1 0 /\ u1 1 `logor` zeros U1 l == u1 1);
    assert_norm (0 `logor_v #U1` 0 == 0 /\ 0 `logor_v #U1` 1 == 1);
    assert_norm (1 `logor_v #U1` 0 == 1 /\ 1 `logor_v #U1` 1 == 1)
  | _ -> ()
  

[@(strict_on_arguments [0])]
let lognot #t #l a =
  match t with
  | U1   -> UInt8.rem (UInt8.lognot a) 2uy
  | U8   -> UInt8.lognot a
  | U16  -> UInt16.lognot a
  | U32  -> UInt32.lognot a
  | U64  -> UInt64.lognot a
  | U128 -> UInt128.lognot a
  | S8   -> Int8.lognot a
  | S16  -> Int16.lognot a
  | S32  -> Int32.lognot a
  | S64  -> Int64.lognot a
  | S128 -> Int128.lognot a

let lognot_lemma #t #l a = 
  match t with 
  |U1 -> assert_norm(lognot (u1 0) == u1 1 /\ lognot (u1 1)  == u1 0)
  | U8 | U16 | U32 | U64 | U128 -> 
    FStar.UInt.lognot_lemma_1 #(bits t); 
    UInt.nth_lemma (FStar.UInt.lognot #(bits t) (UInt.ones (bits t))) (UInt.zero (bits t))
  | S8 | S16 | S32 | S64 | S128 -> 
    Int.nth_lemma (FStar.Int.lognot #(bits t) (Int.zero (bits t))) (Int.ones (bits t));
    Int.nth_lemma (FStar.Int.lognot #(bits t) (Int.ones (bits t))) (Int.zero (bits t))


[@(strict_on_arguments [0])]
let shift_right #t #l a b =
  match t with
  | U1   -> UInt8.shift_right a b
  | U8   -> UInt8.shift_right a b
  | U16  -> UInt16.shift_right a b
  | U32  -> UInt32.shift_right a b
  | U64  -> UInt64.shift_right a b
  | U128 -> UInt128.shift_right a b
  | S8   -> Int8.shift_arithmetic_right a b
  | S16  -> Int16.shift_arithmetic_right a b
  | S32  -> Int32.shift_arithmetic_right a b
  | S64  -> Int64.shift_arithmetic_right a b
  | S128 -> Int128.shift_arithmetic_right a b

val shift_right_value_aux_1: #n:pos{1 < n} -> a:Int.int_t n -> s:nat{n <= s} ->
  Lemma (Int.shift_arithmetic_right #n a s = a / pow2 s)
let shift_right_value_aux_1 #n a s =
  pow2_le_compat s n;
  if a >= 0 then Int.sign_bit_positive a else Int.sign_bit_negative a

#push-options "--z3rlimit 200"

val shift_right_value_aux_2: #n:pos{1 < n} -> a:Int.int_t n ->
  Lemma (Int.shift_arithmetic_right #n a 1 = a / 2)
let shift_right_value_aux_2 #n a =
  if a >= 0 then
    begin
    Int.sign_bit_positive a;
    UInt.shift_right_value_aux_3 #n a 1
    end
  else
    begin
    Int.sign_bit_negative a;
    let a1 = Int.to_vec a in
    let au = Int.to_uint a in
    let sar = Int.shift_arithmetic_right #n a 1 in
    let sar1 = Int.to_vec sar in
    let sr = UInt.shift_right #n au 1 in
    let sr1 = UInt.to_vec sr in
    assert (Seq.equal (Seq.slice sar1 1 n) (Seq.slice sr1 1 n));
    assert (Seq.equal sar1 (Seq.append (BitVector.ones_vec #1) (Seq.slice sr1 1 n)));
    UInt.append_lemma #1 #(n-1) (BitVector.ones_vec #1) (Seq.slice sr1 1 n);
    assert (Seq.equal (Seq.slice a1 0 (n-1)) (Seq.slice sar1 1 n));
    UInt.slice_left_lemma a1 (n-1);
    assert (sar + pow2 n = pow2 (n-1) + (au / 2));
    pow2_double_sum (n-1);
    assert (sar + pow2 (n-1) = (a + pow2 n) / 2);
    pow2_double_mult (n-1);
    lemma_div_plus a (pow2 (n-1)) 2;
    assert (sar = a / 2)
  end

val shift_right_value_aux_3: #n:pos -> a:Int.int_t n -> s:pos{s < n} ->
  Lemma (ensures Int.shift_arithmetic_right #n a s = a / pow2 s)
        (decreases s)
let rec shift_right_value_aux_3 #n a s =
  if s = 1 then
    shift_right_value_aux_2 #n a
  else
    begin
    let a1 = Int.to_vec a in
    assert (Seq.equal (BitVector.shift_arithmetic_right_vec #n a1 s)
                      (BitVector.shift_arithmetic_right_vec #n
                         (BitVector.shift_arithmetic_right_vec #n a1 (s-1)) 1));
    assert (Int.shift_arithmetic_right #n a s =
            Int.shift_arithmetic_right #n (Int.shift_arithmetic_right #n a (s-1)) 1);
    shift_right_value_aux_3 #n a (s-1);
    shift_right_value_aux_2 #n (Int.shift_arithmetic_right #n a (s-1));
    assert (Int.shift_arithmetic_right #n a s = (a / pow2 (s-1)) / 2);
    pow2_double_mult (s-1);
    division_multiplication_lemma a (pow2 (s-1)) 2
    end

let shift_right_lemma #t #l a b =
  match t with
  | U1 | U8 | U16 | U32 | U64 | U128 -> ()
  | S8 | S16 | S32 | S64 | S128 ->
    if v b = 0 then ()
    else if v b >= bits t then
      shift_right_value_aux_1 #(bits t) (v a) (v b)
    else
      shift_right_value_aux_3 #(bits t) (v a) (v b)

[@(strict_on_arguments [0])]
let shift_left #t #l a b =
  match t with
  | U1   -> UInt8.shift_left a b
  | U8   -> UInt8.shift_left a b
  | U16  -> UInt16.shift_left a b
  | U32  -> UInt32.shift_left a b
  | U64  -> UInt64.shift_left a b
  | U128 -> UInt128.shift_left a b
  | S8   -> Int8.shift_left a b
  | S16  -> Int16.shift_left a b
  | S32  -> Int32.shift_left a b
  | S64  -> Int64.shift_left a b
  | S128 -> Int128.shift_left a b

#push-options "--max_fuel 1"

let shift_left_lemma #t #l a b = ()

let rotate_right #t #l a b =
  logor (shift_right a b) (shift_left a (sub #U32 (size (bits t)) b))

let rotate_left #t #l a b =
  logor (shift_left a b) (shift_right a (sub #U32 (size (bits t)) b))

[@(strict_on_arguments [0])]
let ct_abs #t #l a =
  match t with
  | S8  -> Int8.ct_abs a
  | S16 -> Int16.ct_abs a
  | S32 -> Int32.ct_abs a
  | S64 -> Int64.ct_abs a

#pop-options

[@(strict_on_arguments [0])]
let eq_mask #t a b =
  match t with
  | U1   -> lognot (logxor a b)
  | U8   -> UInt8.eq_mask a b
  | U16  -> UInt16.eq_mask a b
  | U32  -> UInt32.eq_mask a b
  | U64  -> UInt64.eq_mask a b
  | U128 -> UInt128.eq_mask a b
  | S8   -> Int.Cast.uint8_to_int8 (UInt8.eq_mask (to_u8 a) (to_u8 b))
  | S16  -> Int.Cast.uint16_to_int16 (UInt16.eq_mask (to_u16 a) (to_u16 b))
  | S32  -> Int.Cast.uint32_to_int32 (UInt32.eq_mask (to_u32 a) (to_u32 b))
  | S64  -> Int.Cast.uint64_to_int64 (UInt64.eq_mask (to_u64 a) (to_u64 b))

val eq_mask_lemma_unsigned: #t:inttype{unsigned t} -> a:int_t t SEC -> b:int_t t SEC -> Lemma
  (if v a = v b then v (eq_mask a b) == ones_v t
                else v (eq_mask a b) == 0)
let eq_mask_lemma_unsigned #t a b =
  match t with
  | U1 ->
    assert_norm (
      logxor (u1 0) (u1 0) == u1 0 /\ logxor (u1 0) (u1 1) == u1 1 /\
      logxor (u1 1) (u1 0) == u1 1 /\ logxor (u1 1) (u1 1) == u1 0 /\
      lognot (u1 1) == u1 0 /\ lognot (u1 0) == u1 1)
  | U8 | U16 | U32 | U64 | U128 -> ()

#push-options "--z3rlimit 100"

val eq_mask_lemma_signed: #t:inttype{signed t /\ ~(S128? t)} -> a:int_t t SEC -> b:int_t t SEC -> Lemma
  (if v a = v b then v (eq_mask a b) == ones_v t
                else v (eq_mask a b) == 0)
let eq_mask_lemma_signed #t a b =
  match t with
  | S8 ->
    begin
    assert_norm (pow2 8 = 2 * pow2 7);
    if 0 <= v a then modulo_lemma (v a) (pow2 8)
    else
      begin
      modulo_addition_lemma (v a) 1 (pow2 8);
      modulo_lemma (v a + pow2 8) (pow2 8)
      end
    end
  | S16 ->
    begin
    assert_norm (pow2 16 = 2 * pow2 15);
    if 0 <= v a then modulo_lemma (v a) (pow2 16)
    else
      begin
      modulo_addition_lemma (v a) 1 (pow2 16);
      modulo_lemma (v a + pow2 16) (pow2 16)
      end
    end
  | S32 ->
    begin
    if 0 <= v a then modulo_lemma (v a) (pow2 32)
    else
      begin
      modulo_addition_lemma (v a) 1 (pow2 32);
      modulo_lemma (v a + pow2 32) (pow2 32)
      end
    end
  | S64 ->
    begin
    if 0 <= v a then modulo_lemma (v a) (pow2 64)
    else
      begin
      modulo_addition_lemma (v a) 1 (pow2 64);
      modulo_lemma (v a + pow2 64) (pow2 64)
      end
    end

#pop-options

let eq_mask_lemma #t a b =
  if signed t then eq_mask_lemma_signed a b
  else eq_mask_lemma_unsigned a b

let eq_mask_logand_lemma #t a b c =
  eq_mask_lemma a b;
  logand_zeros c;
  logand_ones c;
  match t with
  | U1 | U8 | U16 | U32 | U64 | U128 -> UInt.logand_commutative #(bits t) (v (eq_mask a b)) (v c)
  | S8 | S16 | S32 | S64 -> Int.logand_commutative #(bits t) (v (eq_mask a b)) (v c)

[@(strict_on_arguments [0])]
let neq_mask #t a b = lognot (eq_mask #t a b)

let neq_mask_lemma #t a b =
  match t with
  | U1 -> assert_norm (lognot (u1 1) == u1 0 /\ lognot (u1 0) == u1 1)
  | _ ->
    UInt.lognot_lemma_1 #(bits t);
    UInt.lognot_self #(bits t) 0

[@(strict_on_arguments [0])]
let gte_mask #t a b =
  match t with
  | U1   -> logor a (lognot b)
  | U8   -> UInt8.gte_mask a b
  | U16  -> UInt16.gte_mask a b
  | U32  -> UInt32.gte_mask a b
  | U64  -> UInt64.gte_mask a b
  | U128 -> UInt128.gte_mask a b

let gte_mask_lemma #t a b =
  match t with
  | U1 ->
    begin
    assert_norm (
      logor (u1 0) (u1 0) == u1 0 /\ logor (u1 1) (u1 1) == u1 1 /\
      logor (u1 0) (u1 1) == u1 1 /\ logor (u1 1) (u1 0) == u1 1 /\
      lognot (u1 1) == u1 0 /\ lognot (u1 0) == u1 1)
    end
  | _ -> ()

let gte_mask_logand_lemma #t a b c =
  logand_zeros c;
  logand_ones c;
  match t with
  | U1 ->
    assert_norm (
      logor (u1 0) (u1 0) == u1 0 /\ logor (u1 1) (u1 1) == u1 1 /\
      logor (u1 0) (u1 1) == u1 1 /\ logor (u1 1) (u1 0) == u1 1 /\
      lognot (u1 1) == u1 0 /\ lognot (u1 0) == u1 1)
  | _ -> UInt.logand_commutative #(bits t) (v (gte_mask a b)) (v c)

let lt_mask #t a b = lognot (gte_mask a b)

let lt_mask_lemma #t a b =
  assert_norm (lognot (u1 1) == u1 0 /\ lognot (u1 0) == u1 1);
  UInt.lognot_lemma_1 #(bits t);
  UInt.lognot_self #(bits t) 0

let gt_mask #t a b = logand (gte_mask a b) (neq_mask a b)

let gt_mask_lemma #t a b =
  logand_zeros (gte_mask a b);
  logand_ones (gte_mask a b)

let lte_mask #t a b = logor (lt_mask a b) (eq_mask a b)

let lte_mask_lemma #t a b =
  match t with
  | U1 ->
    assert_norm (
      logor (u1 0) (u1 0) == u1 0 /\ logor (u1 1) (u1 1) == u1 1 /\
      logor (u1 0) (u1 1) == u1 1 /\ logor (u1 1) (u1 0) == u1 1)
  | U8 | U16 | U32 | U64 | U128 ->
    if v a > v b then
      UInt.logor_lemma_1 #(bits t) (v (lt_mask a b))
    else if v a = v b then
      UInt.logor_lemma_2 #(bits t) (v (lt_mask a b))
    else
      UInt.logor_lemma_1 #(bits t) (v (lt_mask a b))

#push-options "--max_fuel 1"

val mod_mask_value: #t:inttype -> #l:secrecy_level -> m:shiftval t{pow2 (uint_v m) <= maxint t} ->
  Lemma (v (mod_mask #t #l m) == pow2 (v m) - 1)
let mod_mask_value #t #l m =
  shift_left_lemma (mk_int #t #l 1) m;
  pow2_double_mult (bits t - 1);
  pow2_lt_compat (bits t) (v m);
  small_modulo_lemma_1 (pow2 (v m)) (pow2 (bits t));
  small_modulo_lemma_1 (pow2 (v m) - 1) (pow2 (bits t))

let mod_mask_lemma #t #l a m =
  mod_mask_value #t #l m;
  if unsigned t || 0 <= v a then
    if v m = 0 then
      UInt.logand_lemma_1 #(bits t) (v a)
    else
      UInt.logand_mask #(bits t) (v a) (v m)
  else
    begin
    let a1 = v a in
    let a2 = v a + pow2 (bits t) in
    pow2_plus (bits t - v m) (v m);
    pow2_le_compat (bits t - 1) (v m);
    lemma_mod_plus a1 (pow2 (bits t - v m)) (pow2 (v m));
    if v m = 0 then
      UInt.logand_lemma_1 #(bits t) a2
    else
      UInt.logand_mask #(bits t) a2 (v m)
    end

#pop-options

#push-options "--max_fuel 0 --max_ifuel 0 --z3rlimit 1000"

(**
  Conditionally subtracts 2^(bits t') from a in constant-time,
  so that the result fits in t'; i.e.
  b = if a >= 2^(bits t' - 1) then a - 2^(bits t') else a
*)
inline_for_extraction noextract
val conditional_subtract:
    #t:inttype{signed t}
  -> #l:secrecy_level
  -> t':inttype{signed t' /\ bits t' < bits t}
  -> a:int_t t l{0 <= v a /\ v a <= pow2 (bits t') - 1}
  -> b:int_t t l{v b = v a @%. t'}
let conditional_subtract #t #l t' a =
  assert_norm (pow2 7 = 128);
  assert_norm (pow2 15 = 32768);
  let pow2_bits = shift_left #t #l (mk_int 1) (size (bits t')) in
  shift_left_lemma #t #l (mk_int 1) (size (bits t'));
  let pow2_bits_minus_one = shift_left #t #l (mk_int 1) (size (bits t' - 1)) in
  shift_left_lemma #t #l (mk_int 1) (size (bits t' - 1));
  // assert (v pow2_bits == pow2 (bits t'));
  // assert (v pow2_bits_minus_one == pow2 (bits t' - 1));
  let a2 = a `sub` pow2_bits_minus_one in
  let mask = shift_right a2 (size (bits t - 1)) in
  shift_right_lemma a2 (size (bits t - 1));
  // assert (if v a2 < 0 then v mask = -1 else v mask = 0);
  let a3 = a `sub` pow2_bits in
  logand_lemma mask pow2_bits;
  a3 `add` (mask `logand` pow2_bits)

let cast_mod #t #l t' l' a =
  assert_norm (pow2 7 = 128);
  assert_norm (pow2 15 = 32768);
  if bits t' >= bits t then
    cast t' l' a
  else
    begin
    let m = size (bits t') in
    mod_mask_lemma a m;
    let b = conditional_subtract t' (a `logand` mod_mask m) in
    cast t' l' b
    end

#pop-options

[@(strict_on_arguments [0])]
let div #t x y =
  match t with
  | U1  -> UInt8.div x y
  | U8  -> UInt8.div x y
  | U16 -> UInt16.div x y
  | U32 -> UInt32.div x y
  | U64 -> UInt64.div x y
  | S8  -> Int.pow2_values 8; Int8.div x y
  | S16 -> Int.pow2_values 16; Int16.div x y
  | S32 -> Int.pow2_values 32; Int32.div x y
  | S64 -> Int.pow2_values 64; Int64.div x y

let div_lemma #t a b =
  match t with
  | U1 | U8 | U16 | U32 | U64 -> ()
  | S8  -> Int.pow2_values 8
  | S16 -> Int.pow2_values 16
  | S32 -> Int.pow2_values 32
  | S64 -> Int.pow2_values 64

let mod #t x y =
  match t with
  | U1  -> UInt8.rem x y
  | U8  -> UInt8.rem x y
  | U16 -> UInt16.rem x y
  | U32 -> UInt32.rem x y
  | U64 -> UInt64.rem x y
  | S8  -> Int.pow2_values 8; Int8.rem x y
  | S16 -> Int.pow2_values 16; Int16.rem x y
  | S32 -> Int.pow2_values 32; Int32.rem x y
  | S64 -> Int.pow2_values 64; Int64.rem x y

let mod_lemma #t a b =
  match t with
  | U1 | U8 | U16 | U32 | U64 -> ()
  | S8  -> Int.pow2_values 8
  | S16 -> Int.pow2_values 16
  | S32 -> Int.pow2_values 32
  | S64 -> Int.pow2_values 64

let eq #t x y =
  match t with
  | U1   -> UInt8.eq x y
  | U8   -> UInt8.eq x y
  | U16  -> UInt16.eq x y
  | U32  -> UInt32.eq x y
  | U64  -> UInt64.eq x y
  | U128 -> UInt128.eq x y
  | S8   -> Int8.eq x y
  | S16  -> Int16.eq x y
  | S32  -> Int32.eq x y
  | S64  -> Int64.eq x y
  | S128 -> Int128.eq x y

let eq_lemma #t x y = ()

let ne #t x y = not (eq x y)

let ne_lemma #t x y = ()

let lt #t x y =
  match t with
  | U1   -> UInt8.lt x y
  | U8   -> UInt8.lt x y
  | U16  -> UInt16.lt x y
  | U32  -> UInt32.lt x y
  | U64  -> UInt64.lt x y
  | U128 -> UInt128.lt x y
  | S8   -> Int8.lt x y
  | S16  -> Int16.lt x y
  | S32  -> Int32.lt x y
  | S64  -> Int64.lt x y
  | S128 -> Int128.lt x y

let lt_lemma #t x y = ()

let lte #t x y =
  match t with
  | U1   -> UInt8.lte x y
  | U8   -> UInt8.lte x y
  | U16  -> UInt16.lte x y
  | U32  -> UInt32.lte x y
  | U64  -> UInt64.lte x y
  | U128 -> UInt128.lte x y
  | S8   -> Int8.lte x y
  | S16  -> Int16.lte x y
  | S32  -> Int32.lte x y
  | S64  -> Int64.lte x y
  | S128 -> Int128.lte x y

let lte_lemma #t x y = ()

let gt #t x y =
  match t with
  | U1   -> UInt8.gt x y
  | U8   -> UInt8.gt x y
  | U16  -> UInt16.gt x y
  | U32  -> UInt32.gt x y
  | U64  -> UInt64.gt x y
  | U128 -> UInt128.gt x y
  | S8   -> Int8.gt x y
  | S16  -> Int16.gt x y
  | S32  -> Int32.gt x y
  | S64  -> Int64.gt x y
  | S128 -> Int128.gt x y

let gt_lemma #t x y = ()

let gte #t x y =
  match t with
  | U1   -> UInt8.gte x y
  | U8   -> UInt8.gte x y
  | U16  -> UInt16.gte x y
  | U32  -> UInt32.gte x y
  | U64  -> UInt64.gte x y
  | U128 -> UInt128.gte x y
  | S8   -> Int8.gte x y
  | S16  -> Int16.gte x y
  | S32  -> Int32.gte x y
  | S64  -> Int64.gte x y
  | S128 -> Int128.gte x y

let gte_lemma #t x y = ()
