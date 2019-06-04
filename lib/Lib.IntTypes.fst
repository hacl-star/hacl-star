module Lib.IntTypes

(* Declared in .fsti : intsize, bits, maxint *)
#set-options "--z3rlimit 50 --max_fuel 0 --max_ifuel 1"

let pow2_values n =
    assert_norm (pow2 0 = 1);
    assert_norm (pow2 1 = 2);
    assert_norm (pow2 2 = 4);
    assert_norm (pow2 3 = 8);
    assert_norm (pow2 4 = 16);
    assert_norm (pow2 8 = 0x100);
    assert_norm (pow2 16 = 0x10000);
    assert_norm (pow2 32 = 0x100000000);
    assert_norm (pow2 64 = 0x10000000000000000);
    assert_norm (pow2 128 = 0x100000000000000000000000000000000)

let sec_int_t t = pub_int_t t

let sec_int_v #t u = pub_int_v u

let uintv_extensionality #t #l a b =
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
  //| S128 -> Int128.v_inj a b

(* Declared in .fsti: uint8, uint16, uint32, uint64, uint128 *)

let secret #t x = x

let uint #t #l x =
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
  //| S128 -> Int128.int_to_t x
  
let uintv_injective #t #l a =
  uintv_extensionality a (uint (uint_v a))

let u16_us x = x
let u32_ul x = x
let u64_uL x = x

let u128 x = FStar.UInt128.uint64_to_uint128 (u64 x)

let size_v_size_lemma s = ()

let uint_v_size_lemma s = ()

let size_to_uint32 x = x

let size_to_uint64 x = FStar.Int.Cast.uint32_to_uint64 x

let byte_to_uint8 x = x

let byte_to_int8 x = FStar.Int.Cast.uint8_to_int8 x

let nat_to_uint #t #l x =
  match t with
  | U1 -> u8 x
  | U8 -> u8 x
  | U16 -> u16 x
  | U32 -> u32 x
  | U64 -> u64 x
  | U128 -> UInt128.uint_to_t x
  | S8 -> i8 x
  | S16 -> i16 x
  | S32 -> i32 x
  | S64 -> i64 x
  
#reset-options "--z3rlimit 500"

let cast #t #l t' l' u  =
  match t, t' with
  | U1, U1 -> u
  | U1, U8 -> u
  | U1, U16 -> FStar.Int.Cast.uint8_to_uint16 u
  | U1, U32 -> FStar.Int.Cast.uint8_to_uint32 u
  | U1, U64 -> FStar.Int.Cast.uint8_to_uint64 u
  | U1, U128 -> FStar.UInt128.uint64_to_uint128 (FStar.Int.Cast.uint8_to_uint64 u)
  | U1, S8 -> FStar.Int.Cast.uint8_to_int8 u
  | U1, S16 -> FStar.Int.Cast.uint8_to_int16 u
  | U1, S32 -> FStar.Int.Cast.uint8_to_int32 u
  | U1, S64 -> FStar.Int.Cast.uint8_to_int64 u
  | U8, U1 -> FStar.UInt8.rem u 2uy
  | U8, U8 -> u
  | U8, U16 -> FStar.Int.Cast.uint8_to_uint16 u
  | U8, U32 -> FStar.Int.Cast.uint8_to_uint32 u
  | U8, U64 -> FStar.Int.Cast.uint8_to_uint64 u
  | U8, U128 -> FStar.UInt128.uint64_to_uint128 (FStar.Int.Cast.uint8_to_uint64 u)
  | U8, S8 -> FStar.Int.Cast.uint8_to_int8 u
  | U8, S16 -> FStar.Int.Cast.uint8_to_int16 u
  | U8, S32 -> FStar.Int.Cast.uint8_to_int32 u
  | U8, S64 -> FStar.Int.Cast.uint8_to_int64 u
  | U16, U1 -> FStar.Int.Cast.uint16_to_uint8 (FStar.UInt16.rem u 2us)
  | U16, U8 -> FStar.Int.Cast.uint16_to_uint8 u
  | U16, U16 -> u
  | U16, U32 -> FStar.Int.Cast.uint16_to_uint32 u
  | U16, U64 -> FStar.Int.Cast.uint16_to_uint64 u
  | U16, U128 -> FStar.UInt128.uint64_to_uint128 (FStar.Int.Cast.uint16_to_uint64 u)
  | U16, S8 -> FStar.Int.Cast.uint16_to_int8 u
  | U16, S16 -> FStar.Int.Cast.uint16_to_int16 u
  | U16, S32 -> FStar.Int.Cast.uint16_to_int32 u
  | U16, S64 -> FStar.Int.Cast.uint16_to_int64 u
  | U32, U1 -> FStar.Int.Cast.uint32_to_uint8 (FStar.UInt32.rem u 2ul)
  | U32, U8 -> FStar.Int.Cast.uint32_to_uint8 u
  | U32, U16 -> FStar.Int.Cast.uint32_to_uint16 u
  | U32, U32 -> u
  | U32, U64 -> FStar.Int.Cast.uint32_to_uint64 u
  | U32, U128 -> FStar.UInt128.uint64_to_uint128 (FStar.Int.Cast.uint32_to_uint64 u)
  | U32, S8 -> FStar.Int.Cast.uint32_to_int8 u
  | U32, S16 -> FStar.Int.Cast.uint32_to_int16 u
  | U32, S32 -> FStar.Int.Cast.uint32_to_int32 u
  | U32, S64 -> FStar.Int.Cast.uint32_to_int64 u
  | U64, U1 -> FStar.Int.Cast.uint64_to_uint8 (FStar.UInt64.rem u 2uL)
  | U64, U8 -> FStar.Int.Cast.uint64_to_uint8 u
  | U64, U16 -> FStar.Int.Cast.uint64_to_uint16 u
  | U64, U32 -> FStar.Int.Cast.uint64_to_uint32 u
  | U64, U64 -> u
  | U64, U128 -> FStar.UInt128.uint64_to_uint128 u
  | U64, S8 -> FStar.Int.Cast.uint64_to_int8 u
  | U64, S16 -> FStar.Int.Cast.uint64_to_int16 u
  | U64, S32 -> FStar.Int.Cast.uint64_to_int32 u
  | U64, S64 -> FStar.Int.Cast.uint64_to_int64 u
  | U128, U1 ->
    assert_norm (pow2 64 * pow2 64 = pow2 128);
    assert_norm (pow2 8 * pow2 56 = pow2 64);
    FStar.Math.Lemmas.modulo_modulo_lemma (uint_v u) (pow2 64) (pow2 64);
    FStar.Math.Lemmas.modulo_modulo_lemma (uint_v u) (pow2 8) (pow2 56);
    FStar.UInt8.rem (FStar.Int.Cast.uint64_to_uint8
      (FStar.Int.Cast.Full.uint128_to_uint64 u)) 0x2uy
  | U128, U8 ->
    assert_norm (pow2 64 * pow2 64 = pow2 128);
    assert_norm (pow2 8 * pow2 56 = pow2 64);
    FStar.Math.Lemmas.modulo_modulo_lemma (uint_v u) (pow2 64) (pow2 64);
    FStar.Math.Lemmas.modulo_modulo_lemma (uint_v u) (pow2 8) (pow2 56);
    FStar.Int.Cast.uint64_to_uint8 (FStar.UInt128.uint128_to_uint64 u)
  | U128, U16 ->
    assert_norm (pow2 64 * pow2 64 = pow2 128);
    assert_norm (pow2 16 * pow2 48 = pow2 64);
    FStar.Math.Lemmas.modulo_modulo_lemma (uint_v u) (pow2 64) (pow2 64);
    FStar.Math.Lemmas.modulo_modulo_lemma (uint_v u) (pow2 16) (pow2 48);
    FStar.Int.Cast.uint64_to_uint16 (FStar.UInt128.uint128_to_uint64 u)
  | U128, U32 ->
    assert_norm (pow2 64 * pow2 64 = pow2 128);
    assert_norm (pow2 32 * pow2 32 = pow2 64);
    FStar.Math.Lemmas.modulo_modulo_lemma (uint_v u) (pow2 64) (pow2 64);
    FStar.Math.Lemmas.modulo_modulo_lemma (uint_v u) (pow2 32) (pow2 32);
    FStar.Int.Cast.uint64_to_uint32 (FStar.UInt128.uint128_to_uint64 u)
  | U128, U64 ->
    assert_norm (pow2 64 * pow2 64 = pow2 128);
    FStar.Math.Lemmas.modulo_modulo_lemma (uint_v u) (pow2 64) (pow2 64);
    FStar.UInt128.uint128_to_uint64 u
  | U128, U128 -> u
  | U128, S8 ->
    assert_norm (pow2 64 * pow2 64 = pow2 128);
    assert_norm (pow2 8 * pow2 56 = pow2 64);
    FStar.Math.Lemmas.modulo_modulo_lemma (uint_v u) (pow2 64) (pow2 64);
    FStar.Math.Lemmas.modulo_modulo_lemma (uint_v u) (pow2 8) (pow2 56);
    FStar.Int.Cast.uint64_to_int8 (FStar.UInt128.uint128_to_uint64 u)
  | U128, S16 ->
    assert_norm (pow2 64 * pow2 64 = pow2 128);
    assert_norm (pow2 16 * pow2 48 = pow2 64);
    FStar.Math.Lemmas.modulo_modulo_lemma (uint_v u) (pow2 64) (pow2 64);
    FStar.Math.Lemmas.modulo_modulo_lemma (uint_v u) (pow2 16) (pow2 48);
    FStar.Int.Cast.uint64_to_int16 (FStar.UInt128.uint128_to_uint64 u)
  | U128, S32 ->
    assert_norm (pow2 64 * pow2 64 = pow2 128);
    assert_norm (pow2 32 * pow2 32 = pow2 64);
    FStar.Math.Lemmas.modulo_modulo_lemma (uint_v u) (pow2 64) (pow2 64);
    FStar.Math.Lemmas.modulo_modulo_lemma (uint_v u) (pow2 32) (pow2 32);
    FStar.Int.Cast.uint64_to_int32 (FStar.UInt128.uint128_to_uint64 u)
  | U128, S64 ->
    assert_norm (pow2 64 * pow2 64 = pow2 128);
    FStar.Math.Lemmas.modulo_modulo_lemma (uint_v u) (pow2 64) (pow2 64);
    FStar.Int.Cast.uint64_to_int64 (FStar.UInt128.uint128_to_uint64 u)  
  | S8, U1 -> FStar.UInt8.rem (FStar.Int.Cast.int8_to_uint8 u) 2uy
  | S8, U8 -> FStar.Int.Cast.int8_to_uint8 u
  | S8, U16 -> FStar.Int.Cast.int8_to_uint16 u
  | S8, U32 -> FStar.Int.Cast.int8_to_uint32 u
  | S8, U64 -> FStar.Int.Cast.int8_to_uint64 u
  | S8, S8 -> u
  | S8, S16 -> FStar.Int.Cast.int8_to_int16 u
  | S8, S32 -> FStar.Int.Cast.int8_to_int32 u
  | S8, S64 -> FStar.Int.Cast.int8_to_int64 u
  | S16, U1 -> FStar.UInt8.rem (FStar.Int.Cast.int16_to_uint8 u) 2uy
  | S16, U8 -> FStar.Int.Cast.int16_to_uint8 u
  | S16, U16 -> FStar.Int.Cast.int16_to_uint16 u
  | S16, U32 -> FStar.Int.Cast.int16_to_uint32 u
  | S16, U64 -> FStar.Int.Cast.int16_to_uint64 u
  | S16, S8 -> FStar.Int.Cast.int16_to_int8 u
  | S16, S16 -> u
  | S16, S32 -> FStar.Int.Cast.int16_to_int32 u
  | S16, S64 -> FStar.Int.Cast.int16_to_int64 u
  | S32, U1 -> FStar.UInt8.rem (FStar.Int.Cast.int32_to_uint8 u) 2uy
  | S32, U8 -> FStar.Int.Cast.int32_to_uint8 u
  | S32, U16 -> FStar.Int.Cast.int32_to_uint16 u
  | S32, U32 -> FStar.Int.Cast.int32_to_uint32 u
  | S32, U64 -> FStar.Int.Cast.int32_to_uint64 u
  | S32, S8 -> FStar.Int.Cast.int32_to_int8 u
  | S32, S16 -> FStar.Int.Cast.int32_to_int16 u
  | S32, S32 -> u
  | S32, S64 -> FStar.Int.Cast.int32_to_int64 u
  | S64, U1 -> FStar.UInt8.rem (FStar.Int.Cast.int64_to_uint8 u) 2uy
  | S64, U8 -> FStar.Int.Cast.int64_to_uint8 u
  | S64, U16 -> FStar.Int.Cast.int64_to_uint16 u
  | S64, U32 -> FStar.Int.Cast.int64_to_uint32 u
  | S64, U64 -> FStar.Int.Cast.int64_to_uint64 u
  | S64, S8 -> FStar.Int.Cast.int64_to_int8 u
  | S64, S16 -> FStar.Int.Cast.int64_to_int16 u
  | S64, S32 -> FStar.Int.Cast.int64_to_int32 u
  | S64, S64 -> u
  

let add_mod #t #l a b =
  match t with
  | U1   -> UInt8.rem (UInt8.add_mod a b) 2uy
  | U8   -> UInt8.add_mod a b
  | U16  -> UInt16.add_mod a b
  | U32  -> UInt32.add_mod a b
  | U64  -> UInt64.add_mod a b
  | U128 -> UInt128.add_mod a b
  | S8 -> Int8.int_to_t (Int.add_mod (Int8.v a) (Int8.v b))
  | S16 -> Int16.int_to_t (Int.add_mod (Int16.v a) (Int16.v b))
  | S32 -> Int32.int_to_t (Int.add_mod (Int32.v a) (Int32.v b))
  | S64 -> Int64.int_to_t (Int.add_mod (Int64.v a) (Int64.v b))
  

let add_mod_lemma #t #l a b = ()

let add #t #l a b =
  match t with
  | U1   -> UInt8.add a b
  | U8   -> UInt8.add a b
  | U16  -> UInt16.add a b
  | U32  -> UInt32.add a b
  | U64  -> UInt64.add a b
  | U128 -> UInt128.add a b
  | S8 -> Int8.add a b
  | S16 -> Int16.add a b
  | S32 -> Int32.add a b
  | S64 -> Int64.add a b
  
let add_lemma #t #l a b = ()

let incr #t #l a =
  match t with
  | U1   -> UInt8.add a 0x1uy
  | U8   -> UInt8.add a 0x1uy
  | U16  -> UInt16.add a 0x1us
  | U32  -> UInt32.add a 0x1ul
  | U64  -> UInt64.add a 0x1uL
  | U128 -> UInt128.add a (UInt128.uint_to_t 1)
  | S8 -> Int8.add a 0x1y
  | S16 -> Int16.add a 0x1s
  | S32 -> Int32.add a 0x1l
  | S64 -> Int64.add a 0x1L
  
let incr_lemma #t #l a = ()

let mul_mod #t #l a b =
  match t with
  | U1  -> UInt8.mul_mod a b
  | U8  -> UInt8.mul_mod a b
  | U16 -> UInt16.mul_mod a b
  | U32 -> UInt32.mul_mod a b
  | U64 -> UInt64.mul_mod a b
  | S8 -> Int8.int_to_t (Int.mul_mod (Int8.v a) (Int8.v b))
  | S16 -> Int16.int_to_t (Int.mul_mod (Int16.v a) (Int16.v b))
  | S32 -> Int32.int_to_t (Int.mul_mod (Int32.v a) (Int32.v b))
  | S64 -> Int64.int_to_t (Int.mul_mod (Int64.v a) (Int64.v b))
  
let mul_mod_lemma #t #l a b = ()

let mul #t #l a b =
  match t with
  | U1  -> UInt8.mul a b
  | U8  -> UInt8.mul a b
  | U16 -> UInt16.mul a b
  | U32 -> UInt32.mul a b
  | U64 -> UInt64.mul a b
  | S8 -> Int8.mul a b
  | S16 -> Int16.mul a b
  | S32 -> Int32.mul a b
  | S64 -> Int64.mul a b
  
let mul_lemma #t #l a b = ()

let mul64_wide a b = UInt128.mul_wide a b

let mul64_wide_lemma a b = ()

let sub_mod #t #l a b =
  match t with
  | U1   -> UInt8.rem (UInt8.sub_mod a b) 0x2uy
  | U8   -> UInt8.sub_mod a b
  | U16  -> UInt16.sub_mod a b
  | U32  -> UInt32.sub_mod a b
  | U64  -> UInt64.sub_mod a b
  | U128 -> UInt128.sub_mod a b
  | S8 -> Int8.int_to_t (Int.sub_mod (Int8.v a) (Int8.v b))
  | S16 -> Int16.int_to_t (Int.sub_mod (Int16.v a) (Int16.v b))
  | S32 -> Int32.int_to_t (Int.sub_mod (Int32.v a) (Int32.v b))
  | S64 -> Int64.int_to_t (Int.sub_mod (Int64.v a) (Int64.v b))

let sub_mod_lemma #t #l a b = ()

let sub #t #l a b =
  match t with
  | U1   -> UInt8.sub a b
  | U8   -> UInt8.sub a b
  | U16  -> UInt16.sub a b
  | U32  -> UInt32.sub a b
  | U64  -> UInt64.sub a b
  | U128 -> UInt128.sub a b
  | S8 -> Int8.sub a b
  | S16 -> Int16.sub a b
  | S32 -> Int32.sub a b
  | S64 -> Int64.sub a b

let sub_lemma #t #l a b = ()

let decr #t #l a =
  match t with
  | U1   -> UInt8.sub a 0x1uy
  | U8   -> UInt8.sub a 0x1uy
  | U16  -> UInt16.sub a 0x1us
  | U32  -> UInt32.sub a 0x1ul
  | U64  -> UInt64.sub a 0x1uL
  | U128 -> UInt128.sub a (UInt128.uint_to_t 1)
  | S8 -> Int8.sub a 0x1y
  | S16 -> Int16.sub a 0x1s
  | S32 -> Int32.sub a 0x1l
  | S64 -> Int64.sub a 0x1L
  
let decr_lemma #t #l a = ()

#reset-options "--z3rlimit 300"
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
  | S8 -> Int8.logxor a b
  | S16 -> Int16.logxor a b
  | S32 -> Int32.logxor a b
  | S64 -> Int64.logxor a b
  
#set-options "--max_fuel 1"

val logxor_lemma_: #t:inttype -> a:uint_t t SEC -> b:uint_t t SEC -> Lemma
  (uint_v (a `logxor` (a `logxor` b)) == uint_v b)
let logxor_lemma_ #t a b =
  match t with
  |U1 |U8 |U16 |U32 |U64 |U128 ->
  UInt.logxor_associative #(bits t) (uint_v a) (uint_v a) (uint_v b);
  UInt.logxor_self #(bits t) (uint_v a);
  UInt.logxor_commutative #(bits t) 0 (uint_v b);
  UInt.logxor_lemma_1 #(bits t) (uint_v b)
  |S8 |S16 |S32 |S64 ->
  Int.logxor_associative #(bits t) (uint_v a) (uint_v a) (uint_v b);
  Int.logxor_self #(bits t) (uint_v a);
  Int.logxor_commutative #(bits t) 0 (uint_v b);
  Int.logxor_lemma_1 #(bits t) (uint_v b)

let logxor_lemma #t a b =
  logxor_lemma_ #t a b;
  uintv_extensionality (logxor a (logxor a b)) b;
  assert (a `logxor` (a `logxor` b) == b);
  (match t with |U1 |U8 |U16 |U32 |U64 |U128 ->
   UInt.logxor_commutative #(bits t) (uint_v a) (uint_v b)
   |S8 |S16 |S32 |S64 -> Int.logxor_commutative #(bits t) (uint_v a) (uint_v b));
  logxor_lemma_ #t a b;
  uintv_extensionality (logxor a (logxor b a)) b;
  assert ((a `logxor` (b `logxor` a)) == b);
  (match t with |U1 |U8 |U16 |U32 |U64 |U128 ->
   UInt.logxor_lemma_1 #(bits t) (uint_v a)
   |S8 |S16 |S32 |S64 -> Int.logxor_lemma_1 #(bits t) (uint_v a));
  //UInt.logxor_lemma_1 #(bits t) (uint_v a);
  uintv_extensionality (logxor a (uint #t #SEC 0)) a

let logxor_lemma1 #t a b =
  match (v a, v b) with
  | _, 0 ->
    UInt.logxor_lemma_1 #(bits t) (uint_v a)
  | 0, _ ->
    UInt.logxor_commutative #(bits t) (uint_v a) (uint_v b);
    UInt.logxor_lemma_1 #(bits t) (uint_v b)
  | 1, 1 ->
    uintv_extensionality a b;
    UInt.logxor_self #(bits t) (uint_v a)

#set-options "--max_fuel 0"

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
  | S8 -> Int8.logand a b
  | S16 -> Int16.logand a b
  | S32 -> Int32.logand a b
  | S64 -> Int64.logand a b


let logand_lemma #t a b =
  match t with |U1 |U8 |U16 |U32 |U64 |U128 ->
   if (uint_v a = 0) then begin
    UInt.logand_commutative #(bits t) (uint_v a) (uint_v b);
    UInt.logand_lemma_1 #(bits t) (uint_v b) end
  else begin
    UInt.logand_commutative #(bits t) (uint_v a) (uint_v b);
    UInt.logand_lemma_2 #(bits t) (uint_v b) end
  |S8 |S16 |S32 |S64 ->
   if (uint_v a = 0) then begin
    Int.logand_commutative #(bits t) (uint_v a) (uint_v b);
    Int.logand_lemma_1 #(bits t) (uint_v b) end
  else begin
    Int.logand_commutative #(bits t) (uint_v a) (uint_v b);
    Int.logand_lemma_2 #(bits t) (uint_v b) end

let logand_spec #t #l a b = ()

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
  | S8 -> Int8.logor a b
  | S16 -> Int16.logor a b
  | S32 -> Int32.logor a b
  | S64 -> Int64.logor a b

let logor_spec #t #l a b = ()

#set-options "--max_fuel 1"

let logor_disjoint #t a b m =
  if m > 0 then begin
    UInt.logor_disjoint #(bits t) (uint_v b) (uint_v a) m;
    UInt.logor_commutative #(bits t) (uint_v b) (uint_v a) end
  else begin
    UInt.logor_commutative #(bits t) (uint_v a) (uint_v b);
    UInt.logor_lemma_1 #(bits t) (uint_v b)
  end
    
#set-options "--max_fuel 0"

let lognot #t #l a =
  match t with
  | U1   -> UInt8.rem (UInt8.lognot a) 0x2uy
  | U8   -> UInt8.lognot a
  | U16  -> UInt16.lognot a
  | U32  -> UInt32.lognot a
  | U64  -> UInt64.lognot a
  | U128 -> UInt128.lognot a
  | S8 -> Int8.lognot a
  | S16 -> Int16.lognot a
  | S32 -> Int32.lognot a
  | S64 -> Int64.lognot a

let shift_right_negative (#n:pos) (a:Int.int_t n{a < 0}) (s:nat) : Tot (Int.int_t n) =
  let shift_right_negative_vec (#n:pos) (a:BitVector.bv_t n) (s:nat) : Tot (BitVector.bv_t n) =
  if s>= n then BitVector.ones_vec #n
  else if s = 0 then a
  else Seq.append (BitVector.ones_vec #s) (Seq.slice a 0 (n-s))
  in FStar.Int.from_vec (shift_right_negative_vec #n (FStar.Int.to_vec #n a) s)
  
let shift_right #t #l a b =
  match t with
  | U1   -> UInt8.shift_right a b
  | U8   -> UInt8.shift_right a b
  | U16  -> UInt16.shift_right a b
  | U32  -> UInt32.shift_right a b
  | U64  -> UInt64.shift_right a b
  | U128 -> UInt128.shift_right a b
  | S8 -> Int8.shift_arithmetic_right a b
  | S16 -> Int16.shift_arithmetic_right a b
  | S32 -> Int32.shift_arithmetic_right a b
  | S64 -> Int64.shift_arithmetic_right a b


#reset-options "--z3rlimit 500 --max_fuel 2 --max_ifuel 2"

val shift_right_value_aux_1: #n:pos{n>1} -> a:Int.int_t n -> s:nat{s >= n} ->
  Lemma (requires True)
        (ensures Int.shift_arithmetic_right #n a s = a / pow2 s)
let shift_right_value_aux_1 #n a s =
  pow2_le_compat s n;
  if (a>=0) then (Int.sign_bit_positive a; assert(a=Int.to_uint a); assert(Int.shift_arithmetic_right #n a s == UInt.shift_right #n a s); UInt.shift_right_value_aux_1 #n a s)
  else begin
  Int.sign_bit_negative a;
  assert (Int.shift_arithmetic_right #n a s = -1);
  assert (- pow2 s <= a /\ a < 0);
  small_division_lemma_1 (a+pow2 s) (pow2 s);
  lemma_div_plus a 1 (pow2 s);
  assert((a+pow2 s) / pow2 s = 0)
  end
  
val shift_right_value_aux_2: #n:pos -> a:Int.int_t n ->
  Lemma (requires True)
        (ensures Int.shift_arithmetic_right #n a 0 = a / pow2 0)
let shift_right_value_aux_2 #n a = assert_norm (pow2 0 == 1)

#reset-options "--z3rlimit 500 --max_fuel 2 --max_ifuel 2"

val append_lemma: #n:pos -> #m:pos -> a:BitVector.bv_t n -> b:BitVector.bv_t m ->
  Lemma (Int.from_vec #(n + m) (Seq.append a b) = (Int.from_vec #n a) * pow2 m + (UInt.from_vec #m b))
let append_lemma #n #m a b =
  let a1 = Int.from_vec #n a in
  let a2 = UInt.from_vec #n a in
  let b' = UInt.from_vec #m b in
  let s1 = Int.from_vec #(n+m) (Seq.append a b) in
  let s2 = UInt.from_vec #(n+m) (Seq.append a b) in
  admit()

val shift_right_value_aux_0: #n:pos{n > 1} -> a:Int.int_t n ->
  Lemma (requires True)
        (ensures Int.shift_arithmetic_right #n a 1 = a / 2)

let shift_right_value_aux_0 #n a =
  if a >= 0 then begin
  Int.sign_bit_positive a; 
  assert(a=Int.to_uint a); 
  assert(Int.shift_arithmetic_right #n a 1 == UInt.shift_right #n a 1); 
  UInt.shift_right_value_aux_3 #n a 1
  end
  else begin
  Int.sign_bit_negative a;
  let a1 = Int.to_vec a in
  let au = Int.to_uint a in
  let sar = Int.shift_arithmetic_right #n a 1 in
  let sar1 = Int.to_vec sar in
  let sr = UInt.shift_right #n au 1 in
  let sr1 = UInt.to_vec sr in
  assert(Seq.equal (Seq.slice sar1 1 n) (Seq.slice sr1 1 n));
  assert (Seq.equal sar1 (Seq.append (BitVector.ones_vec #1) (Seq.slice sr1 1 n)));
  UInt.append_lemma #1 #(n-1) (BitVector.ones_vec #1) (Seq.slice sr1 1 n);
  assert(Seq.equal (Seq.slice a1 0 (n-1)) (Seq.slice sar1 1 n));
  UInt.slice_left_lemma a1 (n-1);
  assert (sar + pow2 n = pow2 (n-1) + (au / 2)); 
  pow2_double_sum (n-1);
  assert (sar + pow2 (n-1) = (a + pow2 n) / 2);
  pow2_double_mult (n-1);
  lemma_div_plus a (pow2 (n-1)) 2;
  assert (sar = a / 2)
  end


#reset-options "--z3rlimit 500 --max_fuel 2 --max_ifuel 2"

val shift_right_value_aux_3: #n:pos -> a:Int.int_t n -> s:pos{s < n} ->
  Lemma (requires True)
        (ensures Int.shift_arithmetic_right #n a s = a / pow2 s)
        (decreases s)
        
let rec shift_right_value_aux_3 #n a s =
  if s = 1 then shift_right_value_aux_0 #n a
  else begin
  let a1 = Int.to_vec a in
  assert(Seq.equal (BitVector.shift_arithmetic_right_vec #n a1 s) (BitVector.shift_arithmetic_right_vec #n (BitVector.shift_arithmetic_right_vec #n a1 (s-1)) 1));
  assert (Int.shift_arithmetic_right #n a s = Int.shift_arithmetic_right #n (Int.shift_arithmetic_right #n a (s-1)) 1);
  shift_right_value_aux_3 #n a (s-1);
  shift_right_value_aux_0 #n (Int.shift_arithmetic_right #n a (s-1));
  assert(Int.shift_arithmetic_right #n a s = (a / pow2 (s-1)) / 2);
  pow2_double_mult (s-1);
  division_multiplication_lemma a (pow2 (s-1)) 2
  end

let shift_right_lemma #t #l a b = 
  match t with
  |U1 |U8 |U16 |U32 |U64 |U128 -> ()
  |_ -> if (uint_v b >= bits t) then shift_right_value_aux_1 #(bits t) (uint_v a) (uint_v b)
       else if (uint_v b = 0) then shift_right_value_aux_2 #(bits t) (uint_v a)
       else shift_right_value_aux_3 #(bits t) (uint_v a) (uint_v b)
  
let shift_left_negative (#n:pos) (a:Int.int_t n{a < 0}) (s:nat) : Tot (Int.int_t n) =
  FStar.Int.from_vec (BitVector.shift_left_vec #n (FStar.Int.to_vec #n a) s)

let shift_left #t #l a b =
  match t with
  | U1   -> UInt8.shift_left a b
  | U8   -> UInt8.shift_left a b
  | U16  -> UInt16.shift_left a b
  | U32  -> UInt32.shift_left a b
  | U64  -> UInt64.shift_left a b
  | U128 -> UInt128.shift_left a b
  | S8 -> if (uint_v a >= 0) then Int8.shift_left a b
         else Int8.int_to_t (shift_left_negative (Int8.v a) (UInt32.v b))
  | S16 -> if (uint_v a >= 0) then Int16.shift_left a b
         else Int16.int_to_t (shift_left_negative (Int16.v a) (UInt32.v b))
  | S32 -> if (uint_v a >= 0) then Int32.shift_left a b
         else Int32.int_to_t (shift_left_negative (Int32.v a) (UInt32.v b))
  | S64 -> if (uint_v a >= 0) then Int64.shift_left a b
         else Int64.int_to_t (shift_left_negative (Int64.v a) (UInt32.v b))

#reset-options "--z3rlimit 800 --max_fuel 3 --max_ifuel 3"

let shift_left_lemma #t #l a b = 
  match t with
  |U1 |U8 |U16 |U32 |U64 |U128 -> ()
  |_ -> let a' = uint_v a in
       let b' = uint_v b in
       let n = Int.to_uint a' in
       let sn = UInt.shift_left #(bits t) n b' in
       assert(Int.to_vec a' == UInt.to_vec #(bits t) n); 
       if (a' >= 0) then
       (assert(a' == n);
       assert (sn == (n * pow2 b') % pow2 (bits t));
       ()) else
       (assert(a'+ pow2 (bits t) == n);
       assert (sn == (n * pow2 b') % pow2 (bits t));
       assert (sn == ((a'+pow2 (bits t)) * pow2 b') % pow2 (bits t));
       distributivity_add_left a' (pow2 (bits t)) (pow2 b');
       assert (sn == ((a'*pow2 b')+(pow2 (bits t)* pow2 b')) % pow2 (bits t));   
       swap_mul (pow2 (bits t)) (pow2 b');
       lemma_mod_plus (a' * pow2 b') (pow2 b') (pow2 (bits t));
       assert (sn == (a' * pow2 b') % pow2 (bits t));
       ())


let rotate_right #t #l a b =
  logor (shift_right a b) (shift_left a (sub #U32 (size (bits t)) b))

let rotate_left #t #l a b =
  logor (shift_left a b) (shift_right a (sub #U32 (size (bits t)) b))

let zeroes t l = nat_to_uint #t #l 0

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
  | _  -> uint #t #l (ones_v t)

inline_for_extraction
let minus (#t:inttype) (#l:secrecy_level) (a:uint_t t l) = add_mod (lognot a) (uint #t #l 1)
 
let eq_mask #t a b =
  match t with
  | U1   -> lognot (logxor a b)
  | U8   -> UInt8.eq_mask a b
  | U16  -> UInt16.eq_mask a b
  | U32  -> UInt32.eq_mask a b
  | U64  -> UInt64.eq_mask a b
  | U128 -> UInt128.eq_mask a b
  | S8   -> to_i8 #U8 #SEC (UInt8.eq_mask (to_u8 a) (to_u8 b))
  | S16  -> to_i16 (UInt16.eq_mask (to_u16 a) (to_u16 b))
  | S32  -> to_i32 (UInt32.eq_mask (to_u32 a) (to_u32 b))
  | S64  -> to_i64 (UInt64.eq_mask (to_u64 a) (to_u64 b))

#reset-options "--z3rlimit 3000 --max_fuel 1 --max_ifuel 1"

let eq_mask_lemma #t a b =
  match t with
  | U1 ->
    begin
    assert_norm (
      logxor (u1 0) (u1 0) == u1 0 /\ logxor (u1 1) (u1 1) == u1 0 /\
      logxor (u1 0) (u1 1) == u1 1 /\ logxor (u1 1) (u1 0) == u1 1 /\
      lognot (u1 1) == u1 0 /\ lognot (u1 0) == u1 1)
    end
  | U8 | U16 | U32 | U64 | U128 -> ()
  | S8 -> let a' = to_u8 a in let b' = to_u8 b in
  assert_norm (v a = v b <==> v a' = v b');
    let m' = UInt8.eq_mask a' b' in
    assert_norm(v #U8 #SEC m' = 0 ==> v #S8 #SEC (to_i8 m') = 0);
    assert_norm(v #U8 #SEC m' = ones_v U8 ==> v #S8 #SEC (to_i8 #U8 #SEC m') = -1)
  | S16 -> let a' = to_u16 a in let b' = to_u16 b in
    assert (v a = v a' @% pow2 16); assert( v a' = v a % pow2 16);
    assert (v b = v b' @% pow2 16); assert( v b' = v b % pow2 16);
    let m' = UInt16.eq_mask a' b' in
    assert (v a' = v b' ==> v m' = ones_v U16);
    assert (v a' <> v b' ==> v m' = 0);
    if (v a = v b) then begin
      assert (v a' = v b');
      assert (v m' = ones_v U16);
      assert (v (to_i16 m') = -1) end
    else begin
      assert(v a' <> v b');
      assert(v m' = 0);
      assert(v (to_i16 m') = 0) end
  | S32 -> let a' = to_u32 a in let b' = to_u32 b in
    assert (v a = v a' @% pow2 32); assert( v a' = v a % pow2 32);
    assert (v b = v b' @% pow2 32); assert( v b' = v b % pow2 32);
    let m' = UInt32.eq_mask a' b' in
    assert (v a' = v b' ==> v m' = ones_v U32);
    assert (v a' <> v b' ==> v m' = 0);
    if (v a = v b) then begin
      assert (v a' = v b');
      assert (v m' = ones_v U32);
      assert (v (to_i32 m') = -1) end
    else begin
      assert(v a' <> v b');
      assert(v m' = 0);
      assert(v (to_i32 m') = 0) end
  | S64 -> let a' = to_u64 a in let b' = to_u64 b in
    assert (v a = v a' @% pow2 64); assert( v a' = v a % pow2 64);
    assert (v b = v b' @% pow2 64); assert( v b' = v b % pow2 64);
    let m' = UInt64.eq_mask a' b' in
    assert (v a' = v b' ==> v m' = ones_v U64);
    assert (v a' <> v b' ==> v m' = 0);
    if (v a = v b) then begin
      assert (v a' = v b');
      assert (v m' = ones_v U64);
      assert (v (to_i64 m') = -1) end
    else begin
      assert(v a' <> v b');
      assert(v m' = 0);
      assert(v (to_i64 m') = 0) end

let eq_mask_logand_lemma #t a b c =
  eq_mask_lemma a b;
  logand_lemma (eq_mask a b) c;
  match t with 
  | U8 | U16 | U32 | U64 | U128 -> UInt.logand_commutative #(bits t) (uint_v (eq_mask a b)) (uint_v c)
  | _ -> Int.logand_commutative #(bits t) (uint_v (eq_mask a b)) (uint_v c)
  
let neq_mask #t a b = lognot (eq_mask #t a b)

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
  gte_mask_lemma a b;
  logand_lemma (gte_mask a b) c;
  UInt.logand_commutative #(bits t) (uint_v (gte_mask a b)) (uint_v c)

let lt_mask #t a b = lognot (gte_mask a b)

let gt_mask #t a b = logand (gte_mask a b) (neq_mask a b)

let lte_mask #t a b = logor (lt_mask a b) (eq_mask a b)

#reset-options "--z3rlimit 3000 --max_fuel 3 --max_ifuel 3"
private
val mod_mask_value: #t:inttype{~(S8? t) /\ ~(S16? t) /\ ~(S32? t) /\ ~(S64? t)} -> #l:secrecy_level -> m:shiftval t ->
  Lemma (uint_v (mod_mask #t #l m) == pow2 (uint_v m) - 1)
let mod_mask_value #t #l m =
  if uint_v m > 0 then begin
    let m = uint_v m in
    pow2_lt_compat (bits t) m;
    small_modulo_lemma_1 (pow2 m) (pow2 (bits t));
    assert (FStar.Mul.(1 * pow2 m) == pow2 m);
    UInt.shift_left_value_lemma #(bits t) 1 m
  end

#set-options "--max_fuel 1"

let mod_mask_lemma #t #l a m =
  mod_mask_value #t #l m;
  if uint_v m = 0 then
    UInt.logand_lemma_1 #(bits t) (uint_v a)
  else
    UInt.logand_mask #(bits t) (uint_v a) (uint_v m)

#set-options "--max_fuel 0"

(* defined in .fsti: notations +^, -^, ...*)

let nat_mod_v #m x = x

let div #t x y =
  match t with
  | U1  -> UInt8.div x y
  | U8  -> UInt8.div x y
  | U16 -> UInt16.div x y
  | U32 -> UInt32.div x y
  | U64 -> UInt64.div x y
  
let div_lemma #t x y = ()

let mod #t x y =
  match t with
  | U1  -> UInt8.rem x y
  | U8  -> UInt8.rem x y
  | U16 -> UInt16.rem x y
  | U32 -> UInt32.rem x y
  | U64 -> UInt64.rem x y

let mod_lemma #t x y = ()

let eq #t x y =
  match t with
  | U1  -> UInt8.eq x y
  | U8  -> UInt8.eq x y
  | U16 -> UInt16.eq x y
  | U32 -> UInt32.eq x y
  | U64 -> UInt64.eq x y
  | U128 -> UInt128.eq x y
  | S8  -> Int8.eq x y
  | S16 -> Int16.eq x y
  | S32 -> Int32.eq x y
  | S64 -> Int64.eq x y
  
let eq_lemma #t x y = ()

let ne #t x y =
  match t with
  | U1  -> not (UInt8.eq x y)
  | U8  -> not (UInt8.eq x y)
  | U16 -> not (UInt16.eq x y)
  | U32 -> not (UInt32.eq x y)
  | U64 -> not (UInt64.eq x y)
  | U128 -> not (UInt128.eq x y)
  | S8  -> not (Int8.eq x y)
  | S16 -> not (Int16.eq x y)
  | S32 -> not (Int32.eq x y)
  | S64 -> not (Int64.eq x y)
  
let ne_lemma #t x y = ()

let lt #t x y =
  match t with
  | U1  -> UInt8.lt x y
  | U8  -> UInt8.lt x y
  | U16 -> UInt16.lt x y
  | U32 -> UInt32.lt x y
  | U64 -> UInt64.lt x y
  | U128 -> UInt128.lt x y
  | S8  -> Int8.lt x y
  | S16 -> Int16.lt x y
  | S32 -> Int32.lt x y
  | S64 -> Int64.lt x y
  
let lt_lemma #t x y = ()

let lte #t x y =
  match t with
  | U1  -> UInt8.lte x y
  | U8  -> UInt8.lte x y
  | U16 -> UInt16.lte x y
  | U32 -> UInt32.lte x y
  | U64 -> UInt64.lte x y
  | U128 -> UInt128.lte x y
  | S8  -> Int8.lte x y
  | S16 -> Int16.lte x y
  | S32 -> Int32.lte x y
  | S64 -> Int64.lte x y
  
let lte_lemma #t x y = ()

let gt #t x y =
  match t with
  | U1  -> UInt8.gt x y
  | U8  -> UInt8.gt x y
  | U16 -> UInt16.gt x y
  | U32 -> UInt32.gt x y
  | U64 -> UInt64.gt x y
  | U128 -> UInt128.gt x y
  | S8  -> Int8.gt x y
  | S16 -> Int16.gt x y
  | S32 -> Int32.gt x y
  | S64 -> Int64.gt x y
  
let gt_lemma #t x y = ()

let gte #t x y =
  match t with
  | U1  -> UInt8.gte x y
  | U8  -> UInt8.gte x y
  | U16 -> UInt16.gte x y
  | U32 -> UInt32.gte x y
  | U64 -> UInt64.gte x y
  | U128 -> UInt128.gte x y
  | S8  -> Int8.gte x y
  | S16 -> Int16.gte x y
  | S32 -> Int32.gte x y
  | S64 -> Int64.gte x y
  
let gte_lemma #t x y = ()
