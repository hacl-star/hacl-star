module Lib.IntTypes

open FStar.IFC
open FStar.Integers
open FStar.ConstantTime.Integers

module CT = FStar.ConstantTime.Integers

(* Declared in .fsti : intsize, bits, maxint *)
#set-options "--z3rlimit 20 --max_fuel 0 --max_ifuel 1"

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

unfold let secret (w:fixed_width{w <> W128}) = 
  CT.t (Secret hacl_label (Unsigned w))

unfold let public sw = CT.t (Public sw)

let uint_t t = 
  match t with
  | U8   -> secret W8
  | U16  -> secret W16
  | U32  -> secret W32
  | U64  -> secret W64
  | U128 -> public (Unsigned W128) // We don't have constant-time operations on UInt128
  | SIZE -> public (Unsigned W32)
  | BYTE -> public (Unsigned W8)

inline_for_extraction
let uint_to_nat_ (#t:inttype) (x:uint_t t) =
  match t with
  | U8   -> v (CT.i (x <: secret W8))
  | U16  -> v (CT.i (x <: secret W16))
  | U32  -> v (CT.i (x <: secret W32))
  | U64  -> v (CT.i (x <: secret W64))
  | U128 -> v (x <: int_t (Unsigned W128))
  | SIZE -> v (x <: int_t (Unsigned W32))
  | BYTE -> v (x <: int_t (Unsigned W8))

let uint_v #t u = uint_to_nat_ u

let uintv_extensionality #t a b =
  match t with
  | U8   -> UInt8.v_inj (m (a <: secret W8)) (m (b <: secret W8))
  | U16  -> UInt16.v_inj (m (a <: secret W16)) (m (b <: secret W16))
  | U32  -> UInt32.v_inj (m (a <: secret W32)) (m (b <: secret W32))
  | U64  -> UInt64.v_inj (m (a <: secret W64)) (m (b <: secret W64))
  | U128 -> UInt128.v_inj a b
  | SIZE -> UInt32.v_inj a b
  | BYTE -> UInt8.v_inj a b

(* Declared in .fsti: uint8, uint16, uint32, uint64, uint128 *)

let u8 x = 
  reveal_hide #hacl_lattice #hacl_label #(Unsigned W8) x;
  hide x

let u16 x =
  reveal_hide #hacl_lattice #hacl_label #(Unsigned W16) x;
  hide x

let u32 x =
  reveal_hide #hacl_lattice #hacl_label #(Unsigned W32) x;
  hide x

let u64 x =
  reveal_hide #hacl_lattice #hacl_label #(Unsigned W64) x;
  hide x

let u128 x = UInt128.uint_to_t x

inline_for_extraction
let size x : uint_t SIZE = UInt32.uint_to_t x

inline_for_extraction
let size_v x = UInt32.v x

inline_for_extraction
let byte x = UInt8.uint_to_t x

inline_for_extraction
let byte_v x = UInt8.v x

let size_to_uint32 x = hide (size_v x)
  
let byte_to_uint8 x = hide (byte_v x)

let nat_to_uint #t x : uint_t t =
  match t with
  | U8 -> u8 x
  | U16 -> u16 x
  | U32 -> u32 x
  | U64 -> u64 x
  | U128 -> u128 x
  | SIZE -> size x
  | BYTE -> byte x

#set-options "--z3rlimit 1000 --max_fuel 0"
#set-options "--lax" // TODO: remove this
let cast #t t' u  =
  match t, t' with
  | U8, U8 -> u
  | U8, U16 -> FStar.Int.Cast.uint8_to_uint16 u
  | U8, U32 -> FStar.Int.Cast.uint8_to_uint32 u
  | U8, SIZE -> FStar.Int.Cast.uint8_to_uint32 u
  | U8, U64 -> FStar.Int.Cast.uint8_to_uint64 u
  | U8, U128 -> FStar.UInt128.uint64_to_uint128 (FStar.Int.Cast.uint8_to_uint64 u)
  | U16, U8 -> FStar.Int.Cast.uint16_to_uint8 u
  | U16, U16 -> u
  | U16, U32 -> FStar.Int.Cast.uint16_to_uint32 u
  | U16, SIZE -> FStar.Int.Cast.uint16_to_uint32 u
  | U16, U64 -> FStar.Int.Cast.uint16_to_uint64 u
  | U16, U128 -> FStar.UInt128.uint64_to_uint128 (FStar.Int.Cast.uint16_to_uint64 u)
  | U32, U8 -> FStar.Int.Cast.uint32_to_uint8 u
  | U32, U16 -> FStar.Int.Cast.uint32_to_uint16 u
  | U32, U32 -> u
  | U32, SIZE -> u
  | U32, U64 -> FStar.Int.Cast.uint32_to_uint64 u
  | U32, U128 -> FStar.UInt128.uint64_to_uint128 (FStar.Int.Cast.uint32_to_uint64 u)
  | SIZE, U8 -> FStar.Int.Cast.uint32_to_uint8 u
  | SIZE, U16 -> FStar.Int.Cast.uint32_to_uint16 u
  | SIZE, U32 -> u
  | SIZE, SIZE -> u
  | SIZE, U64 -> FStar.Int.Cast.uint32_to_uint64 u
  | SIZE, U128 -> FStar.UInt128.uint64_to_uint128 (FStar.Int.Cast.uint32_to_uint64 u)
  | U64, U8 -> FStar.Int.Cast.uint64_to_uint8 u
  | U64, U16 -> FStar.Int.Cast.uint64_to_uint16 u
  | U64, U32 -> FStar.Int.Cast.uint64_to_uint32 u
  | U64, SIZE -> FStar.Int.Cast.uint64_to_uint32 u
  | U64, U64 -> u
  | U64, U128 -> FStar.UInt128.uint64_to_uint128 u
  | U128, U8 -> FStar.Int.Cast.uint64_to_uint8 (FStar.UInt128.uint128_to_uint64 u)
  | U128, U16 -> FStar.Int.Cast.uint64_to_uint16 (FStar.UInt128.uint128_to_uint64 u)
  | U128, U32 -> FStar.Int.Cast.uint64_to_uint32 (FStar.UInt128.uint128_to_uint64 u)
  | U128, SIZE -> FStar.Int.Cast.uint64_to_uint32 (FStar.UInt128.uint128_to_uint64 u)
  | U128, U64 -> FStar.UInt128.uint128_to_uint64 u
  | U128, U128 -> u
#reset-options "--z3rlimit 20 --max_fuel 0 --max_ifuel 1"

let add_mod #t a b = 
  match t with
  | U8  -> addition_mod (a <: uint_t U8)  b
  | U16 -> addition_mod (a <: uint_t U16) b
  | U32 -> addition_mod (a <: uint_t U32) b
  | U64 -> addition_mod (a <: uint_t U64) b
  | U128 -> UInt128.add_mod a b
  | SIZE -> UInt32.add_mod a b
  | BYTE -> UInt8.add_mod a b

let add #t a b =
  match t with
  | U8   -> addition (a <: uint_t U8)  b
  | U16  -> addition (a <: uint_t U16) b
  | U32  -> addition (a <: uint_t U32) b
  | U64  -> addition (a <: uint_t U64) b
  | U128 -> UInt128.add a b
  | SIZE -> UInt32.add a b
  | BYTE -> UInt8.add a b

let incr #t a =
  match t with
  | U8   -> addition (a <: uint_t U8)  (u8 1)  
  | U16  -> addition (a <: uint_t U16) (u16 1)
  | U32  -> addition (a <: uint_t U32) (u32 1)
  | U64  -> addition (a <: uint_t U64) (u64 1)
  | U128 -> UInt128.add a (u128 1)
  | SIZE -> UInt32.add a (size 1)
  | BYTE -> UInt8.add a (byte 1)

let mul_mod #t a b =
  match t with
  | U8   -> multiplication_mod (a <: uint_t U8)  b
  | U16  -> multiplication_mod (a <: uint_t U16) b
  | U32  -> multiplication_mod (a <: uint_t U32) b
  | U64  -> multiplication_mod (a <: uint_t U64) b
  | SIZE -> UInt32.mul_mod a b
  | BYTE -> UInt8.mul_mod a b

// SZ: Stopped here
#set-options "--lax"

let mul #t a b =
  match t with
  | U8 -> UInt8.mul a b
  | U16 -> UInt16.mul a b
  | U32 -> UInt32.mul a b
  | U64 -> UInt64.mul a b
  | SIZE -> UInt32.mul a b
  | BYTE -> UInt8.mul a b

let mul_wide a b = UInt128.mul_wide a b

let sub_mod #t a b =
  match t with
  | U8 -> (UInt8.sub_mod a b)
  | U16 -> (UInt16.sub_mod a b)
  | U32 -> (UInt32.sub_mod a b)
  | U64 -> (UInt64.sub_mod a b)
  | U128 -> (UInt128.sub_mod a b)
  | SIZE -> (UInt32.sub_mod a b)
  | BYTE -> (UInt8.sub_mod a b)

let sub #t a b =
  match t with
  | U8 -> (UInt8.sub a b)
  | U16 -> (UInt16.sub a b)
  | U32 -> (UInt32.sub a b)
  | U64 -> (UInt64.sub a b)
  | U128 -> (UInt128.sub a b)
  | SIZE -> (UInt32.sub a b)
  | BYTE -> (UInt8.sub a b)

let decr #t a =
  match t with
  | U8 -> (UInt8.sub a 0x1uy)
  | U16 -> (UInt16.sub a 0x1us)
  | U32 -> (UInt32.sub a 0x1ul)
  | U64 -> (UInt64.sub a 0x1uL)
  | U128 -> (UInt128.sub a (UInt128.uint_to_t 1))
  | SIZE -> (UInt32.sub a 0x1ul)
  | BYTE -> (UInt8.sub a 0x1uy)

let logxor #t a b =
  match t with
  | U8 -> (UInt8.logxor a b)
  | U16 -> (UInt16.logxor a b)
  | U32 -> (UInt32.logxor a b)
  | U64 -> (UInt64.logxor a b)
  | U128 -> (UInt128.logxor a b)
  | SIZE -> (UInt32.logxor a b)
  | BYTE -> (UInt8.logxor a b)


let logand #t a b =
  match t with
  | U8 -> (UInt8.logand a b)
  | U16 -> (UInt16.logand a b)
  | U32 -> (UInt32.logand a b)
  | U64 -> (UInt64.logand a b)
  | U128 -> (UInt128.logand a b)
  | SIZE -> (UInt32.logand a b)
  | BYTE -> (UInt8.logand a b)

let logor #t a b =
  match t with
  | U8 -> (UInt8.logor a b)
  | U16 -> (UInt16.logor a b)
  | U32 -> (UInt32.logor a b)
  | U64 -> (UInt64.logor a b)
  | U128 -> (UInt128.logor a b)
  | SIZE -> (UInt32.logor a b)
  | BYTE -> (UInt8.logor a b)


let lognot #t a =
  match t with
  | U8 -> (UInt8.lognot a)
  | U16 -> (UInt16.lognot a)
  | U32 -> (UInt32.lognot a)
  | U64 -> (UInt64.lognot a)
  | U128 -> (UInt128.lognot a)
  | SIZE -> (UInt32.lognot a)
  | BYTE -> (UInt8.lognot a)


let shift_right #t a b =
  match t with
  | U8 -> (UInt8.shift_right a b)
  | U16 -> (UInt16.shift_right a b)
  | U32 -> (UInt32.shift_right a b)
  | U64 -> (UInt64.shift_right a b)
  | U128 -> (UInt128.shift_right a b)
  | SIZE -> (UInt32.shift_right a b)
  | BYTE -> (UInt8.shift_right a b)

let shift_left #t a b =
  match t with
  | U8 -> (UInt8.shift_left a b)
  | U16 -> (UInt16.shift_left a b)
  | U32 -> (UInt32.shift_left a b)
  | U64 -> (UInt64.shift_left a b)
  | U128 -> (UInt128.shift_left a b)
  | SIZE -> (UInt32.shift_left a b)
  | BYTE -> (UInt8.shift_left a b)


let rotate_right #t a b =
  (logor (shift_right a b)  (shift_left a (sub #SIZE (size (bits t)) b)))

let rotate_left #t a b =
  (logor (shift_left a b)  (shift_right a (sub #SIZE (size (bits t)) b)))

let eq_mask #t a b =
  match t with
  | U8 -> if FStar.UInt8.(a =^ b) then (u8 (maxint U8)) else (u8 0)
  | U16 -> if FStar.UInt16.(a =^ b) then (u16 (maxint U16)) else (u16 0)
  | U32 -> if FStar.UInt32.(a =^ b) then (u32 (maxint U32)) else (u32 0)
  | U64 -> if FStar.UInt64.(a =^ b) then (u64 (maxint U64)) else (u64 0)
  | U128 -> if FStar.UInt128.(a =^ b) then (u128 (maxint U128)) else (u128 0)
  | SIZE -> if FStar.UInt32.(a =^ b) then (size (maxint U32)) else (size 0)
  | BYTE -> if FStar.UInt8.(a =^ b) then (byte (maxint U8)) else (byte 0)

let neq_mask #t a b =
  match t with
  | U8 -> if not FStar.UInt8.(a =^ b) then (u8 (maxint U8)) else (u8 0)
  | U16 -> if not FStar.UInt16.(a =^ b) then (u16 (maxint U16)) else (u16 0)
  | U32 -> if not FStar.UInt32.(a =^ b) then (u32 (maxint U32)) else (u32 0)
  | U64 -> if not FStar.UInt64.(a =^ b) then (u64 (maxint U64)) else (u64 0)
  | U128 -> if not FStar.UInt128.(a =^ b) then (u128 (maxint U128)) else (u128 0)
  | SIZE -> if not FStar.UInt32.(a =^ b) then (size (maxint U32)) else (size 0)
  | BYTE -> if not FStar.UInt8.(a =^ b) then (byte (maxint U8)) else (byte 0)

let gt_mask #t a b =
  match t with
  | U8 -> if FStar.UInt8.(a >^ b) then (u8 (maxint U8)) else (u8 0)
  | U16 -> if FStar.UInt16.(a >^ b) then (u16 (maxint U16)) else (u16 0)
  | U32 -> if FStar.UInt32.(a >^ b) then (u32 (maxint U32)) else (u32 0)
  | U64 -> if FStar.UInt64.(a >^ b) then (u64 (maxint U64)) else (u64 0)
  | U128 -> if FStar.UInt128.(a >^ b) then (u128 (maxint U128)) else (u128 0)
  | SIZE -> if FStar.UInt32.(a >^ b) then (size (maxint U32)) else (size 0)
  | BYTE -> if FStar.UInt8.(a >^ b) then (byte (maxint U8)) else (byte 0)

let gte_mask #t a b =
  match t with
  | U8 -> if FStar.UInt8.(a >=^ b) then (u8 (maxint U8)) else (u8 0)
  | U16 -> if FStar.UInt16.(a >=^ b) then (u16 (maxint U16)) else (u16 0)
  | U32 -> if FStar.UInt32.(a >=^ b) then (u32 (maxint U32)) else (u32 0)
  | U64 -> if FStar.UInt64.(a >=^ b) then (u64 (maxint U64)) else (u64 0)
  | U128 -> if FStar.UInt128.(a >=^ b) then (u128 (maxint U128)) else (u128 0)
  | SIZE -> if FStar.UInt32.(a >=^ b) then (size (maxint U32)) else (size 0)
  | BYTE -> if FStar.UInt8.(a >=^ b) then (byte (maxint U8)) else (byte 0)

let lt_mask #t a b =
  match t with
  | U8 -> if FStar.UInt8.(a <^ b) then (u8 (maxint U8)) else (u8 0)
  | U16 -> if FStar.UInt16.(a <^ b) then (u16 (maxint U16)) else (u16 0)
  | U32 -> if FStar.UInt32.(a <^ b) then (u32 (maxint U32)) else (u32 0)
  | U64 -> if FStar.UInt64.(a <^ b) then (u64 (maxint U64)) else (u64 0)
  | U128 -> if FStar.UInt128.(a <^ b) then (u128 (maxint U128)) else (u128 0)
  | SIZE -> if FStar.UInt32.(a <^ b) then (size (maxint U32)) else (size 0)
  | BYTE -> if FStar.UInt8.(a <^ b) then (byte (maxint U8)) else (byte 0)

let lte_mask #t a b =
  match t with
  | U8 -> if FStar.UInt8.(a <=^ b) then (u8 (maxint U8)) else (u8 0)
  | U16 -> if FStar.UInt16.(a <=^ b) then (u16 (maxint U16)) else (u16 0)
  | U32 -> if FStar.UInt32.(a <=^ b) then (u32 (maxint U32)) else (u32 0)
  | U64 -> if FStar.UInt64.(a <=^ b) then (u64 (maxint U64)) else (u64 0)
  | U128 -> if FStar.UInt128.(a <=^ b) then (u128 (maxint U128)) else (u128 0)
  | SIZE -> if FStar.UInt32.(a <=^ b) then (size (maxint U32)) else (size 0)
  | BYTE -> if FStar.UInt8.(a <=^ b) then (byte (maxint U8)) else (byte 0)

let eq_mask_lemma #t a b d = admit()
let neq_mask_lemma #t a b d = admit()
let gt_mask_lemma #t a b d = admit()
let gte_mask_lemma #t a b d = admit()
let lt_mask_lemma #t a b d = admit()
let lte_mask_lemma #t a b d = admit()

#set-options "--z3rlimit 10 --max_fuel 0 --max_ifuel 0"

private
val mod_mask_value: #t:inttype -> m:shiftval t -> Lemma
  (uint_v (mod_mask #t m) == pow2 (uint_v m) - 1)
let mod_mask_value #t m =
  if uint_v m > 0 then
    begin
    let m = uint_v m in
    pow2_lt_compat (bits t) m;
    small_modulo_lemma_1 (pow2 m) (pow2 (bits t));
    assert (FStar.Mul.(1 * pow2 m) == pow2 m);
    UInt.shift_left_value_lemma #(bits t) 1 m
    end

let mod_mask_lemma #t a m =
  mod_mask_value #t m;
  if uint_v m = 0 then
    UInt.logand_lemma_1 #(bits t) (uint_v a)
  else
    UInt.logand_mask #(bits t) (uint_v a) (uint_v m)

#reset-options "--z3rlimit 100"

(* defined in .fsti: notations +^, -^, ...*)

let nat_mod_v #m x = x

let div #t x y =
  match t with
  | SIZE -> FStar.UInt32.div x y
  | BYTE -> FStar.UInt8.div x y


let mod #t x y =
  match t with
  | SIZE -> FStar.UInt32.rem x y
  | BYTE -> FStar.UInt8.rem x y

let eq #t x y =
  match t with
  | SIZE -> FStar.UInt32.eq x y
  | BYTE -> FStar.UInt8.eq x y

let ne #t x y =
  match t with
  | SIZE -> not (FStar.UInt32.eq x y)
  | BYTE -> not (FStar.UInt8.eq x y)

let lt #t x y =
  match t with
  | SIZE -> FStar.UInt32.lt x y
  | BYTE -> FStar.UInt8.lt x y

let le #t x y =
  match t with
  | SIZE -> FStar.UInt32.lte x y
  | BYTE -> FStar.UInt8.lte x y

let gt #t x y =
  match t with
  | SIZE -> FStar.UInt32.gt x y
  | BYTE -> FStar.UInt8.gt x y

let ge #t x y =
  match t with
  | SIZE -> FStar.UInt32.gte x y
  | BYTE -> FStar.UInt8.gte x y
