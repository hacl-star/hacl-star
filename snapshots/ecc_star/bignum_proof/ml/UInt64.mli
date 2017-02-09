open Prims
open Stdint

val bitsize: 'a -> 'b -> bool
type 'n ulint
type uintN

val fits_size: 'a -> 'b -> 'c -> unit
val fits_platform_size: 'a -> 'b -> unit
val size_of_add_lemma: 'a -> 'b -> 'c -> 'd -> unit
val size_of_sub_lemma: 'a -> 'b -> 'c -> 'd  -> unit
val size_of_mul_lemma: 'a -> 'b -> 'c -> 'd  -> unit
val size_of_mul_by_pow2: 'a -> 'b -> 'c -> unit

type uint_wide
type uint_std

type limb = uint_std
type wide = uint_wide
       
val byte_to_limb: uint8 -> uint_std
val byte_to_wide: uint8 -> uint_wide
val limb_to_byte: limb -> uint8
val limb_to_wide: uint_std -> uint_wide
val wide_to_byte: wide -> uint8
val wide_to_limb: uint_wide -> uint_std
val to_limb: string -> uint_std
val to_wide: string -> uint_wide

val byte_to_int: uint8 -> int
val limb_to_int: uint_std -> int
val wide_to_int: uint_wide -> int

val zero_byte: uint8
val zero_limb: limb
val zero_wide: wide
val one_byte: uint8
val one_limb: limb
val one_wide: wide

val add_byte: uint8 -> uint8 -> uint8
val sub_byte: uint8 -> uint8 -> uint8
val mul_byte: uint8 -> uint8 -> uint8
val div_byte: uint8 -> uint8 -> uint8
val mod_byte: uint8 -> uint8 -> uint8
val neg_byte: uint8 -> uint8
val log_and_byte: uint8 -> uint8 -> uint8
val log_or_byte: uint8 -> uint8 -> uint8
val log_xor_byte: uint8 -> uint8 -> uint8
val log_not_byte: uint8 -> uint8
val to_uint_byte: int -> uint8
val shift_left_byte: uint8 -> int -> uint8
val shift_right_byte: uint8 -> int -> uint8

val add_limb: limb -> limb -> limb
val sub_limb: limb -> limb -> limb
val sub_mod_limb: limb -> limb -> limb
val mul_limb: limb -> limb -> limb
val div_limb: limb -> limb -> limb
val mod_limb: limb -> limb -> limb
val neg_limb: limb -> limb
val log_and_limb: limb -> limb -> limb
val log_or_limb: limb -> limb -> limb
val log_xor_limb: limb -> limb -> limb
val log_not_limb: limb -> limb
val to_uint_limb: int -> limb
val shift_left_limb: limb -> int -> limb
val shift_right_limb: limb -> int -> limb

val mul_limb_to_wide: limb -> limb -> wide

val add_wide: wide -> wide -> wide
val sub_wide: wide -> wide -> wide
val sub_mod_wide: wide -> wide -> wide
val mul_wide: wide -> wide -> wide
val div_wide: wide -> wide -> wide
val mod_wide: wide -> wide -> wide
val neg_wide: wide -> wide
val log_and_wide: wide -> wide -> wide
val log_or_wide: wide -> wide -> wide
val log_xor_wide: wide -> wide -> wide
val log_not_wide: wide -> wide
val to_uint_wide: int -> wide
val shift_left_wide: wide -> int -> wide
val shift_right_wide: wide -> int -> wide

val eq_limb: limb -> limb -> limb
val gte_limb: limb -> limb -> limb

val eq_wide: wide -> wide -> wide
val gte_wide: wide -> wide -> wide

val to_string: limb -> string
val of_string: string -> limb
val wide_to_string: wide -> string
val wide_of_string: string -> wide
val to_int64: limb -> int64
val of_int64: int64 -> limb
