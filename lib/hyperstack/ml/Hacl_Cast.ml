(** Uints to Uints **)
type s8 = Hacl_UInt8.uint8
type s32 = Hacl_UInt32.uint32
type s64 = Hacl_UInt64.uint64
type s128 = Hacl_UInt128.t

type u8 = FStar_UInt8.t
type u32 = FStar_UInt32.t
type u64 = FStar_UInt64.uint64

             
let sint8_to_sint128 (a:s8) : (s128) = Hacl_UInt128.of_string (Hacl_UInt8.to_string a)
let sint8_to_sint64 (a:s8) : (s64) = Hacl_UInt64.of_string (Hacl_UInt8.to_string a)
let sint8_to_sint32 (a:s8) : (s32) = Hacl_UInt32.of_string (Hacl_UInt8.to_string a)

let sint32_to_sint128 (a:s32) : (s128) = Hacl_UInt128.of_string (Hacl_UInt32.to_string a)
let sint32_to_sint64 (a:s32) : (s64) = Hacl_UInt64.of_string (Hacl_UInt32.to_string a)
let sint32_to_sint8  (a:s32) : (s8) = Hacl_UInt8.of_string (Hacl_UInt32.to_string (Hacl_UInt32.logand a(Hacl_UInt32.of_string "255")))

let sint64_to_sint128 (a:s64) : (s128) = Hacl_UInt128.of_string (Hacl_UInt64.to_string a)
let sint64_to_sint32 (a:s64) : (s32) = Hacl_UInt32.of_string (Hacl_UInt64.to_string (Hacl_UInt64.logand a (Hacl_UInt64.of_string "4294967295")))
let sint64_to_sint8  (a:s64) : (s8)  = Hacl_UInt8.of_string (Hacl_UInt64.to_string (Hacl_UInt64.logand a(Hacl_UInt64.of_string "255")))

let sint128_to_sint64 (a:s128) : (s64) = Hacl_UInt64.of_string (Hacl_UInt128.to_string (Hacl_UInt128.logand a (Hacl_UInt128.of_string "0xffffffffffffffff")))
let sint128_to_sint32 (a:s128) : (s32) = Hacl_UInt32.of_string (Hacl_UInt128.to_string (Hacl_UInt128.logand a (Hacl_UInt128.of_string "0xffffffff")))
let sint128_to_sint8  (a:s128) : (s8)  = Hacl_UInt8.of_string (Hacl_UInt128.to_string (Hacl_UInt128.logand a (Hacl_UInt128.of_string "0xff")))
                                                           
let uint64_to_sint128 (a:u64) : s128 = Hacl_UInt128.of_string (FStar_UInt64.to_string a)
let uint64_to_sint64 (a:u64) : s64 = Hacl_UInt64.of_string (FStar_UInt64.to_string a)
let uint64_to_sint32 (a:u64) : s32 = Hacl_UInt32.of_string (FStar_UInt64.to_string (FStar_UInt64.rem a (FStar_UInt64.of_string "4294967295")))
let uint64_to_sint8  (a:u64) : s8  = Hacl_UInt8.of_string  (FStar_UInt64.to_string (FStar_UInt64.rem a (FStar_UInt64.of_string "255")))

let uint32_to_sint128 (a:u32) : s128 = Hacl_UInt128.of_string (string_of_int a)
let uint32_to_sint64 (a:u32) : s64 = Hacl_UInt64.of_string (string_of_int a)
let uint32_to_sint32 (a:u32) : s32 = Hacl_UInt32.of_string (string_of_int a)
let uint32_to_sint8  (a:u32) : s8  = Hacl_UInt8.of_string  (string_of_int (a land 255))

let uint8_to_sint128 (a:u8) : s128 = Hacl_UInt128.of_string (string_of_int a)
let uint8_to_sint64 (a:u8) : s64 = Hacl_UInt64.of_string (string_of_int a)
let uint8_to_sint32 (a:u8) : s32 = Hacl_UInt32.of_string (string_of_int a)
let uint8_to_sint8  (a:u8) : s8  = Hacl_UInt8.of_string  (string_of_int a)
                                                           
