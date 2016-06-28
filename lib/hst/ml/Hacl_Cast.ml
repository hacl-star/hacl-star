(** Uints to Uints **)
type u8 = Hacl_UInt8.uint8
type u32 = Hacl_UInt32.uint32
type u64 = Hacl_UInt64.uint64

let uint8_to_uint64 (a:u8) : (u64) = Hacl_UInt64.of_string (Hacl_UInt8.to_string a)
let uint8_to_uint32 (a:u8) : (u32) = Hacl_UInt32.of_string (Hacl_UInt8.to_string a)

let uint32_to_uint64 (a:u32) : (u64) = Hacl_UInt64.of_string (Hacl_UInt32.to_string a)
let uint32_to_uint8  (a:u32) : (u8) = Hacl_UInt8.of_string (Hacl_UInt32.to_string (Hacl_UInt32.logand a(Hacl_UInt32.of_string "255")))

let uint64_to_uint32 (a:u64) : (u32) = Hacl_UInt32.of_string (Hacl_UInt64.to_string (Hacl_UInt64.logand a (Hacl_UInt64.of_string "4294967295")))
let uint64_to_uint8  (a:u64) : (u8)  = Hacl_UInt8.of_string (Hacl_UInt64.to_string (Hacl_UInt64.logand a(Hacl_UInt64.of_string "255")))
