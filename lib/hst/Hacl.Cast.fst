module Hacl.Cast

module U8  = Hacl.UInt8
module U32 = Hacl.UInt32
module U64 = Hacl.UInt64

let op_At_Percent = FStar.Int.op_At_Percent

(** Uints to Uints **)
assume val uint8_to_uint64: a:U8.t -> Tot (b:U64.t{U64.v b = U8.v a})
assume val uint8_to_uint32: a:U8.t -> Tot (b:U32.t{U32.v b = U8.v a})

assume val uint32_to_uint64: a:U32.t -> Tot (b:U64.t{U64.v b = U32.v a})
assume val uint32_to_uint8 : a:U32.t -> Tot (b:U8.t{U8.v b = U32.v a % pow2 8})

assume val uint64_to_uint32: a:U64.t -> Tot (b:U32.t{U32.v b = U64.v a % pow2 32})
assume val uint64_to_uint8 : a:U64.t -> Tot (b:U8.t{U8.v b = U64.v a % pow2 8})
