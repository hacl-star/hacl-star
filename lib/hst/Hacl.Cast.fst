module Hacl.Cast

module S8  = Hacl.UInt8
module S32 = Hacl.UInt32
module S64 = Hacl.UInt64
module U32 = FStar.UInt32

(** Uints to Sints **)
assume val sint8_to_sint64: a:S8.t -> Tot (b:S64.t{S64.v b = S8.v a})
assume val sint8_to_sint32: a:S8.t -> Tot (b:S32.t{S32.v b = S8.v a})

assume val sint32_to_sint64: a:S32.t -> Tot (b:S64.t{S64.v b = S32.v a})
assume val sint32_to_sint8 : a:S32.t -> Tot (b:S8.t{S8.v b = S32.v a % pow2 8})

assume val sint64_to_sint32: a:S64.t -> Tot (b:S32.t{S32.v b = S64.v a % pow2 32})
assume val sint64_to_sint8 : a:S64.t -> Tot (b:S8.t{S8.v b = S64.v a % pow2 8})

assume val uint64_to_sint64: a:UInt64.t -> Tot (b:S64.t{S64.v b = UInt64.v a})
assume val uint64_to_sint32: a:UInt64.t -> Tot (b:S32.t{S32.v b = UInt64.v a % pow2 32})
assume val uint64_to_sint8: a:UInt64.t -> Tot (b:S8.t{S8.v b = UInt64.v a % pow2 8})

assume val uint32_to_sint64: a:UInt32.t -> Tot (b:S64.t{S64.v b = UInt32.v a})
assume val uint32_to_sint32: a:UInt32.t -> Tot (b:S32.t{S32.v b = UInt32.v a % pow2 32})
assume val uint32_to_sint8: a:UInt32.t -> Tot (b:S8.t{S8.v b = UInt32.v a % pow2 8})

assume val uint8_to_sint64: a:UInt8.t -> Tot (b:S64.t{S64.v b = UInt8.v a})
assume val uint8_to_sint32: a:UInt8.t -> Tot (b:S32.t{S32.v b = UInt8.v a % pow2 32})
assume val uint8_to_sint8: a:UInt8.t -> Tot (b:S8.t{S8.v b = UInt8.v a % pow2 8})
