module Hacl.Cast

module U8 = FStar.UInt8
module S8  = Hacl.UInt8
module U32 = FStar.UInt32
module S32 = Hacl.UInt32
module U64 = FStar.UInt64
module S64 = Hacl.UInt64
module S128 = Hacl.UInt128

(** Uints to Sints **)
assume val sint8_to_sint128: a:S8.t -> Tot (b:S128.t{S128.v b = S8.v a})
assume val sint8_to_sint64: a:S8.t -> Tot (b:S64.t{S64.v b = S8.v a})
assume val sint8_to_sint32: a:S8.t -> Tot (b:S32.t{S32.v b = S8.v a})

assume val sint32_to_sint128: a:S32.t -> Tot (b:S128.t{S128.v b = S32.v a})
assume val sint32_to_sint64: a:S32.t -> Tot (b:S64.t{S64.v b = S32.v a})
assume val sint32_to_sint8 : a:S32.t -> Tot (b:S8.t{S8.v b = S32.v a % pow2 8})

assume val sint64_to_sint128: a:S64.t -> Tot (b:S128.t{S128.v b = S64.v a})
assume val sint64_to_sint32: a:S64.t -> Tot (b:S32.t{S32.v b = S64.v a % pow2 32})
assume val sint64_to_sint8 : a:S64.t -> Tot (b:S8.t{S8.v b = S64.v a % pow2 8})

assume val sint128_to_sint64: a:S128.t -> Tot (b:S64.t{S64.v b = S128.v a % pow2 64})
assume val sint128_to_sint32: a:S128.t -> Tot (b:S32.t{S32.v b = S128.v a % pow2 32})
assume val sint128_to_sint8 : a:S128.t -> Tot (b:S8.t{S8.v b = S128.v a % pow2 8})

assume val uint64_to_sint128: a:U64.t -> Tot (b:S128.t{S128.v b = U64.v a})
assume val uint64_to_sint64: a:U64.t -> Tot (b:S64.t{S64.v b = U64.v a})
assume val uint64_to_sint32: a:U64.t -> Tot (b:S32.t{S32.v b = U64.v a % pow2 32})
assume val uint64_to_sint8: a:U64.t -> Tot (b:S8.t{S8.v b = U64.v a % pow2 8})

assume val uint32_to_sint128: a:U32.t -> Tot (b:S128.t{S128.v b = U32.v a})
assume val uint32_to_sint64: a:U32.t -> Tot (b:S64.t{S64.v b = U32.v a})
assume val uint32_to_sint32: a:U32.t -> Tot (b:S32.t{S32.v b = U32.v a})
assume val uint32_to_sint8: a:U32.t -> Tot (b:S8.t{S8.v b = U32.v a % pow2 8})

assume val uint8_to_sint128: a:U8.t -> Tot (b:S128.t{S128.v b = U8.v a})
assume val uint8_to_sint64: a:U8.t -> Tot (b:S64.t{S64.v b = U8.v a})
assume val uint8_to_sint32: a:U8.t -> Tot (b:S32.t{S32.v b = U8.v a})
assume val uint8_to_sint8: a:U8.t -> Tot (b:S8.t{S8.v b = U8.v a})
