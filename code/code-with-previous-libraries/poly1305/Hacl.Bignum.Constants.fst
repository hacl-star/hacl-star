module Hacl.Bignum.Constants

module ST = FStar.HyperStack.ST

open FStar.HyperStack.All

inline_for_extraction let prime = assert_norm(pow2 130 > 5); pow2 130 - 5
inline_for_extraction let word_size = 64
inline_for_extraction let len = 3
inline_for_extraction let limb_size = 44
inline_for_extraction let limb = Hacl.UInt64.t
inline_for_extraction let wide = Hacl.UInt128.t
