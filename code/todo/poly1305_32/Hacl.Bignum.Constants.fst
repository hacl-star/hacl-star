module Hacl.Bignum.Constants

module ST = FStar.HyperStack.ST

open FStar.HyperStack.All

inline_for_extraction let prime = assert_norm(pow2 130 > 5); pow2 130 - 5
inline_for_extraction let word_size : pos = 32
inline_for_extraction let len : pos = 5
inline_for_extraction let limb_size : pos = 26
inline_for_extraction let limb = Hacl.UInt32.t
inline_for_extraction let wide = Hacl.UInt64.t
