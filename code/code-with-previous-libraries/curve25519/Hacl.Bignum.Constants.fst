module Hacl.Bignum.Constants

module ST = FStar.HyperStack.ST

open FStar.HyperStack.All

inline_for_extraction let prime:pos = assert_norm(pow2 255 > 19); pow2 255 - 19
inline_for_extraction let word_size = 64
inline_for_extraction let len = 5
inline_for_extraction let limb_size = 51
inline_for_extraction let keylen = 32
inline_for_extraction let limb = Hacl.UInt64.t
inline_for_extraction let wide = Hacl.UInt128.t
inline_for_extraction let a24 = assert_norm(121665 < pow2 64); 121665uL
