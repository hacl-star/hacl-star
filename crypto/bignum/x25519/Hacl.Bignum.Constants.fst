module Hacl.Bignum.Constants

inline_for_extraction let prime = assert_norm(pow2 255 > 19); pow2 255 - 19
inline_for_extraction let word_size = 64
inline_for_extraction let len = 5
inline_for_extraction let limb_size = 51
