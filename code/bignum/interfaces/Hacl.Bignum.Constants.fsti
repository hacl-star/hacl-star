module Hacl.Bignum.Constants

module ST = FStar.HyperStack.ST

open FStar.HyperStack.All

inline_for_extraction val prime : p:pos{p > 1}
inline_for_extraction val word_size : w:int{w >= 8} // At least one byte
inline_for_extraction val len : l:int{l > 1} // At least one limb
inline_for_extraction val limb_size: ls:int{ls > 0 /\ ls < word_size} // Sparse
inline_for_extraction val keylen: l:pos
inline_for_extraction val limb: Type0
inline_for_extraction val wide: Type0
