module Interface

/// This is an fsti without an fst, i.e. an interface that we will write our client against.

type w = | W32 | W64

inline_for_extraction
let word = function W32 -> UInt32.t | W64 -> UInt64.t

inline_for_extraction
let add_st w = word w -> word w -> word w
[@ MetaAttribute.specialize ]
val add: #w:w -> add_st w

inline_for_extraction
let mul_st w = word w -> word w -> word w
[@ MetaAttribute.specialize ]
val mul: #w:w -> mul_st w
