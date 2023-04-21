module Interface

/// This is an fsti without an fst, i.e. an interface that we will write our client against.

type w = | W32 | W64

[@ Meta.Attribute.inline_ ]
inline_for_extraction
let word = function W32 -> UInt32.t | W64 -> UInt64.t

inline_for_extraction
let add_st w = word w -> word w -> word w

[@ Meta.Attribute.specialize ]
val add: #w:w -> add_st w

inline_for_extraction
let mul_st w = word w -> word w -> word w
[@ Meta.Attribute.specialize ]
val mul: #w:w -> mul_st w

/// Another example

[@ Meta.Attribute.specialize ]
val key: Type0
[@ Meta.Attribute.specialize ]
val value: Type0
[@ Meta.Attribute.specialize ]
val key_eq: key -> key -> bool

[@ Meta.Attribute.inline_ ]
let a_list = list (key & value)
