module Interface

/// This is an fsti without an fst, i.e. an interface that we will write our client against.

type w = | W32 | W64

let word = function W32 -> UInt32.t | W64 -> UInt64.t

let add_st w = word w -> word w -> word w
[@ MetaAttribute.specialize ]
val add: #w:w -> add_st w

let mul_st w = word w -> word w -> word w
[@ MetaAttribute.specialize ]
val mul: #w:w -> mul_st w
