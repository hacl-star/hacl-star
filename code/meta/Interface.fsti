module Interface

/// This is an fsti without an fst, i.e. an interface that we will write our client against.

let add_st = int -> int -> int
val add: add_st

let mul_st = int -> int -> int
val mul: mul_st
