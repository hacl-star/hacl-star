type 'a type_of_typ = unit
type 'a buffer = unit
let buffer_as_seq _ = raise (Failure "1")
type ('a, 'b, 'c) buffer_readable = unit
let buffer_length _ = raise (Failure "2")
type loc = unit
let loc_none = ()
let loc_union _ = raise (Failure "4")
let loc_buffer _ = raise (Failure "5")
type ('a, 'b) loc_disjoint = unit
type ('a, 'b) loc_includes = unit
type ('a, 'b, 'c) modifies = unit

type t = TUInt8 | TUInt16 | TUInt32 | TUInt64
type typ = TBase of t

type ('a, 'b, 'c) labeled = unit
type ('a, 'b, 'c, 'd) precedes = unit


