module Box.Plain

module KEY = Box.Key

open Crypto.Symmetric.Bytes

abstract type plain_package =
  | PP:
    b:bool ->
    plain_package

val get_flag: pp:plain_package -> GTot bool
let get_flag pp = pp.b

type plain = bytes
abstract type protected_plain (pp:plain_package) (#id:eqtype) (i:id) = bytes

let length (#pp:plain_package) (#id:eqtype) (#i:id) (p:protected_plain pp i) = Seq.length p

val coerce: (#pp:plain_package) -> (#id:eqtype) -> (#i:id) -> (#key_length:nat) -> (kp:KEY.key_package #id key_length i{KEY.hon kp = false \/ ~pp.b}) -> p:plain -> p:protected_plain pp i
let coerce #pp #id #i #key_length kp p =
  p

val repr: #pp:plain_package -> (#id:eqtype) -> (#i:id) -> (#key_length:nat) -> (kp:KEY.key_package #id key_length i{KEY.hon kp = false \/ ~pp.b}) -> p:protected_plain pp i -> plain
let repr #pp #id #i #key_length kp p =
  p
