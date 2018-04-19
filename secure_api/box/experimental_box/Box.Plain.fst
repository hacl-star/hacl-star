module Box.Plain

module KEY = Box.Key

open FStar.Endianness

abstract type plain_package =
  | PP:
    b:bool ->
    plain_package

val get_flag: pp:plain_package -> GTot bool
let get_flag pp = pp.b

type plain = bytes
abstract type protected_plain (pp:plain_package) (#id:eqtype) (i:id) = bytes

let length (#pp:plain_package) (#id:eqtype) (#i:id) (p:protected_plain pp i) =
  //length_reveal p;
  //UInt32.uint_to_t (Seq.length p)
  Seq.length p

val coerce: (#pp:plain_package) -> #key_length:(n:nat{n<=32}) -> (#id:eqtype) -> (#i:id) -> (#key_type:(id -> Type0)) -> (kp:KEY.key_package #id key_length key_type) -> (key:key_type i{KEY.(kp.hon) key == false \/ ~pp.b}) -> p:plain -> p:protected_plain pp i
let coerce #pp #key_length #id #i #kt kp key p =
  p

val repr: (#pp:plain_package) -> #key_length:(n:nat{n<=32}) -> (#id:eqtype) -> (#i:id) -> (#key_type:(id -> Type0)) -> (kp:KEY.key_package #id key_length key_type) -> (key:key_type i{KEY.(kp.hon) key == false \/ ~pp.b}) -> p:protected_plain pp i -> p:plain
let repr #pp #key_length #id #i #kt kp key p =
  p
