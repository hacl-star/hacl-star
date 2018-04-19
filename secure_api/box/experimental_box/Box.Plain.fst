module Box.Plain

module KEY = Box.Key

open FStar.Endianness

noeq type plain_package =
  | PP:
    flag:Type0 ->
    valid_length:(nat -> bool) ->
    plain_package

type plain (pp:plain_package) = p:bytes{pp.valid_length (Seq.length p)}
abstract type protected_plain (pp:plain_package) (#id:eqtype) (i:id) = plain pp

val length: (#pp:plain_package) -> (#id:eqtype) -> (#i:id) -> (p:protected_plain pp i) -> n:nat{pp.valid_length n}
let length (#pp:plain_package) (#id:eqtype) (#i:id) (p:protected_plain pp i) =
  Seq.length p

val coerce: (#pp:plain_package) -> #key_length:(n:nat{n<=32}) -> (#id:eqtype) -> (#i:id) -> (#key_type:(id -> Type0)) -> (kp:KEY.key_package #id key_length key_type) -> (key:key_type i{KEY.(kp.hon) key == false \/ ~pp.flag}) -> p:plain pp -> p:protected_plain pp i
let coerce #pp #key_length #id #i #kt kp key p =
  p

val repr: (#pp:plain_package) -> #key_length:(n:nat{n<=32}) -> (#id:eqtype) -> (#i:id) -> (#key_type:(id -> Type0)) -> (kp:KEY.key_package #id key_length key_type) -> (key:key_type i{KEY.(kp.hon) key == false \/ ~pp.flag}) -> p:protected_plain pp i -> p:plain pp
let repr #pp #key_length #id #i #kt kp key p =
  p
