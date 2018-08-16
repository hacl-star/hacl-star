module Box.Plain

open Box.Index

open FStar.Endianness
open FStar.HyperStack
open FStar.HyperStack.ST

noeq type plain_package =
  | PP:
    flag:Type0 ->
    valid_plain_length:(nat -> bool) ->
    valid_cipher_length:(nat -> bool) ->
    valid_nonce_length:(nat -> bool) ->
    plain_package

type plain (pp:plain_package) = p:bytes{pp.valid_plain_length (Seq.length p)}
type nonce (pp:plain_package) = p:bytes{pp.valid_nonce_length (Seq.length p)}
type cipher (pp:plain_package) = p:bytes{pp.valid_cipher_length (Seq.length p)}

abstract type protected_plain (#ip:index_package) (pp:plain_package) (i:id ip) = plain pp

val length: (#ip:index_package) -> (#pp:plain_package) -> (#i:id ip) -> (p:protected_plain pp i) -> n:nat{pp.valid_plain_length n}
let length #ip #pp #i p =
  Seq.length p

val coerce: (#ip:index_package) -> (#pp:plain_package) -> (i:id ip{corrupt i \/ ~pp.flag}) -> p:plain pp -> p:protected_plain pp i
let coerce #ip #pp i p =
  p

val repr: (#ip:index_package) -> (#pp:plain_package) -> (#i:id ip{corrupt i \/ ~pp.flag}) -> p:protected_plain pp i -> p:plain pp
let repr #ip #pp #i p =
  p
