module Box.Plain

open Box.Key
open Box.Index

open FStar.Endianness
open FStar.HyperStack
open FStar.HyperStack.ST

let n32 = (n:nat{n<=32})

noeq type plain_package =
  | PP:
    flag:Type0 ->
    valid_length:(n32 -> bool) ->
    plain_package

type plain (pp:plain_package) = p:bytes{Seq.length p <= 32 /\ pp.valid_length (Seq.length p)}
abstract type protected_plain (pp:plain_package) (i:inst_id) = plain pp

val length: (#pp:plain_package) -> (#i:inst_id) -> (p:protected_plain pp i) -> n:n32{pp.valid_length n}
let length #pp #i p =
  Seq.length p

val coerce: (#rgn:erid) -> (#pp:plain_package) -> ip:index_package rgn -> (i:inst_id{dishonest ip i \/ ~pp.flag}) -> p:plain pp -> p:protected_plain pp i
let coerce #pp #rgn i ip p =
  p

val repr: (#rgn:erid) -> (#pp:plain_package) -> #ip:index_package rgn -> (#i:inst_id{dishonest ip i \/ ~pp.flag}) -> p:protected_plain pp i -> p:plain pp
let repr #rgn #pp #ip #i p =
  p
