module Box.Key

open FStar.HyperStack
open FStar.HyperStack.ST

open FStar.Endianness
open Box.Index

// Definition KEY package
noeq type key_package (#rgn:erid) (ip:index_package rgn) (key_length:(n:nat{n<=32})) (key_type:(inst_id  -> Type0)) =
  | KP:
  flag: Type0 ->
  getGT: (#i:inst_id -> k:key_type i -> GTot (lbytes key_length)) ->
  leak: (#i:inst_id{dishonest ip i \/ ~flag} -> k:key_type i -> (raw:lbytes key_length{raw = getGT k})) ->
  gen: (i:inst_id -> k:key_type i) ->
  coerce: (i:inst_id{~flag \/ dishonest ip i} -> raw:lbytes key_length -> (k:key_type i{raw = getGT k})) ->
  key_package #rgn ip key_length key_type

#set-options "--z3rlimit 300 --max_ifuel 1 --max_fuel 0"
//val hon: (#inst_id:eqtype) -> (#key_length:(n:nat{n<=32})) -> (#key_type:(inst_id -> Type0)) -> kp:key_package #inst_id key_length key_type -> (kp_hon:(#i:inst_id -> key_type i -> bool){forall i . kp_hon #i === kp.hon #i})
//let hon #inst_id #key_length #key_type kp = kp.hon
//
//val getGT: (#inst_id:eqtype) -> (#key_length:(n:nat{n<=32})) -> (#key_type:(inst_id -> Type0)) -> kp:key_package #inst_id key_length key_type -> (kp_getGT:(#i:inst_id -> k:key_type i -> GTot (lbytes key_length)){kp_getGT == kp.getGT})
//let getGT #inst_id #key_length #key_type kp = kp.getGT
//
//val cget: (#inst_id:eqtype) -> (#key_length:(n:nat{n<=32})) -> (#key_type:(inst_id -> Type0)) -> kp:key_package #inst_id key_length key_type -> (#i:inst_id -> k:key_type i{kp.hon i k = false} -> (raw:lbytes key_length{raw = kp.getGT i k}))
//let cget #inst_id #key_length #key_type kp = kp.cget
//
//val get: (#inst_id:eqtype) -> (#key_length:(n:nat{n<=32})) -> (#key_type:(inst_id -> Type0)) -> kp:key_package #inst_id key_length key_type -> (#i:inst_id -> k:key_type i -> (raw:lbytes key_length{raw = kp.getGT i k}))
//
//val gen: (#inst_id:eqtype) -> (#key_length:(n:nat{n<=32})) -> (#key_type:(inst_id -> Type0)) -> kp:key_package #inst_id key_length key_type -> (#i:inst_id -> k:key_type i{kp.hon i k = true})
//let gen #inst_id #key_length #key_type kp = kp.gen
//
//val cset: (#inst_id:eqtype) -> (#key_length:(n:nat{n<=32})) -> (#key_type:(inst_id -> Type0)) -> kp:key_package #inst_id key_length key_type -> (#i:inst_id -> raw:lbytes key_length -> (k:key_type i{raw = kp.getGT i k /\ kp.hon i k = false}))
//let cset #inst_id #key_length #key_type kp = kp.cset

#set-options "--z3rlimit 300 --max_ifuel 1 --max_fuel 0"
val create_key_package:
  (#rgn:erid) ->
  (ip:index_package rgn) ->
  (flag:Type0) ->
  (key_length:(n:nat{n<=32})) ->
  (key_type:(inst_id -> Type0)) ->
  (param_getGT: (#i:inst_id -> k:key_type i -> GTot (lbytes key_length))) ->
  (param_leak: (#i:inst_id{dishonest ip i \/ ~flag} -> k:key_type i -> (raw:lbytes key_length{raw = param_getGT k}))) ->
  (param_gen: (i:inst_id -> k:key_type i)) ->
  (param_coerce: (i:inst_id{dishonest ip i \/ ~flag} -> raw:lbytes key_length -> (k:key_type i{raw = param_getGT k}))) ->
  (kp:key_package #rgn ip key_length key_type{True
//    param_hon == hon kp
//    /\ param_hon == kp.hon
//    /\ param_getGT == kp.getGT
//    /\ param_getGT == getGT kp
//    /\ param_cget == cget kp
//    /\ param_gen == gen kp
//    /\ param_cset == cset kp
  })
let create_key_package #rgn ip flag key_length key_type getGT leak gen coerce =
  KP flag getGT leak gen coerce
