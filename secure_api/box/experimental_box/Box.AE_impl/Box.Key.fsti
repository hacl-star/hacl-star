module Box.Key

open FStar.Endianness

// Definition KEY package
noeq abstract type key_package (#id:eqtype) (key_length:(n:nat{n<=32})) (key_type:(id  -> Type0)) =
  | KP:
  hon: (i:id -> key_type i -> bool) ->
  getGT: (i:id -> k:key_type i -> GTot (lbytes key_length)) ->
  cget: (i:id -> k:key_type i{hon i k = false} -> (raw:lbytes key_length{raw = getGT i k})) ->
  get: (i:id -> k:key_type i -> (raw:lbytes key_length{raw = getGT i k})) ->
  gen: (i:id -> k:key_type i{hon i k = true}) ->
  cset: (i:id -> raw:lbytes key_length -> (k:key_type i{raw = getGT i k /\ hon i k = false})) ->
  set: (i:id -> raw:lbytes key_length -> (k:key_type i{raw = getGT i k /\ hon i k = true})) ->
  key_package #id key_length key_type

val hon: (#id:eqtype) -> (#key_length:(n:nat{n<=32})) -> (#key_type:(id -> Type0)) -> kp:key_package #id key_length key_type -> (kp_hon:(i:id -> key_type i -> bool){kp_hon == kp.hon})

val getGT: (#id:eqtype) -> (#key_length:(n:nat{n<=32})) -> (#key_type:(id -> Type0)) -> kp:key_package #id key_length key_type -> (kp_getGT:(i:id -> k:key_type i -> GTot (lbytes key_length)){kp_getGT == kp.getGT})

val cget: (#id:eqtype) -> (#key_length:(n:nat{n<=32})) -> (#key_type:(id -> Type0)) -> kp:key_package #id key_length key_type -> (i:id -> k:key_type i{kp.hon i k = false} -> (raw:lbytes key_length{raw = kp.getGT i k}))

val get: (#id:eqtype) -> (#key_length:(n:nat{n<=32})) -> (#key_type:(id -> Type0)) -> kp:key_package #id key_length key_type -> (i:id -> k:key_type i -> (raw:lbytes key_length{raw = kp.getGT i k}))

val gen: (#id:eqtype) -> (#key_length:(n:nat{n<=32})) -> (#key_type:(id -> Type0)) -> kp:key_package #id key_length key_type -> (i:id -> k:key_type i{kp.hon i k = true})

val cset: (#id:eqtype) -> (#key_length:(n:nat{n<=32})) -> (#key_type:(id -> Type0)) -> kp:key_package #id key_length key_type -> (i:id -> raw:lbytes key_length -> (k:key_type i{raw = kp.getGT i k /\ kp.hon i k = false}))

val set: (#id:eqtype) -> (#key_length:(n:nat{n<=32})) -> (#key_type:(id -> Type0)) -> kp:key_package #id key_length key_type -> (i:id -> raw:lbytes key_length -> (k:key_type i{raw = kp.getGT i k /\ kp.hon i k = true}))

#set-options "--z3rlimit 300 --max_ifuel 1 --max_fuel 0"
val create_key_package:
  (#id:eqtype) ->
  (key_length:(n:nat{n<=32})) ->
  (key_type:(id -> Type0)) ->
  (param_hon:(i:id -> key_type i -> bool)) ->
  (param_getGT: (i:id -> k:key_type i -> GTot (lbytes key_length))) ->
  (param_cget: (i:id -> k:key_type i{param_hon i k = false} -> (raw:lbytes key_length{raw = param_getGT i k}))) ->
  (param_get: (i:id -> k:key_type i -> (raw:lbytes key_length{raw = param_getGT i k}))) ->
  (param_gen: (i:id -> k:key_type i{param_hon i k = true})) ->
  (param_cset: (i:id -> raw:lbytes key_length -> (k:key_type i{raw = param_getGT i k /\ param_hon i k = false}))) ->
  (param_set: (i:id -> raw:lbytes key_length -> (k:key_type i{raw = param_getGT i k /\ param_hon i k = true}))) ->
  (kp:key_package #id key_length key_type{
    param_hon == hon kp
    /\ param_hon == kp.hon
    /\ param_getGT == kp.getGT
    /\ param_getGT == getGT kp
    /\ param_cget == cget kp
    /\ param_get == get kp
    /\ param_gen == gen kp
    /\ param_cset == cset kp
    /\ param_set == set kp
  })
