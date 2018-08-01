module Box.Key

open FStar.HyperStack
open FStar.HyperStack.ST

open FStar.Endianness
open Box.Index

// Definition KEY package
noeq type key_package (ip:index_package) (key_length:(n:nat{n<=32})) (key_type:(inst_id  -> Type0)) =
  | KP:
  flag: Type0 ->
  getGT: (#i:inst_id -> k:key_type i -> GTot (lbytes key_length)) ->
  leak: (#i:inst_id{dishonest ip i \/ ~flag} -> k:key_type i -> (raw:lbytes key_length{raw = getGT k})) ->
  gen: (i:inst_id -> k:key_type i) ->
  coerce: (i:inst_id{~flag \/ dishonest ip i} -> raw:lbytes key_length -> (k:key_type i{raw = getGT k})) ->
  key_package ip key_length key_type

#set-options "--z3rlimit 300 --max_ifuel 1 --max_fuel 0"
val create_key_package:
  (ip:index_package) ->
  (flag:Type0) ->
  (key_length:(n:nat{n<=32})) ->
  (key_type:(inst_id -> Type0)) ->
  (param_getGT: (#i:inst_id -> k:key_type i -> GTot (lbytes key_length))) ->
  (param_leak: (#i:inst_id{dishonest ip i \/ ~flag} -> k:key_type i -> (raw:lbytes key_length{raw = param_getGT k}))) ->
  (param_gen: (i:inst_id -> k:key_type i)) ->
  (param_coerce: (i:inst_id{dishonest ip i \/ ~flag} -> raw:lbytes key_length -> (k:key_type i{raw = param_getGT k}))) ->
  (kp:key_package ip key_length key_type{True
//    param_hon == hon kp
//    /\ param_hon == kp.hon
//    /\ param_getGT == kp.getGT
//    /\ param_getGT == getGT kp
//    /\ param_cget == cget kp
//    /\ param_gen == gen kp
//    /\ param_cset == cset kp
  })
let create_key_package ip flag key_length key_type getGT leak gen coerce =
  KP flag getGT leak gen coerce
