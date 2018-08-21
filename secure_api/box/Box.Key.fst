module Box.Key

open FStar.HyperStack
open FStar.HyperStack.ST

open FStar.Endianness
open Box.Index

// Definition KEY package
noeq type key_package (ip:index_package) =
  | KP:
  flag: Type0 ->
  key_length:(n:nat{n<=32}) ->
  key_type:(id ip  -> Type0) ->
  getGT: (#i:id ip -> k:key_type i -> GTot (lbytes key_length)) ->
  leak: (#i:id ip{corrupt i \/ ~flag} -> k:key_type i -> (raw:lbytes key_length{raw = getGT k})) ->
  gen: (i:id ip -> k:key_type i) ->
  coerce: (i:id ip{~flag \/ corrupt i} -> raw:lbytes key_length -> (k:key_type i{raw = getGT k})) ->
  key_package ip

#set-options "--z3rlimit 300 --max_ifuel 1 --max_fuel 0"
val create_key_package:
  (#ip:index_package) ->
  (flag:Type0) ->
  (param_key_length:(n:nat{n<=32})) ->
  (key_type:(id ip -> Type0)) ->
  (param_getGT: (#i:id ip -> k:key_type i -> GTot (lbytes param_key_length))) ->
  (param_leak: (#i:id ip{corrupt i \/ ~flag} -> k:key_type i -> (raw:lbytes param_key_length{raw = param_getGT k}))) ->
  (param_gen: (i:id ip -> k:key_type i)) ->
  (param_coerce: (i:id ip{corrupt i \/ ~flag} -> raw:lbytes param_key_length -> (k:key_type i{raw = param_getGT k}))) ->
  (kp:key_package ip{
    kp.key_length == param_key_length
  })
let create_key_package #ip flag key_length key_type getGT leak gen coerce =
  KP flag key_length key_type getGT leak gen coerce
