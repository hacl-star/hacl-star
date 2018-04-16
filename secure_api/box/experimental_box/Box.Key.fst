module Box.Key

open FStar.Bytes

// Definition KEY package
noeq type key_package (#id:eqtype) (#key_length:u32) (key_type:(id -> u32 -> Type0)) =
  | KP:
  hon: (#i:id -> key_type i key_length -> bool) ->
  get: (#i:id -> k:key_type i key_length{hon k = false} -> lbytes32 key_length) ->
  gen: (i:id -> key_type i key_length) ->
  set: (i:id -> lbytes32 key_length -> key_type i key_length) ->
  key_package #id #key_length key_type
