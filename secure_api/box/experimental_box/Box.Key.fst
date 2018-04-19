module Box.Key

open FStar.Endianness

// Definition KEY package
noeq type key_package (#id:eqtype) (key_length:(n:nat{n<=32})) (key_type:(id  -> Type0)) =
  | KP:
  hon: (#i:id -> key_type i -> bool) ->
  get: (#i:id -> k:key_type i{hon k = false} -> lbytes key_length) ->
  gen: (i:id -> key_type i) ->
  set: (i:id -> lbytes key_length -> key_type i) ->
  key_package #id key_length key_type
