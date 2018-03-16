module Box.Key

open Crypto.Symmetric.Bytes

assume val random_bytes: n:nat -> lbytes n

// Definition KEY package
noeq abstract type key_package (#id:Type0) (key_length:nat) (i:id) =
  | KEY:
  k:lbytes key_length ->
  h:bool ->
  key_package #id key_length i

let get (#kl:nat) (#id:Type0) (#i:id) (kp:key_package #id kl i) = kp.k

let gen (key_length:nat) (#id:Type0) (i:id) : (key_package #id key_length i) =
  KEY (random_bytes key_length) true

let set (key_length:nat) (key:lbytes key_length) (#id:Type0) (i:id) : (key_package #id key_length i) = KEY key false

let hon (#kl:nat) (#id:Type0) (#i:id) (kp:key_package #id kl i) = kp.h
