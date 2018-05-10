(* This is a hand-written implementation of HaclProvider.fst. *)

type hash_alg =
  | HACL_SHA256
  | HACL_SHA384
  | HACL_SHA512

let hash_size = function
  | HACL_SHA256 -> 32
  | HACL_SHA384 -> 48
  | HACL_SHA512 -> 64

external ocaml_crypto_scalarmult: string -> string -> string = "ocaml_crypto_scalarmult"
external ocaml_crypto_hash: hash_alg -> string -> string = "ocaml_crypto_hash"
external ocaml_crypto_hmac: hash_alg -> string -> string -> string = "ocaml_crypto_hmac"

let crypto_scalarmult secret point =
  ocaml_crypto_scalarmult secret point

let crypto_hash a msg =
  ocaml_crypto_hash a msg

let crypto_hmac a key msg =
  ocaml_crypto_hmac a key msg
