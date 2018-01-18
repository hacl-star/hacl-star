(* This is a hand-written implementation of LowCProvider.fst. *)
open CryptoTypes

type aead_state

type aes_impl =
  | HaclAES
  | ValeAES

external ocaml_AEAD_create: aead_cipher -> aes_impl -> string -> aead_state = "ocaml_AEAD_create"
external ocaml_AEAD_encrypt: aead_state -> string -> string -> string -> string = "ocaml_AEAD_encrypt"
external ocaml_AEAD_decrypt: aead_state -> string -> string -> string -> string option = "ocaml_AEAD_decrypt"

let aead_create = ocaml_AEAD_create
let aead_encrypt = ocaml_AEAD_encrypt
let aead_decrypt = ocaml_AEAD_decrypt
