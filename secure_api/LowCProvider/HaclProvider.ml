(* This is a hand-written implementation of HaclProvider.fst. *)

external ocaml_crypto_scalarmult: string -> string -> string -> unit = "ocaml_crypto_scalarmult"

let crypto_scalarmult secret point =
  let out = String.make 32 '\000' in
  ocaml_crypto_scalarmult out secret point;
  out
