module Test.Bytes

open FStar.HyperStack.ST

open EverCrypt
open EverCrypt.Bytes

open Test.Vectors

#set-options "--admit_smt_queries true"

val discard: bool -> St unit
let discard _ = ()
let print h s = discard (IO.debug_print_string ("["^ h ^"] "^ s ^"\n"))

let success h = print h "Success"; true

let failure h e = print h e; false

val test_chacha20_poly1305: v:aead_vector{v.cipher == CHACHA20_POLY1305} -> St bool
let test_chacha20_poly1305 v =
  let open FStar.Bytes in
  let h = "Chacha20-Poly1305 bytes" in
  let key        = bytes_of_hex v.key in
  let iv         = bytes_of_hex v.iv in
  let aad        = bytes_of_hex v.aad in
  let tag        = bytes_of_hex v.tag in
  let plaintext  = bytes_of_hex v.plaintext in
  let ciphertext = bytes_of_hex v.ciphertext in
  let open EverCrypt.Bytes in
  let { cipher=ciphertext'; tag=tag'} = chacha20_poly1305_encrypt plaintext aad key iv in
  if ciphertext' = ciphertext && tag' = tag then
    match chacha20_poly1305_decrypt ciphertext' tag' aad key iv with
    | Correct plaintext' ->
      if plaintext' = plaintext then success h
      else (failure h "Decryption error: plaintext doesn't match")
    | Error ->
      failure h "Decryption error: invalid ciphertext or tag"
  else failure h "Encryption error: ciphertext doesn't match"

val test_aead: list aead_vector -> St bool
let rec test_aead = function
  | [] -> true
  | v :: vs ->
    match v.cipher with
    | CHACHA20_POLY1305 ->
      let this = test_chacha20_poly1305 v in
      let rest = test_aead vs in
      this && rest
    | _ -> test_aead vs

val main: unit -> St unit
let main () =
  let res = test_aead aead_vectors in
  if not res then C.exit 1l
