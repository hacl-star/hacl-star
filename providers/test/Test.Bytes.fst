module Test.Bytes

open FStar.HyperStack.ST

open EverCrypt
open EverCrypt.Bytes
open Test.Vectors
open LowStar.BufferOps
open FStar.Integers

module B = LowStar.Buffer

// TODO: remove this
#set-options "--admit_smt_queries true"

val discard: bool -> St unit
let discard _ = ()
let print h s = discard (FStar.IO.debug_print_string ("["^ h ^"] "^ s ^"\n"))

let success h = print h "Success"; true

let failure h e = print h e; false

val test_chacha20_poly1305: v:aead_vector{v.cipher == CHACHA20_POLY1305} -> St bool
let test_chacha20_poly1305 v =
  let open FStar.Bytes in
  let h = "Chacha20-Poly1305 bytes" in
  let key        = of_buffer v.key_len v.key in
  let iv         = of_buffer v.iv_len v.iv in
  let aad        = of_buffer v.aad_len v.aad in
  let tag        = of_buffer v.tag_len v.tag in
  let plaintext  = of_buffer v.plaintext_len v.plaintext in
  let ciphertext = of_buffer v.ciphertext_len v.ciphertext in
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

// TODO: switch to a C loop
val test_aead: len:UInt32.t -> b:B.buffer aead_vector { B.len b = len } -> St bool
let rec test_aead len b =
  if len = 0ul then
    true
  else
    let v = b.(0ul) in
    match v.cipher with
    | CHACHA20_POLY1305 ->
      let this = test_chacha20_poly1305 v in
      let rest = test_aead (len - 1ul) (B.offset b 1ul) in
      this && rest
    | _ -> test_aead (len - 1ul) (B.offset b 1ul)

val main: unit -> St unit
let main () =
  let res = test_aead aead_vectors_len aead_vectors in
  if not res then C.exit 1l
