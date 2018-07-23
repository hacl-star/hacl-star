module Test.Bytes

open FStar.HyperStack.ST

open EverCrypt
open EverCrypt.Bytes
open Test.Vectors
open LowStar.BufferOps

open C.String

module B = LowStar.Buffer

// TODO: remove this
#set-options "--admit_smt_queries true"

let success h =
  print !$"[";
  print h;
  print !$"] ";
  print !$"SUCCESS\n";
  true

let failure h msg =
  print !$"[";
  print h;
  print !$"] ";
  print !$"FAILURE:";
  print msg;
  print !$"\n";
  false

let vec8 = B.buffer UInt8.t * UInt32.t
let of_vec8 (v: vec8) =
  let buf, len = v in
  FStar.Bytes.of_buffer len buf

type aead_vector = cipher * vec8 * vec8 * vec8 * vec8 * vec8 * vec8

let test_chacha20_poly1305 (arg: aead_vector) =
  let cipher, key, iv, aad, tag, plaintext, ciphertext = arg in
  let open FStar.Bytes in
  let h = !$"Chacha20-Poly1305 bytes" in
  let key        = of_vec8 key in
  let iv         = of_vec8 iv in
  let aad        = of_vec8 aad in
  let tag        = of_vec8 tag in
  let plaintext  = of_vec8 plaintext in
  let ciphertext = of_vec8 ciphertext in
  let open EverCrypt.Bytes in
  let { cipher=ciphertext'; tag=tag'} = chacha20_poly1305_encrypt plaintext aad key iv in
  if ciphertext' = ciphertext && tag' = tag then
    match chacha20_poly1305_decrypt ciphertext' tag' aad key iv with
    | Correct plaintext' ->
      if plaintext' = plaintext then success h
      else (failure h !$"Decryption error: plaintext doesn't match")
    | Error ->
      failure h !$"Decryption error: invalid ciphertext or tag"
  else failure h !$"Encryption error: ciphertext doesn't match"

// TODO: switch to a C loop
val test_aead: len:UInt32.t -> b:B.buffer aead_vector { B.len b = len } -> St bool
let rec test_aead len b =
  let open FStar.Integers in
  if len = 0ul then
    true
  else
    let v = b.(0ul) in
    match v with
    | CHACHA20_POLY1305, _, _, _, _, _, _ ->
      let this = test_chacha20_poly1305 v in
      let rest = test_aead (len - 1ul) (B.offset b 1ul) in
      this && rest
    | _ -> test_aead (len - 1ul) (B.offset b 1ul)

val main: unit -> St unit
let main () =
  let aead_vectors, aead_vectors_len = Test.Vectors.aead_vectors_low in
  let res = test_aead aead_vectors_len aead_vectors in
  if not res then C.exit 1l
