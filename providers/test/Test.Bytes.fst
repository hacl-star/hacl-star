module Test.Bytes

open FStar.HyperStack.ST

open EverCrypt
open EverCrypt.Bytes
open Test.Vectors
open LowStar.BufferOps

open C.String

module B = LowStar.Buffer

#reset-options "--max_fuel 0 --max_ifuel 0 --using_facts_from '* -Test.Vectors'"

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

type vec8 = Lowstarize.lbuffer UInt8.t

let of_vec8 v =
  let Lowstarize.LB len buf = v in
  B.recall buf;
  FStar.Bytes.of_buffer len buf

type aead_vector = cipher * vec8 * vec8 * vec8 * vec8 * vec8 * vec8

let test_chacha20_poly1305 (vec:aead_vector) : Stack bool
  (requires fun _ -> True)
  (ensures  fun h0 _ h1 -> B.modifies (B.loc_none) h0 h1)
=
  let cipher, key, iv, aad, tag, plaintext, ciphertext = vec in
  let open FStar.Bytes in
  let h = !$"Chacha20-Poly1305 bytes" in
  let key        = of_vec8 key in
  let iv         = of_vec8 iv in
  let aad        = of_vec8 aad in
  let tag        = of_vec8 tag in
  let plaintext  = of_vec8 plaintext in
  let ciphertext = of_vec8 ciphertext in
  let open EverCrypt.Bytes in
  if FStar.Bytes.(length key <> 32 || length iv <> 12 || length tag <> 16) then
   failure h !$"Incorrect input lengths in test vector"
  else
    let { cipher=ciphertext'; tag=tag'} = chacha20_poly1305_encrypt plaintext aad key iv in
    if ciphertext' = ciphertext && tag' = tag then
      match chacha20_poly1305_decrypt ciphertext' tag' aad key iv with
      | Correct plaintext' ->
        if plaintext' = plaintext then success h
        else (failure h !$"Decryption error: plaintext doesn't match")
      | _ ->
        failure h !$"Decryption error: invalid ciphertext or tag"
    else failure h !$"Encryption error: ciphertext doesn't match"

let rec test_aead (b:Lowstarize.lbuffer aead_vector) : St bool =
  let open FStar.Integers in
  let Lowstarize.LB len vecs = b in
  push_frame();
  let b = B.alloca true 1ul in
  B.recall vecs;
  let h0 = HyperStack.ST.get() in
  C.Loops.for 0ul len (fun h i -> B.live h vecs /\ B.live h b /\ B.modifies (B.loc_buffer b) h0 h)
  (fun i ->
    let v = vecs.(i) in
    match v with
    | CHACHA20_POLY1305, _, _, _, _, _, _ ->
      let this = test_chacha20_poly1305 v in
      let rest = b.(0ul) in
      b.(0ul) <- this && rest
    | _ -> ()
  );
  let res = b.(0ul) in
  pop_frame();
  res

val main: unit -> St unit
let main () =
  let aead_vectors = Test.Vectors.aead_vectors_low in
  let res = test_aead aead_vectors in
  if not res then C.exit 1l
