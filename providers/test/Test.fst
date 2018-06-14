module Test

module B = FStar.Buffer
module U32 = FStar.UInt32

open FStar.HyperStack.ST
open FStar.Bytes
open EverCrypt.Helpers
open EverCrypt.AutoConfig

open Test.Vectors
open FStar.UInt32

#set-options "--admit_smt_queries true"

type lbuffer (l:nat) = b:B.buffer UInt8.t {Buffer.length b == l}

private val store_bytes_aux: len:U32.t -> buf:lbuffer (U32.v len)
  -> i:U32.t{i <=^ len} -> b:lbytes (v len) -> St unit
let rec store_bytes_aux len buf i b =
  if i <^ len then
   begin
   B.upd buf i (Bytes.index b (v i));
   store_bytes_aux len buf (i +^ 1ul) b
   end

val store_bytes: l:U32.t -> buf:lbuffer (v l) -> b:lbytes (v l) -> St unit
let store_bytes l buf b = store_bytes_aux l buf 0ul b

val buffer_of_hex: string -> StackInline (B.buffer UInt8.t)
 (requires fun _ -> True)
 (ensures  fun _ _ _ -> True)
let buffer_of_hex s =
  let b = bytes_of_hex s in
  let l = Bytes.len b in
  let buf = B.create 0x00uy l in
  store_bytes l buf b;
  buf

val buffer_of_string: string -> StackInline (B.buffer UInt8.t)
 (requires fun _ -> True)
 (ensures  fun _ _ _ -> True)
let buffer_of_string s =
  let b = bytes_of_string s in
  let l = Bytes.len b in
  let buf = B.create 0x00uy l in
  store_bytes l buf b;
  buf

val buffer_of_strings: U32.t -> string -> StackInline (B.buffer UInt8.t)
 (requires fun _ -> True)
 (ensures  fun _ _ _ -> True)
let buffer_of_strings n s =
  let b = bytes_of_string s in
  let l = Bytes.len b in
  let buf = B.rcreate HyperStack.root 0x00uy (l *^ n) in
  C.Loops.for 0ul n (fun _ _ -> True)
    (fun i -> store_bytes l (B.offset buf (i *^ l)) b);
  buf

/// SHA2-256

val test_sha256: v:hash_vector{v.hash_alg == SHA256} -> St unit
let test_sha256 v =
  push_frame();

  let output_len = 32ul in
  let output = B.create 0uy output_len in

  let repeat   = U32.uint_to_t v.repeat in
  let len      = U32.mul (Bytes.len (bytes_of_string v.input)) repeat in
  let input    = buffer_of_strings repeat v.input in
  let expected = buffer_of_hex v.output in

  (* Allocate memory for state *)
  let ctx = B.create 0ul U32.(64ul +^ 64ul +^ 8ul +^ 1ul) in

  (* Compute the number of blocks to process *)
  let size_block = 64ul in
  let n = U32.div len size_block in
  let r = U32.rem len size_block in

  (* Get all full blocks and the last block *)
  let input_blocks = B.sub input 0ul (n *%^ size_block) in
  let input_last   = B.sub input (n *%^ size_block) r in

  (* Call the hash function incrementally *)
  EverCrypt.sha256_init ctx;
  EverCrypt.sha256_update_multi ctx input_blocks n;
  EverCrypt.sha256_update_last ctx input_last r;
  EverCrypt.sha256_finish ctx output;

  // Non-incrementally:
  // EverCrypt.sha256_hash output input len

  (* Display the result *)
  TestLib.compare_and_print !$"of SHA256" expected output 32ul;

  pop_frame()

/// SHA2-384

val test_sha384: v:hash_vector{v.hash_alg == SHA384} -> St unit
let test_sha384 v =
  push_frame();

  let output_len = 48ul in
  let output = B.create 0uy output_len in

  let repeat   = U32.uint_to_t v.repeat in
  let len      = U32.mul (Bytes.len (bytes_of_string v.input)) repeat in
  let input    = buffer_of_strings repeat v.input in
  let expected = buffer_of_hex v.output in

  (* Allocate memory for state *)
  let ctx = B.create 0uL U32.(80ul +^ 80ul +^ 8ul +^ 1ul) in

  (* Compute the number of blocks to process *)
  let size_block = 128ul in
  let n = U32.div len size_block in
  let r = U32.rem len size_block in

  (* Get all full blocks and the last block *)
  let input_blocks = B.sub input 0ul (n *%^ size_block) in
  let input_last   = B.sub input (n *%^ size_block) r in

  (* Call the hash function incrementally *)
  EverCrypt.sha384_init ctx;
  EverCrypt.sha384_update_multi ctx input_blocks n;
  EverCrypt.sha384_update_last ctx input_last r;
  EverCrypt.sha384_finish ctx output;

  // Non-incrementally:
  // EverCrypt.sha384_hash output input len

  (* Display the result *)
  TestLib.compare_and_print !$"of SHA384" expected output 32ul;

  pop_frame()

/// SHA2-512

val test_sha512: v:hash_vector{v.hash_alg == SHA512} -> St unit
let test_sha512 v =
  push_frame();

  let output_len = 64ul in
  let output = B.create 0uy output_len in

  let repeat   = U32.uint_to_t v.repeat in
  let len      = U32.mul (Bytes.len (bytes_of_string v.input)) repeat in
  let input    = buffer_of_strings repeat v.input in
  let expected = buffer_of_hex v.output in

  (* Allocate memory for state *)
  let ctx = B.create 0uL U32.(80ul +^ 80ul +^ 8ul +^ 1ul) in

  (* Compute the number of blocks to process *)
  let size_block = 128ul in
  let n = U32.div len size_block in
  let r = U32.rem len size_block in

  (* Get all full blocks and the last block *)
  let input_blocks = B.sub input 0ul (n *%^ size_block) in
  let input_last   = B.sub input (n *%^ size_block) r in

  (* Call the hash function incrementally *)
  EverCrypt.sha512_init ctx;
  EverCrypt.sha512_update_multi ctx input_blocks n;
  EverCrypt.sha512_update_last ctx input_last r;
  EverCrypt.sha512_finish ctx output;

  // Non-incrementally:
  // EverCrypt.sha512_hash output input len

  (* Display the result *)
  TestLib.compare_and_print !$"of SHA512" expected output 32ul;

  pop_frame()

/// ChaCha20-Poly1305

val test_chacha20_poly1305: v:aead_vector{v.cipher == CHACHA20_POLY1305} -> St unit
let test_chacha20_poly1305 v =
  push_frame();

  let key        = buffer_of_hex v.key in
  let iv         = buffer_of_hex v.iv in
  let aad        = buffer_of_hex v.aad in
  let tag        = buffer_of_hex v.tag in
  let plaintext  = buffer_of_hex v.plaintext in
  let ciphertext = buffer_of_hex v.ciphertext in

  let plaintext_len = Bytes.len (bytes_of_hex v.ciphertext) in
  let aad_len       = Bytes.len (bytes_of_hex v.aad) in
  let plaintext'    = B.create 0uy plaintext_len in
  let ciphertext'   = B.create 0uy plaintext_len in
  let tag'          = B.create 0uy 16ul in

  EverCrypt.chacha20_poly1305_encrypt key iv aad aad_len plaintext plaintext_len ciphertext' tag';
  TestLib.compare_and_print !$"of Chacha20-Poly1305 cipher" ciphertext ciphertext' plaintext_len;
  TestLib.compare_and_print !$"of Chacha20-Poly1305 tag" tag tag' 16ul;

  match EverCrypt.chacha20_poly1305_decrypt key iv aad aad_len plaintext' plaintext_len ciphertext tag with
  | 1ul ->
    TestLib.compare_and_print !$"of Chacha20-Poly1305 plaintext" plaintext plaintext' plaintext_len
  | _ ->
    C.String.print !$"Decryption failed!\n"; C.portable_exit 1l;

  pop_frame()

val test_aes128_gcm: v:aead_vector{v.cipher == AES_128_GCM} -> St unit
let test_aes128_gcm v =
  push_frame();

  let key        = buffer_of_hex v.key in
  let iv         = buffer_of_hex v.iv in
  let aad        = buffer_of_hex v.aad in
  let tag        = buffer_of_hex v.tag in
  let plaintext  = buffer_of_hex v.plaintext in
  let ciphertext = buffer_of_hex v.ciphertext in

  let plaintext_len = Bytes.len (bytes_of_hex v.ciphertext) in
  let aad_len       = Bytes.len (bytes_of_hex v.aad) in
  let plaintext'    = B.create 0uy plaintext_len in
  let ciphertext'   = B.create 0uy plaintext_len in
  let tag'          = B.create 0uy 16ul in

  EverCrypt.aes128_gcm_encrypt key iv aad aad_len plaintext plaintext_len ciphertext' tag';
  TestLib.compare_and_print !$"of AES-GCM 128 cipher" ciphertext ciphertext' plaintext_len;
  TestLib.compare_and_print !$"of AES-GCM 128 tag" tag tag' 16ul;

  match EverCrypt.aes128_gcm_decrypt key iv aad aad_len plaintext' plaintext_len ciphertext tag with
  | 1ul ->
    TestLib.compare_and_print !$"of AES-GCM 128 plaintext" plaintext plaintext' plaintext_len
  | _ ->
    C.String.print !$"Decryption failed!\n"; C.portable_exit 1l;

  pop_frame()

val test_aes256_gcm: v:aead_vector{v.cipher == AES_256_GCM} -> St unit
let test_aes256_gcm v =
  push_frame();

  let key        = buffer_of_hex v.key in
  let iv         = buffer_of_hex v.iv in
  let aad        = buffer_of_hex v.aad in
  let tag        = buffer_of_hex v.tag in
  let plaintext  = buffer_of_hex v.plaintext in
  let ciphertext = buffer_of_hex v.ciphertext in

  let plaintext_len = Bytes.len (bytes_of_hex v.ciphertext) in
  let aad_len       = Bytes.len (bytes_of_hex v.aad) in
  let plaintext'    = B.create 0uy plaintext_len in
  let ciphertext'   = B.create 0uy plaintext_len in
  let tag'          = B.create 0uy 16ul in

  EverCrypt.aes256_gcm_encrypt key iv aad aad_len plaintext plaintext_len ciphertext' tag';
  TestLib.compare_and_print !$"of AES-GCM 256 cipher" ciphertext ciphertext' plaintext_len;
  TestLib.compare_and_print !$"of AES-GCM 256 tag" tag tag' 16ul;

  match EverCrypt.aes256_gcm_decrypt key iv aad aad_len plaintext' plaintext_len ciphertext tag with
  | 1ul ->
    TestLib.compare_and_print !$"of AES-GCM 256 plaintext" plaintext plaintext' plaintext_len
  | _ ->
    C.String.print !$"Decryption failed!\n"; C.portable_exit 1l;

  pop_frame()

let test_aes_ecb (v:block_cipher_vector) : St unit =
  push_frame();
  let key = buffer_of_hex v.rkey in
  let plain = buffer_of_hex v.plain in
  let cipher = buffer_of_hex v.enc in
  let cipher' = B.create 0uy 16ul in
  let () =
    match v.block with
    | AES128 ->
      let k = EverCrypt.aes128_create key in
      EverCrypt.aes128_compute k plain cipher';
      EverCrypt.aes128_free k
    | AES256 ->
      let k = EverCrypt.aes256_create key in
      EverCrypt.aes256_compute k plain cipher';
      EverCrypt.aes256_free k
    in
  TestLib.compare_and_print !$"of AES128 block" cipher cipher' 16ul;
  pop_frame()

/// Test drivers

val test_cipher: list block_cipher_vector -> St unit
let rec test_cipher v =
  match v with
  | [] -> ()
  | v :: vs ->
    match v.block with
    | AES128
    | AES256 ->
      let this = test_aes_ecb v in
      let rest = test_cipher vs in
      ()
    | _ -> test_cipher vs

val test_aead: list aead_vector -> St unit
let rec test_aead v =
  match v with
  | [] -> ()
  | v :: vs ->
    match v.cipher with
    | CHACHA20_POLY1305 ->
      let this = test_chacha20_poly1305 v in
      let rest = test_aead vs in
      ()
    | AES_128_GCM ->
      let this = test_aes128_gcm v in
      let rest = test_aead vs in
      ()
    | AES_256_GCM ->
      let this = test_aes256_gcm v in
      let rest = test_aead vs in
      ()
    | _ -> test_aead vs

val test_hash: list hash_vector -> St unit
let rec test_hash v =
  match v with
  | [] -> ()
  | v :: vs ->
    begin
    match v.hash_alg with
    | SHA256 -> test_sha256 v
    | SHA384 -> test_sha384 v
    | SHA512 -> test_sha512 v
    | SHA1   -> ()
    | MD5    -> ()
    end;
    test_hash vs

let main (): St C.exit_code =
  let open EverCrypt in
  push_frame ();
/// Hacl tests
  Test.Bytes.print "===========Hacl===========" "";
  init (Prefer Hacl);
  test_hash hash_vectors;
  test_cipher block_cipher_vectors;
  test_aead aead_vectors;
  Test.Bytes.main ();
/// Vale tests
  Test.Bytes.print "===========Vale===========" "";
  init (Prefer Vale);
  test_aead aead_vectors;
  test_cipher block_cipher_vectors;
  test_hash hash_vectors;
// OpenSSL tests
  Test.Bytes.print "==========OpenSSL=========" "";
  init (Prefer OpenSSL);
  test_aead aead_vectors;
  test_cipher block_cipher_vectors;
  Test.Bytes.print "==========BCrypt==========" "";
  init (Prefer BCrypt);
  test_aead aead_vectors;
  test_cipher block_cipher_vectors;
  pop_frame ();
  C.EXIT_SUCCESS
