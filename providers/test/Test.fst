module Test

module B = LowStar.Buffer
module U32 = FStar.UInt32

module T = LowStar.ToFStarBuffer

inline_for_extraction noextract
let (!!) = T.new_to_old_st

open FStar.HyperStack.ST
open FStar.Bytes
open EverCrypt.Helpers

module AC = EverCrypt.AutoConfig
module H = EverCrypt.Hash

open Test.Vectors
open LowStar.BufferOps

#set-options "--admit_smt_queries true"

/// Hash function (any of them)

let vec8 = B.buffer UInt8.t * UInt32.t
let hash_vector = hash_alg * C.String.t * vec8 * UInt32.t

noextract unfold inline_for_extraction let (!$) = C.String.((!$))

open C.Failure

let supported_hash_algorithm = function
  | SHA256 | SHA384 -> true
  | _ -> false

let as_alg = function
  | SHA256 -> H.SHA256
  | SHA384 -> H.SHA384
  | _ -> failwith !$"unsupported alg"

val test_one_hash: hash_vector -> St unit
let test_one_hash vec =
  let open FStar.Integers in
  let hash_alg, input, (output, output_len), repeat = vec in

  if supported_hash_algorithm hash_alg then begin

    push_frame();

    let output_len: UInt32.t =
      match hash_alg with
      | SHA256 -> 32ul
      | SHA384 -> 48ul
      | _ -> failwith !$"Unsupported algorithm"
    in
    let output = B.alloca 0uy output_len in

    let input_len = C.String.strlen input in
    let total_input_len = input_len * repeat in
    let total_input = B.alloca 0uy total_input_len in
    C.Loops.for 0ul repeat (fun _ _ -> True) (fun i ->
      C.String.memcpy (B.offset total_input (input_len * i)) input input_len
    );

    (* Allocate memory for state *)
    let a: H.alg = as_alg hash_alg in
    let ctx = EverCrypt.Hash.create a in

    (* Compute the number of blocks to process *)
    let size_block: UInt32.t =
      match hash_alg with
      | SHA256 -> 64ul
      | SHA384 -> 128ul
      | _ -> failwith !$"Unsupported algorithm"
    in
    let n = U32.div total_input_len size_block in
    let r = U32.rem total_input_len size_block in

    (* Get all full blocks and the last block *)
    let input_blocks = B.sub total_input 0ul (n * size_block) in
    let input_last   = B.sub total_input (n * size_block) r in

    (* Call the hash function incrementally *)
    EverCrypt.Hash.init ctx;
    EverCrypt.Hash.update_multi ctx input_blocks n;
    EverCrypt.Hash.update_last ctx input_last r;
    EverCrypt.Hash.finish ctx output;

    // Non-incrementally:
    // EverCrypt.sha256_hash output input len

    let str: C.String.t =
      match hash_alg with
      | SHA256 -> !$"of SHA256"
      | SHA384 -> !$"of SHA384"
    in

    (* Display the result *)
    TestLib.compare_and_print str !!output !!output output_len;

    pop_frame()
  end

/// ChaCha20-Poly1305

let aead_vector = cipher * vec8 * vec8 * vec8 * vec8 * vec8 * vec8

val test_chacha20_poly1305: aead_vector -> St unit
let test_chacha20_poly1305 vec =
  push_frame();

  let cipher, (key, key_len), (iv, iv_len), (aad, aad_len),
    (tag, tag_len), (plaintext, plaintext_len), (ciphertext, ciphertext_len) = vec
  in

  let plaintext'    = B.alloca 0uy plaintext_len in
  let ciphertext'   = B.alloca 0uy plaintext_len in
  let tag'          = B.alloca 0uy 16ul in

  let s0 = TestLib.cpucycles () in
  EverCrypt.chacha20_poly1305_encrypt key iv aad aad_len plaintext plaintext_len ciphertext' tag';
  let s1 = TestLib.cpucycles () in
  TestLib.print_cycles_per_round s0 s1 1ul;
  TestLib.compare_and_print !$"of Chacha20-Poly1305 cipher" !!ciphertext !!ciphertext' plaintext_len;
  TestLib.compare_and_print !$"of Chacha20-Poly1305 tag" !!tag !!tag' 16ul;

  match EverCrypt.chacha20_poly1305_decrypt key iv aad aad_len plaintext' plaintext_len ciphertext tag with
  | 1ul ->
    TestLib.compare_and_print !$"of Chacha20-Poly1305 plaintext" !!plaintext !!plaintext' plaintext_len
  | _ ->
    C.String.print !$"Decryption failed!\n"; C.portable_exit 1l;

  pop_frame()

val test_aes128_gcm: v:aead_vector -> St unit
let test_aes128_gcm vec =
  push_frame();

  let cipher, (key, key_len), (iv, iv_len), (aad, aad_len),
    (tag, tag_len), (plaintext, plaintext_len), (ciphertext, ciphertext_len) = vec
  in

  let plaintext'    = B.alloca 0uy plaintext_len in
  let ciphertext'   = B.alloca 0uy plaintext_len in
  let tag'          = B.alloca 0uy 16ul in

  let s0 = TestLib.cpucycles () in
  EverCrypt.aes128_gcm_encrypt key iv aad aad_len plaintext plaintext_len ciphertext' tag';
  let s1 = TestLib.cpucycles () in
  TestLib.print_cycles_per_round s0 s1 1ul;
  TestLib.compare_and_print !$"of AES-GCM 128 cipher" !!ciphertext !!ciphertext' plaintext_len;
  TestLib.compare_and_print !$"of AES-GCM 128 tag" !!tag !!tag' 16ul;

  match EverCrypt.aes128_gcm_decrypt key iv aad aad_len plaintext' plaintext_len ciphertext tag with
  | 1ul ->
    TestLib.compare_and_print !$"of AES-GCM 128 plaintext" !!plaintext !!plaintext' plaintext_len
  | _ ->
    C.String.print !$"Decryption failed!\n"; C.portable_exit 1l;

  pop_frame()

val test_aes256_gcm: v:aead_vector -> St unit
let test_aes256_gcm vec =
  push_frame();

  let cipher, (key, key_len), (iv, iv_len), (aad, aad_len),
    (tag, tag_len), (plaintext, plaintext_len), (ciphertext, ciphertext_len) = vec
  in

  let plaintext'    = B.alloca 0uy plaintext_len in
  let ciphertext'   = B.alloca 0uy plaintext_len in
  let tag'          = B.alloca 0uy 16ul in

  EverCrypt.aes256_gcm_encrypt key iv aad aad_len plaintext plaintext_len ciphertext' tag';
  TestLib.compare_and_print !$"of AES-GCM 256 cipher" !!ciphertext !!ciphertext' plaintext_len;
  TestLib.compare_and_print !$"of AES-GCM 256 tag" !!tag !!tag' 16ul;

  let s0 = TestLib.cpucycles () in
  EverCrypt.aes256_gcm_encrypt key iv aad aad_len plaintext plaintext_len ciphertext' tag';
  let s1 = TestLib.cpucycles () in

  TestLib.print_cycles_per_round s0 s1 1ul;
  TestLib.compare_and_print !$"of AES-GCM 256 cipher" !!ciphertext !!ciphertext' plaintext_len;
  TestLib.compare_and_print !$"of AES-GCM 256 tag" !!tag !!tag' 16ul;

  match EverCrypt.aes256_gcm_decrypt key iv aad aad_len plaintext' plaintext_len ciphertext tag with
  | 1ul ->
    TestLib.compare_and_print !$"of AES-GCM 256 plaintext" !!plaintext !!plaintext' plaintext_len
  | _ ->
    C.String.print !$"Decryption failed!\n"; C.portable_exit 1l;

  pop_frame()

type block_cipher_vector = block_cipher * vec8 * vec8 * vec8

let test_aes_ecb (v: block_cipher_vector) : St unit =
  push_frame();
  let block, (key, key_len), (plain, plain_len), (cipher, cipher_len) = v in
  let cipher' = B.alloca 0uy 16ul in
  let s0 = TestLib.cpucycles () in
  let () =
    match block with
    | AES128 ->
      let k = EverCrypt.aes128_create key in
      EverCrypt.aes128_compute k plain cipher';
      EverCrypt.aes128_free k
    | AES256 ->
      let k = EverCrypt.aes256_create key in
      EverCrypt.aes256_compute k plain cipher';
      EverCrypt.aes256_free k
    in
  let s1 = TestLib.cpucycles () in
  TestLib.print_cycles_per_round s0 s1 1ul;
  TestLib.compare_and_print !$"of AES128 block" !!cipher !!cipher' 16ul;
  pop_frame()

/// Test drivers

let rec test_cipher (len: U32.t) (vs: B.buffer block_cipher_vector): St unit =
  let open FStar.Integers in
  if len > 0ul then
    let v = vs.(0ul) in
    test_aes_ecb v;
    test_cipher (len - 1ul) (B.offset vs 1ul)

let chacha20_vector = vec8 * vec8 * U32.t * vec8 * vec8

let rec test_chacha20 (len: U32.t) (vs: B.buffer chacha20_vector): St unit =
  let open FStar.Integers in
  if len > 0ul then
    let (key, key_len), (iv, iv_len), ctr, (plain, plain_len), (cipher, cipher_len) = vs.(0ul) in
    let cipher' = B.alloca 0uy len in
    EverCrypt.chacha20 key iv ctr plain plain_len cipher';
    TestLib.compare_and_print !$"of ChaCha20 message" !!cipher !!cipher' cipher_len;
    test_chacha20 (len - 1ul) (B.offset vs 1ul)

val test_aead: len:U32.t -> vs: B.buffer aead_vector {B.len vs = len }-> St unit
let rec test_aead len vs =
  if len = 0ul then
    ()
  else
    let v = vs.(0ul) in
    begin match v with
    | CHACHA20_POLY1305, _, _, _, _, _, _ ->
        test_chacha20_poly1305 v
    | AES_128_GCM, _, _, _, _, _, _ ->
        test_aes128_gcm v
    | AES_256_GCM, _, _, _, _, _, _ ->
        test_aes256_gcm v
    | _ ->
        ()
    end;
    let open FStar.Integers in
    test_aead (len - 1ul) (B.offset vs 1ul)

val test_hash: len:U32.t -> vs: B.buffer hash_vector {B.len vs = len }-> St unit
let rec test_hash len vs =
  let open FStar.Integers in
  if len > 0ul then
    let v = vs.(0ul) in
    test_one_hash v;
    test_hash (len - 1ul) (B.offset vs 1ul)

let main (): St C.exit_code =
  let open EverCrypt in
  let open C.String in
  push_frame ();

  let hash_vectors, hash_vectors_len = hash_vectors_low in
  let aead_vectors, aead_vectors_len = aead_vectors_low in
  let block_cipher_vectors, block_cipher_vectors_len = block_cipher_vectors_low in
  let chacha20_vectors, chacha20_vectors_len = chacha20_vectors_low in

  print !$"===========Hacl===========";
  AC.(init (Prefer Hacl));
  test_hash hash_vectors_len hash_vectors;
  test_aead aead_vectors_len aead_vectors;
  test_cipher block_cipher_vectors_len block_cipher_vectors;
  test_chacha20 chacha20_vectors_len chacha20_vectors;
  Test.Hash.main ();
  Test.Bytes.main ();
  
  print !$"===========Vale===========";
  AC.(init (Prefer Vale));
  test_aead aead_vectors_len aead_vectors;
  test_hash hash_vectors_len hash_vectors;
  test_cipher block_cipher_vectors_len block_cipher_vectors;
  Test.Hash.main ();
  
  print !$"==========OpenSSL=========";
  AC.(init (Prefer OpenSSL));
  test_aead aead_vectors_len aead_vectors;
  test_cipher block_cipher_vectors_len block_cipher_vectors;

  print !$"==========BCrypt==========";
  AC.(init (Prefer BCrypt));
  test_aead aead_vectors_len aead_vectors;
  test_cipher block_cipher_vectors_len block_cipher_vectors;
  Test.Hash.main ();
  pop_frame ();
  C.EXIT_SUCCESS
