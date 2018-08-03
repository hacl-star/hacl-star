module Test

module G = FStar.Ghost
module B = LowStar.Buffer
module U32 = FStar.UInt32


module T = LowStar.ToFStarBuffer

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
  | H.SHA256 | H.SHA384 -> true
  | _ -> false

val test_one_hash: hash_vector -> St unit
let test_one_hash vec =
  let open FStar.Integers in
  let a, input, (expected, expected_len), repeat = vec in

  if supported_hash_algorithm a then (

    push_frame();
    let tlen: UInt32.t = H.tagLen a in
// to avoid double-extraction of failwith
//  let expected: uint8_pl (v tlen) = 
//    if expected_len = tlen 
//    then expected
//    else failwith !$"Wrong output length" in
    let computed = B.alloca 0uy tlen in

    let input_len = C.String.strlen input in
    let total_input_len = input_len * repeat in
    let total_input = B.alloca 0uy total_input_len in
    C.Loops.for 0ul repeat (fun _ _ -> True) (fun i ->
      C.String.memcpy (B.offset total_input (input_len * i)) input input_len
    );

    //18-08-03  this duplicated code now verified in EverCrypt.Hash.Test (and was a bit out of date)
    (*
    (* Allocate memory for state *)
    let ctx = EverCrypt.Hash.create a in

    (* Compute the number of blocks to process *)
    let size_block: UInt32.t = H.blockLen a in 
    let n = U32.div total_input_len size_block in
    let r = U32.rem total_input_len size_block in

    (* Get all full blocks and the last block *)
    let input_blocks = B.sub total_input 0ul (n * size_block) in
    let input_last   = B.sub total_input (n * size_block) r in

    (* Call the hash function incrementally *)
    EverCrypt.Hash.init ctx;
    EverCrypt.Hash.update_multi (G.hide Seq.empty) ctx input_blocks n;
    EverCrypt.Hash.update_last (G.hide Seq.empty) ctx input_last r;
    EverCrypt.Hash.finish ctx computed;
    *) 

    let str: C.String.t = H.string_of_alg a in

    //18-08-03 scopes?!!
    // Incrementally: 
    // EverCrypt.Hash.Test.compute a input_len input computed;
    // TestLib.compare_and_print str expected computed tlen;

    // Non-incrementally:
    EverCrypt.Hash.hash a computed total_input total_input_len;
    TestLib.compare_and_print str expected computed tlen;
    pop_frame()
  )

/// HMAC

let hmac_vector = hash_alg * vec8 * vec8 * vec8

val test_one_hmac: hmac_vector -> St unit
let test_one_hmac vec =
  let open FStar.Integers in
  let ha, (key,keylen), (data,datalen), (expected,expectedlen) = vec in

  if supported_hash_algorithm ha then (

    push_frame();
//  if expectedlen <> H.tagLen ha then failwith !$"Wrong output length"; 
    let computed = B.alloca 0uy (H.tagLen ha) in
    let str = EverCrypt.Hash.string_of_alg ha  in 
    EverCrypt.HMAC.compute ha computed key keylen data datalen;
    TestLib.compare_and_print str expected computed (H.tagLen ha);

    pop_frame() )

val test_hmac: len:U32.t -> vs: B.buffer hmac_vector {B.len vs = len } -> St unit
let rec test_hmac len vs =

  C.String.print !$"HMAC\n";

  let open FStar.Integers in
  if len > 0ul then
    let v = vs.(0ul) in
    test_one_hmac v;
    test_hmac (len - 1ul) (B.offset vs 1ul)

/// HKDF

let hkdf_vector = hash_alg * vec8 * vec8 * vec8 * vec8 * vec8

val test_one_hkdf: hkdf_vector -> St unit
let test_one_hkdf vec =
  let open FStar.Integers in
  let ha, (ikm,ikmlen), (salt,saltlen), (info,infolen), (expected_prk,prklen), (expected_okm,okmlen) = vec in

  if supported_hash_algorithm ha then (

    push_frame();

    // TODO test vector length validation

    let str = EverCrypt.Hash.string_of_alg ha  in 
    let computed_prk = B.alloca 0uy (H.tagLen ha) in
    EverCrypt.HKDF.hkdf_extract ha computed_prk salt saltlen ikm ikmlen;
    TestLib.compare_and_print str expected_prk computed_prk (H.tagLen ha);

    let computed_okm = B.alloca 0uy okmlen in
    EverCrypt.HKDF.hkdf_expand ha computed_okm computed_prk prklen info infolen okmlen;
    TestLib.compare_and_print str expected_okm computed_okm okmlen;

    pop_frame() )

val test_hkdf: len:U32.t -> vs: B.buffer hkdf_vector {B.len vs = len } -> St unit
let rec test_hkdf len vs =
  C.String.print !$"HKDF\n";
  let open FStar.Integers in
  if len > 0ul then
    let v = vs.(0ul) in
    test_one_hkdf v;
    test_hkdf (len - 1ul) (B.offset vs 1ul)


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
  TestLib.compare_and_print !$"of Chacha20-Poly1305 cipher" ciphertext ciphertext' plaintext_len;
  TestLib.compare_and_print !$"of Chacha20-Poly1305 tag" tag tag' 16ul;

  match EverCrypt.chacha20_poly1305_decrypt key iv aad aad_len plaintext' plaintext_len ciphertext tag with
  | 1ul ->
    TestLib.compare_and_print !$"of Chacha20-Poly1305 plaintext" plaintext plaintext' plaintext_len
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
  TestLib.compare_and_print !$"of AES-GCM 128 cipher" ciphertext ciphertext' plaintext_len;
  TestLib.compare_and_print !$"of AES-GCM 128 tag" tag tag' 16ul;

  match EverCrypt.aes128_gcm_decrypt key iv aad aad_len plaintext' plaintext_len ciphertext tag with
  | 1ul ->
    TestLib.compare_and_print !$"of AES-GCM 128 plaintext" plaintext plaintext' plaintext_len
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
  TestLib.compare_and_print !$"of AES-GCM 256 cipher" ciphertext ciphertext' plaintext_len;
  TestLib.compare_and_print !$"of AES-GCM 256 tag" tag tag' 16ul;

  let s0 = TestLib.cpucycles () in
  EverCrypt.aes256_gcm_encrypt key iv aad aad_len plaintext plaintext_len ciphertext' tag';
  let s1 = TestLib.cpucycles () in

  TestLib.print_cycles_per_round s0 s1 1ul;
  TestLib.compare_and_print !$"of AES-GCM 256 cipher" ciphertext ciphertext' plaintext_len;
  TestLib.compare_and_print !$"of AES-GCM 256 tag" tag tag' 16ul;

  match EverCrypt.aes256_gcm_decrypt key iv aad aad_len plaintext' plaintext_len ciphertext tag with
  | 1ul ->
    TestLib.compare_and_print !$"of AES-GCM 256 plaintext" plaintext plaintext' plaintext_len
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
  TestLib.compare_and_print !$"of AES128 block" cipher cipher' 16ul;
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
  if len > 0ul then begin
    push_frame ();
    let (key, key_len), (iv, iv_len), ctr, (plain, plain_len), (cipher, cipher_len) = vs.(0ul) in
    let cipher' = B.alloca 0uy cipher_len in
    EverCrypt.chacha20 key iv ctr plain plain_len cipher';
    TestLib.compare_and_print !$"of ChaCha20 message" cipher cipher' cipher_len;
    pop_frame ();
    test_chacha20 (len - 1ul) (B.offset vs 1ul)
  end

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
  let hmac_vectors, hmac_vectors_len = hmac_vectors_low in
  let hkdf_vectors, hkdf_vectors_len = hkdf_vectors_low in
  let aead_vectors, aead_vectors_len = aead_vectors_low in
  let block_cipher_vectors, block_cipher_vectors_len = block_cipher_vectors_low in
  let chacha20_vectors, chacha20_vectors_len = chacha20_vectors_low in

  print !$"===========Hacl===========\n";
  AC.(init (Prefer Hacl));
  test_hash hash_vectors_len hash_vectors;
  test_hmac hmac_vectors_len hmac_vectors;
  test_hkdf hkdf_vectors_len hkdf_vectors;
  test_aead aead_vectors_len aead_vectors;
  test_cipher block_cipher_vectors_len block_cipher_vectors;
  test_chacha20 chacha20_vectors_len chacha20_vectors;
  Test.Hash.main ();
  Test.Bytes.main ();
  
  print !$"===========Vale===========\n";
  AC.(init (Prefer Vale));
  test_aead aead_vectors_len aead_vectors;
  test_hash hash_vectors_len hash_vectors;
  test_cipher block_cipher_vectors_len block_cipher_vectors;
  Test.Hash.main ();
  
  print !$"==========OpenSSL=========\n";
  AC.(init (Prefer OpenSSL));
  test_aead aead_vectors_len aead_vectors;
  test_cipher block_cipher_vectors_len block_cipher_vectors;

  print !$"==========BCrypt==========\n";
  AC.(init (Prefer BCrypt));
  test_aead aead_vectors_len aead_vectors;
  test_cipher block_cipher_vectors_len block_cipher_vectors;
  Test.Hash.main ();
  pop_frame ();
  C.EXIT_SUCCESS
