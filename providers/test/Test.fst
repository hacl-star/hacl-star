module Test

module G = FStar.Ghost
module B = LowStar.Buffer
module U32 = FStar.UInt32

open FStar.HyperStack.ST
open EverCrypt.Helpers

module AC = EverCrypt.AutoConfig
module H = EverCrypt.Hash

open Test.Vectors
open LowStar.BufferOps
open C.Failure

open Test.Lowstarize

#reset-options "--z3rlimit 50 --max_fuel 1 --max_ifuel 0 --using_facts_from '* -Test.Vectors'"

/// Hash function (any of them)

let vec8 = lbuffer UInt8.t
let hash_vector = hash_alg * C.String.t * vec8 * UInt32.t

noextract unfold inline_for_extraction
let (!$) = C.String.((!$))

let supported_hash_algorithm = function
  | H.SHA256 | H.SHA384 -> true
  | _ -> false

val compute:
  a: EverCrypt.Hash.alg ->
  len: UInt32.t ->
  text: uint8_pl (U32.v len) ->
  tag: uint8_pl (EverCrypt.Hash.tagLength (Ghost.hide a)) -> ST unit
  (requires fun h0 ->
    B.live h0 text /\
    B.live h0 tag /\
    B.(loc_disjoint (loc_buffer text) (loc_buffer tag)))
  (ensures fun h0 () h1 ->
    B.live h1 text /\ B.live h1 tag /\
    //B.modifies (B.loc_buffer tag) h0 h1 /\
    U32.v len <= EverCrypt.Hash.maxLength (Ghost.hide a) /\ (* required for subtyping the RHS below *)
    B.as_seq h1 tag = EverCrypt.Hash.spec (Ghost.hide a) (B.as_seq h0 text))
//18-07-07 CF: TODO add deallocation; restore Stack (not ST); restore modifies clause
let compute a len text tag =
  let open FStar.Integers in
  let open FStar.HyperStack.ST in
  let open EverCrypt.Hash in
  push_frame();
  let s = create a in
  assert_norm(U32.v len <= maxLength (Ghost.hide a));
  let ll = len % blockLen a in
  let lb = len - ll in
  let blocks = B.sub text 0ul lb in
  let last = B.offset text lb in
  let h1 = get() in
  init s;
  let h10 = get() in
  update_multi (Ghost.hide Seq.empty) s blocks lb;
  let h11 = get() in
  //18-07-10 CF: improve style on ghosts and lists?
  FStar.Seq.(lemma_eq_intro (empty @| (B.as_seq h10 blocks)) (B.as_seq h10 blocks));
  update_last (Ghost.hide (B.as_seq h11 blocks)) s last len;
  finish s tag;
  let h2 = get() in
  pop_frame();

  let vblocks = B.as_seq h1 blocks in
  let vlast = B.as_seq h1 last in
  let vsuffix = suffix (Ghost.hide a) (U32.v len) in
  FStar.Seq.(lemma_eq_intro (B.as_seq h1 text) (vblocks @| vlast));
  lemma_hash2 (acc0 #(Ghost.hide a)) vblocks FStar.Seq.(vlast @| vsuffix);
  Seq.append_assoc vblocks vlast vsuffix

#set-options "--max_fuel 0"

val test_one_hash: hash_vector -> ST unit
  (requires fun _ -> True)
  (ensures  fun h0 _ h1 -> True)
let test_one_hash vec =
  let open FStar.Integers in
  let a, input, (LB expected_len expected), repeat = vec in
  if supported_hash_algorithm a then
    begin
    push_frame();
    let tlen = H.tagLen a in
    let computed = B.alloca 0uy tlen in
    let input_len = C.String.strlen input in
    assume (v input_len * v repeat < pow2 32);
    let total_input_len = input_len * repeat in
    if total_input_len = 0ul then
      begin
      let total_input = B.null in
      assert_norm (v total_input_len <= EverCrypt.Hash.maxLength (Ghost.hide a));

      match AC.sha256_impl() with
      | AC.Vale -> compute a total_input_len total_input computed
      | _       -> EverCrypt.Hash.hash a computed total_input total_input_len
      end
    else
      begin
      push_frame();
      let total_input = B.alloca 0uy total_input_len in
      let h0 = get () in
      C.Loops.for 0ul repeat
      (fun h i -> B.live h total_input /\ B.modifies (B.loc_buffer total_input) h0 h)
      (fun i ->
        assert (v input_len * v i + v input_len <= v input_len * (v repeat - 1) + v input_len);
        assert (v input_len * v i + v input_len <= v input_len * v repeat);
        C.String.memcpy (B.sub total_input (input_len * i) input_len) input input_len
      );
      assert_norm (v total_input_len <= EverCrypt.Hash.maxLength (Ghost.hide a));

      match AC.sha256_impl() with
      | AC.Vale -> compute a total_input_len total_input computed
      | _       -> EverCrypt.Hash.hash a computed total_input total_input_len;
      pop_frame()
      end;

    B.recall expected;
    assume (expected_len == tlen);
    let str = H.string_of_alg a in
    TestLib.compare_and_print str expected computed tlen;
    pop_frame()
    end

// 2018.08.06 SZ: TODO: verify the rest of the file
#set-options "--admit_smt_queries true"

/// HMAC

let hmac_vector = hash_alg * vec8 * vec8 * vec8

val test_one_hmac: hmac_vector -> St unit
let test_one_hmac vec =
  let open FStar.Integers in
  let ha, (LB keylen key), (LB datalen data), (LB expectedlen expected) = vec in
  if supported_hash_algorithm ha then
    begin
    push_frame();
//  if expectedlen <> H.tagLen ha then failwith !$"Wrong output length"; 
    let computed = B.alloca 0uy (H.tagLen ha) in
    let str = EverCrypt.Hash.string_of_alg ha  in
    EverCrypt.HMAC.compute ha computed key keylen data datalen;
    TestLib.compare_and_print str expected computed (H.tagLen ha);
    pop_frame()
    end

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
  let ha, (LB ikmlen ikm), (LB saltlen salt), (LB infolen info), (LB prklen expected_prk), (LB okmlen expected_okm) = vec in

  if supported_hash_algorithm ha then
    begin
    push_frame();
    // TODO test vector length validation
    let str = EverCrypt.Hash.string_of_alg ha  in 
    let computed_prk = B.alloca 0uy (H.tagLen ha) in
    EverCrypt.HKDF.hkdf_extract ha computed_prk salt saltlen ikm ikmlen;
    TestLib.compare_and_print str expected_prk computed_prk (H.tagLen ha);

    let computed_okm = B.alloca 0uy okmlen in
    EverCrypt.HKDF.hkdf_expand ha computed_okm computed_prk prklen info infolen okmlen;
    TestLib.compare_and_print str expected_okm computed_okm okmlen;
    pop_frame()
    end

val test_hkdf: len:U32.t -> vs: B.buffer hkdf_vector {B.len vs == len} -> St unit
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

  let cipher, (LB key_len key), (LB iv_len iv), (LB aad_len aad),
    (LB tag_len tag), (LB plaintext_len plaintext), (LB ciphertext_len ciphertext) = vec
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

  let cipher, (LB key_len key), (LB iv_len iv), (LB aad_len aad),
    (LB tag_len tag), (LB plaintext_len plaintext), (LB ciphertext_len ciphertext) = vec
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

  let cipher, (LB key_len key), (LB iv_len iv), (LB aad_len aad),
    (LB tag_len tag), (LB plaintext_len plaintext), (LB ciphertext_len ciphertext) = vec
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
  let block, (LB key_len key), (LB plain_len plain), (LB cipher_len cipher) = v in
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
    let (LB key_len key), (LB iv_len iv), ctr, (LB plain_len plain), (LB cipher_len cipher) = vs.(0ul) in
    let cipher' = B.alloca 0uy cipher_len in
    EverCrypt.chacha20 key iv ctr plain plain_len cipher';
    TestLib.compare_and_print !$"of ChaCha20 message" cipher cipher' cipher_len;
    pop_frame ();
    test_chacha20 (len - 1ul) (B.offset vs 1ul)
  end

val test_aead: len:U32.t -> vs: B.buffer aead_vector {B.len vs == len} -> St unit
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

val test_hash: len:U32.t -> vs: B.buffer hash_vector{B.len vs == len} -> St unit
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

  let LB hash_vectors_len hash_vectors = hash_vectors_low in
  let LB hmac_vectors_len hmac_vectors = hmac_vectors_low in
  let LB hkdf_vectors_len hkdf_vectors = hkdf_vectors_low in
  let LB aead_vectors_len aead_vectors = aead_vectors_low in
  let LB block_cipher_vectors_len block_cipher_vectors = block_cipher_vectors_low in
  let LB chacha20_vectors_len chacha20_vectors = chacha20_vectors_low in

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
