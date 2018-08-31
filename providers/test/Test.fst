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

val test_one_hash: hash_vector -> St unit
let test_one_hash vec =
  let open FStar.Integers in
  let a, input, (LB expected_len expected), repeat = vec in
  let input_len = C.String.strlen input in
  let tlen = H.tagLen a in  
  if expected_len <> tlen then failwith !$"Wrong length of expected tag\n"
  else if supported_hash_algorithm a then
    begin
    push_frame();
    let computed = B.alloca 0uy tlen in
    assume (v input_len * v repeat < pow2 32);
    let total_input_len = input_len * repeat in
    if total_input_len = 0ul then
      begin
      let total_input = B.null in
      assert_norm (v total_input_len <= EverCrypt.Hash.maxLength (Ghost.hide a));

      if AC.Vale? (AC.sha256_impl()) then
        compute a total_input_len total_input computed
      else 
        EverCrypt.Hash.hash a computed total_input total_input_len
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

      if AC.Vale? (AC.sha256_impl()) then
        compute a total_input_len total_input computed
      else
        EverCrypt.Hash.hash a computed total_input total_input_len;
      pop_frame()
      end;

    B.recall expected;
    let str = H.string_of_alg a in
    TestLib.compare_and_print str expected computed tlen;
    pop_frame()
    end

val test_hash: vs:lbuffer hash_vector -> St unit
let rec test_hash (LB len vs) =
  let open FStar.Integers in
  B.recall vs;
  if len > 0ul then
    let v = vs.(0ul) in
    test_one_hash v;
    B.recall vs;
    test_hash (LB (len - 1ul) (B.offset vs 1ul))


/// HMAC

let hmac_vector = hash_alg * vec8 * vec8 * vec8

val test_one_hmac: hmac_vector -> St unit
let test_one_hmac vec =
  let open FStar.Integers in
  let ha, (LB keylen key), (LB datalen data), (LB expectedlen expected) = vec in
  if expectedlen <> H.tagLen ha then failwith !$"Wrong length of expected tag\n" 
  else if supported_hash_algorithm ha then
    begin
    push_frame();
    assume (EverCrypt.HMAC.keysized (Ghost.hide ha) (v keylen));
    assume (v datalen + H.blockLength (Ghost.hide ha) < pow2 32);
    B.recall key;
    B.recall data;
    let computed = B.alloca 0uy (H.tagLen ha) in
    EverCrypt.HMAC.compute ha computed key keylen data datalen;
    let str = EverCrypt.Hash.string_of_alg ha  in
    B.recall expected;
    TestLib.compare_and_print str expected computed (H.tagLen ha);
    pop_frame()
    end

val test_hmac: vs:lbuffer hmac_vector -> St unit
let rec test_hmac (LB len vs) =
  let open FStar.Integers in
  C.String.print !$"HMAC\n";
  B.recall vs;
  if len > 0ul then
    let v = vs.(0ul) in
    test_one_hmac v;
    B.recall vs;
    test_hmac (LB (len - 1ul) (B.offset vs 1ul))


/// HKDF

let hkdf_vector = hash_alg * vec8 * vec8 * vec8 * vec8 * vec8

val test_one_hkdf: hkdf_vector -> St unit
let test_one_hkdf vec =
  let open FStar.Integers in
  let ha, (LB ikmlen ikm), (LB saltlen salt), 
    (LB infolen info), (LB prklen expected_prk), (LB okmlen expected_okm) = vec in
  if prklen <> H.tagLen ha then failwith !$"Wrong length of expected PRK\n"
  else if (okmlen > 255ul * H.tagLen ha) then failwith !$"Wrong output length\n"
  else if supported_hash_algorithm ha then
    begin
    push_frame();
    assume (EverCrypt.HMAC.keysized (Ghost.hide ha) (v saltlen));
    assume (v ikmlen + H.blockLength (Ghost.hide ha) < pow2 32);
    assume (H.tagLength (Ghost.hide ha) 
      + v infolen + 1 + H.blockLength (Ghost.hide ha) < pow2 32);   
    B.recall salt;
    B.recall ikm;
    B.recall info;
    // TODO test vector length validation
    let str = EverCrypt.Hash.string_of_alg ha  in 
    let computed_prk = B.alloca 0uy (H.tagLen ha) in
    EverCrypt.HKDF.hkdf_extract ha computed_prk salt saltlen ikm ikmlen;
    B.recall expected_prk;
    TestLib.compare_and_print str expected_prk computed_prk (H.tagLen ha);

    if okmlen = 0ul then
      begin
      let computed_okm = B.null in
      EverCrypt.HKDF.hkdf_expand ha computed_okm computed_prk prklen info infolen okmlen;
      B.recall expected_okm;
      TestLib.compare_and_print str expected_okm computed_okm okmlen
      end
    else
      begin
      push_frame();
      let computed_okm = B.alloca 0uy okmlen in
      EverCrypt.HKDF.hkdf_expand ha computed_okm computed_prk prklen info infolen okmlen;
      B.recall expected_okm;
      TestLib.compare_and_print str expected_okm computed_okm okmlen;
      pop_frame()
      end;
    pop_frame()
    end

val test_hkdf: vs:lbuffer hkdf_vector -> St unit
let rec test_hkdf (LB len vs) =
  let open FStar.Integers in
  C.String.print !$"HKDF\n";
  B.recall vs;
  if len > 0ul then
    let v = vs.(0ul) in
    test_one_hkdf v;
    B.recall vs;
    test_hkdf (LB (len - 1ul) (B.offset vs 1ul))


/// ChaCha20-Poly1305

let aead_vector = cipher * vec8 * vec8 * vec8 * vec8 * vec8 * vec8

// 2018.08.08 SZ: TODO: verify the rest once we have a proper EverCrypt.Specs
#set-options "--admit_smt_queries true"

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

val test_aes128_gcm: aead_vector -> St unit
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

val test_aes256_gcm: aead_vector -> St unit
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

val test_aes_ecb: block_cipher_vector -> St unit
let test_aes_ecb v =
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

val test_cipher: lbuffer block_cipher_vector -> St unit
let rec test_cipher (LB len vs) =
  let open FStar.Integers in
  B.recall vs;
  if len > 0ul then
    let v = vs.(0ul) in
    test_aes_ecb v;
    B.recall vs;
    test_cipher (LB (len - 1ul) (B.offset vs 1ul))

let chacha20_vector = vec8 * vec8 * U32.t * vec8 * vec8

val test_chacha20: lbuffer chacha20_vector -> St unit
let rec test_chacha20 (LB len vs) =
  let open FStar.Integers in
  B.recall vs;
  if len > 0ul then begin
    push_frame ();
    let (LB key_len key), (LB iv_len iv), ctr, (LB plain_len plain), (LB cipher_len cipher) = vs.(0ul) in
    let cipher' = B.alloca 0uy cipher_len in
    EverCrypt.chacha20 key iv ctr plain plain_len cipher';
    TestLib.compare_and_print !$"of ChaCha20 message" cipher cipher' cipher_len;
    pop_frame ();
    B.recall vs;
    test_chacha20 (LB (len - 1ul) (B.offset vs 1ul))
  end

#reset-options "--z3rlimit 50 --max_fuel 1 --max_ifuel 0 --using_facts_from '* -Test.Vectors'"

val test_aead: lbuffer aead_vector -> St unit
let rec test_aead (LB len vs) =
  if len = 0ul then ()
  else
    let _ = B.recall vs in
    let v = vs.(0ul) in
    begin match v with
    | CHACHA20_POLY1305, _, _, _, _, _, _ ->
      test_chacha20_poly1305 v
    | AES_128_GCM, _, _, _, _, _, _ ->
      test_aes128_gcm v
    | AES_256_GCM, _, _, _, _, _, _ ->
      test_aes256_gcm v
    | _ -> ()
    end;
    let open FStar.Integers in
    B.recall vs;
    test_aead (LB (len - 1ul) (B.offset vs 1ul))

let rec test_rng (ctr:UInt32.t) : St unit =
  let open FStar.Integers in
  if ctr = 0ul then ()
  else
   begin
    let b = B.alloca 0uy 32ul in
    EverCrypt.random_sample 32ul b;
    C.print_bytes b 32ul;
    test_rng (ctr - 1ul)
   end

let main (): St C.exit_code =
  let open EverCrypt in
  let open C.String in
  push_frame ();

  print !$"===========Hacl===========\n";
  AC.(init (Prefer Hacl));
  test_hash hash_vectors_low;
  test_hmac hmac_vectors_low;
  test_hkdf hkdf_vectors_low;
  test_aead aead_vectors_low;
  test_cipher block_cipher_vectors_low;
  test_chacha20 chacha20_vectors_low;
  Test.Hash.main ();
  Test.Bytes.main ();

  print !$"===========Vale===========\n";
  AC.(init (Prefer Vale));
  test_aead aead_vectors_low;
  test_hash hash_vectors_low;
  test_cipher block_cipher_vectors_low;
  Test.Hash.main ();

  print !$"==========OpenSSL=========\n";
  AC.(init (Prefer OpenSSL));
  test_aead aead_vectors_low;
  test_cipher block_cipher_vectors_low;

  print !$"==========BCrypt==========\n";
  AC.(init (Prefer BCrypt));
  test_aead aead_vectors_low;
  test_cipher block_cipher_vectors_low;

  print !$"\n  HASHING TESTS\n";
  Test.Hash.main ();
  
  print !$"\n  PSEUDO-RANDOM GENERATOR\n";
  if EverCrypt.random_init () = 1ul then
   begin
    test_rng 10ul;
    EverCrypt.random_cleanup ()
   end
  else
   begin
    print !$"Failed to seed the PRNG!\n";
    C.portable_exit 3l
   end;
  
  pop_frame ();
  C.EXIT_SUCCESS
