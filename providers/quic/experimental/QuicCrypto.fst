module QuicCrypto

module G = FStar.Ghost
module B = LowStar.Buffer
module U32 = FStar.UInt32

open FStar.HyperStack.ST
open EverCrypt.Helpers
open EverCrypt.Error

module AC = EverCrypt.AutoConfig2
module SC = EverCrypt.StaticConfig
module H = EverCrypt.Hash

open Test.Vectors
open LowStar.BufferOps
open C.Failure
open Spec.Hash.Definitions

open Test.Lowstarize

// This contains hashes, hmac, hkdf.
open Test.NoHeap

#reset-options "--z3rlimit 50 --max_fuel 1 --max_ifuel 0 --using_facts_from '* -Test.Vectors'"

/// Poly1305

#set-options "--z3rlimit 100"
let test_poly1305_one (v: Test.Vectors.Poly1305.vector): St unit =
  let open Test.Vectors.Poly1305 in
  let Vector tag tag_len key key_len input input_len = v in
  push_frame ();
  assume (U32.v input_len + 16 <= UInt.max_int 32);
  // WHY?!! These are in the refinement in the vectors file.
  assume (B.recallable key);
  assume (B.recallable tag);
  assume (B.recallable input);
  B.recall key;
  B.recall tag;
  B.recall input;
  let h0 = get () in
  let dst = B.alloca 0uy 16ul in
  // WHY?! key, tag and input were live before dst was created fresh
  assume (B.disjoint dst input);
  assume (B.disjoint dst key);
  let h1 = get () in
  B.recall input;
  B.recall key;
  B.recall tag;
  if key_len = 32ul then
    EverCrypt.Poly1305.poly1305 dst input input_len key;
  B.recall tag;
  if tag_len = 16ul then
    TestLib.compare_and_print !$"Poly1305" tag dst 16ul;
  pop_frame ()

let rec test_poly1305 (i: U32.t): St unit =
  let open Test.Vectors.Poly1305 in
  if i `U32.gte` vectors_len then
    ()
  else begin
    assume (B.recallable vectors);
    B.recall vectors;
    // WHY? This is the refinement!
    assume (U32.v vectors_len = B.length vectors);
    assert (U32.v i < B.length vectors);
    test_poly1305_one (B.index vectors i);
    test_poly1305 (i `U32.add_mod` 1ul)
  end

/// Curve25519

let test_curve25519_one (v: Test.Vectors.Curve25519.vector): St unit =
  let open Test.Vectors.Curve25519 in
  let Vector result result_len public public_len private_ private__len valid = v in
  push_frame ();
  // WHY?!! These are in the refinement in the vectors file.
  assume (B.recallable result);
  assume (B.recallable public);
  assume (B.recallable private_);
  B.recall result;
  B.recall public;
  B.recall private_;
  let h0 = get () in
  let dst = B.alloca 0uy 32ul in
  // WHY?! key, tag and input were live before dst was created fresh
  assume (B.disjoint dst public);
  assume (B.disjoint dst private_);
  let h1 = get () in
  B.recall result;
  B.recall public;
  B.recall private_;
  admit (); // HACL* libraries getting in our way, once again
  if public_len = 32ul && private__len = 32ul then
    EverCrypt.Curve25519.ecdh dst private_ public;
  B.recall result;
  if result_len = 32ul && valid then
    TestLib.compare_and_print !$"Curve25519" result dst 32ul;
  pop_frame ()

let rec test_curve25519 (i: U32.t): St unit =
  let open Test.Vectors.Curve25519 in
  if i `U32.gte` vectors_len then
    ()
  else begin
    assume (B.recallable vectors);
    B.recall vectors;
    // WHY? This is the refinement!
    assume (U32.v vectors_len = B.length vectors);
    assert (U32.v i < B.length vectors);
    test_curve25519_one (B.index vectors i);
    test_curve25519 (i `U32.add_mod` 1ul)
  end



/// ChaCha20-Poly1305

let aead_vector = cipher * vec8 * vec8 * vec8 * vec8 * vec8 * vec8

// 2018.08.08 SZ: TODO: verify the rest once we have a proper EverCrypt.Specs
#set-options "--admit_smt_queries true"


type block_cipher_vector = block_cipher * vec8 * vec8 * vec8

val test_aes_ecb: block_cipher_vector -> St unit
let test_aes_ecb v =
  let wh = AC.wants_hacl () in
  let wv = AC.wants_vale () in
  if not wh && not wv then
    C.String.print !$"Warning: not testing aes_ecb because Vale & Hacl are \
      disabled, no implementation\n"
  else begin
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
  end

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
    EverCrypt.Cipher.chacha20 plain_len cipher' plain key iv ctr;
    TestLib.compare_and_print !$"of ChaCha20 message" cipher cipher' cipher_len;
    pop_frame ();
    B.recall vs;
    test_chacha20 (LB (len - 1ul) (B.offset vs 1ul))
  end

let test_aead_st alg key key_len iv iv_len aad aad_len tag tag_len plaintext plaintext_len
  ciphertext ciphertext_len: St unit
=

  let wh = AC.wants_hacl () in
  let wo = AC.wants_openssl () in

  if alg = Spec.AEAD.CHACHA20_POLY1305 && not wh && not wo then
    C.String.print !$"Warning: skipping test_aead_st/chachapoly because no BCrypt implementation\n"
  else begin
    push_frame();
    let st = B.alloca B.null 1ul in
    let _ = EverCrypt.AEAD.create_in #alg HyperStack.root st key in
    let st = B.index st 0ul in
    let plaintext'    = B.alloca 0uy plaintext_len in
    let ciphertext'   = B.alloca 0uy plaintext_len in
    let tag' = B.alloca 0uy tag_len in

    if EverCrypt.AEAD.(encrypt #(G.hide alg) st iv aad aad_len plaintext plaintext_len ciphertext' tag' <> Success) then
      C.Failure.failwith !$"Failure AEAD encrypt\n";
    (match EverCrypt.AEAD.decrypt #(G.hide alg) st iv aad aad_len ciphertext' ciphertext_len tag' plaintext' with
    | Success ->
      TestLib.compare_and_print !$"of AEAD cipher" ciphertext ciphertext' plaintext_len;
      TestLib.compare_and_print !$"of AEAD plain" plaintext plaintext' plaintext_len;
      TestLib.compare_and_print !$"of AEAD tag" tag tag' tag_len
    | _ -> 
      C.Failure.failwith !$"Failure AEAD decrypt\n");
    //EverCrypt.aead_free st;
    pop_frame ()
  end

#reset-options "--max_ifuel 1"
let alg_of_alg = function
| CHACHA20_POLY1305 -> Spec.AEAD.CHACHA20_POLY1305
| AES_128_GCM -> Spec.AEAD.AES128_GCM
| AES_256_GCM -> Spec.AEAD.AES256_GCM

#reset-options "--z3rlimit 50 --max_fuel 1 --max_ifuel 0 --using_facts_from '* -Test.Vectors'"

val test_aead: lbuffer aead_vector -> St unit
let rec test_aead (LB len vs) =
  if len = 0ul then ()
  else
    let open FStar.Integers in
    let _ = B.recall vs in
    let v = vs.(0ul) in

    let alg, (LB key_len key), (LB iv_len iv), (LB aad_len aad),
      (LB tag_len tag), (LB plaintext_len plaintext), (LB ciphertext_len ciphertext) = v
    in
    admit ();
    test_aead_st (alg_of_alg alg) key key_len iv iv_len aad aad_len tag tag_len plaintext
      plaintext_len ciphertext ciphertext_len;
    B.recall vs;
    test_aead (LB (len - 1ul) (B.offset vs 1ul))

let rec test_chacha20poly1305 (i: U32.t): St unit =
  let open Test.Vectors.Chacha20Poly1305 in
  if i `U32.gte` vectors_len then
    ()
  else begin
    assume (B.recallable vectors);
    B.recall vectors;
    // WHY? This is the refinement!
    assume (U32.v vectors_len = B.length vectors);
    assert (U32.v i < B.length vectors);
    let Vector output output_len input input_len aad aad_len nonce nonce_len key key_len =
      vectors.(i)
    in
    admit ();
    let tag = B.sub output input_len 16ul in
    let output = B.sub output 0ul input_len in
    test_aead_st Spec.AEAD.CHACHA20_POLY1305 key key_len nonce nonce_len aad aad_len tag 16ul
      input input_len output input_len;
    test_chacha20poly1305 (i `U32.add_mod` 1ul)
  end

let rec test_aes128_gcm (i: U32.t): St unit =
  let open Test.Vectors.Aes128Gcm in
  if i `U32.gte` vectors_len then
    ()
  else begin
    assume (B.recallable vectors);
    B.recall vectors;
    // WHY? This is the refinement!
    assume (U32.v vectors_len = B.length vectors);
    assert (U32.v i < B.length vectors);
    let Vector output output_len tag tag_len input input_len aad aad_len nonce nonce_len key key_len =
      vectors.(i)
    in
    admit ();
    test_aead_st Spec.AEAD.AES128_GCM key key_len nonce nonce_len aad aad_len tag tag_len
      input input_len output output_len;
    test_aes128_gcm (i `U32.add_mod` 1ul)
  end

let rec test_rng (ctr:UInt32.t) : St unit = ()
  // AR: 09/07: B.alloca won't work, we don't know is_stack_region (get_tip h0)
  // let open FStar.Integers in
  // if ctr = 0ul then ()
  // else
  //  begin
  //   let b = B.alloca 0uy 32ul in
  //   EverCrypt.random_sample 32ul b;
  //   C.print_bytes b 32ul;
  //   test_rng (ctr - 1ul)
  //  end

let test_dh () : St unit =
  let p = h"ffffffffffffffffadf85458a2bb4a9aafdc5620273d3cf1d8b9c583ce2d3695a9e13641146433fbcc939dce249b3ef97d2fe363630c75d8f681b202aec4617ad3df1ed5d5fd65612433f51f5f066ed0856365553ded1af3b557135e7f57c935984f0c70e0e68b77e2a689daf3efe8721df158a136ade73530acca4f483a797abc0ab182b324fb61d108a94bb2c8e3fbb96adab760d7f4681d4f42a3de394df4ae56ede76372bb190b07a7c8ee0a6d709e02fce1cdf7e2ecc03404cd28342f619172fe9ce98583ff8e4f1232eef28183c3fe3b1b4c6fad733bb5fcbc2ec22005c58ef1837d1683b2c6f34a26c1b2effa886b423861285c97ffffffffffffffff" in
  let q = "7fffffffffffffffd6fc2a2c515da54d57ee2b10139e9e78ec5ce2c1e7169b4ad4f09b208a3219fde649cee7124d9f7cbe97f1b1b1863aec7b40d901576230bd69ef8f6aeafeb2b09219fa8faf83376842b1b2aa9ef68d79daab89af3fabe49acc278638707345bbf15344ed79f7f4390ef8ac509b56f39a98566527a41d3cbd5e0558c159927db0e88454a5d96471fddcb56d5bb06bfa340ea7a151ef1ca6fa572b76f3b1b95d8c8583d3e4770536b84f017e70e6fbf176601a0266941a17b0c8b97f4e74c2c1ffc7278919777940c1e1ff1d8da637d6b99ddafe5e17611002e2c778c1be8b41d96379a51360d977fd4435a11c30942e4bffffffffffffffff" in
  let g = h"02" in
  // TODO supposed to use tactics now?
  ()

let main (): St C.exit_code =
  let equal_heap_dom_lemma (h1 h2:Heap.heap)
    : Lemma
      (requires Heap.equal_dom h1 h2)
      (ensures  ((forall (a:Type0) (rel:Preorder.preorder a) (r:Heap.mref a rel).
                    h1 `Heap.contains` r <==> h2 `Heap.contains` r) /\ 
                 (forall (a:Type0) (rel:Preorder.preorder a) (r:Heap.mref a rel).
                     r `Heap.unused_in` h1 <==> r `Heap.unused_in` h2)))
      [SMTPat (Heap.equal_dom h1 h2)]
    = ()
  in
    
  EverCrypt.AutoConfig2.init ();

  let open EverCrypt in
  let open C.String in

  push_frame ();

  print !$"\n  HASHING TESTS\n";
  Test.Hash.main ();

  print !$"\n  FINITE-FIELD DIFFIE-HELLMAN\n";
  test_dh ();

  if EverCrypt.StaticConfig.vale then begin
    print !$"===========Vale===========\n";
    Test.Hash.main ();
    print !$">>> Hash\n";
    test_hash hash_vectors_low;
    print !$">>> AEAD (old vectors)\n";
    test_aead aead_vectors_low;
    print !$">>> AEAD (AES128_GCM vectors)\n";
    test_aes128_gcm 0ul;
    print !$">>> Cipher\n";
    test_cipher block_cipher_vectors_low;
    print !$">>> Curve25519\n";
    test_curve25519 0ul;

    print !$">>> Poly1305 (Vale/X64)\n";
    EverCrypt.AutoConfig2.disable_avx2 ();
    EverCrypt.AutoConfig2.disable_avx ();
    test_poly1305 0ul;
    EverCrypt.AutoConfig2.init ()
  end;
  AC.disable_vale ();

  print !$"===========Hacl===========\n";
  print !$">>> Hash\n";
  Test.Hash.main ();
  test_hash hash_vectors_low;
  test_hmac hmac_vectors_low;
  test_hkdf hkdf_vectors_low;
  print !$">>> Chacha20\n";
  test_chacha20 chacha20_vectors_low;
  print !$">>> Block ciphers\n";
  test_cipher block_cipher_vectors_low;
  print !$">>> AEAD (old vectors)\n";
  test_aead aead_vectors_low;
  print !$">>> AEAD (ChachaPoly vectors)\n";
  test_chacha20poly1305 0ul;
  print !$">>> Curve25519 (HACL Curve51)\n";
  test_curve25519 0ul;
  //Test.Bytes.main ();

  print !$"\n  AVX2/POLY1305\n";
  test_poly1305 0ul;
  EverCrypt.AutoConfig2.disable_avx2 ();
  print !$"\n  AVX/POLY1305\n";
  test_poly1305 0ul;
  EverCrypt.AutoConfig2.disable_avx ();
  print !$"\n  C/POLY1305\n";
  test_poly1305 0ul;

  AC.disable_hacl ();

  if EverCrypt.StaticConfig.openssl then begin
    print !$"==========OpenSSL=========\n";
    test_aead aead_vectors_low;
    test_cipher block_cipher_vectors_low
  end;
  AC.disable_openssl ();

  if EverCrypt.StaticConfig.bcrypt then begin
    print !$"==========BCrypt==========\n";
    test_aead aead_vectors_low;
    test_cipher block_cipher_vectors_low
  end;
  // AR: 09/07: commenting it, random_init calls fails to verify, also see comment on test_rng above
  // print !$"\n  PSEUDO-RANDOM GENERATOR\n";
  // if EverCrypt.random_init () = 1ul then
  //  begin
  //   test_rng 10ul;
  //   EverCrypt.random_cleanup ()
  //  end
  // else
  //  begin
  //   print !$"Failed to seed the PRNG!\n";
  //   C.portable_exit 3l
  //  end;

  pop_frame ();
  C.EXIT_SUCCESS
