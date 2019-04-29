module Test

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

// This contains hashes, hmac, hkdf, chacha20
open Test.NoHeap

(* the following two are necessary to connect with EverCrypt.Cipher and EverCrypt.Curve25519 *)
friend Lib.Buffer
friend Lib.IntTypes

// #reset-options "--using_facts_from '* -Test.Vectors'"

// #push-options "--z3rlimit 50 --max_fuel 1 --max_ifuel 0"

/// Poly1305

let test_poly1305_one (v: Test.Vectors.Poly1305.vector): Stack unit (fun _ -> True) (fun _ _ _ -> True) =
  let open Test.Vectors.Poly1305 in
  let Vector tag tag_len key key_len input input_len = v in
  push_frame ();
  if not (4294967295ul `U32.sub` 16ul `U32.gte` input_len)
  then
      C.String.print !$"Warning: skipping a test_poly1305 instance because bounds do not hold\n"
  else begin
    B.recall key;
    B.recall tag;
    B.recall input;
    let h0 = get () in
    let dst = B.alloca 0uy 16ul in
    let h1 = get () in
    B.recall input;
    B.recall key;
    B.recall tag;
    if key_len = 32ul then
      EverCrypt.Poly1305.poly1305 dst input input_len key;
    B.recall tag;
    if tag_len = 16ul then
      TestLib.compare_and_print !$"Poly1305" tag dst 16ul
  end;
  pop_frame ()

let test_poly1305 () : Stack unit (fun _ -> True) (fun _ _ _ -> True) =
  Test.NoHeap.test_many !$"poly1305" test_poly1305_one Test.Vectors.Poly1305.(LB vectors_len vectors)

/// Curve25519

let test_curve25519_one (v: Test.Vectors.Curve25519.vector): Stack unit (fun _ -> True) (fun _ _ _ -> True) =
  let open Test.Vectors.Curve25519 in
  let Vector result result_len public public_len private_ private__len valid = v in
  push_frame ();
  B.recall result;
  B.recall public;
  B.recall private_;
  let h0 = get () in
  let dst = B.alloca 0uy 32ul in
  let h1 = get () in
  B.recall result;
  B.recall public;
  B.recall private_;
  if public_len = 32ul && private__len = 32ul then
    EverCrypt.Curve25519.ecdh dst private_ public;
  B.recall result;
  if result_len = 32ul && valid then
    TestLib.compare_and_print !$"Curve25519" result dst 32ul;
  pop_frame ()

let test_curve25519 () : Stack unit (fun _ -> True) (fun _ _ _ -> True) =
  Test.NoHeap.test_many !$"curve25519" test_curve25519_one Test.Vectors.Curve25519.(LB vectors_len vectors)

/// ChaCha20-Poly1305

let aead_vector = cipher * vec8 * vec8 * vec8 * vec8 * vec8 * vec8

// 2018.08.08 SZ: TODO: verify the rest once we have a proper EverCrypt.Specs

type block_cipher_vector = block_cipher * vec8 * vec8 * vec8

module HST = FStar.HyperStack.ST

val test_aes_ecb: block_cipher_vector -> Stack unit (fun _ -> True) (fun _ _ _ -> True)
let test_aes_ecb v =
  let wh = AC.wants_hacl () in
  let wv = AC.wants_vale () in
  if (not wh) && (not wv) then
    C.String.print !$"Warning: not testing aes_ecb because Vale & Hacl are \
      disabled, no implementation\n"
  else begin
    let block, (LB key_len key), (LB plain_len plain), (LB cipher_len cipher) = v in
    if block = AES256 && not wh
    then C.String.print !$"Warning: not testing aes256 because Hacl is disabled\n"
    else if not (cipher_len = 16ul)
    then
      C.String.print !$"Warning: skipping a test_aes_ecb instance because bounds do not hold\n"
    else begin
      push_frame();
      let cipher' = B.alloca 0uy 16ul in
      let s0 = TestLib.cpucycles () in
      let h0 = HST.get () in
      [@inline_let] // to isolate the "assume False" into a delimited scope
      let f () : HST.Stack unit (requires (fun h -> h == h0)) (ensures (fun _ _ h -> B.modifies (B.loc_buffer cipher') h0 h)) =
        match block with
        | AES128 ->
          let k = assume False; EverCrypt.aes128_create key in
          EverCrypt.aes128_compute k plain cipher';
          EverCrypt.aes128_free k
        | AES256 ->
          let k = assume False; EverCrypt.aes256_create key in
          EverCrypt.aes256_compute k plain cipher';
          EverCrypt.aes256_free k
      in
      f ();
      let s1 = TestLib.cpucycles () in
      TestLib.print_cycles_per_round s0 s1 1ul;
      B.recall cipher;
      TestLib.compare_and_print !$"of AES128 block" cipher cipher' 16ul;
      pop_frame()
    end
  end

/// Test drivers

let test_cipher () : Stack unit (fun _ -> True) (fun _ _ _ -> True) =
  Test.NoHeap.test_many !$"cipher" test_aes_ecb block_cipher_vectors_low

let aead_key_length32 (al: Spec.AEAD.alg) : Tot (x: U32.t { U32.v x == Spec.AEAD.key_length al } ) =
  let open Spec.AEAD in
  match al with
  | AES128_GCM        -> 16ul
  | AES256_GCM        -> 32ul
  | CHACHA20_POLY1305 -> 32ul
  | AES128_CCM        -> 16ul
  | AES128_CCM8       -> 16ul
  | AES256_CCM        -> 32ul
  | AES256_CCM8       -> 32ul

let aead_max_length32 (al: Spec.AEAD.supported_alg) : Tot (x: U32.t { U32.v x == Spec.AEAD.max_length al }) =
  let open Spec.AEAD in
  match al with
  | CHACHA20_POLY1305 -> 4294967295ul `U32.sub` 16ul
  | AES128_GCM | AES256_GCM -> [@inline_let] let _ = assert_norm (pow2 20 == 1048576) in 1048575ul `U32.sub` 16ul

let aead_tag_length32 (al: Spec.AEAD.alg) : Tot (x: U32.t { U32.v x == Spec.AEAD.tag_length al /\ (Spec.AEAD.is_supported_alg al ==> U32.v x <= Spec.AEAD.max_length al) } ) =
  let open Spec.AEAD in
  [@inline_let] let _ =
    assert_norm (pow2 20 == 1048576)
  in
  match al with
  | AES128_CCM8       ->  8ul
  | AES256_CCM8       ->  8ul
  | AES128_GCM        -> 16ul
  | AES256_GCM        -> 16ul
  | CHACHA20_POLY1305 -> 16ul
  | AES128_CCM        -> 16ul
  | AES256_CCM        -> 16ul

let aead_iv_length32 (al: Spec.AEAD.alg) : Tot (x: U32.t { U32.v x == Spec.AEAD.iv_length al}) =
  12ul

#reset-options "--using_facts_from '* -Test.Vectors'"

#push-options "--z3rlimit 128"

let test_aead_st alg key key_len iv iv_len aad aad_len tag tag_len plaintext plaintext_len
  ciphertext ciphertext_len: ST unit
  (requires (fun _ ->
    B.recallable key /\
    B.recallable iv /\
    B.recallable aad /\
    B.recallable tag /\
    B.recallable plaintext /\
    B.recallable ciphertext /\
    B.len key == key_len /\
    B.len iv == iv_len /\
    B.len aad == aad_len /\
    B.len tag == tag_len /\
    B.len plaintext == plaintext_len /\
    B.len ciphertext == ciphertext_len /\
    B.disjoint plaintext aad // required by EverCrypt.AEAD.encrypt_st
  ))
  (ensures (fun _ _ _ -> True))
=

  let wh = AC.wants_hacl () in
  let wo = AC.wants_openssl () in
  if not (AC.has_avx ())
  then
    C.String.print !$"skipping test_aead_st, avx not present\n"
  else
  if alg = Spec.AEAD.CHACHA20_POLY1305 && (not wh) && (not wo) then
    C.String.print !$"Warning: skipping test_aead_st/chachapoly poly1305 because HACL and OpenSSL both disabled\n"
  else if not (
    Spec.AEAD.is_supported_alg alg
  )
  then
    C.String.print !$"Warning: skipping a test_aead_st instance because algo unsupported etc.\n"
  else if not (
    let max_len = aead_max_length32 alg in 
    let _ = assert_norm (pow2 31 == 2147483648) in
    key_len = aead_key_length32 alg &&
    plaintext_len `U32.gt` 0ul &&
    tag_len `U32.gt` 0ul &&
    tag_len = aead_tag_length32 alg &&
    ciphertext_len = plaintext_len &&
    iv_len = aead_iv_length32 alg &&
    aad_len `U32.lte` max_len &&
    aad_len `U32.lte` 2147483648ul &&
    (max_len `U32.sub` tag_len) `U32.gte` ciphertext_len
  )
  then
    C.String.print !$"Warning: skipping a test_aead_st instance because bounds do not hold\n"
  else begin
    push_frame();
    B.recall key;
    B.recall iv;
    B.recall aad;
    B.recall plaintext;
    let st = B.alloca B.null 1ul in
    let e = EverCrypt.AEAD.create_in #alg HyperStack.root st key in
    begin match e with
    | UnsupportedAlgorithm -> C.Failure.failwith !$"Failure: AEAD create_in UnsupportedAlgorithm"
    | Success ->
      let h1 = HST.get () in
      let st = B.index st 0ul in
      assert (B.loc_disjoint (B.loc_buffer iv) (EverCrypt.AEAD.footprint h1 st));
      push_frame ();
      let plaintext'    = B.alloca 0uy plaintext_len in
      let ciphertext'   = B.alloca 0uy ciphertext_len in
      let tag' = B.alloca 0uy tag_len in
      let h2 = HST.get () in
      EverCrypt.AEAD.frame_invariant B.loc_none st h1 h2;

      if EverCrypt.AEAD.(encrypt #(G.hide alg) st iv aad aad_len plaintext plaintext_len ciphertext' tag' <> Success) then
        C.Failure.failwith !$"Failure AEAD encrypt\n";
      let h3 = HST.get () in
      EverCrypt.AEAD.frame_invariant (B.loc_buffer ciphertext' `B.loc_union` B.loc_buffer tag') st h2 h3;
      (match EverCrypt.AEAD.decrypt #(G.hide alg) st iv aad aad_len ciphertext' ciphertext_len tag' plaintext' with
      | Success ->
        B.recall ciphertext;
        TestLib.compare_and_print !$"of AEAD cipher" ciphertext ciphertext' plaintext_len;
        TestLib.compare_and_print !$"of AEAD plain" plaintext plaintext' plaintext_len;
        B.recall tag;
        TestLib.compare_and_print !$"of AEAD tag" tag tag' tag_len
      | _ -> 
        C.Failure.failwith !$"Failure AEAD decrypt\n");
      pop_frame ()
    end;
    //EverCrypt.aead_free st;
    pop_frame ()
  end

#pop-options

#reset-options

let alg_of_alg = function
| CHACHA20_POLY1305 -> Spec.AEAD.CHACHA20_POLY1305
| AES_128_GCM -> Spec.AEAD.AES128_GCM
| AES_256_GCM -> Spec.AEAD.AES256_GCM

val test_aead_loop: lbuffer aead_vector -> St unit
let rec test_aead_loop (LB len vs) =
  if len = 0ul then ()
  else begin
    let open FStar.Integers in
    let _ = B.recall vs in
    let v = vs.(0ul) in

    let alg, (LB key_len key), (LB iv_len iv), (LB aad_len aad),
      (LB tag_len tag), (LB plaintext_len plaintext), (LB ciphertext_len ciphertext) = v
    in
    assume (B.disjoint plaintext aad); // required by EverCrypt.AEAD.encrypt_st, and currently we cannot have the tactic automatically prove it
    test_aead_st (alg_of_alg alg) key key_len iv iv_len aad aad_len tag tag_len plaintext
      plaintext_len ciphertext ciphertext_len;
    B.recall vs;
    test_aead_loop (LB (len - 1ul) (B.offset vs 1ul))
  end

let test_aead () : St unit =
  test_aead_loop aead_vectors_low

#push-options "--z3rlimit 32"

let test_chacha20poly1305_one (v: Test.Vectors.Chacha20Poly1305.vector): Stack unit (fun _ -> True) (fun _ _ _ -> True) =
  let Test.Vectors.Chacha20Poly1305.Vector cipher_and_tag cipher_and_tag_len plain plain_len aad aad_len nonce nonce_len key key_len = v in
  if not (
    key_len = 32ul &&
    nonce_len = 12ul &&
    0ul `U32.lt` plain_len &&
    (4294967295ul `U32.sub` 16ul) `U32.gte` plain_len &&
    (plain_len `U32.div` 64ul) `U32.lte` (4294967295ul `U32.sub` aad_len) &&
    cipher_and_tag_len = plain_len `U32.add` 16ul
  ) then
    C.String.print !$"Warning: skipping a chacha20poly1305 instance because bounds do not hold"
  else begin
    B.recall plain;
    B.recall cipher_and_tag;
    B.recall aad;
    B.recall nonce;
    B.recall key;
    HST.push_frame ();
    let tmp = B.alloca 0uy (plain_len `U32.add` 16ul) in
    let tmp_msg' = B.sub tmp 0ul plain_len in
    let tag' = B.sub tmp plain_len 16ul in
    EverCrypt.Chacha20Poly1305.aead_encrypt key nonce aad_len aad plain_len plain tmp_msg' tag';
    TestLib.compare_and_print !$"chacha20poly1305 cipher and tag" cipher_and_tag tmp cipher_and_tag_len;
    let cipher = B.sub cipher_and_tag 0ul plain_len in
    let tag = B.sub cipher_and_tag plain_len 16ul in
    let res = EverCrypt.Chacha20Poly1305.aead_decrypt key nonce aad_len aad plain_len tmp_msg' cipher tag in
    if res = 0ul
    then
      TestLib.compare_and_print !$"chacha20poly1305 plain" plain tmp_msg' plain_len
    else
      C.Failure.failwith !$"Failure: chacha20poly1305 aead_decrypt returned nonzero value";
    HST.pop_frame ()
  end

#pop-options

let test_chacha20poly1305 () : Stack unit (fun _ -> True) (fun _ _ _ -> True) =
  Test.NoHeap.test_many !$"chacha20poly1305" test_chacha20poly1305_one Test.Vectors.Chacha20Poly1305.(LB vectors_len vectors)

let rec test_aes128_gcm_loop (i: U32.t): St unit =
  let open Test.Vectors.Aes128Gcm in
  if i `U32.gte` vectors_len then
    ()
  else begin
    B.recall vectors;
    assert (U32.v i < B.length vectors);
    let Vector output output_len tag tag_len input input_len aad aad_len nonce nonce_len key key_len =
      vectors.(i)
    in
    test_aead_st Spec.AEAD.AES128_GCM key key_len nonce nonce_len aad aad_len tag tag_len
      input input_len output output_len;
    test_aes128_gcm_loop (i `U32.add_mod` 1ul)
  end

let test_aes128_gcm () : St unit =
  test_aes128_gcm_loop 0ul

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

#reset-options "--z3rlimit 40"
inline_for_extraction
noextract
let test_all_body (print: C.String.t -> St unit) : St unit =
    print !$"  >>>>>>>>> Hash (Test.Hash)\n";
    Test.Hash.main ();
    print !$"  >>>>>>>>> Hash (Test.NoHeap)\n";
    test_hash hash_vectors_low;
    print !$"  >>>>>>>>> Hmac (Test.NoHeap)\n";
    test_hmac hmac_vectors_low;
    print !$"  >>>>>>>>> HKDF (Test.NoHeap)\n";
    test_hkdf hkdf_vectors_low;
    print !$"  >>>>>>>>> FINITE-FIELD DIFFIE-HELLMAN\n";
    test_dh ();
    print !$"  >>>>>>>>> AEAD (old vectors)\n";
    test_aead ();
    print !$"  >>>>>>>>> AEAD (AES128_GCM vectors)\n";
    test_aes128_gcm ();
    print !$"  >>>>>>>>> Cipher\n";
    test_cipher ();
    print !$"  >>>>>>>>> Curve25519\n";
    test_curve25519 ();
    print !$"  >>>>>>>>> Poly1305\n";
    test_poly1305 ();
    print !$"  >>>>>>>>> Chacha20\n";
    test_chacha20 chacha20_vectors_low;
    print !$"  >>>>>>>>> AEAD (ChachaPoly vectors)\n";
    test_chacha20poly1305 ()
#reset-options

inline_for_extraction
type platform = | Vale | HACL | OpenSSL | BCrypt

inline_for_extraction
noextract
let static_config_ok (p: platform) : St bool =
  match p with
  | Vale -> EverCrypt.StaticConfig.vale
  | HACL -> EverCrypt.StaticConfig.hacl
  | OpenSSL -> EverCrypt.StaticConfig.openssl
  | BCrypt -> EverCrypt.StaticConfig.bcrypt

inline_for_extraction
noextract
let print_config (p: platform) (avx avx2: bool) : St unit =
  begin match p with
  | Vale -> C.String.print !$"VALE "
  | HACL -> C.String.print !$"HACL "
  | OpenSSL -> C.String.print !$"OpenSSL "
  | BCrypt -> C.String.print !$"BCrypt "
  end;
  (if avx then C.String.print !$"AVX ");
  (if avx2 then C.String.print !$"AVX2 ")

#push-options "--z3rlimit 16"

inline_for_extraction
noextract
let test_all_on_config (p: platform) (avx avx2: bool) : St unit =
  C.String.print !$"=================================================\n";
  print_config p avx avx2;
  C.String.print !$"\n";
  AC.init ();
  let has_avx = AC.has_avx () in
  let has_avx2 = AC.has_avx2 () in
  if avx && not has_avx
  then
    C.String.print !$"skipping, AVX wanted but not present\n"
  else if avx2 && not has_avx2
  then
    C.String.print !$"skipping, AVX2 wanted but not present\n"
  else if not (static_config_ok p)
  then
    C.String.print !$"skipping, not in static config\n"
  else begin
    (if p <> Vale then AC.disable_vale ());
    (if p <> HACL then AC.disable_hacl ());
    (if p <> OpenSSL then AC.disable_openssl ());
    (if p <> BCrypt then AC.disable_bcrypt ());
    (if not avx then AC.disable_avx ());
    (if not avx2 then AC.disable_avx2 ());
    let wants_vale = AC.wants_vale () in
    let wants_hacl = AC.wants_hacl () in
    let wants_openssl = AC.wants_openssl () in
    let wants_bcrypt = AC.wants_bcrypt () in 
    let wants_avx = AC.has_avx () in
    let wants_avx2 = AC.has_avx2 () in
    if not (
      (wants_vale = (p = Vale)) &&
      (wants_hacl = (p = HACL)) &&
      (wants_openssl = (p = OpenSSL)) &&
      (wants_bcrypt = (p = BCrypt)) &&
      (wants_avx = avx) &&
      (wants_avx2 = avx2)
    )
    then
      C.Failure.failwith !$"autoconfig is inconsistent"
    else
      test_all_body (fun s -> print_config p avx avx2; C.String.print s)
  end

#pop-options

inline_for_extraction
noextract
let test_all_on_platform_avx (p: platform) (avx: bool) : St unit =
  test_all_on_config p avx false;
  test_all_on_config p avx true

inline_for_extraction
noextract
let test_all_on_platform (p: platform) : St unit =
  test_all_on_platform_avx p false;
  test_all_on_platform_avx p true

let test_all () : St unit =
  test_all_on_platform Vale;
  test_all_on_platform HACL;
  test_all_on_platform OpenSSL;
  test_all_on_platform BCrypt

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

  push_frame ();

  test_all ();
  
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
