module Test.NoHeap

module H = EverCrypt.Hash
module B = LowStar.Buffer
module L = Test.Lowstarize
module U32 = FStar.UInt32

open FStar.HyperStack.ST
open FStar.Integers
open LowStar.BufferOps
open Test.Lowstarize

/// A module that contains stack-only tests, suitable for both C and Wasm. Other
/// tests that may make arbitrary use of the heap are in Test and Test.Hash.
///
/// .. note::
///   Tests in this module are *VERIFIED*. Please keep it this way.

noextract unfold inline_for_extraction
let (!$) = C.String.((!$))

noextract unfold inline_for_extraction
let failwith = C.Failure.failwith

/// Using meta-evaluated Low* test vectors from Test.Vectors
/// ========================================================
///
/// Hashes
/// ------

#set-options "--max_fuel 0 --max_ifuel 0 --z3rlimit 300"

val test_one_hash: hash_vector -> Stack unit (fun _ -> true) (fun _ _ _ -> true)
let test_one_hash vec =
  let a, input, (LB expected_len expected), repeat = vec in
  let input_len = C.String.strlen input in
  let tlen = Hacl.Hash.Definitions.hash_len a in
  if expected_len <> tlen then
    failwith !$"Wrong length of expected tag\n"
  else if repeat = 0ul then
    failwith !$"Repeat must be non-zero\n"
  else if not (input_len <= (0xfffffffful - 1ul) / repeat) then
    failwith !$"Repeated input is too large\n"
  else begin
    push_frame();
    let computed = B.alloca 0uy tlen in
    assert_norm (v 0xfffffffful = pow2 32 - 1);
    assert (v input_len * v repeat + 1 < pow2 32);
    let total_input_len = input_len * repeat in
    let total_input = B.alloca 0uy (total_input_len + 1ul) in
    let total_input = B.sub total_input 0ul total_input_len in
    let h0 = get () in
    C.Loops.for 0ul repeat
    (fun h i -> B.live h total_input /\ B.modifies (B.loc_buffer total_input) h0 h)
    (fun i ->
      assert (v input_len * v i + v input_len <= v input_len * (v repeat - 1) + v input_len);
      assert (v input_len * v i + v input_len <= v input_len * v repeat);
      C.String.memcpy (B.sub total_input (input_len * i) input_len) input input_len
    );
    EverCrypt.Hash.uint32_fits_maxLength a total_input_len;
    assert (v total_input_len <= Spec.Hash.Definitions.max_input_length a + 1);

    EverCrypt.Hash.hash a computed total_input total_input_len;

    B.recall expected;
    let str = H.string_of_alg a in
    TestLib.compare_and_print str expected computed tlen;
    pop_frame()
    end

let test_hash = test_many !$"Hashes" test_one_hash

/// HMAC
/// ----

let supported_hmac_algorithm a =
  let open Spec.Hash.Definitions in
  match a with
  | MD5 | SHA2_224 -> false
  | _ -> true

let keysized (a:H.alg) (l: UInt32.t): Tot (b:bool{b ==> Spec.Agile.HMAC.keysized a (UInt32.v l) }) =
  EverCrypt.Hash.uint32_fits_maxLength a l;
  assert (v l <= Spec.Hash.Definitions.max_input_length a);
  assert_norm (v 0xfffffffful = pow2 32 - 1);
  l <= 0xfffffffful - Hacl.Hash.Definitions.block_len a

val test_one_hmac: hmac_vector -> Stack unit (fun _ -> True) (fun _ _ _ -> True)
let test_one_hmac vec =
  let ha, (LB keylen key), (LB datalen data), (LB expectedlen expected) = vec in
  if expectedlen <> Hacl.Hash.Definitions.hash_len ha then
    failwith !$"Wrong length of expected tag\n"
  else if not (keysized ha keylen) then
    failwith !$"Keysized predicate not satisfied\n"
  else if not (datalen <= 0xfffffffful - Hacl.Hash.Definitions.block_len ha) then
    failwith !$"Datalen predicate not satisfied\n"
  else if supported_hmac_algorithm ha then
    begin
    push_frame();
    assert (Spec.Agile.HMAC.keysized ha (v keylen));
    assert (v datalen + Spec.Hash.Definitions.block_length ha < pow2 32);
    B.recall key;
    B.recall data;
    let computed = B.alloca 0uy (Hacl.Hash.Definitions.hash_len ha) in
    EverCrypt.HMAC.compute ha computed key keylen data datalen;
    let str = EverCrypt.Hash.string_of_alg ha  in
    B.recall expected;
    TestLib.compare_and_print str expected computed (Hacl.Hash.Definitions.hash_len ha);
    pop_frame()
    end

let test_hmac = test_many !$"HMAC" test_one_hmac

/// HMAC-DRBG
/// ----

val test_one_hmac_drbg: hmac_drbg_vector -> Stack unit (fun _ -> True) (fun _ _ _ -> True)
let test_one_hmac_drbg vec =
  let open Hacl.HMAC_DRBG in
  let open EverCrypt.DRBG in
  let open Lib.IntTypes in
  let a,
      LB entropy_input_len entropy_input,
      LB nonce_len nonce,
      LB personalization_string_len personalization_string,
      LB entropy_input_reseed_len entropy_input_reseed,
      LB additional_input_reseed_len additional_input_reseed,
      (LB additional_input_1_len additional_input_1,
       LB additional_input_2_len additional_input_2),
      LB returned_bits_len returned_bits = vec
  in
  // EverCrypt.DRBG sources entropy internally.
  // We don't use entropy_input, entropy_input_reseed, nonce, and returned_bits
  // from the test vector, but we test safety of the API.
  B.recall personalization_string;
  B.recall additional_input_reseed;
  B.recall additional_input_1;
  B.recall additional_input_2;
  if not (Spec.Agile.HMAC.is_supported_alg a &&
          0ul <. returned_bits_len &&
          returned_bits_len <. 0xFFFFFFFFul)
  then C.exit (-1l)
  else
    begin
    push_frame();
    let output = B.alloca (u8 0) returned_bits_len in
    let st = alloca a in
    [@inline_let]
    let a = Ghost.hide a in
    let ok = instantiate a st personalization_string personalization_string_len in
    if ok then
      // We always provide prediction_resistance, so technically we don't need to reseed
      let ok = reseed a st additional_input_reseed additional_input_reseed_len in
      if ok then
        let ok = generate a output st returned_bits_len
                   additional_input_1 additional_input_1_len
        in
        if ok then
          let ok = generate a output st returned_bits_len
                     additional_input_2 additional_input_2_len
          in
          if ok then
            TestLib.compare_and_print !$"HMAC-DRBG" output output returned_bits_len
          else C.exit 1l
        else C.exit 1l
      else C.exit 1l
    else C.exit 1l;
    pop_frame()
    end

let test_hmac_drbg = test_many !$"HMAC-DRBG" test_one_hmac_drbg


/// HKDF
/// ----

val test_one_hkdf: hkdf_vector -> Stack unit (fun _ -> True) (fun _ _ _ -> True)
let test_one_hkdf vec =
  let ha, (LB ikmlen ikm), (LB saltlen salt),
    (LB infolen info), (LB prklen expected_prk), (LB okmlen expected_okm) = vec in
  if prklen <> Hacl.Hash.Definitions.hash_len ha then
    failwith !$"Wrong length of expected PRK\n"
  else if okmlen > 255ul * Hacl.Hash.Definitions.hash_len ha then
    failwith !$"Wrong output length\n"
  else if not (keysized ha saltlen) then
    failwith !$"Saltlen is not keysized\n"
  else if not (keysized ha prklen) then
    failwith !$"Prklen is not keysized\n"
  else if not (ikmlen <= 0xfffffffful - Hacl.Hash.Definitions.block_len ha) then
    failwith !$"ikmlen is too large\n"
  else if not (infolen <= 0xfffffffful -
    Hacl.Hash.Definitions.(block_len ha + hash_len ha + 1ul)) then
    failwith !$"infolen is too large\n"
  else if supported_hmac_algorithm ha then begin
    push_frame();
    assert (Spec.Agile.HMAC.keysized ha (v saltlen));
    assert (v ikmlen + Spec.Hash.Definitions.block_length ha < pow2 32);
    assert Spec.Hash.Definitions.(hash_length ha
      + v infolen + 1 + block_length ha < pow2 32);
    B.recall salt;
    B.recall ikm;
    B.recall info;
    let str = EverCrypt.Hash.string_of_alg ha in
    let computed_prk = B.alloca 0uy (Hacl.Hash.Definitions.hash_len ha) in
    EverCrypt.HKDF.extract ha computed_prk salt saltlen ikm ikmlen;
    B.recall expected_prk;
    TestLib.compare_and_print str expected_prk computed_prk (Hacl.Hash.Definitions.hash_len ha);

    let computed_okm = B.alloca 0uy (okmlen + 1ul) in
    let computed_okm = B.sub computed_okm 0ul okmlen in
    EverCrypt.HKDF.expand ha computed_okm computed_prk prklen info infolen okmlen;
    B.recall expected_okm;
    TestLib.compare_and_print str expected_okm computed_okm okmlen;
    pop_frame()
  end

let test_hkdf = test_many !$"HKDF" test_one_hkdf

/// Chacha20
/// --------

friend Lib.IntTypes

let test_one_chacha20 (v: chacha20_vector): Stack unit (fun _ -> True) (fun _ _ _ -> True) =
  let (LB key_len key), (LB iv_len iv), ctr, (LB plain_len plain), (LB cipher_len cipher) = v in
  if cipher_len = 0xfffffffful then
    failwith !$"Cipher too long"
  else if cipher_len <> plain_len then
    failwith !$"Cipher len and plain len don't match"
  else if key_len <> 32ul then
    failwith !$"invalid key len"
  else if iv_len <> 12ul then
    failwith !$"invalid iv len"
  else if not (ctr <= 0xfffffffful - cipher_len / 64ul) then
    failwith !$"invalid len"
  else begin
    push_frame ();
    B.recall key;
    B.recall iv;
    B.recall plain;
    B.recall cipher;
    let cipher' = B.alloca 0uy (cipher_len + 1ul) in
    let cipher' = B.sub cipher' 0ul cipher_len in
    EverCrypt.Cipher.chacha20 plain_len cipher' plain key iv ctr;
    TestLib.compare_and_print !$"of ChaCha20 message" cipher cipher' cipher_len;
    pop_frame ()
  end

let test_chacha20 = test_many !$"CHACHA20" test_one_chacha20

/// Using generated vectors in the vectors/ directory
/// =================================================

/// Poly1305
/// --------

let test_one_poly1305 (v: Test.Vectors.Poly1305.vector): Stack unit (fun _ -> True) (fun _ _ _ -> True) =
  let open Test.Vectors.Poly1305 in
  let Vector tag tag_len key key_len input input_len = v in
  push_frame ();
  if not (4294967295ul `U32.sub` 16ul `U32.gte` input_len)
  then
      C.Failure.failwith !$"Error: skipping a test_poly1305 instance because bounds do not hold\n"
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
  test_many !$"poly1305" test_one_poly1305 Test.Vectors.Poly1305.(LB vectors_len vectors)

/// Curve25519
/// ----------

let test_one_curve25519 (v: Test.Vectors.Curve25519.vector): Stack unit (fun _ -> True) (fun _ _ _ -> True) =
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
    EverCrypt.Curve25519.scalarmult dst private_ public;
  B.recall result;
  if result_len = 32ul && valid then
    TestLib.compare_and_print !$"Curve25519" result dst 32ul;
  pop_frame ()

let test_curve25519 () : Stack unit (fun _ -> True) (fun _ _ _ -> True) =
  test_many !$"curve25519" test_one_curve25519 Test.Vectors.Curve25519.(LB vectors_len vectors)

/// Chacha20-Poly1305
/// -----------------

#push-options "--z3rlimit 32"

let test_one_chacha20poly1305 (v: Test.Vectors.Chacha20Poly1305.vector): Stack unit (fun _ -> True) (fun _ _ _ -> True) =
  let Test.Vectors.Chacha20Poly1305.Vector cipher_and_tag cipher_and_tag_len plain plain_len aad aad_len nonce nonce_len key key_len = v in
  if not (key_len = 32ul)
  then C.Failure.failwith !$"chacha20poly1305: not (key_len = 32ul)"
  else if not (nonce_len = 12ul)
  then C.Failure.failwith !$"chacha20poly1305: not (nonce_len = 12ul)"
  else if not ((4294967295ul `U32.sub` 16ul) `U32.gte` plain_len)
  then C.Failure.failwith !$"chacha20poly1305: not ((4294967295ul `U32.sub` 16ul) `U32.gte` plain_len)"
  else if not ((plain_len `U32.div` 64ul) `U32.lte` (4294967295ul `U32.sub` aad_len))
  then C.Failure.failwith !$"chacha20poly1305: not ((plain_len `U32.div` 64ul) `U32.lte` (4294967295ul `U32.sub` aad_len))"
  else if not (cipher_and_tag_len = plain_len `U32.add` 16ul)
  then C.Failure.failwith !$"chacha20poly1305: not (cipher_and_tag_len = plain_len `U32.add` 16ul)"
  else begin
    B.recall plain;
    B.recall cipher_and_tag;
    B.recall aad;
    B.recall nonce;
    B.recall key;
    push_frame ();
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
    pop_frame ()
  end

#pop-options

let test_chacha20poly1305 () : Stack unit (fun _ -> True) (fun _ _ _ -> True) =
  test_many !$"chacha20poly1305" test_one_chacha20poly1305 Test.Vectors.Chacha20Poly1305.(LB vectors_len vectors)


/// A main for WASM tests only (ignored by Test)
/// ============================================

let main () =
  let open Test.Vectors in
  C.String.print !$"Start WASM tests\n";
  test_hash hash_vectors_low;
  test_hmac hmac_vectors_low;
  test_hmac_drbg hmac_drbg_vectors_low;
  test_hkdf hkdf_vectors_low;
  test_chacha20 chacha20_vectors_low;
  test_poly1305 ();
  test_curve25519 ();
  test_chacha20poly1305 ();
  C.String.print !$"End WASM tests\n";
  0l
