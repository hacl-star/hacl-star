module Test.NoHeap

module H = EverCrypt.Hash
module B = LowStar.Buffer
module L = Test.Lowstarize

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
  let tlen = H.tagLen a in
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
    assert (v total_input_len <= EverCrypt.Hash.maxLength a);

    EverCrypt.Hash.hash a computed total_input total_input_len;

    B.recall expected;
    let str = H.string_of_alg a in
    TestLib.compare_and_print str expected computed tlen;
    pop_frame()
    end

inline_for_extraction noextract
let test_many #a (label: C.String.t)
  (f: a -> Stack unit (fun _ -> True) (fun _ _ _ -> True)) (vec: L.lbuffer a):
  Stack unit (fun _ -> True) (fun _ _ _ -> True)
=
  C.String.print label;
  let L.LB len vs = vec in
  let f (i:UInt32.t{FStar.UInt32.(0 <= v i /\ v i < v len)}): Stack unit
    (requires fun h -> True)
    (ensures fun h0 _ h1 -> True)
  =
    B.recall vs;
    f vs.(i)
  in
  C.Loops.for 0ul len (fun _ _ -> True) f

let test_hash = test_many !$"Hashes" test_one_hash

/// HMAC
/// ----

let supported_hmac_algorithm a =
  let open Spec.Hash.Definitions in
  match a with
  | MD5 | SHA2_224 -> false
  | _ -> true

let keysized (a:H.alg) (l: UInt32.t): Tot (b:bool{b ==> EverCrypt.HMAC.keysized a (UInt32.v l) }) =
  EverCrypt.Hash.uint32_fits_maxLength a l;
  assert (v l < Spec.Hash.Definitions.max_input_length a);
  assert_norm (v 0xfffffffful = pow2 32 - 1);
  l <= 0xfffffffful - Hacl.Hash.Definitions.block_len a

val test_one_hmac: hmac_vector -> Stack unit (fun _ -> True) (fun _ _ _ -> True)
let test_one_hmac vec =
  let ha, (LB keylen key), (LB datalen data), (LB expectedlen expected) = vec in
  if expectedlen <> H.tagLen ha then
    failwith !$"Wrong length of expected tag\n"
  else if not (keysized ha keylen) then
    failwith !$"Keysized predicate not satisfied\n"
  else if not (datalen <= 0xfffffffful - Hacl.Hash.Definitions.block_len ha) then
    failwith !$"Datalen predicate not satisfied\n"
  else if supported_hmac_algorithm ha then
    begin
    push_frame();
    assert (EverCrypt.HMAC.keysized ha (v keylen));
    assert (v datalen + H.blockLength ha < pow2 32);
    B.recall key;
    B.recall data;
    let computed = B.alloca 0uy (H.tagLen ha) in
    EverCrypt.HMAC.compute ha computed key keylen data datalen;
    let str = EverCrypt.Hash.string_of_alg ha  in
    B.recall expected;
    TestLib.compare_and_print str expected computed (H.tagLen ha);
    pop_frame()
    end

let test_hmac = test_many !$"HMAC" test_one_hmac


/// HKDF
/// ----

val test_one_hkdf: hkdf_vector -> Stack unit (fun _ -> True) (fun _ _ _ -> True)
let test_one_hkdf vec =
  let ha, (LB ikmlen ikm), (LB saltlen salt),
    (LB infolen info), (LB prklen expected_prk), (LB okmlen expected_okm) = vec in
  if prklen <> H.tagLen ha then
    failwith !$"Wrong length of expected PRK\n"
  else if okmlen > 255ul * H.tagLen ha then
    failwith !$"Wrong output length\n"
  else if not (keysized ha saltlen) then
    failwith !$"Saltlen is not keysized\n"
  else if not (ikmlen <= 0xfffffffful - Hacl.Hash.Definitions.block_len ha) then
    failwith !$"ikmlen is too large\n"
  else if not (infolen <= 0xfffffffful -
    Hacl.Hash.Definitions.(block_len ha + hash_len ha + 1ul)) then
    failwith !$"infolen is too large\n"
  else if supported_hmac_algorithm ha then begin
    push_frame();
    assert (EverCrypt.HMAC.keysized ha (v saltlen));
    assert (v ikmlen + H.blockLength ha < pow2 32);
    assert (H.tagLength ha
      + v infolen + 1 + H.blockLength ha < pow2 32);
    B.recall salt;
    B.recall ikm;
    B.recall info;
    let str = EverCrypt.Hash.string_of_alg ha in
    let computed_prk = B.alloca 0uy (H.tagLen ha) in
    EverCrypt.HKDF.hkdf_extract ha computed_prk salt saltlen ikm ikmlen;
    B.recall expected_prk;
    TestLib.compare_and_print str expected_prk computed_prk (H.tagLen ha);

    let computed_okm = B.alloca 0uy (okmlen + 1ul) in
    let computed_okm = B.sub computed_okm 0ul okmlen in
    EverCrypt.HKDF.hkdf_expand ha computed_okm computed_prk prklen info infolen okmlen;
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

/// A main for WASM tests only (ignored by Test)
/// ============================================

let main () =
  let open Test.Vectors in
  C.String.print !$"Start WASM tests\n";
  test_hash hash_vectors_low;
  test_hmac hmac_vectors_low;
  test_hkdf hkdf_vectors_low;
  test_chacha20 chacha20_vectors_low;
  C.String.print !$"End WASM tests\n";
  0l
