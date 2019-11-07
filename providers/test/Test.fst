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

// This contains hashes, hmac, hmac_drbg, hkdf, chacha20, poly1305, curve25519, chacha20poly1305
open Test.NoHeap

(* the following two are necessary to connect with EverCrypt.Cipher and EverCrypt.Curve25519 *)
friend Lib.Buffer
friend Lib.IntTypes

// #reset-options "--using_facts_from '* -Test.Vectors'"

// #push-options "--z3rlimit 50 --max_fuel 1 --max_ifuel 0"


let aead_vector = cipher * vec8 * vec8 * vec8 * vec8 * vec8 * vec8

// 2018.08.08 SZ: TODO: verify the rest once we have a proper EverCrypt.Specs

type block_cipher_vector = block_cipher * vec8 * vec8 * vec8

module HST = FStar.HyperStack.ST

val test_one_aes_ecb : block_cipher -> block_cipher_vector -> Stack unit (fun _ -> True) (fun _ _ _ -> True)
let test_one_aes_ecb block0 v =
    let block, (LB key_len key), (LB plain_len plain), (LB cipher_len cipher) = v in
    if block <> block0
    then ()
    else if not (cipher_len = 16ul)
    then
      C.Failure.failwith !$"Error: skipping a test_aes_ecb instance because bounds do not hold\n"
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

/// Test drivers

let test_aes_ecb (block0: block_cipher) : Stack unit (fun _ -> True) (fun _ _ _ -> True) =
  Test.NoHeap.test_many !$"cipher" (test_one_aes_ecb block0) block_cipher_vectors_low

let aead_key_length32 (al: Spec.Agile.AEAD.alg) : Tot (x: U32.t { U32.v x == Spec.Agile.AEAD.key_length al } ) =
  let open Spec.Agile.AEAD in
  match al with
  | AES128_GCM        -> 16ul
  | AES256_GCM        -> 32ul
  | CHACHA20_POLY1305 -> 32ul
  | AES128_CCM        -> 16ul
  | AES128_CCM8       -> 16ul
  | AES256_CCM        -> 32ul
  | AES256_CCM8       -> 32ul

let aead_max_length32 (al: Spec.Agile.AEAD.alg) : Tot (x: U32.t { Spec.Agile.AEAD.is_supported_alg al ==> U32.v x == Spec.Agile.AEAD.max_length al }) =
  let open Spec.Agile.AEAD in
  match al with
  | CHACHA20_POLY1305 -> 4294967295ul `U32.sub` 16ul
  | AES128_GCM | AES256_GCM -> 4294967295ul
  | _ -> 0ul // dummy

let aead_tag_length32 (al: Spec.Agile.AEAD.alg) : Tot (x: U32.t { U32.v x == Spec.Agile.AEAD.tag_length al /\ (Spec.Agile.AEAD.is_supported_alg al ==> U32.v x <= Spec.Agile.AEAD.max_length al) } ) =
  let open Spec.Agile.AEAD in
  match al with
  | AES128_CCM8       ->  8ul
  | AES256_CCM8       ->  8ul
  | AES128_GCM        -> 16ul
  | AES256_GCM        -> 16ul
  | CHACHA20_POLY1305 -> 16ul
  | AES128_CCM        -> 16ul
  | AES256_CCM        -> 16ul

let aead_iv_length32 (al: Spec.Agile.AEAD.supported_alg) (x:U32.t) : Tot
  (res:bool{res <==> Spec.Agile.AEAD.iv_length al (U32.v x)}) =
  let open Spec.Agile.AEAD in
  match al with
  | AES128_GCM -> 0ul `U32.lt` x
  | AES256_GCM -> 0ul `U32.lt` x
  | CHACHA20_POLY1305 -> x = 12ul


#reset-options "--using_facts_from '* -Test.Vectors'"

#push-options "--z3rlimit 700 --max_fuel 0 --max_ifuel 0"

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
  let max_len = aead_max_length32 alg in
  let _ = assert_norm (pow2 31 == 2147483648) in
  if not (
    Spec.Agile.AEAD.is_supported_alg alg
  )
  then
    C.Failure.failwith !$"Error: skipping a test_aead_st instance because algo unsupported etc.\n"
  else
  if not (key_len = aead_key_length32 alg)
  then C.Failure.failwith !$"test_aead_st: not (key_len = aead_key_length32 alg)"
  else if not (tag_len = aead_tag_length32 alg)
  then C.Failure.failwith !$"test_aead_st: not (tag_len = aead_tag_length32 alg)"
  else if not (ciphertext_len = plaintext_len)
  then C.Failure.failwith !$"test_aead_st: not (ciphertext_len = plaintext_len)"
  else if not (aead_iv_length32 alg iv_len)
  then C.Failure.failwith !$"test_aead_st: not (iv_len = aead_iv_length32 alg)"
  else if not (aad_len `U32.lte` max_len)
  then C.Failure.failwith !$"test_aead_st: not (aad_len `U32.lte` max_len)"
  else if not (aad_len `U32.lte` 2147483648ul)
  then C.Failure.failwith !$"test_aead_st: not (aad_len `U32.lte` 2147483648ul)"
  else if not ((max_len `U32.sub` tag_len) `U32.gte` ciphertext_len)
  then C.Failure.failwith !$"test_aead_st: not ((max_len `U32.sub` tag_len) `U32.gte` ciphertext_len)"
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
      let plaintext_blen = if plaintext_len = 0ul then 1ul else plaintext_len in
      let plaintext'    = B.alloca 0uy plaintext_blen in
      let plaintext'    = B.sub plaintext' 0ul plaintext_len in
      let ciphertext_blen = if ciphertext_len = 0ul then 1ul else ciphertext_len in
      let ciphertext'   = B.alloca 0uy ciphertext_blen in
      let ciphertext'   = B.sub ciphertext' 0ul ciphertext_len in
      let tag_blen = if tag_len = 0ul then 1ul else tag_len in
      let tag' = B.alloca 0uy tag_len in
      let tag' = B.sub tag' 0ul tag_len in
      let h2 = HST.get () in
      EverCrypt.AEAD.frame_invariant B.loc_none st h1 h2;

      if EverCrypt.AEAD.(encrypt #(G.hide alg) st iv iv_len aad aad_len plaintext plaintext_len ciphertext' tag' <> Success) then
        C.Failure.failwith !$"Failure AEAD encrypt\n";
      let h3 = HST.get () in
      (match EverCrypt.AEAD.decrypt #(G.hide alg) st iv iv_len aad aad_len ciphertext' ciphertext_len tag' plaintext' with
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
| CHACHA20_POLY1305 -> Spec.Agile.AEAD.CHACHA20_POLY1305
| AES_128_GCM -> Spec.Agile.AEAD.AES128_GCM
| AES_256_GCM -> Spec.Agile.AEAD.AES256_GCM

val test_aead_loop: Test.Vectors.cipher -> lbuffer aead_vector -> St unit
let rec test_aead_loop alg0 (LB len vs) =
  if len = 0ul then ()
  else begin
    let open FStar.Integers in
    let _ = B.recall vs in
    let v = vs.(0ul) in

    let alg, (LB key_len key), (LB iv_len iv), (LB aad_len aad),
      (LB tag_len tag), (LB plaintext_len plaintext), (LB ciphertext_len ciphertext) = v
    in
    if alg = alg0 then begin
      assume (B.disjoint plaintext aad); // required by EverCrypt.AEAD.encrypt_st, and currently we cannot have the tactic automatically prove it
      test_aead_st (alg_of_alg alg) key key_len iv iv_len aad aad_len tag tag_len plaintext
        plaintext_len ciphertext ciphertext_len
    end;
    B.recall vs;
    test_aead_loop alg0 (LB (len - 1ul) (B.offset vs 1ul))
  end

let test_aead (alg0: Test.Vectors.cipher) : St unit =
  test_aead_loop alg0 aead_vectors_low

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
    test_aead_st Spec.Agile.AEAD.AES128_GCM key key_len nonce nonce_len aad aad_len tag tag_len
      input input_len output output_len;
    test_aes128_gcm_loop (i `U32.add_mod` 1ul)
  end

let test_aes128_gcm () : St unit =
  test_aes128_gcm_loop 0ul

let nonce_bound a (len: UInt32.t):
  Tot (b:bool { b ==> Spec.Agile.Cipher.nonce_bound a (UInt32.v len) })
=
  let open Spec.Agile.Cipher in
  match a with
  | CHACHA20 -> len = 12ul
  | _ -> len `U32.lte` 16ul

let block_len a: Tot (x:UInt32.t { UInt32.v x = Spec.Agile.Cipher.block_length a }) =
  match a with
  | Spec.Agile.Cipher.CHACHA20 -> 64ul
  | _ -> 16ul

let key_len a: Tot (x:UInt32.t { UInt32.v x = Spec.Agile.Cipher.key_length a }) =
  match a with
  | Spec.Agile.Cipher.CHACHA20 -> 32ul
  | Spec.Agile.Cipher.AES128 -> 16ul
  | Spec.Agile.Cipher.AES256 -> 32ul

#push-options "--max_fuel 0 --max_ifuel 0 --z3rlimit 100"
let rec test_ctr_st (a: Spec.Agile.Cipher.cipher_alg)
  (counter: B.buffer UInt8.t)
  (counter_len: UInt32.t)
  (nonce: B.buffer UInt8.t)
  (nonce_len: UInt32.t)
  (k: B.buffer UInt8.t)
  (k_len: UInt32.t)
  (input: B.buffer UInt8.t)
  (input_len: UInt32.t)
  (output: B.buffer UInt8.t)
  (output_len: UInt32.t):
  ST unit
  (requires (fun h0 ->
    B.live h0 counter /\
    B.recallable nonce /\
    B.recallable k /\
    B.recallable input /\
    B.recallable output /\
    B.len k == k_len /\
    B.len nonce == nonce_len /\
    B.len counter == counter_len /\
    B.len input == input_len /\
    B.len output == output_len /\
    B.disjoint input output
  ))
  (ensures (fun _ _ _ -> True))
=
  let open EverCrypt.CTR in

  if not (k_len = key_len a) then
    C.Failure.failwith !$"test_ctr_st: not (key_len = key_len a)"
  else if not (counter_len = 4ul) then
    C.Failure.failwith !$"test_ctr_st: not (counter_len = 4)"
  else if not (nonce_bound a nonce_len) then
    C.Failure.failwith !$"test_ctr_st: not (nonce_bound a nonce_len)"
  else if not (input_len = output_len) then
    C.Failure.failwith !$"test_ctr_st: not (input_len = output_len)"
  else if not (input_len `U32.gte` block_len a) then
    C.Failure.failwith !$"test_ctr_st: not (input_len >= block_len a)"

  else begin
    B.recall k;
    B.recall nonce;
    B.recall input;
    B.recall output;

    // Might only be correct for AES
    let ctr = LowStar.Endianness.load32_be counter in
    if ctr = 0xfffffffful then
      C.Failure.failwith !$"test_ctr_st: ctr = max_uint32"
    else begin
      push_frame ();
      let output' = B.alloca 0uy (block_len a) in

      let s = B.alloca B.null 1ul in
      let r = EverCrypt.CTR.create_in a HyperStack.root s k nonce nonce_len ctr in
      if r <> Success then
        C.Failure.failwith !$"test_ctr_st: create_in <> Success"
      else begin
        let s = B.index s 0ul in
        let input_block = B.sub input 0ul (block_len a) in
        let output_block = B.sub output 0ul (block_len a) in
        update_block (Ghost.hide a) s output' input_block;
        free (Ghost.hide a) s;

        TestLib.compare_and_print !$"of CTR" output_block output' (block_len a);

        let rest = input_len `U32.sub` block_len a in
        if rest `U32.gt` 0ul then begin
          LowStar.Endianness.store32_be counter (ctr `U32.add_mod` 1ul);
          test_ctr_st a counter counter_len nonce nonce_len k k_len
            (B.sub input (block_len a) rest) rest
            (B.sub output (block_len a) rest) rest
        end
      end;
      pop_frame ()
    end
  end


let rec test_chacha20_ctr_loop (vs: lbuffer chacha20_vector): St unit =
  let LB len vs = vs in
  if len <> 0ul then begin
    B.recall vs;
    let v = vs.(0ul) in

    let (LB key_len key), (LB iv_len iv), ctr, (LB plain_len plain), (LB cipher_len cipher) = v in
    let round_len = (plain_len `U32.div` 64ul) `U32.mul` 64ul in
    B.recall plain;
    B.recall cipher;
    B.recall key;
    B.recall iv;
    if cipher_len <> plain_len then
      failwith !$"chacha-ctr: cipher len and plain len don't match"
    else begin
      let plain = B.sub plain 0ul round_len in
      let cipher = B.sub cipher 0ul round_len in
      push_frame ();
      let counter = B.alloca 0uy 4ul in
      LowStar.Endianness.store32_be counter ctr;
      assume (B.disjoint plain cipher);
      test_ctr_st Spec.Agile.Cipher.CHACHA20 counter 4ul iv iv_len key key_len
        plain round_len cipher round_len;
      pop_frame ()
    end;

    B.recall vs;
    test_chacha20_ctr_loop (LB (len `U32.sub` 1ul) (B.offset vs 1ul))
  end
#pop-options

let test_chacha20_ctr () : St unit =
  test_chacha20_ctr_loop Test.Vectors.chacha20_vectors_low

let rec test_aes128_ctr_loop (i: U32.t): St unit =
  let open Test.Vectors.Aes128 in
  if i `U32.gte` vectors_len then
    ()
  else begin
    B.recall vectors;
    assert (U32.v i < B.length vectors);
    let Vector output output_len counter counter_len nonce nonce_len key key_len input input_len =
      vectors.(i)
    in
    assume (B.disjoint input output);
    B.recall counter;
    test_ctr_st Spec.Agile.Cipher.AES128 counter counter_len nonce nonce_len key key_len
      input input_len output output_len;
    test_aes128_ctr_loop (i `U32.add_mod` 1ul)
  end

let test_aes128_ctr () : St unit =
  test_aes128_ctr_loop 0ul

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

inline_for_extraction
noeq
type features = {
  features_avx: bool;
  features_avx2: bool;
  features_bmi2: bool;
  features_adx: bool;
  features_aesni: bool;
  features_shaext: bool;
}

inline_for_extraction
let f_concat (f1 f2: features) : Tot features =
  [@inline_let]
  let avx = f1.features_avx || f2.features_avx in
  [@inline_let]
  let avx2 = f1.features_avx2 || f2.features_avx2 in
  [@inline_let]
  let bmi2 = f1.features_bmi2 || f2.features_bmi2 in
  [@inline_let]
  let adx = f1.features_adx || f2.features_adx in
  [@inline_let]
  let aesni = f1.features_aesni || f2.features_aesni in
  [@inline_let]
  let shaext = f1.features_shaext || f2.features_shaext in
  {
    features_avx = avx;
    features_avx2 = avx2;
    features_bmi2 = bmi2;
    features_adx = adx;
    features_aesni = aesni;
    features_shaext = shaext;
  }

inline_for_extraction
let f_none : features = {
  features_avx = false;
  features_avx2 = false;
  features_bmi2 = false;
  features_adx = false;
  features_aesni = false;
  features_shaext = false;
}

inline_for_extraction
let f_avx : features = // [@inline_let] ({ f_none with features_avx = true; })
{
  features_avx = true;
  features_avx2 = false;
  features_bmi2 = false;
  features_adx = false;
  features_aesni = false;
  features_shaext = false;
}

inline_for_extraction
let f_avx2 : features = // [@inline_let] ({ f_none with features_avx2 = true; })
{
  features_avx = false;
  features_avx2 = true;
  features_bmi2 = false;
  features_adx = false;
  features_aesni = false;
  features_shaext = false;
}

inline_for_extraction
let f_bmi2 : features = // [@inline_let] ({ f_none with features_bmi2 = true; })
{
  features_avx = false;
  features_avx2 = false;
  features_bmi2 = true;
  features_adx = false;
  features_aesni = false;
  features_shaext = false;
}

inline_for_extraction
let f_adx : features = // [@inline_let] ({ f_none with features_adx = true; })
{
  features_avx = false;
  features_avx2 = false;
  features_bmi2 = false;
  features_adx = true;
  features_aesni = false;
  features_shaext = false;
}

inline_for_extraction
let f_aesni : features = // [@inline_let] ({ f_none with features_aesni = true; })
{
  features_avx = false;
  features_avx2 = false;
  features_bmi2 = false;
  features_adx = false;
  features_aesni = true;
  features_shaext = false;
}

inline_for_extraction
let f_shaext : features = // [@inline_let] ({ f_none with features_shaext = true; })
{
  features_avx = false;
  features_avx2 = false;
  features_bmi2 = false;
  features_adx = false;
  features_aesni = false;
  features_shaext = true;
}

inline_for_extraction
type impl = | Hacl | Vale | OpenSSL | BCrypt

inline_for_extraction
let config = (impl & features)

inline_for_extraction
let check_static_config (c: config) : Stack bool (fun _ -> True) (fun _ _ _ -> True) =
  match c with
  | (i, f) ->
    AC.init ();
    let no_avx = not (AC.has_avx ()) in
    let no_avx2 = not (AC.has_avx2 ()) in
    let no_bmi2 = not (AC.has_bmi2 ()) in
    let no_adx = not (AC.has_adx ()) in
    let no_aesni = not (AC.has_aesni ()) in
    let no_shaext = not (AC.has_shaext ()) in
    if
      (f.features_avx && no_avx) ||
      (f.features_avx2 && no_avx2) ||
      (f.features_bmi2 && no_bmi2) ||
      (f.features_adx && no_adx) ||
      (f.features_aesni && no_aesni) ||
      (f.features_shaext && no_shaext)
    then
      false
    else
      match i with
      | Hacl -> SC.hacl
      | Vale -> SC.vale
      | OpenSSL -> SC.openssl
      | BCrypt -> SC.bcrypt

#push-options "--z3rlimit 16"

inline_for_extraction
let set_config (c: config) : Stack unit (fun _ -> True) (fun _ _ _ -> True) =
  match c with
  | (i, f) ->
    (if i <> Hacl then AC.disable_hacl ());
    (if i <> Vale then AC.disable_vale ());
    (if i <> OpenSSL then AC.disable_openssl ());
    (if i <> BCrypt then AC.disable_bcrypt ());
    (if not f.features_avx then AC.disable_avx ());
    (if not f.features_avx2 then AC.disable_avx2 ());
    (if not f.features_bmi2 then AC.disable_bmi2 ());
    (if not f.features_adx then AC.disable_adx ());
    (if not f.features_aesni then AC.disable_aesni ());
    (if not f.features_shaext then AC.disable_shaext ())

#pop-options

inline_for_extraction
let print_config (c: config) : Stack unit (fun _ -> True) (fun _ _ _ -> True) =
  match c with
  | (i, f) ->
    begin match i with
    | Hacl -> C.String.print !$"HACL"
    | Vale -> C.String.print !$"Vale"
    | OpenSSL -> C.String.print !$"OpenSSL"
    | BCrypt -> C.String.print !$"BCrypt"
    end;
    (if f.features_avx then C.String.print !$" avx");
    (if f.features_avx2 then C.String.print !$" avx2");
    (if f.features_bmi2 then C.String.print !$" bmi2");
    (if f.features_adx then C.String.print !$" adx");
    (if f.features_aesni then C.String.print !$" aesni");
    (if f.features_shaext then C.String.print !$" shaext")

inline_for_extraction
noextract
type test_set = ((C.String.t -> St unit) -> St unit) -> St unit

inline_for_extraction
noextract
let ts_nil : test_set = fun _ -> ()

inline_for_extraction
noextract
let ts_one (c: config) : Tot test_set =
  fun test ->
    if check_static_config c
    then begin
      set_config c;
      test (fun s -> print_config c; C.String.print s)
    end else begin
      print_config c;
      C.String.print !$" SKIP because not in static config\n"
    end

inline_for_extraction
noextract
let ts_append (ts1 ts2: test_set) : Tot test_set =
  fun test ->
    ts1 test;
    ts2 test

inline_for_extraction
noextract
let ts_snoc (ts: test_set) (c: config)  : Tot test_set =
  ts `ts_append` ts_one c

inline_for_extraction
noextract
let ts_cons (c: config) (ts: test_set) : Tot test_set =
  ts_one c `ts_append` ts

inline_for_extraction
noextract
let poly1305_test_set =
  (Hacl, f_avx2) `ts_cons` (
  (Hacl, f_avx) `ts_cons` (
  (Hacl, f_none) `ts_cons` (
  (Vale, f_none) `ts_cons` (
  ts_nil))))

inline_for_extraction
noextract
let curve25519_test_set =
  (Hacl, f_bmi2 `f_concat` f_adx) `ts_cons` (
  (Hacl, f_none) `ts_cons`
  ts_nil)

inline_for_extraction
noextract
let aes_gcm_test_set =
  (Vale, f_aesni `f_concat` f_avx) `ts_cons` (
  ts_nil)

inline_for_extraction
noextract
let chacha20poly1305_test_set =
  (Hacl, f_none) `ts_cons`
  ts_nil

inline_for_extraction
noextract
let hash_test_set =
  (Vale, f_none) `ts_cons` (
  (Vale, f_shaext) `ts_cons` (
  (Hacl, f_none) `ts_cons` (
  ts_nil)))

inline_for_extraction
noextract
let chacha20_test_set =
  (Hacl, f_none) `ts_cons`
  ts_nil

inline_for_extraction
noextract
let aes128_ecb_test_set =
  (Vale, f_aesni) `ts_cons` (
  (Hacl, f_none) `ts_cons` (
  ts_nil))

inline_for_extraction
noextract
let aes256_ecb_test_set =
  (Hacl, f_none) `ts_cons` (
  ts_nil)

(* Test bodies *)

inline_for_extraction
noextract
let test_poly1305_body (print: C.String.t -> St unit) : St unit =
    print !$"  >>>>>>>>> Poly1305\n";
    test_poly1305 ()

inline_for_extraction
noextract
let test_curve25519_body (print: C.String.t -> St unit) : St unit =
    print !$"  >>>>>>>>> Curve25519\n";
    test_curve25519 ()

inline_for_extraction
noextract
let test_aes_gcm_body (print: C.String.t -> St unit) : St unit =
    print !$"  >>>>>>>>> AEAD (AES128_GCM old vectors)\n";
    test_aead AES_128_GCM;
    print !$"  >>>>>>>>> AEAD (AES256_GCM old vectors)\n";
    test_aead AES_256_GCM;
    print !$"  >>>>>>>>> AEAD (AES128_GCM vectors)\n";
    test_aes128_gcm ()

inline_for_extraction
noextract
let test_aes_ctr_body (print: C.String.t -> St unit) : St unit =
    print !$"  >>>>>>>>> CTR (AES128_CTR vectors)\n";
    test_aes128_ctr ()

inline_for_extraction
noextract
let test_chacha20_ctr_body (print: C.String.t -> St unit) : St unit =
    print !$"  >>>>>>>>> CTR (CHACHA20 vectors)\n";
    test_chacha20_ctr ()

inline_for_extraction
let test_chacha20poly1305_body (print: C.String.t -> St unit) : St unit =
    print !$"  >>>>>>>>> AEAD (ChachaPoly vectors)\n";
    test_chacha20poly1305 ();
    print !$"  >>>>>>>>> AEAD (ChachaPoly old vectors)\n";
    test_aead CHACHA20_POLY1305

inline_for_extraction
noextract
let test_hash_body (print: C.String.t -> St unit) : St unit =
    print !$"  >>>>>>>>> Hash (Test.Hash)\n";
    Test.Hash.main ();
    print !$"  >>>>>>>>> Hash (Test.NoHeap)\n";
    test_hash hash_vectors_low;
    print !$"  >>>>>>>>> HMAC (Test.NoHeap)\n";
    test_hmac hmac_vectors_low;
    print !$"  >>>>>>>>> HMAC_DRBG (Test.NoHeap)\n";
    test_hmac_drbg hmac_drbg_vectors_low;
    print !$"  >>>>>>>>> HKDF (Test.NoHeap)\n";
    test_hkdf hkdf_vectors_low

inline_for_extraction
noextract
let test_chacha20_body (print: C.String.t -> St unit) : St unit =
    print !$"  >>>>>>>>> Chacha20\n";
    test_chacha20 chacha20_vectors_low

inline_for_extraction
noextract
let test_aes128_ecb_body (print: C.String.t -> St unit) : St unit =
    print !$"  >>>>>>>>> AES128_ECB\n";
    test_aes_ecb AES128

inline_for_extraction
noextract
let test_aes256_ecb_body (print: C.String.t -> St unit) : St unit =
    print !$"  >>>>>>>>> AES256_ECB\n";
    test_aes_ecb AES256

(* Summary *)

let print_sep () : St unit =
  C.String.print !$"=====================\n"

let test_all () : St unit =
  // The CTR-mode tests reuse the test modifiers for the underlying ciphers.
  poly1305_test_set         test_poly1305_body;
  print_sep ();
  curve25519_test_set       test_curve25519_body;
  print_sep ();
  aes_gcm_test_set          test_aes_gcm_body;
  print_sep ();
  aes_gcm_test_set          test_aes_ctr_body;
  print_sep ();
  chacha20_test_set         test_chacha20_ctr_body;
  print_sep ();
  chacha20poly1305_test_set test_chacha20poly1305_body;
  print_sep ();
  hash_test_set             test_hash_body;
  print_sep ();
  chacha20_test_set         test_chacha20_body;
  print_sep ();
  aes128_ecb_test_set       test_aes128_ecb_body;
  print_sep ();
  aes256_ecb_test_set       test_aes256_ecb_body

let main (): St C.exit_code =
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
