module EverCrypt.AEAD

module S = FStar.Seq
module G = FStar.Ghost

module HS = FStar.HyperStack
module ST = FStar.HyperStack.ST
module MB = LowStar.Monotonic.Buffer
module B = LowStar.Buffer

open FStar.HyperStack.ST
open FStar.Integers
open FStar.Int.Cast

open Spec.AEAD

friend Spec.AEAD

#set-options "--z3rlimit 100 --max_fuel 0 --max_ifuel 0"

/// Defining abstract predicates, invariants, footprint, etc.
/// ---------------------------------------------------------

/// This type serves several purposes. First, it captures valid combinations:
/// some pair of ``(alg, provider)`` might not be valid, and for a pair of
/// ``(alg, provider)``, there may be multiple options. Second, it maintains at
/// run-time which algorithm we're dealing with, which in turn allows encrypt
/// and decrypt to take only an erased algorithm.
type impl =
| Hacl_CHACHA20_POLY1305
| Vale_AES128_GCM
| Vale_AES256_GCM

let _: squash (inversion impl) = allow_inversion impl

noeq
type state_s a =
| Ek: impl:impl ->
    kv:G.erased (kv a) ->
    ek:B.buffer UInt8.t ->
    state_s a

let invert_state_s (a: alg): Lemma
  (requires True)
  (ensures (inversion (state_s a)))
  [ SMTPat (state_s a) ]
=
  allow_inversion (state_s a)

let freeable_s #a (Ek _ _ ek) = B.freeable ek

let footprint_s #a (Ek _ _ ek) = B.loc_addr_of_buffer ek

// Note: once we start having a new implementation of AES-GCM, either the new
// implementation will have to be compatible with the run-time representation of
// expanded keys used by Vale, or we'll have to make the Spec.expand take an
// `impl` instead of an `alg`.
let invariant_s #a h (Ek i kv ek) =
  is_supported_alg a /\
  B.live h ek /\
  B.as_seq h ek `S.equal` expand #a (G.reveal kv) /\ (
  match i with
  | Vale_AES128_GCM ->
      a = AES128_GCM /\
      EverCrypt.TargetConfig.x64 /\ X64.CPU_Features_s.(aesni_enabled /\ pclmulqdq_enabled)
  | Vale_AES256_GCM ->
      a = AES256_GCM /\
      EverCrypt.TargetConfig.x64 /\ X64.CPU_Features_s.(aesni_enabled /\ pclmulqdq_enabled)
  | Hacl_CHACHA20_POLY1305 ->
      a = CHACHA20_POLY1305 /\
      True)

let invariant_loc_in_footprint #a s m =
  ()

let frame_invariant #a l s h0 h1 =
  ()


/// Actual stateful API
/// -------------------

let as_kv #a (Ek _ kv _) =
  G.reveal kv

let create_in_chacha20_poly1305: create_in_st CHACHA20_POLY1305 = fun r dst k ->
  let open LowStar.BufferOps in
  let h0 = ST.get () in
  let ek = B.malloc r 0uy 32ul in
  let p = B.malloc r (Ek Hacl_CHACHA20_POLY1305 (G.hide (B.as_seq h0 k)) ek) 1ul in
  B.blit k 0ul ek 0ul 32ul;
  let h1 = ST.get () in
  dst *= p;
  B.modifies_only_not_unused_in B.(loc_buffer dst) h0 h1;
  Success

inline_for_extraction noextract
let aes_gcm_alg = a:alg { a = AES128_GCM \/ a = AES256_GCM }

inline_for_extraction noextract
let key_offset (a: aes_gcm_alg) =
  match a with
  | AES128_GCM -> 176ul
  | AES256_GCM -> 240ul

inline_for_extraction
let ekv_len (a: supported_alg): Tot (x:UInt32.t { UInt32.v x = ekv_length a }) =
  match a with
  | CHACHA20_POLY1305 -> 32ul
  | AES128_GCM -> key_offset a + 128ul
  | AES256_GCM -> key_offset a + 128ul

inline_for_extraction noextract
let aes_gcm_key_expansion (a: aes_gcm_alg): AES_stdcalls.key_expansion_st (vale_alg_of_alg a) =
  match a with
  | AES128_GCM -> AES_stdcalls.aes128_key_expansion_stdcall
  | AES256_GCM -> AES_stdcalls.aes256_key_expansion_stdcall

inline_for_extraction noextract
let aes_gcm_keyhash_init (a: aes_gcm_alg): AEShash_stdcalls.keyhash_init_st (vale_alg_of_alg a) =
  match a with
  | AES128_GCM -> AEShash_stdcalls.aes128_keyhash_init_stdcall
  | AES256_GCM -> AEShash_stdcalls.aes256_keyhash_init_stdcall

inline_for_extraction noextract
let impl_of_aes_gcm_alg (a: aes_gcm_alg): impl =
  match a with
  | AES128_GCM -> Vale_AES128_GCM
  | AES256_GCM -> Vale_AES256_GCM

inline_for_extraction noextract
let create_in_aes_gcm (a: aes_gcm_alg):
  create_in_st a =
fun r dst k ->
  let h0 = ST.get () in
  let kv: G.erased (kv a) = G.hide (B.as_seq h0 k) in
  let has_aesni = EverCrypt.AutoConfig2.has_aesni () in
  let has_pclmulqdq = EverCrypt.AutoConfig2.has_pclmulqdq () in
  if EverCrypt.TargetConfig.x64 && (has_aesni && has_pclmulqdq) then (
    let ek = B.malloc r 0uy (ekv_len a) in
    let keys_b = B.sub ek 0ul (key_offset a) in
    let hkeys_b = B.sub ek (key_offset a) 128ul in
    aes_gcm_key_expansion a k keys_b;
    aes_gcm_keyhash_init a
      (let k = G.reveal kv in
      let k_nat = Words.Seq_s.seq_uint8_to_seq_nat8 k in
      let k_w = Words.Seq_s.seq_nat8_to_seq_nat32_LE k_nat in G.hide k_w)
      keys_b hkeys_b;
    let h1 = ST.get() in

    // We need to prove that we are copying the
    // expanded key into it. In particular, that the hashed part corresponds to the spec
    let lemma_aux_hkeys () : Lemma
      (let k = G.reveal kv in
        let k_nat = Words.Seq_s.seq_uint8_to_seq_nat8 k in
        let k_w = Words.Seq_s.seq_nat8_to_seq_nat32_LE k_nat in
        let hkeys_quad = OptPublic.get_hkeys_reqs (Types_s.reverse_bytes_quad32 (
          AES_s.aes_encrypt_LE (vale_alg_of_alg a) k_w (Words_s.Mkfour 0 0 0 0))) in
        let hkeys = Words.Seq_s.seq_nat8_to_seq_uint8 (Types_s.le_seq_quad32_to_bytes hkeys_quad) in
        Seq.equal (B.as_seq h1 hkeys_b) hkeys)
        = let k = G.reveal kv in
          let k_nat = Words.Seq_s.seq_uint8_to_seq_nat8 k in
          let k_w = Words.Seq_s.seq_nat8_to_seq_nat32_LE k_nat in
          let hkeys_quad = OptPublic.get_hkeys_reqs (Types_s.reverse_bytes_quad32 (
            AES_s.aes_encrypt_LE (vale_alg_of_alg a) k_w (Words_s.Mkfour 0 0 0 0))) in
          let hkeys = Words.Seq_s.seq_nat8_to_seq_uint8 (Types_s.le_seq_quad32_to_bytes hkeys_quad) in
        Gcm_simplify.le_bytes_to_seq_quad32_uint8_to_nat8_length (B.as_seq h1 hkeys_b);
        assert_norm (128 / 16 = 8);
        // These two are equal
        OptPublic.get_hkeys_reqs_injective
          (Types_s.reverse_bytes_quad32 (
            AES_s.aes_encrypt_LE (vale_alg_of_alg a) k_w (Words_s.Mkfour 0 0 0 0)))
          hkeys_quad
          (Types_s.le_bytes_to_seq_quad32 (Words.Seq_s.seq_uint8_to_seq_nat8 (B.as_seq h1 hkeys_b)));
        Arch.Types.le_seq_quad32_to_bytes_to_seq_quad32 (Words.Seq_s.seq_uint8_to_seq_nat8 (B.as_seq h1 hkeys_b))

    in lemma_aux_hkeys ();

    let h2 = ST.get() in
    assert (Seq.equal (B.as_seq h2 ek)  (expand #a (G.reveal kv)));
    B.modifies_only_not_unused_in B.loc_none h0 h2;
    let p = B.malloc r (Ek (impl_of_aes_gcm_alg a) (G.hide (B.as_seq h0 k)) ek) 1ul in
    let open LowStar.BufferOps in
    dst *= p;
    let h3 = ST.get() in
    B.modifies_only_not_unused_in B.(loc_buffer dst) h2 h3;
    Success

  ) else
    UnsupportedAlgorithm


let create_in_aes128_gcm: create_in_st AES128_GCM = create_in_aes_gcm AES128_GCM
let create_in_aes256_gcm: create_in_st AES256_GCM = create_in_aes_gcm AES256_GCM

let create_in #a r dst k =
  match a with
  | AES128_GCM -> create_in_aes128_gcm r dst k
  | AES256_GCM -> create_in_aes256_gcm r dst k
  | CHACHA20_POLY1305 -> create_in_chacha20_poly1305 r dst k
  | _ -> UnsupportedAlgorithm

inline_for_extraction noextract
let aes_gcm_encrypt (a:aes_gcm_alg): GCMencryptOpt_stdcalls.encrypt_opt_stdcall_st (vale_alg_of_alg a) =
  match a with
  | AES128_GCM -> GCMencryptOpt_stdcalls.gcm128_encrypt_opt_stdcall
  | AES256_GCM -> GCMencryptOpt256_stdcalls.gcm256_encrypt_opt_stdcall

#set-options "--z3rlimit 200 --max_fuel 0 --max_ifuel 0"
inline_for_extraction noextract
let encrypt_aes_gcm (a: aes_gcm_alg): encrypt_st a =
fun s iv ad ad_len plain plain_len cipher tag ->
  if B.is_null s then
    InvalidKey
  else
    let open LowStar.BufferOps in
    let Ek i kv ek = !*s in
    assert (
      let k = G.reveal kv in
      let k_nat = Words.Seq_s.seq_uint8_to_seq_nat8 k in
      let k_w = Words.Seq_s.seq_nat8_to_seq_nat32_LE k_nat in
      AES_s.is_aes_key_LE (vale_alg_of_alg a) k_w);

    push_frame();
    let keys_b = B.sub ek 0ul (key_offset a) in
    let hkeys_b = B.sub ek (key_offset a) 128ul in

    let h0 = get() in

    // The iv is modified by Vale, which the API does not allow. Hence
    // we allocate a temporary buffer and blit the contents of the iv
    let tmp_iv = B.alloca 0uy 16ul in
    let h_pre = get() in

    MB.blit iv 0ul tmp_iv 0ul 12ul;

    let h0 = get() in

    // Some help is needed to prove that the end of the tmp_iv buffer
    // is still 0s after blitting the contents of iv into the start of the buffer
    let lemma_iv_eq () : Lemma
      (let iv_nat = Words.Seq_s.seq_uint8_to_seq_nat8 (B.as_seq h0 iv) in
      let iv_nat = Seq.append iv_nat (Seq.create 4 0) in
      Seq.equal
        (Words.Seq_s.seq_uint8_to_seq_nat8 (B.as_seq h0 tmp_iv))
        iv_nat)
      = let iv_nat = Words.Seq_s.seq_uint8_to_seq_nat8 (B.as_seq h0 iv) in
        let iv_nat = Seq.append iv_nat (Seq.create 4 0) in
        let s_tmp = Words.Seq_s.seq_uint8_to_seq_nat8 (B.as_seq h0 tmp_iv) in
        Seq.lemma_index_slice (B.as_seq h0 tmp_iv) 12 16 0;
        Seq.lemma_index_slice (B.as_seq h0 tmp_iv) 12 16 1;
        Seq.lemma_index_slice (B.as_seq h0 tmp_iv) 12 16 2;
        Seq.lemma_index_slice (B.as_seq h0 tmp_iv) 12 16 3;
        assert (Seq.equal iv_nat s_tmp)


    in lemma_iv_eq ();

    // There is no SMTPat on le_bytes_to_seq_quad32_to_bytes and the converse,
    // so we need an explicit lemma
    let lemma_hkeys_reqs () : Lemma
      (let k = G.reveal kv in
      let k_nat = Words.Seq_s.seq_uint8_to_seq_nat8 k in
      let k_w = Words.Seq_s.seq_nat8_to_seq_nat32_LE k_nat in
      OptPublic.hkeys_reqs_pub
        (Types_s.le_bytes_to_seq_quad32 (Words.Seq_s.seq_uint8_to_seq_nat8 (B.as_seq h0 hkeys_b)))
        (Types_s.reverse_bytes_quad32 (AES_s.aes_encrypt_LE (vale_alg_of_alg a) k_w (Words_s.Mkfour 0 0 0 0))))
      = let k = G.reveal kv in
        let k_nat = Words.Seq_s.seq_uint8_to_seq_nat8 k in
        let k_w = Words.Seq_s.seq_nat8_to_seq_nat32_LE k_nat in
        let hkeys_quad = OptPublic.get_hkeys_reqs (Types_s.reverse_bytes_quad32 (
          AES_s.aes_encrypt_LE (vale_alg_of_alg a) k_w (Words_s.Mkfour 0 0 0 0))) in
        let hkeys = Words.Seq_s.seq_nat8_to_seq_uint8 (Types_s.le_seq_quad32_to_bytes hkeys_quad) in
        assert (Seq.equal (B.as_seq h0 hkeys_b) hkeys);
        calc (==) {
          Types_s.le_bytes_to_seq_quad32 (Words.Seq_s.seq_uint8_to_seq_nat8 hkeys);
          (==) { Arch.Types.le_bytes_to_seq_quad32_to_bytes hkeys_quad }
          hkeys_quad;
        }

    in lemma_hkeys_reqs ();

    // These asserts prove that 4096 * (len {plain, ad}) are smaller than pow2_32
    assert (max_length a = pow2 20 - 1 - 16);
    assert_norm (4096 * (pow2 20 - 1) < Words_s.pow2_32);
    assert_norm (4096 * (pow2 20 - 1 - 16) < Words_s.pow2_32);

    aes_gcm_encrypt a
      (let k = G.reveal kv in
      let k_nat = Words.Seq_s.seq_uint8_to_seq_nat8 k in
      let k_w = Words.Seq_s.seq_nat8_to_seq_nat32_LE k_nat in G.hide k_w)
      plain
      (uint32_to_uint64 plain_len)
      ad
      (uint32_to_uint64 ad_len)
      tmp_iv
      cipher
      tag
      keys_b
      hkeys_b;

    let h1 = get() in

    // This assert is needed for z3 to pick up sequence equality for ciphertext
    // and tag. It could be avoided if the spec returned both instead of appending them
    assert (
      let kv_nat = Words.Seq_s.seq_uint8_to_seq_nat8 (G.reveal kv) in
      let iv_nat = Words.Seq_s.seq_uint8_to_seq_nat8 (B.as_seq h0 iv) in
      // the specification takes a seq16 for convenience, but actually discards
      // the trailing four bytes; we are, however, constrained by it and append
      // zeroes just to satisfy the spec
      let iv_nat = S.append iv_nat (S.create 4 0) in
      // `ad` is called `auth` in Vale world; "additional data", "authenticated
      // data", potato, potato
      let ad_nat = Words.Seq_s.seq_uint8_to_seq_nat8 (B.as_seq h0 ad) in
      let plain_nat = Words.Seq_s.seq_uint8_to_seq_nat8 (B.as_seq h0 plain) in
      assert (max_length a = pow2 20 - 1 - 16);
      assert_norm (4096 * (pow2 20 - 1 - 16) < Words_s.pow2_32);
      let cipher_nat, tag_nat =
        GCM_s.gcm_encrypt_LE (vale_alg_of_alg a) kv_nat iv_nat plain_nat ad_nat
      in
      Seq.equal (B.as_seq h1 cipher) (Words.Seq_s.seq_nat8_to_seq_uint8 cipher_nat) /\
      Seq.equal (B.as_seq h1 tag) (Words.Seq_s.seq_nat8_to_seq_uint8 tag_nat));


    pop_frame();
    Success

let encrypt_aes128_gcm: encrypt_st AES128_GCM = encrypt_aes_gcm AES128_GCM
let encrypt_aes256_gcm: encrypt_st AES256_GCM = encrypt_aes_gcm AES256_GCM

let encrypt #a s iv ad ad_len plain plain_len cipher tag =
  if B.is_null s then
    InvalidKey
  else
    let open LowStar.BufferOps in
    let Ek i kv ek = !*s in
    match i with
    | Vale_AES128_GCM ->
        encrypt_aes128_gcm s iv ad ad_len plain plain_len cipher tag
    | Vale_AES256_GCM ->
        encrypt_aes256_gcm s iv ad ad_len plain plain_len cipher tag
    | Hacl_CHACHA20_POLY1305 ->
        // Length restrictions
        assert_norm (pow2 31 + pow2 32 / 64 <= pow2 32 - 1);
        Hacl.Impl.Chacha20Poly1305.aead_encrypt_chacha_poly
          ek iv ad_len ad plain_len plain cipher tag;
        Success

inline_for_extraction noextract
let aes_gcm_decrypt (a:aes_gcm_alg): GCMdecryptOpt_stdcalls.decrypt_opt_stdcall_st (vale_alg_of_alg a) =
  match a with
  | AES128_GCM -> GCMdecryptOpt_stdcalls.gcm128_decrypt_opt_stdcall
  | AES256_GCM -> GCMdecryptOpt256_stdcalls.gcm256_decrypt_opt_stdcall

#set-options "--z3rlimit 200"
inline_for_extraction noextract
let decrypt_aes_gcm (a: aes_gcm_alg): decrypt_st a =
fun s iv ad ad_len cipher cipher_len tag dst ->
  if B.is_null s then
    InvalidKey

  else
    let open LowStar.BufferOps in
    let Ek i kv ek = !*s in
      assert (
        let k = G.reveal kv in
        let k_nat = Words.Seq_s.seq_uint8_to_seq_nat8 k in
        let k_w = Words.Seq_s.seq_nat8_to_seq_nat32_LE k_nat in
        AES_s.is_aes_key_LE (vale_alg_of_alg a) k_w);

      push_frame();
      let keys_b = B.sub ek 0ul (key_offset a) in
      let hkeys_b = B.sub ek (key_offset a) 128ul in

      // The iv is modified by Vale, which the API does not allow. Hence
      // we allocate a temporary buffer and blit the contents of the iv
      let tmp_iv = B.alloca 0uy 16ul in
      let h_pre = get() in

      MB.blit iv 0ul tmp_iv 0ul 12ul;

      let h0 = get() in

      // Some help is needed to prove that the end of the tmp_iv buffer
      // is still 0s after blitting the contents of iv into the start of the buffer
      let lemma_iv_eq () : Lemma
        (let iv_nat = Words.Seq_s.seq_uint8_to_seq_nat8 (B.as_seq h0 iv) in
        let iv_nat = Seq.append iv_nat (Seq.create 4 0) in
        Seq.equal
          (Words.Seq_s.seq_uint8_to_seq_nat8 (B.as_seq h0 tmp_iv))
          iv_nat)
        = let iv_nat = Words.Seq_s.seq_uint8_to_seq_nat8 (B.as_seq h0 iv) in
          let iv_nat = Seq.append iv_nat (Seq.create 4 0) in
          let s_tmp = Words.Seq_s.seq_uint8_to_seq_nat8 (B.as_seq h0 tmp_iv) in
          Seq.lemma_index_slice (B.as_seq h0 tmp_iv) 12 16 0;
          Seq.lemma_index_slice (B.as_seq h0 tmp_iv) 12 16 1;
          Seq.lemma_index_slice (B.as_seq h0 tmp_iv) 12 16 2;
          Seq.lemma_index_slice (B.as_seq h0 tmp_iv) 12 16 3;
          assert (Seq.equal iv_nat s_tmp)


      in lemma_iv_eq ();

      // These asserts prove that 4096 * (len {cipher, ad}) are smaller than pow2_32
      assert (max_length AES128_GCM = pow2 20 - 1 - 16);
      assert (max_length AES256_GCM = pow2 20 - 1 - 16);
      assert_norm (4096 * (pow2 20 - 1) < Words_s.pow2_32);
      assert_norm (4096 * (pow2 20 - 1 - 16) < Words_s.pow2_32);


      let h0 = get() in

      // There is no SMTPat on le_bytes_to_seq_quad32_to_bytes and the converse,
      // so we need an explicit lemma
      let lemma_hkeys_reqs () : Lemma
        (let k = G.reveal kv in
        let k_nat = Words.Seq_s.seq_uint8_to_seq_nat8 k in
        let k_w = Words.Seq_s.seq_nat8_to_seq_nat32_LE k_nat in
        OptPublic.hkeys_reqs_pub
          (Types_s.le_bytes_to_seq_quad32 (Words.Seq_s.seq_uint8_to_seq_nat8 (B.as_seq h0 hkeys_b)))
          (Types_s.reverse_bytes_quad32 (AES_s.aes_encrypt_LE (vale_alg_of_alg a) k_w (Words_s.Mkfour 0 0 0 0))))
        = let k = G.reveal kv in
          let k_nat = Words.Seq_s.seq_uint8_to_seq_nat8 k in
          let k_w = Words.Seq_s.seq_nat8_to_seq_nat32_LE k_nat in
          let hkeys_quad = OptPublic.get_hkeys_reqs (Types_s.reverse_bytes_quad32 (
            AES_s.aes_encrypt_LE (vale_alg_of_alg a) k_w (Words_s.Mkfour 0 0 0 0))) in
          let hkeys = Words.Seq_s.seq_nat8_to_seq_uint8 (Types_s.le_seq_quad32_to_bytes hkeys_quad) in
          assert (Seq.equal (B.as_seq h0 hkeys_b) hkeys);
          calc (==) {
            Types_s.le_bytes_to_seq_quad32 (Words.Seq_s.seq_uint8_to_seq_nat8 hkeys);
            (==) { Arch.Types.le_bytes_to_seq_quad32_to_bytes hkeys_quad }
            hkeys_quad;
          }

      in lemma_hkeys_reqs ();

      let r = aes_gcm_decrypt a
        (let k = G.reveal kv in
        let k_nat = Words.Seq_s.seq_uint8_to_seq_nat8 k in
        let k_w = Words.Seq_s.seq_nat8_to_seq_nat32_LE k_nat in G.hide k_w)
        cipher
        (uint32_to_uint64 cipher_len)
        ad
        (uint32_to_uint64 ad_len)
        tmp_iv
        dst
        tag
        keys_b
        hkeys_b in

      let h1 = get() in

      // This assert is needed for z3 to pick up sequence equality for ciphertext
      // It could be avoided if the spec returned both instead of appending them
      assert (
        let kv_nat = Words.Seq_s.seq_uint8_to_seq_nat8 (G.reveal kv) in
        let iv_nat = Words.Seq_s.seq_uint8_to_seq_nat8 (B.as_seq h0 iv) in
        // the specification takes a seq16 for convenience, but actually discards
        // the trailing four bytes; we are, however, constrained by it and append
        // zeroes just to satisfy the spec
        let iv_nat = S.append iv_nat (S.create 4 0) in
        // `ad` is called `auth` in Vale world; "additional data", "authenticated
        // data", potato, potato
        let ad_nat = Words.Seq_s.seq_uint8_to_seq_nat8 (B.as_seq h0 ad) in
        let cipher_nat = Words.Seq_s.seq_uint8_to_seq_nat8 (B.as_seq h0 cipher) in
        let tag_nat = Words.Seq_s.seq_uint8_to_seq_nat8 (B.as_seq h0 tag) in
        assert (max_length AES128_GCM = pow2 20 - 1 - 16);
        assert (max_length AES256_GCM = pow2 20 - 1 - 16);
        assert_norm (4096 * (pow2 20 - 1 - 16) < Words_s.pow2_32);
        let plain_nat, success =
          GCM_s.gcm_decrypt_LE (vale_alg_of_alg a) kv_nat iv_nat cipher_nat ad_nat tag_nat
        in
        Seq.equal (B.as_seq h1 dst) (Words.Seq_s.seq_nat8_to_seq_uint8 plain_nat) /\
        (UInt64.v r = 0) == success);

      assert (
        let kv = G.reveal kv in
        let cipher_tag = B.as_seq h0 cipher `S.append` B.as_seq h0 tag in
        Seq.equal (Seq.slice cipher_tag (S.length cipher_tag - tag_length a) (S.length cipher_tag))
          (B.as_seq h0 tag) /\
        Seq.equal (Seq.slice cipher_tag 0 (S.length cipher_tag - tag_length a)) (B.as_seq h0 cipher));

      pop_frame();

      if r = 0uL then
        Success
      else
        AuthenticationFailure

let decrypt_aes128_gcm: decrypt_st AES128_GCM = decrypt_aes_gcm AES128_GCM
let decrypt_aes256_gcm: decrypt_st AES256_GCM = decrypt_aes_gcm AES256_GCM

let decrypt #a s iv ad ad_len cipher cipher_len tag dst =
  if B.is_null s then
    InvalidKey
  else
    let open LowStar.BufferOps in
    let Ek i kv ek = !*s in
    match i with
    | Vale_AES128_GCM ->
        decrypt_aes128_gcm s iv ad ad_len cipher cipher_len tag dst
    | Vale_AES256_GCM ->
        decrypt_aes256_gcm s iv ad ad_len cipher cipher_len tag dst
    | Hacl_CHACHA20_POLY1305 ->
        [@ inline_let ] let bound = pow2 32 - 1 - 16 in
        assert (v cipher_len <= bound);
        assert_norm (bound + 16 <= pow2 32 - 1);
        assert_norm (pow2 31 + bound / 64 <= pow2 32 - 1);

        let h0 = ST.get () in
        let r = Hacl.Impl.Chacha20Poly1305.aead_decrypt_chacha_poly
          ek iv ad_len ad cipher_len dst cipher tag
        in
        assert (
          let cipher_tag = B.as_seq h0 cipher `S.append` B.as_seq h0 tag in
          let tag_s = S.slice cipher_tag (S.length cipher_tag - tag_length CHACHA20_POLY1305) (S.length cipher_tag) in
          let cipher_s = S.slice cipher_tag 0 (S.length cipher_tag - tag_length CHACHA20_POLY1305) in
          S.equal cipher_s (B.as_seq h0 cipher) /\ S.equal tag_s (B.as_seq h0 tag));

        if r = 0ul then
          Success
        else
          AuthenticationFailure

let free #a s =
  let open LowStar.BufferOps in
  let Ek _ _ ek = !*s in
  B.free ek;
  B.free s
