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
  B.length ek >= ekv_length a /\
  B.as_seq h (B.gsub ek 0ul (UInt32.uint_to_t (ekv_length a))) `S.equal` expand #a (G.reveal kv) /\ (
  match i with
  | Vale_AES128_GCM ->
      a = AES128_GCM /\
      EverCrypt.TargetConfig.x64 /\ Vale.X64.CPU_Features_s.(aesni_enabled /\ pclmulqdq_enabled /\ avx_enabled) /\
      B.length ek = ekv_length a + 176
  | Vale_AES256_GCM ->
      a = AES256_GCM /\
      EverCrypt.TargetConfig.x64 /\ Vale.X64.CPU_Features_s.(aesni_enabled /\ pclmulqdq_enabled /\ avx_enabled) /\
      B.length ek = ekv_length a + 176
  | Hacl_CHACHA20_POLY1305 ->
      a = CHACHA20_POLY1305 /\
      B.length ek = ekv_length a /\
      True)

let invariant_loc_in_footprint #a s m =
  ()

let frame_invariant #a l s h0 h1 =
  ()


/// Actual stateful API
/// -------------------

let alg_of_state a s =
  let open LowStar.BufferOps in
  let Ek impl _ _ = !*s in
  match impl with
  | Hacl_CHACHA20_POLY1305 -> CHACHA20_POLY1305
  | Vale_AES128_GCM -> AES128_GCM
  | Vale_AES256_GCM -> AES256_GCM

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
let aes_gcm_key_expansion (a: aes_gcm_alg): Vale.Wrapper.X64.AES.key_expansion_st (vale_alg_of_alg a) =
  match a with
  | AES128_GCM -> Vale.Wrapper.X64.AES.aes128_key_expansion_stdcall
  | AES256_GCM -> Vale.Wrapper.X64.AES.aes256_key_expansion_stdcall

inline_for_extraction noextract
let aes_gcm_keyhash_init (a: aes_gcm_alg): Vale.Wrapper.X64.AEShash.keyhash_init_st (vale_alg_of_alg a) =
  match a with
  | AES128_GCM -> Vale.Wrapper.X64.AEShash.aes128_keyhash_init_stdcall
  | AES256_GCM -> Vale.Wrapper.X64.AEShash.aes256_keyhash_init_stdcall

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
  let has_avx = EverCrypt.AutoConfig2.has_avx() in
  if EverCrypt.TargetConfig.x64 && (has_aesni && has_pclmulqdq && has_avx) then (
    let ek = B.malloc r 0uy (ekv_len a + 176ul) in
    let keys_b = B.sub ek 0ul (key_offset a) in
    let hkeys_b = B.sub ek (key_offset a) 128ul in
    aes_gcm_key_expansion a k keys_b;
    aes_gcm_keyhash_init a
      (let k = G.reveal kv in
      let k_nat = Vale.Def.Words.Seq_s.seq_uint8_to_seq_nat8 k in
      let k_w = Vale.Def.Words.Seq_s.seq_nat8_to_seq_nat32_LE k_nat in G.hide k_w)
      keys_b hkeys_b;
    let h1 = ST.get() in

    // We need to prove that we are copying the
    // expanded key into it. In particular, that the hashed part corresponds to the spec
    let lemma_aux_hkeys () : Lemma
      (let k = G.reveal kv in
        let k_nat = Vale.Def.Words.Seq_s.seq_uint8_to_seq_nat8 k in
        let k_w = Vale.Def.Words.Seq_s.seq_nat8_to_seq_nat32_LE k_nat in
        let hkeys_quad = Vale.AES.OptPublic.get_hkeys_reqs (Vale.Def.Types_s.reverse_bytes_quad32 (
          Vale.AES.AES_s.aes_encrypt_LE (vale_alg_of_alg a) k_w (Vale.Def.Words_s.Mkfour 0 0 0 0))) in
        let hkeys = Vale.Def.Words.Seq_s.seq_nat8_to_seq_uint8 (Vale.Def.Types_s.le_seq_quad32_to_bytes hkeys_quad) in
        Seq.equal (B.as_seq h1 hkeys_b) hkeys)
        = let k = G.reveal kv in
          let k_nat = Vale.Def.Words.Seq_s.seq_uint8_to_seq_nat8 k in
          let k_w = Vale.Def.Words.Seq_s.seq_nat8_to_seq_nat32_LE k_nat in
          let hkeys_quad = Vale.AES.OptPublic.get_hkeys_reqs (Vale.Def.Types_s.reverse_bytes_quad32 (
            Vale.AES.AES_s.aes_encrypt_LE (vale_alg_of_alg a) k_w (Vale.Def.Words_s.Mkfour 0 0 0 0))) in
          let hkeys = Vale.Def.Words.Seq_s.seq_nat8_to_seq_uint8 (Vale.Def.Types_s.le_seq_quad32_to_bytes hkeys_quad) in
        Vale.AES.Gcm_simplify.le_bytes_to_seq_quad32_uint8_to_nat8_length (B.as_seq h1 hkeys_b);
        assert_norm (128 / 16 = 8);
        // These two are equal
        Vale.AES.OptPublic.get_hkeys_reqs_injective
          (Vale.Def.Types_s.reverse_bytes_quad32 (
            Vale.AES.AES_s.aes_encrypt_LE (vale_alg_of_alg a) k_w (Vale.Def.Words_s.Mkfour 0 0 0 0)))
          hkeys_quad
          (Vale.Def.Types_s.le_bytes_to_seq_quad32 (Vale.Def.Words.Seq_s.seq_uint8_to_seq_nat8 (B.as_seq h1 hkeys_b)));
        Vale.Arch.Types.le_seq_quad32_to_bytes_to_seq_quad32 (Vale.Def.Words.Seq_s.seq_uint8_to_seq_nat8 (B.as_seq h1 hkeys_b))

    in lemma_aux_hkeys ();

    let h2 = ST.get() in
    assert (Seq.equal (B.as_seq h2 (B.gsub ek 0ul (ekv_len a))) (expand #a (G.reveal kv)));
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
let aes_gcm_encrypt (a:aes_gcm_alg): Vale.Wrapper.X64.GCMencryptOpt.encrypt_opt_stdcall_st (vale_alg_of_alg a) =
  match a with
  | AES128_GCM -> Vale.Wrapper.X64.GCMencryptOpt.gcm128_encrypt_opt_stdcall
  | AES256_GCM -> Vale.Wrapper.X64.GCMencryptOpt256.gcm256_encrypt_opt_stdcall

#reset-options "--z3rlimit 100 --max_fuel 0 --max_ifuel 0 --using_facts_from '* -FStar.Seq.Properties.slice_slice'"
inline_for_extraction noextract
let encrypt_aes_gcm (a: aes_gcm_alg): encrypt_st a =
fun s iv iv_len ad ad_len plain plain_len cipher tag ->
  if B.is_null s then
    InvalidKey
  else
    // This condition is never satisfied in F* because of the iv_length precondition on iv.
    // We keep it here to be defensive when extracting to C    
    if iv_len = 0ul then
      InvalidIVLength
    else (
    let open LowStar.BufferOps in
    let Ek i kv ek = !*s in
    assert (
      let k = G.reveal kv in
      let k_nat = Vale.Def.Words.Seq_s.seq_uint8_to_seq_nat8 k in
      let k_w = Vale.Def.Words.Seq_s.seq_nat8_to_seq_nat32_LE k_nat in
      Vale.AES.AES_s.is_aes_key_LE (vale_alg_of_alg a) k_w);

    push_frame();
    let scratch_b = B.sub ek (ekv_len a) 176ul in

    let ek = B.sub ek 0ul (ekv_len a) in
    let keys_b = B.sub ek 0ul (key_offset a) in
    let hkeys_b = B.sub ek (key_offset a) 128ul in

    let h0 = get() in

    // The iv can be arbitrary length, hence we need to allocate a new one to perform the hashing
    let tmp_iv = B.alloca 0uy 16ul in

    // There is no SMTPat on le_bytes_to_seq_quad32_to_bytes and the converse,
    // so we need an explicit lemma
    let lemma_hkeys_reqs () : Lemma
      (let k = G.reveal kv in
      let k_nat = Vale.Def.Words.Seq_s.seq_uint8_to_seq_nat8 k in
      let k_w = Vale.Def.Words.Seq_s.seq_nat8_to_seq_nat32_LE k_nat in
      Vale.AES.OptPublic.hkeys_reqs_pub
        (Vale.Def.Types_s.le_bytes_to_seq_quad32 (Vale.Def.Words.Seq_s.seq_uint8_to_seq_nat8 (B.as_seq h0 hkeys_b)))
        (Vale.Def.Types_s.reverse_bytes_quad32 (Vale.AES.AES_s.aes_encrypt_LE (vale_alg_of_alg a) k_w (Vale.Def.Words_s.Mkfour 0 0 0 0))))
    = let k = G.reveal kv in
        let k_nat = Vale.Def.Words.Seq_s.seq_uint8_to_seq_nat8 k in
        let k_w = Vale.Def.Words.Seq_s.seq_nat8_to_seq_nat32_LE k_nat in
        let hkeys_quad = Vale.AES.OptPublic.get_hkeys_reqs (Vale.Def.Types_s.reverse_bytes_quad32 (
          Vale.AES.AES_s.aes_encrypt_LE (vale_alg_of_alg a) k_w (Vale.Def.Words_s.Mkfour 0 0 0 0))) in
        let hkeys = Vale.Def.Words.Seq_s.seq_nat8_to_seq_uint8 (Vale.Def.Types_s.le_seq_quad32_to_bytes hkeys_quad) in
        assert (Seq.equal (B.as_seq h0 hkeys_b) hkeys);
        calc (==) {
          Vale.Def.Types_s.le_bytes_to_seq_quad32 (Vale.Def.Words.Seq_s.seq_uint8_to_seq_nat8 hkeys);
          (==) { Vale.Arch.Types.le_bytes_to_seq_quad32_to_bytes hkeys_quad }
          hkeys_quad;
        }

    in lemma_hkeys_reqs ();

    // We perform the hashing of the iv. The extra buffer and the hashed iv are the same
    Vale.Wrapper.X64.GCM_IV.compute_iv (vale_alg_of_alg a) 
    (let k = G.reveal kv in
      let k_nat = Vale.Def.Words.Seq_s.seq_uint8_to_seq_nat8 k in
      let k_w = Vale.Def.Words.Seq_s.seq_nat8_to_seq_nat32_LE k_nat in G.hide k_w ) 
      iv iv_len 
      tmp_iv tmp_iv 
      hkeys_b;

    let h0 = get() in

    aes_gcm_encrypt a
      (let k = G.reveal kv in
      let k_nat = Vale.Def.Words.Seq_s.seq_uint8_to_seq_nat8 k in
      let k_w = Vale.Def.Words.Seq_s.seq_nat8_to_seq_nat32_LE k_nat in G.hide k_w)
      (Ghost.hide (Vale.Def.Words.Seq_s.seq_uint8_to_seq_nat8 (B.as_seq h0 iv)))
      plain
      (uint32_to_uint64 plain_len)
      ad
      (uint32_to_uint64 ad_len)
      tmp_iv
      cipher
      tag
      keys_b
      hkeys_b
      scratch_b;

    let h1 = get() in

    // This assert is needed for z3 to pick up sequence equality for ciphertext
    // and tag. It could be avoided if the spec returned both instead of appending them
    assert (
      let kv_nat = Vale.Def.Words.Seq_s.seq_uint8_to_seq_nat8 (G.reveal kv) in
      let iv_nat = Vale.Def.Words.Seq_s.seq_uint8_to_seq_nat8 (B.as_seq h0 iv) in
      // `ad` is called `auth` in Vale world; "additional data", "authenticated
      // data", potato, potato
      let ad_nat = Vale.Def.Words.Seq_s.seq_uint8_to_seq_nat8 (B.as_seq h0 ad) in
      let plain_nat = Vale.Def.Words.Seq_s.seq_uint8_to_seq_nat8 (B.as_seq h0 plain) in
      let cipher_nat, tag_nat =
        Vale.AES.GCM_s.gcm_encrypt_LE (vale_alg_of_alg a) kv_nat iv_nat plain_nat ad_nat
      in
      Seq.equal (B.as_seq h1 cipher) (Vale.Def.Words.Seq_s.seq_nat8_to_seq_uint8 cipher_nat) /\
      Seq.equal (B.as_seq h1 tag) (Vale.Def.Words.Seq_s.seq_nat8_to_seq_uint8 tag_nat));


    pop_frame();
    Success
    )

let encrypt_aes128_gcm: encrypt_st AES128_GCM = encrypt_aes_gcm AES128_GCM
let encrypt_aes256_gcm: encrypt_st AES256_GCM = encrypt_aes_gcm AES256_GCM

let encrypt #a s iv iv_len ad ad_len plain plain_len cipher tag =
  if B.is_null s then
    InvalidKey
  else
    let open LowStar.BufferOps in
    let Ek i kv ek = !*s in
    match i with
    | Vale_AES128_GCM ->
        encrypt_aes128_gcm s iv iv_len ad ad_len plain plain_len cipher tag
    | Vale_AES256_GCM ->
        encrypt_aes256_gcm s iv iv_len ad ad_len plain plain_len cipher tag
    | Hacl_CHACHA20_POLY1305 ->
        // This condition is never satisfied in F* because of the iv_length precondition on iv.
        // We keep it here to be defensive when extracting to C    
        if iv_len <> 12ul then
          InvalidIVLength
        else begin
          // Length restrictions
          assert_norm (pow2 31 + pow2 32 / 64 <= pow2 32 - 1);
          Hacl.Impl.Chacha20Poly1305.aead_encrypt_chacha_poly
            ek iv ad_len ad plain_len plain cipher tag;
          Success
        end

inline_for_extraction noextract
let aes_gcm_decrypt (a:aes_gcm_alg): Vale.Wrapper.X64.GCMdecryptOpt.decrypt_opt_stdcall_st (vale_alg_of_alg a) =
  match a with
  | AES128_GCM -> Vale.Wrapper.X64.GCMdecryptOpt.gcm128_decrypt_opt_stdcall
  | AES256_GCM -> Vale.Wrapper.X64.GCMdecryptOpt256.gcm256_decrypt_opt_stdcall

#reset-options "--z3rlimit 100 --max_fuel 0 --max_ifuel 0 --using_facts_from '* -FStar.Seq.Properties.slice_slice'"
inline_for_extraction noextract
let decrypt_aes_gcm (a: aes_gcm_alg): decrypt_st a =
fun s iv iv_len ad ad_len cipher cipher_len tag dst ->
  if B.is_null s then
    InvalidKey
  else
    // This condition is never satisfied in F* because of the iv_length precondition on iv.
    // We keep it here to be defensive when extracting to C
    if iv_len = 0ul then
      InvalidIVLength
    else (
    let open LowStar.BufferOps in
    let Ek i kv ek = !*s in
      assert (
        let k = G.reveal kv in
        let k_nat = Vale.Def.Words.Seq_s.seq_uint8_to_seq_nat8 k in
        let k_w = Vale.Def.Words.Seq_s.seq_nat8_to_seq_nat32_LE k_nat in
        Vale.AES.AES_s.is_aes_key_LE (vale_alg_of_alg a) k_w);

      push_frame();
      let scratch_b = B.sub ek (ekv_len a) 176ul in

      let ek = B.sub ek 0ul (ekv_len a) in
      let keys_b = B.sub ek 0ul (key_offset a) in
      let hkeys_b = B.sub ek (key_offset a) 128ul in

      let h0 = get() in

      // The iv can be arbitrary length, hence we need to allocate a new one to perform the hashing
      let tmp_iv = B.alloca 0uy 16ul in

      // There is no SMTPat on le_bytes_to_seq_quad32_to_bytes and the converse,
      // so we need an explicit lemma
      let lemma_hkeys_reqs () : Lemma
        (let k = G.reveal kv in
        let k_nat = Vale.Def.Words.Seq_s.seq_uint8_to_seq_nat8 k in
        let k_w = Vale.Def.Words.Seq_s.seq_nat8_to_seq_nat32_LE k_nat in
        Vale.AES.OptPublic.hkeys_reqs_pub
          (Vale.Def.Types_s.le_bytes_to_seq_quad32 (Vale.Def.Words.Seq_s.seq_uint8_to_seq_nat8 (B.as_seq h0 hkeys_b)))
          (Vale.Def.Types_s.reverse_bytes_quad32 (Vale.AES.AES_s.aes_encrypt_LE (vale_alg_of_alg a) k_w (Vale.Def.Words_s.Mkfour 0 0 0 0))))
      = let k = G.reveal kv in
            let k_nat = Vale.Def.Words.Seq_s.seq_uint8_to_seq_nat8 k in
            let k_w = Vale.Def.Words.Seq_s.seq_nat8_to_seq_nat32_LE k_nat in
            let hkeys_quad = Vale.AES.OptPublic.get_hkeys_reqs (Vale.Def.Types_s.reverse_bytes_quad32 (
            Vale.AES.AES_s.aes_encrypt_LE (vale_alg_of_alg a) k_w (Vale.Def.Words_s.Mkfour 0 0 0 0))) in
            let hkeys = Vale.Def.Words.Seq_s.seq_nat8_to_seq_uint8 (Vale.Def.Types_s.le_seq_quad32_to_bytes hkeys_quad) in
            assert (Seq.equal (B.as_seq h0 hkeys_b) hkeys);
            calc (==) {
            Vale.Def.Types_s.le_bytes_to_seq_quad32 (Vale.Def.Words.Seq_s.seq_uint8_to_seq_nat8 hkeys);
            (==) { Vale.Arch.Types.le_bytes_to_seq_quad32_to_bytes hkeys_quad }
            hkeys_quad;
            }

      in lemma_hkeys_reqs ();

      // We perform the hashing of the iv. The extra buffer and the hashed iv are the same
      Vale.Wrapper.X64.GCM_IV.compute_iv (vale_alg_of_alg a) 
      (let k = G.reveal kv in
        let k_nat = Vale.Def.Words.Seq_s.seq_uint8_to_seq_nat8 k in
        let k_w = Vale.Def.Words.Seq_s.seq_nat8_to_seq_nat32_LE k_nat in G.hide k_w ) 
        iv iv_len
        tmp_iv tmp_iv 
        hkeys_b;

      let r = aes_gcm_decrypt a
        (let k = G.reveal kv in
        let k_nat = Vale.Def.Words.Seq_s.seq_uint8_to_seq_nat8 k in
        let k_w = Vale.Def.Words.Seq_s.seq_nat8_to_seq_nat32_LE k_nat in G.hide k_w)
        (Ghost.hide (Vale.Def.Words.Seq_s.seq_uint8_to_seq_nat8 (B.as_seq h0 iv)))
        cipher
        (uint32_to_uint64 cipher_len)
        ad
        (uint32_to_uint64 ad_len)
        tmp_iv
        dst
        tag
        keys_b
        hkeys_b 
        scratch_b in

      let h1 = get() in

      // This assert is needed for z3 to pick up sequence equality for ciphertext
      // It could be avoided if the spec returned both instead of appending them
      assert (
        let kv_nat = Vale.Def.Words.Seq_s.seq_uint8_to_seq_nat8 (G.reveal kv) in
        let iv_nat = Vale.Def.Words.Seq_s.seq_uint8_to_seq_nat8 (B.as_seq h0 iv) in
        // `ad` is called `auth` in Vale world; "additional data", "authenticated
        // data", potato, potato
        let ad_nat = Vale.Def.Words.Seq_s.seq_uint8_to_seq_nat8 (B.as_seq h0 ad) in
        let cipher_nat = Vale.Def.Words.Seq_s.seq_uint8_to_seq_nat8 (B.as_seq h0 cipher) in
        let tag_nat = Vale.Def.Words.Seq_s.seq_uint8_to_seq_nat8 (B.as_seq h0 tag) in
        let plain_nat, success =
          Vale.AES.GCM_s.gcm_decrypt_LE (vale_alg_of_alg a) kv_nat iv_nat cipher_nat ad_nat tag_nat
        in
        Seq.equal (B.as_seq h1 dst) (Vale.Def.Words.Seq_s.seq_nat8_to_seq_uint8 plain_nat) /\
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
      )

let decrypt_aes128_gcm: decrypt_st AES128_GCM = decrypt_aes_gcm AES128_GCM
let decrypt_aes256_gcm: decrypt_st AES256_GCM = decrypt_aes_gcm AES256_GCM

let decrypt #a s iv iv_len ad ad_len cipher cipher_len tag dst =
  if B.is_null s then
    InvalidKey
  else
    let open LowStar.BufferOps in
    let Ek i kv ek = !*s in
    match i with
    | Vale_AES128_GCM ->
        decrypt_aes128_gcm s iv iv_len ad ad_len cipher cipher_len tag dst
    | Vale_AES256_GCM ->
        decrypt_aes256_gcm s iv iv_len ad ad_len cipher cipher_len tag dst
    | Hacl_CHACHA20_POLY1305 ->
        // This condition is never satisfied in F* because of the iv_length precondition on iv.
        // We keep it here to be defensive when extracting to C
        if iv_len <> 12ul then
          InvalidIVLength
        else begin
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
        end

let free #a s =
  let open LowStar.BufferOps in
  let Ek _ _ ek = !*s in
  B.free ek;
  B.free s
