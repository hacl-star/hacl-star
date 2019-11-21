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

open Spec.Agile.AEAD
open Spec.Cipher.Expansion
open EverCrypt.CTR.Keys

friend Spec.Agile.AEAD
friend Spec.Cipher.Expansion
friend EverCrypt.CTR.Keys

#set-options "--z3rlimit 100 --max_fuel 0 --max_ifuel 0"

/// Defining abstract predicates, invariants, footprint, etc.
/// ---------------------------------------------------------

let _: squash (inversion impl) = allow_inversion impl

/// We now distinguish between an expanded key (as mandated by NIST spec) and a
/// **concrete** expanded key, which may contain implementation-specific details
/// and extra precomputations. In the rest of this module, we rely on concrete
/// expanded keys, which are parameterized over an implementation, instead of
/// regular expanded keys, which are parameterized over an algorithm. Helpers
/// allow us to move from one notion to the other.

let supported_alg_of_impl (i: impl): supported_alg =
  match i with
  | Vale_AES128 -> AES128_GCM
  | Vale_AES256 -> AES256_GCM
  | Hacl_CHACHA20 -> CHACHA20_POLY1305

let alg_of_vale_impl (i: vale_impl) =
  match i with
  | Vale_AES128 -> AES128_GCM
  | Vale_AES256 -> AES256_GCM

noeq
type state_s a =
| Ek: impl:impl ->
    kv:G.erased (kv a) ->
    ek:B.buffer UInt8.t -> // concrete expanded key
    state_s a

let invert_state_s (a: alg): Lemma
  (requires True)
  (ensures (inversion (state_s a)))
  [ SMTPat (state_s a) ]
=
  allow_inversion (state_s a)

let freeable_s #a (Ek _ _ ek) = B.freeable ek

let footprint_s #a (Ek _ _ ek) = B.loc_addr_of_buffer ek

let invariant_s #a h (Ek i kv ek) =
  is_supported_alg a /\
  a = supported_alg_of_impl i /\
  B.live h ek /\
  B.length ek >= concrete_xkey_length i /\
  B.as_seq h (B.gsub ek 0ul (UInt32.uint_to_t (concrete_xkey_length i)))
    `S.equal` concrete_expand i (G.reveal kv) /\ (
  match i with
  | Vale_AES128
  | Vale_AES256 ->
      EverCrypt.TargetConfig.x64 /\
      Vale.X64.CPU_Features_s.(aesni_enabled /\ pclmulqdq_enabled /\ avx_enabled /\ movbe_enabled /\ sse_enabled) /\
      // Expanded key length + precomputed stuff + scratch space (AES-GCM specific)
      B.length ek =
        vale_xkey_length (cipher_alg_of_supported_alg a) + 176
  | Hacl_CHACHA20 ->
      B.length ek = concrete_xkey_length i)

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
  | Hacl_CHACHA20 -> CHACHA20_POLY1305
  | Vale_AES128 -> AES128_GCM
  | Vale_AES256 -> AES256_GCM

let as_kv #a (Ek _ kv _) =
  G.reveal kv

#push-options "--z3rlimit 10 --max_fuel 0 --max_ifuel 0 --z3cliopt smt.QI.EAGER_THRESHOLD=5"

let create_in_chacha20_poly1305: create_in_st CHACHA20_POLY1305 = fun r dst k ->
  let h0 = ST.get () in
  let ek = B.malloc r 0uy 32ul in
  let p = B.malloc r (Ek Hacl_CHACHA20 (G.hide (B.as_seq h0 k)) ek) 1ul in
  B.blit k 0ul ek 0ul 32ul;
  B.upd dst 0ul p;
  let h2 = ST.get() in
  B.modifies_only_not_unused_in B.(loc_buffer dst) h0 h2;
  Success

#pop-options

inline_for_extraction noextract
let create_in_aes_gcm (i: vale_impl):
  create_in_st (alg_of_vale_impl i) =
fun r dst k ->
  let a = alg_of_vale_impl i in
  let h0 = ST.get () in
  let kv: G.erased (kv a) = G.hide (B.as_seq h0 k) in
  let has_aesni = EverCrypt.AutoConfig2.has_aesni () in
  let has_pclmulqdq = EverCrypt.AutoConfig2.has_pclmulqdq () in
  let has_avx = EverCrypt.AutoConfig2.has_avx() in
  let has_sse = EverCrypt.AutoConfig2.has_sse() in
  let has_movbe = EverCrypt.AutoConfig2.has_movbe() in
  if EverCrypt.TargetConfig.x64 && (has_aesni && has_pclmulqdq && has_avx && has_sse && has_movbe) then (
    let ek = B.malloc r 0uy (concrete_xkey_len i + 176ul) in

    vale_expand i k ek;

    let h2 = ST.get () in
    B.modifies_only_not_unused_in B.loc_none h0 h2;
    let p = B.malloc r (Ek i (G.hide (B.as_seq h0 k)) ek) 1ul in
    let open LowStar.BufferOps in
    dst *= p;
    let h3 = ST.get() in
    B.modifies_only_not_unused_in B.(loc_buffer dst) h2 h3;
    Success

  ) else
    UnsupportedAlgorithm


let create_in_aes128_gcm: create_in_st AES128_GCM = create_in_aes_gcm Vale_AES128
let create_in_aes256_gcm: create_in_st AES256_GCM = create_in_aes_gcm Vale_AES256

let create_in #a r dst k =
  match a with
  | AES128_GCM -> create_in_aes128_gcm r dst k
  | AES256_GCM -> create_in_aes256_gcm r dst k
  | CHACHA20_POLY1305 -> create_in_chacha20_poly1305 r dst k
  | _ -> UnsupportedAlgorithm

inline_for_extraction noextract
let aes_gcm_encrypt (i: vale_impl):
  Vale.Wrapper.X64.GCMencryptOpt.encrypt_opt_stdcall_st (vale_alg_of_vale_impl i) =
  match i with
  | Vale_AES128 -> Vale.Wrapper.X64.GCMencryptOpt.gcm128_encrypt_opt_stdcall
  | Vale_AES256 -> Vale.Wrapper.X64.GCMencryptOpt256.gcm256_encrypt_opt_stdcall

#reset-options "--z3rlimit 100 --max_fuel 0 --max_ifuel 0 --using_facts_from '* -FStar.Seq.Properties.slice_slice'"
inline_for_extraction noextract
let encrypt_aes_gcm (i: vale_impl): encrypt_st (alg_of_vale_impl i) =
fun s iv iv_len ad ad_len plain plain_len cipher tag ->
  if B.is_null s then
    InvalidKey
  else
    let a = alg_of_vale_impl i in
    // This condition is never satisfied in F* because of the iv_length precondition on iv.
    // We keep it here to be defensive when extracting to C
    if iv_len = 0ul then
      InvalidIVLength
    else
      let open LowStar.BufferOps in
      let Ek _ kv ek = !*s in
      assert (
        let k = G.reveal kv in
        let k_nat = Vale.Def.Words.Seq_s.seq_uint8_to_seq_nat8 k in
        let k_w = Vale.Def.Words.Seq_s.seq_nat8_to_seq_nat32_LE k_nat in
        Vale.AES.AES_s.is_aes_key_LE (vale_alg_of_alg a) k_w);

      push_frame();
      let scratch_b = B.sub ek (concrete_xkey_len i) 176ul in

      let ek = B.sub ek 0ul (concrete_xkey_len i) in
      let keys_b = B.sub ek 0ul (key_offset i) in
      let hkeys_b = B.sub ek (key_offset i) 128ul in

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

      aes_gcm_encrypt i
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

let encrypt_aes128_gcm: encrypt_st AES128_GCM = encrypt_aes_gcm Vale_AES128
let encrypt_aes256_gcm: encrypt_st AES256_GCM = encrypt_aes_gcm Vale_AES256

let encrypt #a s iv iv_len ad ad_len plain plain_len cipher tag =
  if B.is_null s then
    InvalidKey
  else
    let open LowStar.BufferOps in
    let Ek i kv ek = !*s in
    match i with
    | Vale_AES128 ->
        encrypt_aes128_gcm s iv iv_len ad ad_len plain plain_len cipher tag
    | Vale_AES256 ->
        encrypt_aes256_gcm s iv iv_len ad ad_len plain plain_len cipher tag
    | Hacl_CHACHA20 ->
        // This condition is never satisfied in F* because of the iv_length precondition on iv.
        // We keep it here to be defensive when extracting to C
        if iv_len <> 12ul then
          InvalidIVLength
        else begin
          // Length restrictions
          assert_norm (pow2 31 + pow2 32 / 64 <= pow2 32 - 1);
          EverCrypt.Chacha20Poly1305.aead_encrypt
            ek iv ad_len ad plain_len plain cipher tag;
          Success
        end

inline_for_extraction noextract
let aes_gcm_decrypt (i: vale_impl):
  Vale.Wrapper.X64.GCMdecryptOpt.decrypt_opt_stdcall_st (vale_alg_of_vale_impl i) =
  match i with
  | Vale_AES128 -> Vale.Wrapper.X64.GCMdecryptOpt.gcm128_decrypt_opt_stdcall
  | Vale_AES256 -> Vale.Wrapper.X64.GCMdecryptOpt256.gcm256_decrypt_opt_stdcall

#reset-options "--z3rlimit 100 --max_fuel 0 --max_ifuel 0 --using_facts_from '* -FStar.Seq.Properties.slice_slice'"
inline_for_extraction noextract
let decrypt_aes_gcm (i: vale_impl): decrypt_st (alg_of_vale_impl i) =
fun s iv iv_len ad ad_len cipher cipher_len tag dst ->
  if B.is_null s then
    InvalidKey
  else
    // This condition is never satisfied in F* because of the iv_length precondition on iv.
    // We keep it here to be defensive when extracting to C
    if iv_len = 0ul then
      InvalidIVLength
    else
      let a = alg_of_vale_impl i in
      let open LowStar.BufferOps in
      let Ek _ kv ek = !*s in
        assert (
          let k = G.reveal kv in
          let k_nat = Vale.Def.Words.Seq_s.seq_uint8_to_seq_nat8 k in
          let k_w = Vale.Def.Words.Seq_s.seq_nat8_to_seq_nat32_LE k_nat in
          Vale.AES.AES_s.is_aes_key_LE (vale_alg_of_alg a) k_w);

        push_frame();
        let scratch_b = B.sub ek (concrete_xkey_len i) 176ul in

        let ek = B.sub ek 0ul (concrete_xkey_len i) in
        let keys_b = B.sub ek 0ul (key_offset i) in
        let hkeys_b = B.sub ek (key_offset i) 128ul in

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

        let r = aes_gcm_decrypt i
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

let decrypt_aes128_gcm: decrypt_st AES128_GCM = decrypt_aes_gcm Vale_AES128
let decrypt_aes256_gcm: decrypt_st AES256_GCM = decrypt_aes_gcm Vale_AES256

let decrypt #a s iv iv_len ad ad_len cipher cipher_len tag dst =
  if B.is_null s then
    InvalidKey
  else
    let open LowStar.BufferOps in
    let Ek i kv ek = !*s in
    match i with
    | Vale_AES128 ->
        decrypt_aes128_gcm s iv iv_len ad ad_len cipher cipher_len tag dst
    | Vale_AES256 ->
        decrypt_aes256_gcm s iv iv_len ad ad_len cipher cipher_len tag dst
    | Hacl_CHACHA20 ->
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
          let r = EverCrypt.Chacha20Poly1305.aead_decrypt
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
