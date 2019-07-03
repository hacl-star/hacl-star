module EverCrypt.CTR.Keys

/// This is an internal-to-EverCrypt module, which provides low-level
/// definitions corresponding to Spec.Cipher.Expansion, i.e. shared between CTR
/// and AEAD.

module S = FStar.Seq
module G = FStar.Ghost

module HS = FStar.HyperStack
module ST = FStar.HyperStack.ST
module MB = LowStar.Monotonic.Buffer
module B = LowStar.Buffer

open FStar.HyperStack.ST
open FStar.Integers

open Spec.Agile.Cipher
open Spec.Cipher.Expansion

friend Spec.Cipher.Expansion

#set-options "--z3rlimit 100 --max_fuel 0 --max_ifuel 0"

let _: squash (inversion impl) = allow_inversion impl

inline_for_extraction noextract
let vale_impl = a:impl { a = Vale_AES128 \/ a = Vale_AES256 }

let vale_alg_of_vale_impl (i: vale_impl) =
  match i with
  | Vale_AES128 -> Vale.AES.AES_s.AES_128
  | Vale_AES256 -> Vale.AES.AES_s.AES_256

inline_for_extraction noextract
let key_offset (i: vale_impl):
  o:UInt32.t { UInt32.v o = Vale.Wrapper.X64.AES.key_offset (vale_alg_of_vale_impl i) }
=
  match i with
  | Vale_AES128 -> 176ul
  | Vale_AES256 -> 240ul

inline_for_extraction
let concrete_xkey_len (i: impl): Tot (x:UInt32.t { UInt32.v x = concrete_xkey_length i }) =
  match i with
  | Hacl_CHACHA20 -> 32ul
  | Vale_AES256
  | Vale_AES128 ->
      key_offset i + 128ul

inline_for_extraction noextract
let aes_gcm_key_expansion (i: vale_impl):
  Vale.Wrapper.X64.AES.key_expansion_st (vale_alg_of_vale_impl i) =
  match i with
  | Vale_AES128 -> Vale.Wrapper.X64.AES.aes128_key_expansion_stdcall
  | Vale_AES256 -> Vale.Wrapper.X64.AES.aes256_key_expansion_stdcall

inline_for_extraction noextract
let aes_gcm_keyhash_init (i: vale_impl):
  Vale.Wrapper.X64.AEShash.keyhash_init_st (vale_alg_of_vale_impl i) =
  match i with
  | Vale_AES128 -> Vale.Wrapper.X64.AEShash.aes128_keyhash_init_stdcall
  | Vale_AES256 -> Vale.Wrapper.X64.AEShash.aes256_keyhash_init_stdcall

let uint8 = Lib.IntTypes.uint8

// Because the wrapper are over UInt8.t not Lib.IntTypes.uint8
friend Lib.IntTypes

inline_for_extraction noextract
let vale_expand (i: vale_impl) (k ek: B.buffer uint8):
  Stack unit
    (requires (fun h0 ->
      let a = cipher_alg_of_impl i in
      Vale.X64.CPU_Features_s.(aesni_enabled /\ pclmulqdq_enabled /\ avx_enabled) /\
      B.live h0 k /\ B.live h0 ek /\
      B.disjoint k ek /\
      B.length k = key_length a /\
      B.length ek >= concrete_xkey_length i))
    (ensures (fun h0 _ h1 ->
      B.(modifies (loc_buffer ek) h0 h1) /\
      B.as_seq h1 (B.gsub ek 0ul (concrete_xkey_len i)) `S.equal`
        concrete_expand i (B.as_seq h0 k)))
=
  let h0 = ST.get () in
  [@ inline_let ]
  let a = cipher_alg_of_impl i in
  [@ inline_let ]
  let va = vale_alg_of_vale_impl i in
  let kv: G.erased (key a) = G.hide (B.as_seq h0 k) in
  let keys_b = B.sub ek 0ul (key_offset i) in
  let hkeys_b = B.sub ek (key_offset i) 128ul in

  aes_gcm_key_expansion i k keys_b;
  aes_gcm_keyhash_init i
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
        Vale.AES.AES_s.aes_encrypt_LE va k_w (Vale.Def.Words_s.Mkfour 0 0 0 0))) in
      let hkeys = Vale.Def.Words.Seq_s.seq_nat8_to_seq_uint8 (Vale.Def.Types_s.le_seq_quad32_to_bytes hkeys_quad) in
      Seq.equal (B.as_seq h1 hkeys_b) hkeys)
      = let k = G.reveal kv in
        let k_nat = Vale.Def.Words.Seq_s.seq_uint8_to_seq_nat8 k in
        let k_w = Vale.Def.Words.Seq_s.seq_nat8_to_seq_nat32_LE k_nat in
        let hkeys_quad = Vale.AES.OptPublic.get_hkeys_reqs (Vale.Def.Types_s.reverse_bytes_quad32 (
          Vale.AES.AES_s.aes_encrypt_LE va k_w (Vale.Def.Words_s.Mkfour 0 0 0 0))) in
        let hkeys = Vale.Def.Words.Seq_s.seq_nat8_to_seq_uint8 (Vale.Def.Types_s.le_seq_quad32_to_bytes hkeys_quad) in
      Vale.AES.Gcm_simplify.le_bytes_to_seq_quad32_uint8_to_nat8_length (B.as_seq h1 hkeys_b);
      assert_norm (128 / 16 = 8);
      // These two are equal
      Vale.AES.OptPublic.get_hkeys_reqs_injective
        (Vale.Def.Types_s.reverse_bytes_quad32 (
          Vale.AES.AES_s.aes_encrypt_LE va k_w (Vale.Def.Words_s.Mkfour 0 0 0 0)))
        hkeys_quad
        (Vale.Def.Types_s.le_bytes_to_seq_quad32 (Vale.Def.Words.Seq_s.seq_uint8_to_seq_nat8 (B.as_seq h1 hkeys_b)));
      Vale.Arch.Types.le_seq_quad32_to_bytes_to_seq_quad32 (Vale.Def.Words.Seq_s.seq_uint8_to_seq_nat8 (B.as_seq h1 hkeys_b))

  in lemma_aux_hkeys ()
