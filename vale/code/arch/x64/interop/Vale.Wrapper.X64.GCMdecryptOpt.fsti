module Vale.Wrapper.X64.GCMdecryptOpt

open Vale.X64.CPU_Features_s
open FStar.HyperStack.ST
module B = LowStar.Buffer
module HS = FStar.HyperStack
module DV = LowStar.BufferView.Down
module UV = LowStar.BufferView.Up
open Vale.AsLowStar.MemoryHelpers
open FStar.Mul
open Vale.Def.Words_s
open Vale.Def.Words.Seq_s
open Vale.Def.Types_s
open Vale.AES.GCM_helpers
open Vale.AES.AES_s
open Vale.AES.GCM_s
open Vale.AES.GHash_s
open Vale.AES.GCTR_s
open Vale.AES.GCTR
open Vale.Interop.Base
open Vale.Arch.Types
open Vale.AES.OptPublic

let uint8_p = B.buffer UInt8.t
let uint64 = UInt64.t

let disjoint_or_eq (b1 b2:uint8_p) = B.disjoint b1 b2 \/ b1 == b2

let length_aux (b:uint8_p) : Lemma
  (requires B.length b = 176)
  (ensures DV.length (get_downview b) % 16 = 0) =
    let db = get_downview b in
    DV.length_eq db

let length_aux2 (b:uint8_p) : Lemma
  (requires B.length b = 240)
  (ensures DV.length (get_downview b) % 16 = 0) =
    let db = get_downview b in
    DV.length_eq db

let length_aux3 (b:uint8_p) (n:nat) : Lemma
  (requires B.length b = 16 * n)
  (ensures DV.length (get_downview b) % 16 = 0) =
    let db = get_downview b in
    DV.length_eq db;
    FStar.Math.Lemmas.cancel_mul_mod n 16

let length_aux4 (b:uint8_p) : Lemma
  (requires B.length b = 16)
  (ensures DV.length (get_downview b) % 16 = 0) =
    let db = get_downview b in
    DV.length_eq db

let length_aux5 (b:uint8_p) : Lemma
  (requires B.length b = 128)
  (ensures DV.length (get_downview b) % 16 = 0) =
    let db = get_downview b in
    DV.length_eq db

#set-options "--z3rlimit 30 --max_fuel 0 --max_ifuel 0"

inline_for_extraction noextract
let decrypt_opt_stdcall_st (a: algorithm { a = AES_128 \/ a = AES_256 }) =
  key:Ghost.erased (Seq.seq nat32) ->
  iv:Ghost.erased supported_iv_LE ->
  cipher_b:uint8_p ->
  cipher_len:uint64 ->
  auth_b:uint8_p ->
  auth_len:uint64 ->
  iv_b:uint8_p ->
  out_b:uint8_p ->
  tag_b:uint8_p ->
  keys_b:uint8_p ->
  hkeys_b:uint8_p ->
  scratch_b:uint8_p ->

  Stack UInt64.t
    (requires fun h0 ->
      B.disjoint tag_b out_b /\ B.disjoint tag_b hkeys_b /\
      B.disjoint tag_b cipher_b /\ B.disjoint tag_b auth_b /\
      B.disjoint tag_b iv_b /\ disjoint_or_eq tag_b keys_b /\

      B.disjoint iv_b keys_b /\ B.disjoint iv_b out_b /\
      B.disjoint iv_b cipher_b /\ B.disjoint iv_b hkeys_b /\
      B.disjoint iv_b auth_b /\

      B.disjoint out_b keys_b /\ B.disjoint out_b hkeys_b /\
      B.disjoint out_b auth_b /\ disjoint_or_eq out_b cipher_b /\

      B.disjoint cipher_b keys_b /\ B.disjoint cipher_b hkeys_b /\
      B.disjoint cipher_b auth_b /\

      disjoint_or_eq keys_b hkeys_b /\
      B.disjoint keys_b auth_b /\ B.disjoint hkeys_b auth_b /\

      B.disjoint cipher_b scratch_b /\ B.disjoint auth_b scratch_b /\
      B.disjoint iv_b scratch_b /\ B.disjoint out_b scratch_b /\
      B.disjoint tag_b scratch_b /\ B.disjoint keys_b scratch_b /\
      B.disjoint hkeys_b scratch_b /\

      B.live h0 auth_b /\ B.live h0 keys_b /\
      B.live h0 iv_b /\ B.live h0 hkeys_b /\
      B.live h0 out_b /\ B.live h0 cipher_b /\
      B.live h0 tag_b /\ B.live h0 scratch_b /\

      B.length auth_b = UInt64.v auth_len /\
      B.length iv_b = 16 /\
      B.length cipher_b = UInt64.v cipher_len /\
      B.length out_b = B.length cipher_b /\
      B.length hkeys_b = 128 /\
      B.length tag_b == 16 /\
      B.length keys_b = Vale.Wrapper.X64.AES.key_offset a /\
      B.length scratch_b = 176 /\

      aesni_enabled /\ pclmulqdq_enabled /\ avx_enabled /\ sse_enabled /\ movbe_enabled /\
      is_aes_key_LE a (Ghost.reveal key) /\
      (Seq.equal (B.as_seq h0 keys_b)
        (seq_nat8_to_seq_uint8 (le_seq_quad32_to_bytes (key_to_round_keys_LE a (Ghost.reveal key))))) /\

      hkeys_reqs_pub (le_bytes_to_seq_quad32 (seq_uint8_to_seq_nat8 (B.as_seq h0 hkeys_b)))
        (reverse_bytes_quad32 (aes_encrypt_LE a (Ghost.reveal key) (Mkfour 0 0 0 0))) /\

      (le_bytes_to_quad32 (seq_uint8_to_seq_nat8 (B.as_seq h0 iv_b)) ==
        compute_iv_BE (aes_encrypt_LE a (Ghost.reveal key) (Mkfour 0 0 0 0)) (Ghost.reveal iv))
    )
    (ensures fun h0 c h1 ->
      B.modifies (B.loc_union (B.loc_buffer scratch_b)
                 (B.loc_union (B.loc_buffer iv_b)
                 (B.loc_buffer out_b))) h0 h1 /\

      (let cipher = seq_uint8_to_seq_nat8 (B.as_seq h0 cipher_b) in
       let auth = seq_uint8_to_seq_nat8 (B.as_seq h0 auth_b) in
       let expected_tag = seq_uint8_to_seq_nat8 (B.as_seq h0 tag_b) in
       let plain, result = gcm_decrypt_LE a (seq_nat32_to_seq_nat8_LE (Ghost.reveal key)) (Ghost.reveal iv) cipher auth expected_tag in
       Seq.equal (seq_uint8_to_seq_nat8 (B.as_seq h1 out_b)) plain /\
       (UInt64.v c = 0) == result)
  )

inline_for_extraction
val gcm128_decrypt_opt_stdcall: decrypt_opt_stdcall_st AES_128
