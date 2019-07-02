module EverCrypt.CTR

module ST = FStar.HyperStack.ST
module HS = FStar.HyperStack
module B = LowStar.Buffer
module G = FStar.Ghost

friend Spec.Cipher.Expansion
friend EverCrypt.CTR.Keys

open EverCrypt.CTR.Keys
open FStar.HyperStack.ST
open LowStar.BufferOps
open Spec.Cipher.Expansion
open Spec.Agile.CTR

let uint8 = Lib.IntTypes.uint8
let uint32 = Lib.IntTypes.uint32
let buffer8 = B.buffer uint8

noeq
type state_s (a: Spec.cipher_alg) =
| State:
    i:impl ->
    g_iv: G.erased (Spec.nonce a) ->
    iv: buffer8 { Spec.nonce_bound a (B.length iv) } ->
    g_key: G.erased (Spec.key a) ->
    xkey: buffer8 { B.length xkey = concrete_xkey_length i } ->
    ctr: uint32 ->
    state_s a

let freeable_s #a s =
  let State _ _ iv _ key _ = s in
  B.freeable iv /\ B.freeable key

let footprint_s #a s =
  let State _ _ iv _ key _ = s in
  B.(loc_addr_of_buffer iv `loc_union` loc_addr_of_buffer key)

let invariant_s #a h s =
  let State i g_iv iv g_key key _ = s in
  a = cipher_alg_of_impl i /\
  B.live h iv /\ B.live h key /\
  G.reveal g_iv `Seq.equal` B.as_seq h iv /\
  concrete_expand i (G.reveal g_key) `Seq.equal` B.as_seq h key /\ (
  match i with
  | Vale_AES128 | Vale_AES256 ->
      EverCrypt.TargetConfig.x64 /\
      Vale.X64.CPU_Features_s.(aesni_enabled /\ pclmulqdq_enabled /\ avx_enabled)
  | Hacl_CHACHA20 ->
      True)

let invariant_loc_in_footprint #_ _ _ = ()

let frame_invariant #_ _ _ _ _ = ()

let kv #a (s: state_s a) =
  let State _ _ _ g_key _ _ = s in
  G.reveal g_key

let iv #a (s: state_s a) =
  let State _ g_iv _ _ _ _ = s in
  G.reveal g_iv

let ctr #a (h: HS.mem) (s: state a) =
  UInt32.v (State?.ctr (B.deref h s))

let alg_of_state _ s =
  let State i _ _ _ _ _ = !*s in
  cipher_alg_of_impl i

let vale_impl_of_alg (a: vale_cipher_alg): vale_impl =
  match a with
  | AES128 -> Vale_AES128
  | AES256 -> Vale_AES256

let create_in a r dst k iv iv_len =
  match a with
  | AES128 | AES256 ->
      let has_aesni = EverCrypt.AutoConfig2.has_aesni () in
      let has_pclmulqdq = EverCrypt.AutoConfig2.has_pclmulqdq () in
      let has_avx = EverCrypt.AutoConfig2.has_avx() in
      let i = vale_impl_of_alg a in
      if EverCrypt.TargetConfig.x64 && (has_aesni && has_pclmulqdq && has_avx) then
        let h0 = ST.get () in
        let g_iv = G.hide (B.as_seq h0 iv) in
        let g_key = G.hide (as_seq h0 key) in
        let ek = B.malloc r 0uy (concrete_xkey_len i) in
        let iv' = B.malloc r 0uy (iv_len i) in
        let p = B.malloc r (State (vale_impl_of_alg a) g_iv iv g_key ek ctr) 1ul in
        vale_expand i k ek;
        B.blit iv 0ul iv' 0ul iv_len;
        dst *= p;
        Success
      else
        UnsupportedAlgorithm
  | CHACHA20 -> admit ()
