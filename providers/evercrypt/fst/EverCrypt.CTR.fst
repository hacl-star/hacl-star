module EverCrypt.CTR

module ST = FStar.HyperStack.ST
module HS = FStar.HyperStack
module B = LowStar.Buffer
module G = FStar.Ghost

module Spec = Spec.Agile.CTR

friend Spec.Cipher.Expansion

open FStar.HyperStack.ST
open LowStar.BufferOps
open Spec.Cipher.Expansion

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

let create_in a r dst =
  
