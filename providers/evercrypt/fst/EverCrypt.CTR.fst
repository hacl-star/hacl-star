module EverCrypt.CTR

module ST = FStar.HyperStack.ST
module HS = FStar.HyperStack
module B = LowStar.Buffer
module G = FStar.Ghost

module Spec = Spec.Agile.CTR

open FStar.HyperStack.ST
open LowStar.BufferOps

let uint8 = Lib.IntTypes.uint8
let uint32 = Lib.IntTypes.uint32
let buffer8 = B.buffer uint8

/// Some implementations may choose to reserve more space in the expanded key
/// for other pre-computations.
let concrete_xkey_length: cipher_alg -> size_nat =
  function
  | CHACHA20 -> 32
  | AES128 -> 176 + 128 // Include the hashed keys here
  | AES256 -> 240 + 128 // Include the hashed keys here


let expand (#a: supported_alg) (k: kv a): ekv a =
  match a with
  | CHACHA20_POLY1305 -> k
  | AES256_GCM | AES128_GCM ->
      let open Vale.AES.AES_s in
      assert_norm (32 % 4 = 0);
      assert_norm (16 % 4 = 0);
      let k_nat = Vale.Def.Words.Seq_s.seq_uint8_to_seq_nat8 k in
      let k_w = Vale.Def.Words.Seq_s.seq_nat8_to_seq_nat32_LE k_nat in
      let ekv_w = key_to_round_keys_LE (vale_alg_of_alg a) k_w in
      let ekv_nat = Vale.Def.Types_s.le_seq_quad32_to_bytes ekv_w in
      Vale.Def.Types_s.le_seq_quad32_to_bytes_length ekv_w;
      let ek = Vale.Def.Words.Seq_s.seq_nat8_to_seq_uint8 ekv_nat in
      let hkeys_quad = Vale.AES.OptPublic.get_hkeys_reqs (Vale.Def.Types_s.reverse_bytes_quad32 (
        aes_encrypt_LE (vale_alg_of_alg a) k_w (Vale.Def.Words_s.Mkfour 0 0 0 0))) in
      let hkeys = Vale.Def.Words.Seq_s.seq_nat8_to_seq_uint8 (Vale.Def.Types_s.le_seq_quad32_to_bytes hkeys_quad) in
      Seq.append ek hkeys



/// Duplicated with EverCrypt.AEAD. Unify?
type impl =
  | Vale_AES128
  | Vale_AES256
  | Hacl_CHACHA20

noeq
type state_s (a: Spec.cipher_alg) =
| State:
    impl:impl ->
    g_iv: G.erased (Spec.nonce a) ->
    iv: buffer8 { Spec.nonce_bound a (B.length iv) } ->
    g_key: G.erased (Spec.xkey a) ->
    xkey: buffer8 { B.length xkey = Spec.concrete_xkey_length a } ->
    ctr: uint32 ->
    state_s a

let freeable_s #a s =
  let State _ _ iv _ key _ = s in
  B.freeable iv /\ B.freeable key

let footprint_s #a s =
  let State _ _ iv _ key _ = s in
  B.(loc_addr_of_buffer iv `loc_union` loc_addr_of_buffer key)

let invariant_s #a h s =
  let State impl g_iv iv g_key key _ = s in
  B.live h iv /\ B.live h key /\
  G.reveal g_iv `Seq.equal` B.as_seq h iv /\
  G.reveal g_key `Seq.equal` B.as_seq h key /\
  true
