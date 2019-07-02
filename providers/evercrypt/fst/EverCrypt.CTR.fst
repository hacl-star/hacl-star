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

#set-options "--max_fuel 0 --max_ifuel 0"

noextract
let nonce_upper_bound a =
  match a with
  | AES128 | AES256 -> block_length a
  | CHACHA20 -> 12

noeq
type state_s (a: Spec.cipher_alg) =
| State:
    i:impl ->
    g_iv: G.erased (Spec.nonce a) ->
    iv: buffer8 { B.length iv = nonce_upper_bound a } ->
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
  let g_iv = G.reveal g_iv in
  a = cipher_alg_of_impl i /\
  B.live h iv /\ B.live h key /\
  g_iv `Seq.equal` Seq.slice (B.as_seq h iv) 0 (Seq.length g_iv) /\
  concrete_expand i (G.reveal g_key) `Seq.equal` B.as_seq h key /\ (
  match i with
  | Vale_AES128 | Vale_AES256 ->
      EverCrypt.TargetConfig.x64 /\
      Vale.X64.CPU_Features_s.(aesni_enabled /\ pclmulqdq_enabled /\ avx_enabled)
  | Hacl_CHACHA20 ->
      True)

let _: squash (inversion impl) = allow_inversion impl
let _: squash (inversion cipher_alg) = allow_inversion cipher_alg

let invert_state_s (a: alg): Lemma
  (requires True)
  (ensures (inversion (state_s a)))
  [ SMTPat (state_s a) ]
=
  allow_inversion (state_s a)

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

friend Lib.IntTypes

#push-options "--z3rlimit 100"
let create_in a r dst k iv iv_len c =
  match a with
  | AES128 | AES256 ->
      let has_aesni = EverCrypt.AutoConfig2.has_aesni () in
      let has_pclmulqdq = EverCrypt.AutoConfig2.has_pclmulqdq () in
      let has_avx = EverCrypt.AutoConfig2.has_avx() in
      let i = vale_impl_of_alg a in
      if iv_len `UInt32.lt` 12ul then
        InvalidIVLength

      else if EverCrypt.TargetConfig.x64 && (has_aesni && has_pclmulqdq && has_avx) then
        (**) let h0 = ST.get () in
        (**) let g_iv = G.hide (B.as_seq h0 iv) in
        (**) let g_key: G.erased (key a) = G.hide (B.as_seq h0 (k <: B.buffer uint8)) in

        let ek = B.malloc r 0uy (concrete_xkey_len i) in
        vale_expand i k ek;
        (**) let h1 = ST.get () in
        (**) B.modifies_only_not_unused_in B.loc_none h0 h1;

        let iv' = B.malloc r 0uy 16ul in
        B.blit iv 0ul iv' 0ul iv_len;
        (**) let h2 = ST.get () in
        (**) B.modifies_only_not_unused_in B.loc_none h0 h2;

        let p = B.malloc r (State (vale_impl_of_alg a) g_iv iv' g_key ek c) 1ul in
        (**) let h3 = ST.get () in
        (**) B.modifies_only_not_unused_in B.loc_none h0 h3;
        assert (B.fresh_loc (footprint h3 p) h0 h3);

        dst *= p;
        (**) let h4 = ST.get () in
        (**) B.modifies_only_not_unused_in B.(loc_buffer dst) h0 h4;

        Success

      else
        UnsupportedAlgorithm

  | CHACHA20 ->
        (**) let h0 = ST.get () in
        (**) let g_iv = G.hide (B.as_seq h0 iv) in
        (**) let g_key: G.erased (key a) = G.hide (B.as_seq h0 (k <: B.buffer uint8)) in

        [@inline_let]
        let l = concrete_xkey_len Hacl_CHACHA20 in
        let ek = B.malloc r 0uy l in
        B.blit (k <: B.buffer uint8) 0ul ek 0ul l;
        (**) let h1 = ST.get () in
        (**) B.modifies_only_not_unused_in B.loc_none h0 h1;

        let iv' = B.malloc r 0uy iv_len in
        B.blit iv 0ul iv' 0ul iv_len;
        (**) let h2 = ST.get () in
        (**) B.modifies_only_not_unused_in B.loc_none h0 h2;

        let p = B.malloc r (State Hacl_CHACHA20 g_iv iv' g_key ek c) 1ul in
        (**) let h3 = ST.get () in
        (**) B.modifies_only_not_unused_in B.loc_none h0 h3;
        assert (B.fresh_loc (footprint h3 p) h0 h3);

        dst *= p;
        (**) let h4 = ST.get () in
        (**) B.modifies_only_not_unused_in B.(loc_buffer dst) h0 h4;

        Success

let init a p k iv iv_len c =
  let State i _ iv' _ ek _ = !*p in
  match i with
  | Vale_AES128 | Vale_AES256 ->
        (**) let h0 = ST.get () in
        (**) let g_iv = G.hide (B.as_seq h0 iv) in
        (**) let g_key: G.erased (key (cipher_alg_of_impl i)) =
          G.hide (B.as_seq h0 (k <: B.buffer uint8)) in

        vale_expand i k ek;
        B.blit iv 0ul iv' 0ul iv_len;
        // TODO: two in-place updates
        p *= (State i g_iv iv' g_key ek c)

  | _ -> admit ()
