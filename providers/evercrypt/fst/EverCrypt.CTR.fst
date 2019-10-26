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
    iv: B.buffer uint8 { B.length iv = nonce_upper_bound a } ->
    iv_len: UInt32.t { UInt32.v iv_len = Seq.length (G.reveal g_iv) } ->
    g_key: G.erased (Spec.key a) ->
    xkey: B.buffer uint8 { B.length xkey = concrete_xkey_length i } ->
    ctr: UInt32.t ->
    state_s a

let freeable_s #a s =
  let State _ _ iv _ _ key _ = s in
  B.freeable iv /\ B.freeable key

let footprint_s #a s =
  let State _ _ iv _ _ key _ = s in
  B.(loc_addr_of_buffer iv `loc_union` loc_addr_of_buffer key)

let cpu_features_invariant (i: impl): Type0 =
  match i with
  | Vale_AES128 | Vale_AES256 ->
      EverCrypt.TargetConfig.x64 /\
      Vale.X64.CPU_Features_s.(aesni_enabled /\ pclmulqdq_enabled /\ avx_enabled)
  | Hacl_CHACHA20 ->
      True

let invariant_s #a h s =
  let State i g_iv iv _ g_key ek _ = s in
  let g_iv = G.reveal g_iv in
  a = cipher_alg_of_impl i /\
  B.live h iv /\ B.live h ek /\
  B.disjoint ek iv /\
  g_iv `Seq.equal` Seq.slice (B.as_seq h iv) 0 (Seq.length g_iv) /\
  concrete_expand i (G.reveal g_key) `Seq.equal` B.as_seq h ek /\
  cpu_features_invariant i

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
  let State _ _ _ _ g_key _ _ = s in
  G.reveal g_key

let iv #a (s: state_s a) =
  let State _ g_iv _ _ _ _ _ = s in
  G.reveal g_iv

let ctr #a (h: HS.mem) (s: state a) =
  UInt32.v (State?.ctr (B.deref h s))

let alg_of_state _ s =
  let State i _ _ _ _ _ _ = !*s in
  cipher_alg_of_impl i

let vale_impl_of_alg (a: vale_cipher_alg): vale_impl =
  match a with
  | AES128 -> Vale_AES128
  | AES256 -> Vale_AES256

friend Lib.IntTypes

#push-options "--z3rlimit 100"

inline_for_extraction noextract
let create_in_vale (i: vale_impl): create_in_st (cipher_alg_of_impl i) =
fun r dst k iv iv_len c ->
  let has_aesni = EverCrypt.AutoConfig2.has_aesni () in
  let has_pclmulqdq = EverCrypt.AutoConfig2.has_pclmulqdq () in
  let has_avx = EverCrypt.AutoConfig2.has_avx() in
  [@inline_let]
  let a = cipher_alg_of_impl i in

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

    let p = B.malloc r (State (vale_impl_of_alg a) g_iv iv' iv_len g_key ek c) 1ul in
    (**) let h3 = ST.get () in
    (**) B.modifies_only_not_unused_in B.loc_none h0 h3;
    assert (B.fresh_loc (footprint h3 p) h0 h3);

    dst *= p;
    (**) let h4 = ST.get () in
    (**) B.modifies_only_not_unused_in B.(loc_buffer dst) h0 h4;

    Success

  else
    UnsupportedAlgorithm

let create_in a r dst k iv iv_len c =
  match a with
  | AES128 ->
      create_in_vale Vale_AES128 r dst k iv iv_len c
  | AES256 ->
      create_in_vale Vale_AES256 r dst k iv iv_len c
  | CHACHA20 ->
      (**) let h0 = ST.get () in
      (**) let g_iv = G.hide (B.as_seq h0 iv) in
      (**) let g_key: G.erased (key a) = G.hide (B.as_seq h0 (k <: B.buffer uint8)) in

      [@inline_let]
      let l = concrete_xkey_len Hacl_CHACHA20 in
      let ek = B.malloc r 0uy l in
      B.blit k 0ul ek 0ul l;
      (**) let h1 = ST.get () in
      (**) B.modifies_only_not_unused_in B.loc_none h0 h1;

      let iv' = B.malloc r 0uy iv_len in
      B.blit iv 0ul iv' 0ul iv_len;
      (**) let h2 = ST.get () in
      (**) B.modifies_only_not_unused_in B.loc_none h0 h2;

      let p = B.malloc r (State Hacl_CHACHA20 g_iv iv' 12ul g_key ek c) 1ul in
      (**) let h3 = ST.get () in
      (**) B.modifies_only_not_unused_in B.loc_none h0 h3;
      assert (B.fresh_loc (footprint h3 p) h0 h3);

      dst *= p;
      (**) let h4 = ST.get () in
      (**) B.modifies_only_not_unused_in B.(loc_buffer dst) h0 h4;

      Success

inline_for_extraction noextract
let copy_or_expand (i: impl)
  (k: B.buffer uint8 { B.length k = Spec.key_length (cipher_alg_of_impl i) })
  (ek: B.buffer uint8 { B.len ek = concrete_xkey_len i }):
  Stack unit
    (requires (fun h0 ->
      B.live h0 k /\ B.live h0 ek /\
      B.disjoint k ek /\
      cpu_features_invariant i))
    (ensures (fun h0 _ h1 ->
      B.(modifies (loc_buffer ek) h0 h1) /\
      B.as_seq h1 ek `Seq.equal` concrete_expand i (B.as_seq h0 k)))
=
  match i with
  | Vale_AES128 ->
      vale_expand Vale_AES128 k ek
  | Vale_AES256 ->
      vale_expand Vale_AES256 k ek
  | Hacl_CHACHA20 ->
      B.blit k 0ul ek 0ul 32ul

let init a p k iv iv_len c =
  let State i _ iv' _ _ ek _ = !*p in
  [@inline_let]
  let k: B.buffer uint8 = k in

  (**) let h0 = ST.get () in
  (**) let g_iv = G.hide (B.as_seq h0 iv) in
  (**) let g_key: G.erased (key (cipher_alg_of_impl i)) = G.hide (B.as_seq h0 k) in

  B.blit iv 0ul iv' 0ul iv_len;
  (**) let h1 = ST.get () in
  (**) assert B.(modifies (footprint_s (B.deref h0 p)) h0 h1);

  copy_or_expand i k ek;
  (**) let h2 = ST.get () in
  (**) assert B.(modifies (footprint_s (B.deref h0 p)) h1 h2);

  // TODO: two in-place updates
  p *= (State i g_iv iv' iv_len g_key ek c)

noextract
let as_vale_key (i: vale_impl) (k: key (cipher_alg_of_impl i)):
  s:Seq.seq Vale.Def.Types_s.nat32 {
    Vale.AES.AES_s.is_aes_key_LE (vale_alg_of_vale_impl i) s
  }
=
  let open Vale.Def.Words.Seq_s in
  let k_nat = seq_uint8_to_seq_nat8 k in
  let k_w = seq_nat8_to_seq_nat32_LE k_nat in
  k_w

// Main (missing) proof of functional equivalence between Vale and HACL.
let vale_encrypt_is_hacl_encrypt (i: vale_impl)
  (k: key (cipher_alg_of_impl i))
  (ctr_block: Seq.lseq uint8 16)
  (input: Seq.lseq uint8 16):
  Lemma
    (ensures (
      let open Vale.Def.Words_s in
      let open Vale.Def.Types_s in
      let open Vale.Def.Words.Seq_s in
      // Vale version
      let a = vale_alg_of_vale_impl i in
      let ctr_block_nat8 = seq_uint8_to_seq_nat8 ctr_block in
      let k_nat32 = as_vale_key i k in
      let input_nat8 = seq_uint8_to_seq_nat8 input in
      let cipher_nat8 = Vale.AES.GCTR_s.gctr_encrypt_LE
        (le_bytes_to_quad32 ctr_block_nat8) (Vale.AES.GCTR.make_gctr_plain_LE input_nat8)
        a k_nat32
      in
      let cipher = seq_nat8_to_seq_uint8 cipher_nat8 in

      // HACL version
      let a = aes_alg_of_alg (cipher_alg_of_impl i) in
      let cipher' = Spec.Loops.seq_map2 xor8 input
        Spec.AES.(aes_encrypt_block a (aes_key_expansion a k) ctr_block)
      in
      cipher `Seq.equal` cipher'))
=
  admit ()

inline_for_extraction noextract
let gctr_bytes (i: vale_impl): Vale.Wrapper.X64.GCTR.gctr_bytes_st (vale_alg_of_vale_impl i) =
  match i with
  | Vale_AES128 -> Vale.Wrapper.X64.GCTR.gctr_bytes_stdcall128
  | Vale_AES256 -> Vale.Wrapper.X64.GCTR.gctr_bytes_stdcall256

friend Spec.Agile.Cipher

inline_for_extraction
let uint128_of_uint32 (x: UInt32.t): y:UInt128.t { UInt128.v y = UInt32.v x } =
  let open FStar.Int.Cast.Full in
  uint64_to_uint128 (uint32_to_uint64 x)

inline_for_extraction noextract
let update_block_vale (i: vale_impl): update_block_st (cipher_alg_of_impl i) =
fun p dst src ->
  let State _ g_iv iv iv_len g_key ek c0 = !*p in

  let open Vale.Wrapper.X64.GCTR in
  let open LowStar.Endianness in
  push_frame ();

  // Prepare the block. See Spec.AES.aes_ctr_key_block for instance.
  let ctr_block = B.alloca (0uy <: uint8) 16ul in
  (**) let h0 = ST.get () in

  B.blit iv 0ul ctr_block 0ul iv_len;
  (**) let h1 = ST.get () in

  // Proof steps missing:
  // - show that repeati is equivalent to a blit
  // - show that the uint128 addition does what aes_ctr_block_add_counter
  //   does (the right lemmas should be there already...)
  (* assert (
    let open Lib.ByteSequence in
    let open Lib.IntTypes in
    let open Lib.Sequence in
    let open Lib.LoopCombinators in
    let block0 = B.as_seq h0 ctr_block in
    let spec0 = create 16 (u8 0) in
    let iv = B.as_seq h0 iv in
    let block1 = B.as_seq h1 ctr_block in
    let spec1 =
      repeati #(lbytes 16) (length iv) (fun i b -> b.[i] <- Seq.index iv i) spec0
    in
    block0 `Seq.equal` spec0 /\
    block1 `Seq.equal` spec1
  );
  admit () | _ -> admit () *)

  // Interpreting potential overflow bytes of the IV as part of a 128-bit
  // counter dictated by HACL* spec.
  let c: UInt128.t = load128_be ctr_block `UInt128.add_mod` (uint128_of_uint32 c0) in
  store128_le ctr_block c;
  (**) let h2 = ST.get () in
  (**) Vale.Arch.BufferFriend.lemma_be_to_n_is_nat_from_bytes (B.as_seq h1 ctr_block);
  (**) Vale.Arch.BufferFriend.lemma_n_to_be_is_nat_to_bytes 16 (UInt128.v c);

  gctr_bytes i
    (G.elift1 (as_vale_key i) g_key)
    src 16uL
    dst
    (B.sub ek 0ul (key_offset i))
    ctr_block;
  (**) vale_encrypt_is_hacl_encrypt i (G.reveal g_key) (B.as_seq h2 ctr_block)
    (B.as_seq h2 src);

  let c = c0 `UInt32.add_mod` 1ul in
  p *= (State #(cipher_alg_of_impl i) i g_iv iv iv_len g_key ek c);

  pop_frame ();

  admit ()

let update_block a p dst src =
  let State i g_iv iv iv_len g_key ek c0 = !*p in
  match i with
  | Vale_AES128 ->
      update_block_vale Vale_AES128 p dst src

  | Vale_AES256 ->
      update_block_vale Vale_AES256 p dst src

  | Hacl_CHACHA20 ->
      let open Hacl.Impl.Chacha20 in
      push_frame ();
      let ctx = B.alloca 0ul 16ul in
      // NOTE: chacha20_init must be called with 0ul because encrypt_block also
      // takes a counter argument and increments too! There may be a way to keep
      // the allocated initial block in the state, but not doing that for now.
      chacha20_init ctx ek (B.sub iv 0ul 12ul) 0ul;
      chacha20_encrypt_block ctx dst c0 src;

      pop_frame ();

      // There's a non-trivial proof of spec equivalence here. See discussion in
      // Spec.Chacha20.
      admit ()

let free a p =
  let State i g_iv iv iv_len g_key ek c0 = !*p in
  B.free iv;
  B.free ek;
  B.free p
