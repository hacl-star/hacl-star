module Impl.QUIC

// This MUST be kept in sync with Impl.QUIC.fsti...
module G = FStar.Ghost
module B = LowStar.Buffer
module IB = LowStar.ImmutableBuffer
module S = FStar.Seq
module HS = FStar.HyperStack
module ST = FStar.HyperStack.ST


module U64 = FStar.UInt64
module U32 = FStar.UInt32
module U8 = FStar.UInt8

open FStar.HyperStack
open FStar.HyperStack.ST

open EverCrypt.Helpers
open EverCrypt.Error

#set-options "--max_fuel 0 --max_ifuel 0"
// ... up to here!

module Cipher = EverCrypt.Cipher
module AEAD = EverCrypt.AEAD
module HKDF = EverCrypt.HKDF

friend Spec.QUIC

open LowStar.BufferOps

/// https://tools.ietf.org/html/draft-ietf-quic-tls-23#section-5
///
/// We perform the three key derivations (AEAD key; AEAD iv; header protection
/// key) when ``create`` is called. We thus store the original traffic secret
/// only ghostly.
///
/// We retain the AEAD state, in order to perform the packet payload encryption.
///
/// We retain the Cipher state, in order to compute the mask for header protection.
noeq
type state_s (i: index) =
  | State:
      the_hash_alg:hash_alg { the_hash_alg == i.hash_alg } ->
      the_aead_alg:aead_alg { the_aead_alg == i.aead_alg } ->
      traffic_secret:G.erased (Spec.Hash.Definitions.bytes_hash the_hash_alg) ->
      initial_pn:G.erased Spec.QUIC.nat62 ->
      aead_state:EverCrypt.AEAD.state the_aead_alg ->
      iv:EverCrypt.AEAD.iv_p the_aead_alg ->
      hp_key:B.buffer U8.t { B.length hp_key = Spec.QUIC.ae_keysize the_aead_alg } ->
      pn:B.pointer u62 ->
      state_s i

let footprint_s #i h s =
  let open LowStar.Buffer in
  AEAD.footprint h (State?.aead_state s) `loc_union`
  loc_buffer (State?.iv s) `loc_union`
  loc_buffer (State?.hp_key s) `loc_union`
  loc_buffer (State?.pn s)

let g_traffic_secret #i s =
  // Automatic reveal insertion doesn't work here
  G.reveal (State?.traffic_secret s)

let g_initial_packet_number #i s =
  // New style: automatic insertion of reveal
  State?.initial_pn s

let invariant_s #i h s =
  let open Spec.QUIC in
  let State hash_alg aead_alg traffic_secret initial_pn aead_state iv hp_key pn = s in
  hash_is_keysized s; (
  AEAD.invariant h aead_state /\
  B.(all_live h [ buf iv; buf hp_key; buf pn ])  /\
  B.(all_disjoint [
    AEAD.footprint h aead_state; loc_buffer iv; loc_buffer hp_key; loc_buffer pn ]) /\
  // JP: automatic insertion of reveal does not work here
  G.reveal initial_pn <= U64.v (B.deref h pn) /\
  AEAD.as_kv (B.deref h aead_state) ==
    derive_secret i.hash_alg (G.reveal traffic_secret) label_key (Spec.Agile.AEAD.key_length aead_alg) /\
  B.as_seq h iv ==
    derive_secret i.hash_alg (G.reveal traffic_secret) label_iv 12 /\
  B.as_seq h hp_key ==
    derive_secret i.hash_alg (G.reveal traffic_secret) label_hp (Spec.QUIC.ae_keysize aead_alg)
  )

let invariant_loc_in_footprint #_ _ _ = ()

let g_packet_number #i s h =
  U64.v (B.deref h (State?.pn s))

let frame_invariant #i l s h0 h1 =
  AEAD.frame_invariant l (State?.aead_state (B.deref h0 s)) h0 h1

let aead_alg_of_state #i s =
  let State _ the_aead_alg _ _ _ _ _ _ = !*s in
  the_aead_alg

let hash_alg_of_state #i s =
  let State the_hash_alg _ _ _ _ _ _ _ = !*s in
  the_hash_alg

let packet_number_of_state #i s =
  let State _ _ _ _ _ _ _ pn = !*s in
  !*pn

#push-options "--max_ifuel 1 --initial_ifuel 1"
/// One ifuel for inverting on the hash algorithm for computing bounds (the
/// various calls to assert_norm should help ensure this proof goes through
/// reliably). Note that I'm breaking from the usual convention where lengths
/// are UInt32's, mostly to avoid trouble reasoning with modulo when casting
/// from UInt32 to UInt8 to write the label for the key derivation. This could
/// be fixed later.
val derive_secret: a: Spec.QUIC.ha ->
  dst:B.buffer U8.t ->
  dst_len: U8.t { B.length dst = U8.v dst_len /\ U8.v dst_len <= 255 } ->
  secret:B.buffer U8.t { B.length secret = Spec.Hash.Definitions.hash_length a } ->
  label:IB.ibuffer U8.t ->
  label_len:U8.t { IB.length label = U8.v label_len /\ U8.v label_len <= 244 } ->
  Stack unit
    (requires fun h0 ->
      B.(all_live h0 [ buf secret; buf label; buf dst ]) /\
      B.disjoint dst secret)
    (ensures fun h0 _ h1 ->
      assert_norm (255 < pow2 61);
      assert_norm (pow2 61 < pow2 125);
      B.(modifies (loc_buffer dst) h0 h1) /\
      B.as_seq h1 dst == Spec.QUIC.derive_secret a (B.as_seq h0 secret)
        (IB.as_seq h0 label) (U8.v dst_len))
#pop-options

let prefix = LowStar.ImmutableBuffer.igcmalloc_of_list HS.root Spec.QUIC.prefix_l

let lemma_five_cuts (s: S.seq U8.t) (i1 i2 i3 i4 i5: nat) (s0 s1 s2 s3 s4 s5: S.seq U8.t): Lemma
  (requires (
    i1 <= S.length s /\
    i2 <= S.length s /\
    i3 <= S.length s /\
    i4 <= S.length s /\
    i5 <= S.length s /\
    i1 <= i2 /\
    i2 <= i3 /\
    i3 <= i4 /\
    i4 <= i5 /\
    s0 `Seq.equal` S.slice s 0 i1 /\
    s1 `Seq.equal` S.slice s i1 i2 /\
    s2 `Seq.equal` S.slice s i2 i3 /\
    s3 `Seq.equal` S.slice s i3 i4 /\
    s4 `Seq.equal` S.slice s i4 i5 /\
    s5 `Seq.equal` S.slice s i5 (S.length s)))
  (ensures (
    let open S in
    s `equal` (s0 @| s1 @| s2 @| s3 @| s4 @| s5)))
=
  ()

let hash_is_keysized_ (a: Spec.QUIC.ha): Lemma
  (ensures (Spec.QUIC.keysized a (Spec.Hash.Definitions.hash_length a)))
=
  assert_norm (512 < pow2 61);
  assert_norm (512 < pow2 125)

#set-options "--z3rlimit 100"
let derive_secret a dst dst_len secret label label_len =
  LowStar.ImmutableBuffer.recall prefix;
  LowStar.ImmutableBuffer.recall_contents prefix Spec.QUIC.prefix;
  (**) let h0 = ST.get () in

  push_frame ();
  (**) let h1 = ST.get () in

  let label_len32 = FStar.Int.Cast.uint8_to_uint32 label_len in
  let dst_len32 = FStar.Int.Cast.uint8_to_uint32 dst_len in
  let info_len = U32.(1ul +^ 1ul +^ 1ul +^ 11ul +^ label_len32 +^ 1ul) in
  let info = B.alloca 0uy info_len in

  // JP: best way to reason about this sort of code is to slice the buffer very thinly
  let info_z = B.sub info 0ul 1ul in
  let info_lb = B.sub info 1ul 1ul in
  let info_llen = B.sub info 2ul 1ul in
  let info_prefix = B.sub info 3ul 11ul in
  let info_label = B.sub info 14ul label_len32 in
  let info_z' = B.sub info (14ul `U32.add` label_len32) 1ul in
  (**) assert (14ul `U32.add` label_len32 `U32.add` 1ul = B.len info);
  (**) assert B.(all_disjoint [ loc_buffer info_z; loc_buffer info_lb; loc_buffer info_llen;
  (**)   loc_buffer info_prefix; loc_buffer info_label; loc_buffer info_z' ]);

  info_lb.(0ul) <- dst_len;
  info_llen.(0ul) <- U8.(label_len +^ 11uy);
  B.blit prefix 0ul info_prefix 0ul 11ul;
  B.blit label 0ul info_label 0ul label_len32;

  (**) let h2 = ST.get () in
  (**) assert (
  (**)   let z = S.create 1 0uy in
  (**)   let lb = S.create 1 dst_len in // len <= 255
  (**)   let llen = S.create 1 (U8.uint_to_t (11 + Seq.length (B.as_seq h0 label))) in
  (**)   let info = B.as_seq h2 info in
  (**)   B.as_seq h2 info_z `Seq.equal` z /\
  (**)   B.as_seq h2 info_lb `Seq.equal` lb /\
  (**)   B.as_seq h2 info_llen `Seq.equal` llen /\
  (**)   B.as_seq h2 info_prefix `Seq.equal` Spec.QUIC.prefix /\
  (**)   B.as_seq h2 info_label `Seq.equal` (B.as_seq h0 label) /\
  (**)   B.as_seq h2 info_z' `Seq.equal` z
  (**) );
  (**) (
  (**)   let z = S.create 1 0uy in
  (**)   let lb = S.create 1 dst_len in // len <= 255
  (**)   let llen = S.create 1 (U8.uint_to_t (11 + Seq.length (B.as_seq h0 label))) in
  (**)   let info = B.as_seq h2 info in
  (**)   lemma_five_cuts info 1 2 3 14 (14 + U8.v label_len)
  (**)     z lb llen Spec.QUIC.prefix (B.as_seq h0 label) z
  (**) );
  (**) hash_is_keysized_ a;
  HKDF.expand a dst secret (Hacl.Hash.Definitions.hash_len a) info info_len dst_len32;
  (**) let h3 = ST.get () in
  pop_frame ();
  (**) let h4 = ST.get () in
  (**) B.modifies_fresh_frame_popped h0 h1 (B.loc_buffer dst) h3 h4;
  (**) assert (ST.equal_domains h0 h4)

let key_len (a: Spec.QUIC.ea): x:U8.t { U8.v x = Spec.Agile.AEAD.key_length a } =
  let open Spec.Agile.AEAD in
  match a with
  | AES128_GCM -> 16uy
  | AES256_GCM -> 32uy
  | CHACHA20_POLY1305 -> 32uy

let key_len32 a = FStar.Int.Cast.uint8_to_uint32 (key_len a)

let label_key = LowStar.ImmutableBuffer.igcmalloc_of_list HS.root Spec.QUIC.label_key_l
let label_iv = LowStar.ImmutableBuffer.igcmalloc_of_list HS.root Spec.QUIC.label_iv_l
let label_hp = LowStar.ImmutableBuffer.igcmalloc_of_list HS.root Spec.QUIC.label_hp_l

#set-options "--z3rlimit 350"
let create_in i r dst initial_pn traffic_secret =
  LowStar.ImmutableBuffer.recall label_key;
  LowStar.ImmutableBuffer.recall_contents label_key Spec.QUIC.label_key;
  LowStar.ImmutableBuffer.recall label_iv;
  LowStar.ImmutableBuffer.recall_contents label_iv Spec.QUIC.label_iv;
  LowStar.ImmutableBuffer.recall label_hp;
  LowStar.ImmutableBuffer.recall_contents label_hp Spec.QUIC.label_hp;
  (**) let h0 = ST.get () in
  [@inline_let]
  let e_traffic_secret: G.erased (Spec.Hash.Definitions.bytes_hash i.hash_alg) =
    G.hide (B.as_seq h0 traffic_secret)
  in
  [@inline_let]
  let e_initial_pn: G.erased Spec.QUIC.nat62 = G.hide (U64.v initial_pn) in
  [@inline_let]
  let hash_alg = i.hash_alg in
  [@inline_let]
  let aead_alg = i.aead_alg in

  push_frame ();
  (**) let h1 = ST.get () in

  let aead_key = B.alloca 0uy (key_len32 aead_alg) in
  derive_secret hash_alg aead_key (key_len aead_alg) traffic_secret label_key 3uy;

  (**) let h2 = ST.get () in
  (**) B.(modifies_loc_includes (loc_unused_in h1) h1 h2 (loc_buffer aead_key));

  let aead_state: B.pointer (B.pointer_or_null (AEAD.state_s aead_alg)) = B.alloca B.null 1ul in
  let ret = AEAD.create_in #aead_alg r aead_state aead_key in

  (**) let h3 = ST.get () in
  (**) B.(modifies_loc_includes (loc_unused_in h1) h2 h3 (loc_buffer aead_state));
  (**) B.(modifies_trans (loc_unused_in h1) h1 h2 (loc_unused_in h1) h3);
  match ret with
  | UnsupportedAlgorithm ->
      pop_frame ();
      UnsupportedAlgorithm

  | Success ->
      // JP: there is something difficult to prove here... confused.
      let aead_state: AEAD.state aead_alg = !*aead_state in
      (**) assert (AEAD.invariant h3 aead_state);

      let iv = B.malloc r 0uy 12ul in
      (**) assert_norm FStar.Mul.(8 * 12 <= pow2 64 - 1);
      (**) let h4 = ST.get () in
      (**) B.(modifies_loc_includes (loc_buffer dst) h3 h4 loc_none);

      let hp_key = B.malloc r 0uy (key_len32 aead_alg) in
      (**) let h5 = ST.get () in
      (**) B.(modifies_loc_includes (loc_buffer dst) h4 h5 loc_none);

      let pn = B.malloc r initial_pn 1ul in
      (**) let h6 = ST.get () in
      (**) B.(modifies_loc_includes (loc_buffer dst) h5 h6 loc_none);

      (**) assert (B.length hp_key = Spec.QUIC.ae_keysize aead_alg);
      let s: state_s i = State #i
        hash_alg aead_alg e_traffic_secret
        e_initial_pn aead_state iv hp_key pn
      in
      let s:B.pointer_or_null (state_s i) = B.malloc r s 1ul in
      (**) let h7 = ST.get () in
      (**) B.(modifies_loc_includes (loc_buffer dst) h6 h7 loc_none);

      derive_secret hash_alg iv 12uy traffic_secret label_iv 2uy;
      (**) let h8 = ST.get () in
      (**) B.(modifies_loc_includes (loc_unused_in h1) h7 h8 (loc_buffer iv));

      derive_secret hash_alg hp_key (key_len aead_alg) traffic_secret label_hp 2uy;
      (**) let h9 = ST.get () in
      (**) B.(modifies_loc_includes (loc_unused_in h1) h8 h9 (loc_buffer hp_key));
      (**) B.(modifies_trans (loc_unused_in h1) h7 h8 (loc_unused_in h1) h9);

      dst *= s;

      (**) let h10 = ST.get () in
      (**) B.(modifies_trans (loc_unused_in h1) h7 h9 (loc_buffer dst) h10);
      (**) B.(modifies_trans (loc_unused_in h1) h1 h3 (loc_buffer dst) h7);
      (**) B.(modifies_trans (loc_buffer dst) h3 h7
      (**)   (loc_unused_in h1 `loc_union` loc_buffer dst) h10);
      (**) B.(modifies_only_not_unused_in (loc_buffer dst) h1 h10);
      (**) B.(modifies_only_not_unused_in (loc_buffer dst) h3 h10);
      (**) B.fresh_frame_modifies h0 h1;
      (**) B.(modifies_trans loc_none h0 h1 (loc_buffer dst) h10);

      // TODO: everything goes through well up to here; and we know:
      //   B.modifies (loc_buffer dst) h0 h10
      // NOTE: how to conclude efficiently the same thing with h11?
      pop_frame ();
      (**) let h11 = ST.get () in
      (**) assert (AEAD.invariant #aead_alg h11 aead_state);
      (**) B.popped_modifies h10 h11;
      (**) assert B.(modifies (loc_buffer dst) h0 h11);
      (**) assert (ST.equal_stack_domains h0 h11);

      Success

val xor_inplace (dst src: B.buffer U8.t) (len: U32.t { B.length dst = U32.v len }):
  Stack unit
    (requires fun h0 ->
      B.(all_live h0 [ buf dst; buf src ]) /\
      B.disjoint dst src /\
      B.length dst = B.length src)
    (ensures fun h0 _ h1 ->
      B.(modifies (loc_buffer dst) h0 h1) /\
      B.as_seq h1 dst `S.equal` Spec.QUIC.xor_inplace (B.as_seq h0 dst) (B.as_seq h0 src) 0)

let lemma_slice s (i: nat { i <= S.length s }): Lemma
  (ensures (s `S.equal` S.append (S.slice s 0 i) (S.slice s i (S.length s))))
=
  ()

#set-options "--max_fuel 1 --z3rlimit 100"
let rec pointwise_upd (#a: eqtype) f b1 b2 i pos (x: a): Lemma
  (requires (S.length b2 + pos <= S.length b1 /\ i < pos))
  (ensures (S.upd (Spec.QUIC.pointwise_op f b1 b2 pos) i x `S.equal`
    Spec.QUIC.pointwise_op f (S.upd b1 i x) b2 pos))
  (decreases (S.length b2))
=
  calc (S.equal) {
    Spec.QUIC.pointwise_op f (S.upd b1 i x) b2 pos;
  (S.equal) { lemma_slice (S.upd b1 i x) (i + 1) }
    Spec.QUIC.pointwise_op f
      S.(slice (S.upd b1 i x) 0 (i + 1) @| S.slice (S.upd b1 i x) (i + 1) (S.length b1))
      b2 pos;
  (S.equal) { }
    Spec.QUIC.pointwise_op f
      S.(slice (S.upd b1 i x) 0 (i + 1) @| S.slice b1 (i + 1) (S.length b1))
      b2 pos;
  (S.equal) {
    Spec.QUIC.pointwise_op_suff f
      (S.slice (S.upd b1 i x) 0 (i + 1))
      (S.slice b1 (i + 1) (S.length b1)) b2 pos
  }
    S.slice (S.upd b1 i x) 0 (i + 1) `S.append`
    Spec.QUIC.pointwise_op f
      (S.slice b1 (i + 1) (S.length b1))
      b2 (pos - (i + 1));
  (S.equal) { }
    S.upd (S.slice b1 0 (i + 1)) i x `S.append`
    Spec.QUIC.pointwise_op f
      (S.slice b1 (i + 1) (S.length b1))
      b2 (pos - (i + 1));
  (S.equal) { }
    S.upd (S.slice b1 0 (i + 1) `S.append`
    Spec.QUIC.pointwise_op f
      (S.slice b1 (i + 1) (S.length b1))
      b2 (pos - (i + 1))
    ) i x;
  (S.equal) {
    Spec.QUIC.pointwise_op_suff f
      (S.slice b1 0 (i + 1))
      (S.slice b1 (i + 1) (S.length b1)) b2 pos
  }
    S.upd (
      Spec.QUIC.pointwise_op f
      (S.slice b1 0 (i + 1) `S.append` S.slice b1 (i + 1) (S.length b1))
      b2 pos
    ) i x;
  (S.equal) { lemma_slice b1 (i + 1) }
    S.upd (Spec.QUIC.pointwise_op f b1 b2 pos) i x;
  };
  ()

#push-options "--z3rlimit 50"
let rec lemma_xor_inplace0 (s1 s2: S.seq U8.t) (i: nat): Lemma
  (requires (
    let l = S.length s1 in
    S.length s2 = l - i /\ i <= S.length s1))
  (ensures (
    let l = S.length s1 in
    Spec.Loops.seq_map2 U8.logxor (S.slice s1 i l) s2 `S.equal`
    S.slice (Spec.QUIC.xor_inplace s1 s2 i) i l))
  (decreases (S.length s2))
=
  if S.length s2 = 0 then
    ()
  else
    let l = S.length s1 in
    let s2l = S.slice s2 0 1 in
    let s2r = S.slice s2 1 (S.length s2) in
    let s1p = S.slice s1 0 i in
    let s1l = S.slice s1 i (i + 1) in
    let s1r = S.slice s1 (i + 1) l in
    assert S.(s2 `equal` (s2l @| s2r));
    assert S.(s1 `equal` (s1p @| s1l @| s1r));
    assert (i < S.length s1);
    assert (i < S.length (Spec.QUIC.xor_inplace s1 s2 i));
    calc (S.equal) {
      Spec.Loops.seq_map2 U8.logxor (S.slice s1 i l) s2;
    (S.equal) {}
      S.cons (U8.logxor (S.head (S.slice s1 i l)) (S.head s2))
        (Spec.Loops.seq_map2 U8.logxor (S.tail (S.slice s1 i l)) (S.tail s2));
    (S.equal) {}
      S.cons (U8.logxor (S.head (S.slice s1 i l)) (S.head s2))
        (Spec.Loops.seq_map2 U8.logxor (S.slice s1 (i + 1) l) (S.tail s2));
    (S.equal) { lemma_xor_inplace0 s1 (S.slice s2 1 (S.length s2)) (i + 1) }
      S.cons (U8.logxor (S.head (S.slice s1 i l)) (S.head s2))
        (S.slice (Spec.QUIC.xor_inplace s1 (S.tail s2) (i + 1)) (i + 1) l);
    (S.equal) { }
      S.cons (U8.logxor (S.head (S.slice s1 i l)) (S.head s2))
        (S.slice (Spec.QUIC.pointwise_op U8.logxor s1 (S.tail s2) (i + 1)) (i + 1) l);
    (S.equal) { }
      S.slice (
        S.upd (Spec.QUIC.pointwise_op U8.logxor s1 (S.tail s2) (i + 1))
          i
          (U8.logxor (S.head (S.slice s1 i l)) (S.head s2)))
        i
        l;
    (S.equal) { }
      S.slice (
        S.upd (Spec.QUIC.pointwise_op U8.logxor s1 (S.slice s2 1 (S.length s2)) (i + 1))
          i
          (U8.logxor (S.head (S.slice s1 i l)) (S.head s2)))
        i
        l;
    (S.equal) {
      pointwise_upd U8.logxor s1 (S.slice s2 1 (S.length s2)) i (i + 1)
        (U8.logxor (S.head (S.slice s1 i l)) (S.head s2))
    }
      S.slice
        (Spec.QUIC.pointwise_op U8.logxor
          (S.upd s1 i (U8.logxor (S.head (S.slice s1 i l)) (S.head s2)))
          (S.slice s2 1 (S.length s2))
          (i + 1))
        i l;

    };
    ()
#pop-options

let lemma_xor_inplace (s1 s2: S.seq U8.t): Lemma
  (requires (S.length s1 = S.length s2))
  (ensures (
    let l = S.length s1 in
    Spec.Loops.seq_map2 U8.logxor s1 s2 `S.equal`
    Spec.QUIC.xor_inplace s1 s2 0))
=
  lemma_xor_inplace0 s1 s2 0

let xor_inplace dst src len =
  let h0 = ST.get () in
  C.Loops.in_place_map2 dst src len U8.logxor;
  lemma_xor_inplace (B.as_seq h0 dst) (B.as_seq h0 src)

let encrypt #i s dst h plain plain_len pn_len =
  let State hash_alg aead_alg e_traffic_secret e_initial_pn aead_state iv hp_key pn = !*s in
  (**) let h0 = ST.get () in
  assert (
    let s0 = g_traffic_secret (B.deref h0 s) in
    let open Spec.QUIC in
    let k = derive_secret i.hash_alg s0 label_key (Spec.Agile.AEAD.key_length i.aead_alg) in
    let iv_seq = derive_secret i.hash_alg s0 label_iv 12 in
    let hp_key_seq = derive_secret i.hash_alg s0 label_hp (ae_keysize i.aead_alg) in
    AEAD.as_kv (B.deref h0 aead_state) `S.equal` k /\
    B.as_seq h0 iv `S.equal` iv_seq /\
    B.as_seq h0 hp_key `S.equal` hp_key_seq);
  admit ()

let decrypt #i s dst packet len cid_len =
  admit ()
