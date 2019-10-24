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
module CTR = EverCrypt.CTR

friend Spec.QUIC

open LowStar.BufferOps

inline_for_extraction noextract
let as_cipher_alg (a: Spec.QUIC.ea) =
  Spec.Agile.AEAD.cipher_alg_of_supported_alg a

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
      ctr_state:CTR.state (as_cipher_alg the_aead_alg) ->
      state_s i

let footprint_s #i h s =
  let open LowStar.Buffer in
  AEAD.footprint h (State?.aead_state s) `loc_union`
  CTR.footprint h (State?.ctr_state s) `loc_union`
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
  let State hash_alg aead_alg traffic_secret initial_pn aead_state iv hp_key pn ctr_state =
    s
  in
  hash_is_keysized s; (
  AEAD.invariant h aead_state /\
  CTR.invariant h ctr_state /\
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
  AEAD.frame_invariant l (State?.aead_state (B.deref h0 s)) h0 h1;
  CTR.frame_invariant l (State?.ctr_state (B.deref h0 s)) h0 h1

let aead_alg_of_state #i s =
  let State _ the_aead_alg _ _ _ _ _ _ _ = !*s in
  the_aead_alg

let hash_alg_of_state #i s =
  let State the_hash_alg _ _ _ _ _ _ _ _ = !*s in
  the_hash_alg

let packet_number_of_state #i s =
  let State _ _ _ _ _ _ _ pn _ = !*s in
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

// JP: this proof currently takes 12 minutes. It could conceivably be improved.
#push-options "--z3rlimit 1000 --query_stats"
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

  let aead_state: B.pointer (B.pointer_or_null (AEAD.state_s aead_alg)) =
    B.alloca B.null 1ul
  in
  let ret = AEAD.create_in #aead_alg r aead_state aead_key in

  let ctr_state: B.pointer (B.pointer_or_null (CTR.state_s (as_cipher_alg aead_alg))) =
    B.alloca B.null 1ul
  in
  let dummy_iv = B.alloca 0uy 12ul in
  let ret' = CTR.create_in (as_cipher_alg aead_alg) r ctr_state aead_key dummy_iv 12ul 0ul in

  (**) let h3 = ST.get () in
  (**) B.(modifies_loc_includes (loc_unused_in h1) h2 h3
    (loc_buffer ctr_state `loc_union` loc_buffer aead_state));
  (**) B.(modifies_trans (loc_unused_in h1) h1 h2 (loc_unused_in h1) h3);

  match ret with
  | UnsupportedAlgorithm ->
      pop_frame ();
      UnsupportedAlgorithm

  | Success ->

      match ret' with
      | UnsupportedAlgorithm ->
          pop_frame ();
          UnsupportedAlgorithm

      | Success ->
      // JP: there is something difficult to prove here... confused.
      let aead_state: AEAD.state aead_alg = !*aead_state in
      (**) assert (AEAD.invariant h3 aead_state);

      let ctr_state: CTR.state (as_cipher_alg aead_alg) = !*ctr_state in
      (**) assert (CTR.invariant h3 ctr_state);

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
        hash_alg aead_alg e_traffic_secret e_initial_pn
        aead_state iv hp_key pn ctr_state
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
      (**) assert (CTR.invariant #(as_cipher_alg aead_alg) h11 ctr_state);
      (**) B.popped_modifies h10 h11;
      (**) assert B.(modifies (loc_buffer dst) h0 h11);
      (**) assert (ST.equal_stack_domains h0 h11);

      Success
#pop-options

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
  }

#push-options "--z3rlimit 50"
let rec pointwise_seq_map2 (#a: eqtype) (f: a -> a -> a) (s1 s2: S.seq a) (i: nat): Lemma
  (requires (
    let l = S.length s1 in
    S.length s2 = l - i /\ i <= S.length s1))
  (ensures (
    let l = S.length s1 in
    Spec.Loops.seq_map2 f (S.slice s1 i l) s2 `S.equal`
    S.slice (Spec.QUIC.pointwise_op f s1 s2 i) i l))
  (decreases (S.length s2))
=
  if S.length s2 = 0 then
    ()
  else
    let l = S.length s1 in
    calc (S.equal) {
      Spec.Loops.seq_map2 f (S.slice s1 i l) s2;
    (S.equal) {}
      S.cons (f (S.head (S.slice s1 i l)) (S.head s2))
        (Spec.Loops.seq_map2 f (S.tail (S.slice s1 i l)) (S.tail s2));
    (S.equal) {}
      S.cons (f (S.head (S.slice s1 i l)) (S.head s2))
        (Spec.Loops.seq_map2 f (S.slice s1 (i + 1) l) (S.tail s2));
    (S.equal) { pointwise_seq_map2 f s1 (S.slice s2 1 (S.length s2)) (i + 1) }
      S.cons (f (S.head (S.slice s1 i l)) (S.head s2))
        (S.slice (Spec.QUIC.pointwise_op f s1 (S.tail s2) (i + 1)) (i + 1) l);
    (S.equal) { }
      S.slice (
        S.upd (Spec.QUIC.pointwise_op f s1 (S.tail s2) (i + 1))
          i
          (f (S.head (S.slice s1 i l)) (S.head s2)))
        i
        l;
    (S.equal) { }
      S.slice (
        S.upd (Spec.QUIC.pointwise_op f s1 (S.slice s2 1 (S.length s2)) (i + 1))
          i
          (f (S.head (S.slice s1 i l)) (S.head s2)))
        i
        l;
    (S.equal) {
      pointwise_upd f s1 (S.slice s2 1 (S.length s2)) i (i + 1)
        (f (S.head (S.slice s1 i l)) (S.head s2))
    }
      S.slice
        (Spec.QUIC.pointwise_op f
          (S.upd s1 i (f (S.head (S.slice s1 i l)) (S.head s2)))
          (S.slice s2 1 (S.length s2))
          (i + 1))
        i l;

    };
    ()
#pop-options

inline_for_extraction noextract
let op_inplace (dst src: B.buffer U8.t)
  (src_len: U32.t)
  (ofs: U32.t)
  (op: U8.t -> U8.t -> U8.t)
:
  Stack unit
    (requires fun h0 ->
      B.(all_live h0 [ buf dst; buf src ]) /\
      B.disjoint dst src /\
      B.length src = U32.v src_len /\
      B.length dst = U32.v ofs + B.length src)
    (ensures fun h0 _ h1 ->
      B.(modifies (loc_buffer dst) h0 h1) /\
      B.as_seq h1 dst `S.equal`
        Spec.QUIC.pointwise_op op (B.as_seq h0 dst) (B.as_seq h0 src) (U32.v ofs))
=
  let h0 = ST.get () in
  let dst0 = B.sub dst 0ul ofs in
  let dst' = B.sub dst ofs src_len in
  C.Loops.in_place_map2 dst' src src_len op;
  let h1 = ST.get () in
  calc (S.equal) {
    B.as_seq h1 dst;
  (S.equal) { lemma_slice (B.as_seq h1 dst) (U32.v ofs) }
    S.append (S.slice (B.as_seq h1 dst) 0 (U32.v ofs))
      (S.slice (B.as_seq h1 dst) (U32.v ofs) (B.length dst));
  (S.equal) { (* needs dst0 in scope for this step to go through *) }
    S.append (S.slice (B.as_seq h0 dst) 0 (U32.v ofs))
      (S.slice (B.as_seq h1 dst) (U32.v ofs) (B.length dst));
  (S.equal) { }
    S.append (S.slice (B.as_seq h0 dst) 0 (U32.v ofs))
      (S.slice (B.as_seq h1 dst) (U32.v ofs) (B.length dst));
  (S.equal) { pointwise_seq_map2 op (B.as_seq h0 dst') (B.as_seq h0 src) 0 }
    S.append (S.slice (B.as_seq h0 dst) 0 (U32.v ofs))
      (Spec.QUIC.pointwise_op op
        (S.slice (B.as_seq h0 dst) (U32.v ofs) (B.length dst))
        (B.as_seq h0 src)
        0);
  (S.equal) { Spec.QUIC.pointwise_op_suff op (S.slice (B.as_seq h0 dst) 0 (U32.v ofs))
    (S.slice (B.as_seq h0 dst) (U32.v ofs) (B.length dst))
    (B.as_seq h0 src)
    (U32.v ofs)
  }
    Spec.QUIC.pointwise_op op
      (S.append (S.slice (B.as_seq h0 dst) 0 (U32.v ofs))
        (S.slice (B.as_seq h0 dst) (U32.v ofs) (B.length dst)))
      (B.as_seq h0 src)
      (U32.v ofs);
  (S.equal) { lemma_slice (B.as_seq h0 dst) (U32.v ofs) }
    Spec.QUIC.pointwise_op op
      (B.as_seq h0 dst)
      (B.as_seq h0 src)
      (U32.v ofs);
  }

let header_footprint (h: header) =
  let open B in
  match h with
  | Short _ _ cid _ -> loc_buffer cid
  | Long _ _ dcid _ scid _ _ -> loc_buffer dcid `loc_union` loc_buffer scid

let header_disjoint (h: header) =
  let open B in
  match h with
  | Short _ _ cid _ -> True
  | Long _ _ dcid _ scid _ _ -> B.disjoint dcid scid

let format_header (dst: B.buffer U8.t) (h: header) (npn: B.buffer U8.t) (pn_len: u2):
  Stack unit
    (requires (fun h0 ->
      B.length dst = Spec.QUIC.header_len (g_header h h0) (U8.v pn_len) /\
      B.length npn = 1 + U8.v pn_len /\
      header_live h h0 /\
      header_disjoint h /\
      B.(all_disjoint [ loc_buffer dst; header_footprint h; loc_buffer npn ])))
    (ensures (fun h0 _ h1 ->
      B.(modifies (loc_buffer dst) h0 h1) /\ (
      let fh = Spec.QUIC.format_header (g_header h h0) (B.as_seq h0 npn) in
      S.slice (B.as_seq h1 dst) 0 (S.length fh) `S.equal` fh)))
=
  admit ();
  C.Failure.failwith C.String.(!$"TODO")

let vlen (n:u62) : x:U8.t { U8.v x = Spec.QUIC.vlen (U64.v n) } =
  assert_norm (pow2 6 = 64);
  assert_norm (pow2 14 = 16384);
  assert_norm (pow2 30 = 1073741824);
  if n `U64.lt` 64UL then 1uy
  else if n `U64.lt` 16384UL then 2uy
  else if n `U64.lt` 1073741824UL then 4uy
  else 8uy

let header_len (h: header) (pn_len: u2): Stack U32.t
  (requires fun h0 -> True)
  (ensures fun h0 x h1 ->
    U32.v x = Spec.QUIC.header_len (g_header h h0) (U8.v pn_len) /\
    h0 == h1)
=
  [@inline_let]
  let u32_of_u8 = FStar.Int.Cast.uint8_to_uint32 in
  [@inline_let]
  let u64_of_u32 = FStar.Int.Cast.uint32_to_uint64 in
  match h with
  | Short _ _ _ cid_len ->
      U32.(1ul +^ u32_of_u8 cid_len +^ 1ul +^ u32_of_u8 pn_len)
  | Long _ _ _ dcil _ scil plain_len ->
      assert_norm (pow2 32 < pow2 62);
      U32.(6ul +^ u32_of_u8 (add3 dcil) +^ u32_of_u8 (add3 scil) +^
        u32_of_u8 (vlen (u64_of_u32 plain_len)) +^ 1ul +^ u32_of_u8 pn_len)

let block_len (a: Spec.Agile.Cipher.cipher_alg):
  x:U32.t { U32.v x = Spec.Agile.Cipher.block_length a }
=
  let open Spec.Agile.Cipher in
  match a with | CHACHA20 -> 64ul | _ -> 16ul

#push-options "--max_fuel 1"
let rec seq_map2_xor0 (s1 s2: S.seq U8.t): Lemma
  (requires
    S.length s1 = S.length s2 /\
    s1 `S.equal` S.create (S.length s2) 0uy)
  (ensures
    Spec.Loops.seq_map2 CTR.xor8 s1 s2 `S.equal` s2)
  (decreases (S.length s1))
=
  if S.length s1 = 0 then
    ()
  else
    let open FStar.UInt in
    logxor_lemma_1 #8 (U8.v (S.head s2));
    logxor_lemma_1 #8 (U8.v (S.head s1));
    logxor_commutative (U8.v (S.head s1)) (U8.v (S.head s2));
    seq_map2_xor0 (S.tail s1) (S.tail s2)
#pop-options

#push-options "--z3rlimit 100"
inline_for_extraction
let block_of_sample (a: Spec.Agile.Cipher.cipher_alg)
  (dst: B.buffer U8.t)
  (s: CTR.state a)
  (k: B.buffer U8.t)
  (sample: B.buffer U8.t):
  Stack unit
    (requires fun h0 ->
      B.(all_live h0 [ buf dst; buf k; buf sample ]) /\
      CTR.invariant h0 s /\
      B.(all_disjoint
        [ CTR.footprint h0 s; loc_buffer dst; loc_buffer k; loc_buffer sample ]) /\
      Spec.Agile.Cipher.(a == AES128 \/ a == AES256 \/ a == CHACHA20) /\
      B.length k = Spec.Agile.Cipher.key_length a /\
      B.length dst = 16 /\
      B.length sample = 16)
    (ensures fun h0 _ h1 ->
      B.(modifies (loc_buffer dst `loc_union` CTR.footprint h0 s) h0 h1) /\
      B.as_seq h1 dst `S.equal`
        Spec.QUIC.block_of_sample a (B.as_seq h0 k) (B.as_seq h0 sample))
=
  push_frame ();
  (**) let h0 = ST.get () in
  let zeroes = B.alloca 0uy (block_len a) in
  let dst_block = B.alloca 0uy (block_len a) in
  begin match a with
  | Spec.Agile.Cipher.CHACHA20 ->
      let ctr = LowStar.Endianness.load32_le (B.sub sample 0ul 4ul) in
      let iv = B.sub sample 4ul 12ul in
      (**) let h1 = ST.get () in
      CTR.init (G.hide a) s k iv 12ul ctr;
      CTR.update_block (G.hide a) s dst_block zeroes;
      (**) let h2 = ST.get () in
      (**) seq_map2_xor0 (B.as_seq h1 dst_block)
      (**)   (Spec.Agile.Cipher.ctr_block a (B.as_seq h0 k) (B.as_seq h1 iv) (U32.v ctr));
      (**) assert (B.as_seq h2 dst_block `S.equal`
      (**)   Spec.Agile.Cipher.ctr_block a (B.as_seq h0 k) (B.as_seq h1 iv) (U32.v ctr));
      let dst_slice = B.sub dst_block 0ul 16ul in
      (**) assert (B.as_seq h2 dst_slice `S.equal` S.slice (
      (**)   Spec.Agile.Cipher.ctr_block a (B.as_seq h0 k) (B.as_seq h1 iv) (U32.v ctr)
      (**) ) 0 16);
      B.blit dst_slice 0ul dst 0ul 16ul
  | _ ->
      let ctr = LowStar.Endianness.load32_be (B.sub sample 12ul 4ul) in
      let iv = B.sub sample 0ul 12ul in
      (**) let h1 = ST.get () in
      CTR.init (G.hide a) s k iv 12ul ctr;
      CTR.update_block (G.hide a) s dst_block zeroes;
      (**) let h2 = ST.get () in
      (**) seq_map2_xor0 (B.as_seq h1 dst_block)
      (**)   (Spec.Agile.Cipher.ctr_block a (B.as_seq h0 k) (B.as_seq h1 iv) (U32.v ctr));
      (**) assert (B.as_seq h2 dst_block `S.equal`
      (**)   Spec.Agile.Cipher.ctr_block a (B.as_seq h0 k) (B.as_seq h1 iv) (U32.v ctr));
      let dst_slice = B.sub dst_block 0ul 16ul in
      (**) assert (B.as_seq h2 dst_slice `S.equal` S.slice (
      (**)   Spec.Agile.Cipher.ctr_block a (B.as_seq h0 k) (B.as_seq h1 iv) (U32.v ctr)
      (**) ) 0 16);
      B.blit dst_slice 0ul dst 0ul 16ul

  end;
  pop_frame ()
#pop-options

let encrypt #i s dst h plain plain_len pn_len =
  let State hash_alg aead_alg e_traffic_secret e_initial_pn
    aead_state iv hp_key pn ctr_state = !*s
  in
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
