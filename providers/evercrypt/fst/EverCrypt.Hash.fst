module EverCrypt.Hash

#set-options "--max_fuel 0 --max_ifuel 0 --z3rlimit 100"

open FStar.HyperStack.ST

module B = LowStar.Buffer
module IB = LowStar.ImmutableBuffer
module HS = FStar.HyperStack
module ST = FStar.HyperStack.ST

module AC = EverCrypt.AutoConfig2
module SC = EverCrypt.StaticConfig

open LowStar.BufferOps
open FStar.Integers
open C.Failure

// Allow *just* the alg type to be inverted, so that the entire module can run
// with ifuel 0
let _: squash (inversion alg) = allow_inversion alg

let string_of_alg =
  let open C.String in function
  | MD5 -> !$"MD5"
  | SHA1 -> !$"SHA1"
  | SHA2_224 -> !$"SHA2_224"
  | SHA2_256 -> !$"SHA2_256"
  | SHA2_384 -> !$"SHA2_384"
  | SHA2_512 -> !$"SHA2_512"
  | Blake2S -> !$"Blake2S"
  | Blake2B -> !$"Blake2B"

let uint32_p = B.buffer uint_32
let uint64_p = B.buffer uint_64

inline_for_extraction noextract
let blake2_spec = Hacl.Impl.Blake2.Core.M32

inline_for_extraction noextract
let impl_of_alg (a:alg) : impl =
  match a with
  | MD5 | SHA1 | SHA2_224 | SHA2_256 | SHA2_384 | SHA2_512 -> (|a, ()|)
  | Blake2S | Blake2B -> (|a, blake2_spec|)


// JP: not sharing the 224/256 and 384/512 cases, even though the internal state
//   is the same, to avoid the additional proof burden.
// JP: also note that we are sharing state between implementations, since Vale
//   kindly offers a wrapper that is compatible with the HACL* representation
noeq
type state_s: alg -> Type0 =
| MD5_s: p:Hacl.Hash.Definitions.state (|MD5, ()|) -> state_s MD5
| SHA1_s: p:Hacl.Hash.Definitions.state (|SHA1, ()|) -> state_s SHA1
| SHA2_224_s: p:Hacl.Hash.Definitions.state (|SHA2_224, ()|) -> state_s SHA2_224
| SHA2_256_s: p:Hacl.Hash.Definitions.state (|SHA2_256, ()|) -> state_s SHA2_256
| SHA2_384_s: p:Hacl.Hash.Definitions.state (|SHA2_384, ()|) -> state_s SHA2_384
| SHA2_512_s: p:Hacl.Hash.Definitions.state (|SHA2_512, ()|) -> state_s SHA2_512
| Blake2S_s: p:Hacl.Hash.Definitions.state (|Blake2S, blake2_spec|) -> state_s Blake2S
| Blake2B_s: p:Hacl.Hash.Definitions.state (|Blake2B, blake2_spec|) -> state_s Blake2B

let invert_state_s (a: alg): Lemma
  (requires True)
  (ensures (inversion (state_s a)))
  [ SMTPat (state_s a) ]
=
  allow_inversion (state_s a)

let mk_state_s (#a:alg) (p:Hacl.Hash.Definitions.state (impl_of_alg a)) :
  GTot (state_s a) =
  match a with
  | MD5 -> MD5_s p
  | SHA1 -> SHA1_s p
  | SHA2_224 -> SHA2_224_s p
  | SHA2_256 -> SHA2_256_s p
  | SHA2_384 -> SHA2_384_s p
  | SHA2_512 -> SHA2_512_s p
  | Blake2S -> Blake2S_s p
  | Blake2B -> Blake2B_s p

inline_for_extraction
let p #a (s: state_s a): Hacl.Hash.Definitions.state (impl_of_alg a) =
  match s with
  | MD5_s p -> p
  | SHA1_s p -> p
  | SHA2_224_s p -> p
  | SHA2_256_s p -> p
  | SHA2_384_s p -> p
  | SHA2_512_s p -> p
  | Blake2S_s p -> p
  | Blake2B_s p -> p

let freeable_s #a s = B.freeable (p #a s)

let footprint_s #a (s: state_s a) =
  B.loc_addr_of_buffer (p s)

let invariant_s #a (s: state_s a) h =
  B.live h (p s)

let repr #a s h: GTot _ =
  as_seq h (p s)

let alg_of_state a s =
  let open LowStar.BufferOps in
  match s with
  | MD5_s _ -> MD5
  | SHA1_s _ -> SHA1
  | SHA2_224_s _ -> SHA2_224
  | SHA2_256_s _ -> SHA2_256
  | SHA2_384_s _ -> SHA2_384
  | SHA2_512_s _ -> SHA2_512
  | Blake2S_s _ -> Blake2S
  | Blake2B_s _ -> Blake2B

let repr_eq (#a:alg) (r1 r2: Spec.Hash.Definitions.words_state' a) =
  Seq.equal r1 r2

let fresh_is_disjoint l1 l2 h0 h1 = ()

let invariant_loc_in_footprint #a s m = ()

let frame_invariant #a l s h0 h1 =
  assert (repr_eq #a (repr #a s h0) (repr #a s h1))

inline_for_extraction noextract
let alloca a =
  let s: state_s a =
    match a with
    | MD5 -> MD5_s (B.alloca 0ul 4ul)
    | SHA1 -> SHA1_s (B.alloca 0ul 5ul)
    | SHA2_224 -> SHA2_224_s (B.alloca 0ul 8ul)
    | SHA2_256 -> SHA2_256_s (B.alloca 0ul 8ul)
    | SHA2_384 -> SHA2_384_s (B.alloca 0UL 8ul)
    | SHA2_512 -> SHA2_512_s (B.alloca 0UL 8ul)
    | Blake2S -> Blake2S_s (B.alloca 0ul 16ul)
    | Blake2B -> Blake2B_s (B.alloca 0uL 16ul)
  in
  s

let create_in a r =
  let s: state_s a =
    match a with
    | MD5 -> MD5_s (B.malloc r 0ul 4ul)
    | SHA1 -> SHA1_s (B.malloc r 0ul 5ul)
    | SHA2_224 -> SHA2_224_s (B.malloc r 0ul 8ul)
    | SHA2_256 -> SHA2_256_s (B.malloc r 0ul 8ul)
    | SHA2_384 -> SHA2_384_s (B.malloc r 0UL 8ul)
    | SHA2_512 -> SHA2_512_s (B.malloc r 0UL 8ul)
    | Blake2S -> Blake2S_s (B.malloc r 0ul 16ul)
    | Blake2B -> Blake2B_s (B.malloc r 0uL 16ul)
  in
  s

let create a =
  create_in a HS.root

#push-options "--ifuel 1"

let init #a s =
  match s with
  | MD5_s p -> Hacl.Hash.MD5.legacy_init p
  | SHA1_s p -> Hacl.Hash.SHA1.legacy_init p
  | SHA2_224_s p -> Hacl.Hash.SHA2.init_224 p
  | SHA2_256_s p -> Hacl.Hash.SHA2.init_256 p
  | SHA2_384_s p -> Hacl.Hash.SHA2.init_384 p
  | SHA2_512_s p -> Hacl.Hash.SHA2.init_512 p
  | Blake2S_s p -> let _ = Hacl.Hash.Blake2.init_blake2s_32 p in ()
  | Blake2B_s p -> let _ = Hacl.Hash.Blake2.init_blake2b_32 p in ()
#pop-options

friend Vale.SHA.SHA_helpers

// Avoid a cross-compilation unit symbol visibility... duplicate locally.
let k224_256 =
  LowStar.ImmutableBuffer.igcmalloc_of_list HS.root Spec.SHA2.Constants.k224_256_l

#push-options "--ifuel 1"

// A new switch between HACL and Vale; can be used in place of Hacl.Hash.SHA2.update_256
let update_multi_256 s ev blocks n =
  let has_shaext = AC.has_shaext () in
  let has_sse = AC.has_sse () in
  if EverCrypt.TargetConfig.x64 && (SC.vale && has_shaext && has_sse) then begin
    let n = Int.Cast.Full.uint32_to_uint64 n in
    B.recall k224_256;
    IB.recall_contents k224_256 Spec.SHA2.Constants.k224_256;
    IB.buffer_immutable_buffer_disjoint s k224_256 (ST.get ());
    IB.buffer_immutable_buffer_disjoint blocks k224_256 (ST.get ());
    Vale.Wrapper.X64.Sha.sha256_update s blocks n k224_256
  end else
    Hacl.Hash.SHA2.update_multi_256 s () blocks n

#pop-options

inline_for_extraction noextract
let update_multi_224 s ev blocks n =
  assert_norm (words_state SHA2_224 == words_state SHA2_256);
  let h0 = ST.get () in
  Spec.SHA2.Lemmas.update_multi_224_256 (B.as_seq h0 s, ()) (B.as_seq h0 blocks);
  update_multi_256 s ev blocks n

// Need to unroll the definition of update_multi once to prove that it's update
#push-options "--max_fuel 1 --ifuel 1"
let update #a s prevlen block =
  match s with
  | MD5_s p -> Hacl.Hash.MD5.legacy_update p () block
  | SHA1_s p -> Hacl.Hash.SHA1.legacy_update p () block
  | SHA2_224_s p -> update_multi_224 p () block 1ul
  | SHA2_256_s p -> update_multi_256 p () block 1ul
  | SHA2_384_s p -> Hacl.Hash.SHA2.update_384 p () block
  | SHA2_512_s p -> Hacl.Hash.SHA2.update_512 p () block
  | Blake2S_s p ->
      let _ = Hacl.Hash.Blake2.update_blake2s_32 p prevlen block in
      ()
  | Blake2B_s p ->
      [@inline_let] let prevlen = Int.Cast.Full.uint64_to_uint128 prevlen in
      let _ = Hacl.Hash.Blake2.update_blake2b_32 p prevlen block in
      ()
#pop-options

#push-options "--ifuel 1"

let update_multi #a s prevlen blocks len =
  match s with
  | MD5_s p ->
      let n = len / block_len MD5 in
      Hacl.Hash.MD5.legacy_update_multi p () blocks n
  | SHA1_s p ->
      let n = len / block_len SHA1 in
      Hacl.Hash.SHA1.legacy_update_multi p () blocks n
  | SHA2_224_s p ->
      let n = len / block_len SHA2_224 in
      update_multi_224 p () blocks n
  | SHA2_256_s p ->
      let n = len / block_len SHA2_256 in
      update_multi_256 p () blocks n
  | SHA2_384_s p ->
      let n = len / block_len SHA2_384 in
      Hacl.Hash.SHA2.update_multi_384 p () blocks n
  | SHA2_512_s p ->
      let n = len / block_len SHA2_512 in
      Hacl.Hash.SHA2.update_multi_512 p () blocks n
  | Blake2S_s p ->
      let n = len / block_len Blake2S in
      let _ = Hacl.Hash.Blake2.update_multi_blake2s_32 p prevlen blocks n in
      ()
  | Blake2B_s p ->
      [@inline_let] let prevlen = Int.Cast.Full.uint64_to_uint128 prevlen in
      let n = len / block_len Blake2B in
      let _ = Hacl.Hash.Blake2.update_multi_blake2b_32 p prevlen blocks n in
      ()

#pop-options

// Re-using the higher-order stateful combinator to get an instance of
// update_last that is capable of calling Vale under the hood
let update_last_256 s prev_len input input_len =
  Hacl.Hash.MD.mk_update_last SHA2_256 update_multi_256 Hacl.Hash.SHA2.pad_256 s prev_len input input_len

let update_last_224 s prev_len input input_len =
  assert_norm (words_state SHA2_224 == words_state SHA2_256);
  [@inline_let]
  let l x y:
    Lemma
      (ensures (Spec.Agile.Hash.update_multi SHA2_224 x y == Spec.Agile.Hash.update_multi SHA2_256 x y))
    [ SMTPat (Spec.Agile.Hash.update_multi SHA2_224 x y); SMTPat (Spec.Agile.Hash.update_multi SHA2_256 x y) ]
  =
    Spec.SHA2.Lemmas.update_multi_224_256 x y
  in
  update_last_256 s prev_len input input_len

// Splitting out these proof bits; the proof is highly unreliable when all six
// cases are done together in a single match
inline_for_extraction
let update_last_st (#a:e_alg) =
  let a = Ghost.reveal a in
  p:Hacl.Hash.Definitions.state (impl_of_alg a) ->
  ev:extra_state a ->
  prev_len:uint64_t ->
  last:uint8_p { B.length last <= block_length a } ->
  last_len:uint32_t {
    v last_len = B.length last /\
    v prev_len + v last_len <= max_input_length a /\
    v prev_len % block_length a = 0 /\
    extra_state_v ev + B.length last <= max_input_length a
    } ->
  Stack (extra_state a)
  (requires fun h0 ->
    B.live h0 p /\
    B.live h0 last /\
    B.(loc_disjoint (loc_buffer p) (loc_buffer last)))
  (ensures fun h0 ev' h1 ->
    B.(modifies (loc_buffer p) h0 h1) /\
    (Hacl.Hash.Definitions.as_seq h1 p, ev') ==
      Spec.Hash.Incremental.update_last a (Hacl.Hash.Definitions.as_seq h0 p, ev)
                                        (v prev_len) (B.as_seq h0 last))

inline_for_extraction
val update_last_64 (a: e_alg{ G.reveal a <> SHA2_384 /\
                              G.reveal a <> SHA2_512 /\
                              G.reveal a <> Blake2B })
  (update_last: Hacl.Hash.Definitions.update_last_st (impl_of_alg (G.reveal a))):
  update_last_st #a
inline_for_extraction
let update_last_64 a update_last p ev prev_len last last_len =
  update_last p ev prev_len last last_len

inline_for_extraction
val update_last_128 (a: e_alg{ G.reveal a = SHA2_384 \/
                               G.reveal a = SHA2_512 \/
                               G.reveal a = Blake2B})
  (update_last: Hacl.Hash.Definitions.update_last_st (impl_of_alg (G.reveal a))):
  update_last_st #a
inline_for_extraction
let update_last_128 a update_last p ev prev_len last last_len =
  [@inline_let] let prev_len : UInt128.t = Int.Cast.Full.uint64_to_uint128 prev_len in
  update_last p ev prev_len last last_len

/// Before defining ``update_last`` we introduce auxiliary functions for Blake2S
/// and Blake2B, because trying to define it completely at once leads to a proof loop.
/// Besides, even with this the Blake functions themselves are very brittle (they tend to loop).
inline_for_extraction noextract
let update_last_with_internal_st (a : alg) =
  s:state a ->
  p:Hacl.Hash.Definitions.state (impl_of_alg a) ->
  prev_len:uint64_t ->
  last:B.buffer Lib.IntTypes.uint8 { B.length last <= block_length a } ->
  last_len:uint32_t {
    v last_len = B.length last /\
    v prev_len + v last_len <= max_input_length a /\
    v prev_len % block_length a = 0
    } ->
  Stack unit
  (requires fun h0 ->
    invariant s h0 /\
    s == mk_state_s p /\
    B.live h0 last /\
    M.(loc_disjoint (footprint s h0) (loc_buffer last) /\
    v prev_len + v last_len <= max_input_length a))
  (ensures fun h0 _ h1 ->
    invariant s h1 /\
    repr s h1 ==
      fst (Spec.Hash.Incremental.update_last a (repr_with_counter s h0 prev_len) (v prev_len)
                                             (B.as_seq h0 last)) /\
    M.(modifies (footprint s h0) h0 h1) /\
    footprint s h0 == footprint s h1 /\
    preserves_freeable s h0 h1)

inline_for_extraction noextract
val update_last_blake2s : update_last_with_internal_st Blake2S

let update_last_blake2s s p prev_len last last_len =
  [@inline_let] let ev = prev_len in
  let x:Lib.IntTypes.uint_t Lib.IntTypes.U64 Lib.IntTypes.SEC =
    update_last_64 Blake2S Hacl.Hash.Blake2.update_last_blake2s_32 p ev
                   prev_len last last_len in
  ()

inline_for_extraction noextract
val update_last_blake2b : update_last_with_internal_st Blake2B

let update_last_blake2b s p prev_len last last_len =
  [@inline_let] let ev = Int.Cast.Full.uint64_to_uint128 prev_len in
  let x:Lib.IntTypes.uint_t Lib.IntTypes.U128 Lib.IntTypes.SEC =
    update_last_128 Blake2B Hacl.Hash.Blake2.update_last_blake2b_32 p ev
                    prev_len last last_len in
  ()

let update_last #a s prev_len last last_len =
  match s with
  | MD5_s p ->
      update_last_64 a Hacl.Hash.MD5.legacy_update_last p () prev_len last last_len
  | SHA1_s p ->
      update_last_64 a Hacl.Hash.SHA1.legacy_update_last p () prev_len last last_len
  | SHA2_224_s p ->
      update_last_64 a update_last_224 p () prev_len last last_len
  | SHA2_256_s p ->
      update_last_64 a update_last_256 p () prev_len last last_len
  | SHA2_384_s p ->
      update_last_128 a Hacl.Hash.SHA2.update_last_384 p () prev_len last last_len
  | SHA2_512_s p ->
      update_last_128 a Hacl.Hash.SHA2.update_last_512 p () prev_len last last_len
  | Blake2S_s p ->
      update_last_blake2s s p prev_len last last_len
  | Blake2B_s p ->
      update_last_blake2b s p prev_len last last_len

#push-options "--ifuel 1"

let finish #a s dst =
  match s with
  | MD5_s p -> Hacl.Hash.MD5.legacy_finish p () dst
  | SHA1_s p -> Hacl.Hash.SHA1.legacy_finish p () dst
  | SHA2_224_s p -> Hacl.Hash.SHA2.finish_224 p () dst
  | SHA2_256_s p -> Hacl.Hash.SHA2.finish_256 p () dst
  | SHA2_384_s p -> Hacl.Hash.SHA2.finish_384 p () dst
  | SHA2_512_s p -> Hacl.Hash.SHA2.finish_512 p () dst
  | Blake2S_s p -> Hacl.Hash.Blake2.finish_blake2s_32 p 0UL dst
  | Blake2B_s p ->
    Hacl.Hash.Blake2.finish_blake2b_32 p (Int.Cast.Full.uint64_to_uint128
                                             (UInt64.uint_to_t 0)) dst

#pop-options

let free #ea s =
  begin match s with
    | MD5_s p -> B.free p
    | SHA1_s p -> B.free p
    | SHA2_224_s p -> B.free p
    | SHA2_256_s p -> B.free p
    | SHA2_384_s p -> B.free p
    | SHA2_512_s p -> B.free p
    | Blake2S_s p -> B.free p
    | Blake2B_s p -> B.free p
  end

#push-options "--ifuel 1"

let copy #a s_src s_dst =
  match s_src with
  | MD5_s p_src ->
      [@inline_let]
      let s_dst: state MD5 = s_dst in
      let p_dst = MD5_s?.p s_dst in
      B.blit p_src 0ul p_dst 0ul 4ul
  | SHA1_s p_src ->
      [@inline_let]
      let s_dst: state SHA1 = s_dst in
      let p_dst = SHA1_s?.p s_dst in
      B.blit p_src 0ul p_dst 0ul 5ul
  | SHA2_224_s p_src ->
      [@inline_let]
      let s_dst: state SHA2_224 = s_dst in
      let p_dst = SHA2_224_s?.p s_dst in
      B.blit p_src 0ul p_dst 0ul 8ul
  | SHA2_256_s p_src ->
      [@inline_let]
      let s_dst: state SHA2_256 = s_dst in
      let p_dst = SHA2_256_s?.p s_dst in
      B.blit p_src 0ul p_dst 0ul 8ul
  | SHA2_384_s p_src ->
      [@inline_let]
      let s_dst: state SHA2_384 = s_dst in
      let p_dst = SHA2_384_s?.p s_dst in
      B.blit p_src 0ul p_dst 0ul 8ul
  | SHA2_512_s p_src ->
      [@inline_let]
      let s_dst: state SHA2_512 = s_dst in
      let p_dst = SHA2_512_s?.p s_dst in
      B.blit p_src 0ul p_dst 0ul 8ul
  | Blake2S_s p_src ->
      [@inline_let]
      let s_dst: state Blake2S = s_dst in
      let p_dst = Blake2S_s?.p s_dst in
      B.blit p_src 0ul p_dst 0ul 16ul
  | Blake2B_s p_src ->
      [@inline_let]
      let s_dst: state Blake2B = s_dst in
      let p_dst = Blake2B_s?.p s_dst in
      B.blit p_src 0ul p_dst 0ul 16ul

#pop-options

// A full one-shot hash that relies on vale at each multiplexing point
let hash_256 input input_len dst =
  Hacl.Hash.MD.mk_hash SHA2_256 Hacl.Hash.SHA2.alloca_256 update_multi_256
    update_last_256 Hacl.Hash.SHA2.finish_256 input input_len dst

let hash_224 input input_len dst =
  Hacl.Hash.MD.mk_hash SHA2_224 Hacl.Hash.SHA2.alloca_224 update_multi_224
    update_last_224 Hacl.Hash.SHA2.finish_224 input input_len dst

let hash a dst input len =
  match a with
  | MD5 -> Hacl.Hash.MD5.legacy_hash input len dst
  | SHA1 -> Hacl.Hash.SHA1.legacy_hash input len dst
  | SHA2_224 -> hash_224 input len dst
  | SHA2_256 -> hash_256 input len dst
  | SHA2_384 -> Hacl.Hash.SHA2.hash_384 input len dst
  | SHA2_512 -> Hacl.Hash.SHA2.hash_512 input len dst
  | Blake2S -> Hacl.Hash.Blake2.hash_blake2s_32 input len dst
  | Blake2B -> Hacl.Hash.Blake2.hash_blake2b_32 input len dst
