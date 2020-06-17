module Hacl.Streaming.Blake2s_32

module HS = FStar.HyperStack
module B = LowStar.Buffer
module G = FStar.Ghost
module S = FStar.Seq
module U32 = FStar.UInt32
module U64 = FStar.UInt64
module U128 = FStar.UInt128
module Case = FStar.Int.Cast.Full
module F = Hacl.Streaming.Functor
module I = Hacl.Streaming.Interface
module P = Hacl.Impl.Poly1305
module ST = FStar.HyperStack.ST

module Agile = Spec.Agile.Hash
module Hash = Spec.Hash.Definitions

open LowStar.BufferOps
open FStar.Mul

module Loops = Lib.LoopCombinators

/// Opening a bunch of modules for Blake2
/// =======================================

inline_for_extraction noextract
let uint8 = Lib.IntTypes.uint8

inline_for_extraction noextract
let uint32 = Lib.IntTypes.uint32

module Spec = Spec.Blake2
open Hacl.Impl.Blake2.Core
module Core = Hacl.Impl.Blake2.Core
open Hacl.Impl.Blake2.Generic
module Impl = Hacl.Impl.Blake2.Generic
module Incr = Spec.Hash.Incremental

/// An instance of the stateful type class for blake2
/// =========================================================

#set-options "--max_fuel 0 --max_ifuel 0 --z3rlimit 100"

inline_for_extraction noextract
let a = Spec.Blake2S

inline_for_extraction noextract
let m = M32

let to_hash_alg (a : Spec.alg) =
  match a with
  | Spec.Blake2S -> Hash.Blake2S
  | Spec.Blake2B -> Hash.Blake2B

let index = unit

/// The stateful state: (wv, hash)
inline_for_extraction noextract
let s = state_p a m & state_p a m

inline_for_extraction noextract
let extra_state_zero_element a : Hash.extra_state (to_hash_alg a) =
  Hash.nat_to_extra_state (to_hash_alg a) 0

inline_for_extraction noextract
let t = Hash.words_state' (to_hash_alg a)

inline_for_extraction noextract
let get_wv (s : s) : Tot (state_p a m) =
  match s with wv, _ -> wv

inline_for_extraction noextract
let get_state_p (s : s) : Tot (state_p a m) =
  match s with _, p -> p

inline_for_extraction noextract
let state_v (h : HS.mem) (s : s) : GTot (Spec.state a) =
  Core.state_v h (get_state_p s)

inline_for_extraction noextract
let s_v (h : HS.mem) (s : s) : GTot t =
  state_v h s

/// Small helper which facilitates inferencing implicit arguments for buffer
/// operations
inline_for_extraction noextract
let state_to_lbuffer (s : state_p a m) :
  B.lbuffer (element_t a m) (4 * U32.v (row_len a m)) =
  s

inline_for_extraction noextract
let stateful_blake2s_32: I.stateful unit =
  I.Stateful
    (fun () -> s) (* s *)
    (* footprint *)
    (fun #_ _ acc ->
      let wv, b = acc in
      B.loc_union
       (B.loc_addr_of_buffer (state_to_lbuffer wv))
       (B.loc_addr_of_buffer (state_to_lbuffer b)))
    (* freeable *)
    (fun #_ _ acc ->
      let wv, b = acc in
      B.freeable (state_to_lbuffer wv) /\
      B.freeable (state_to_lbuffer b))
    (* invariant *)
    (fun #_ h acc ->
      let wv, b = acc in
      B.live h (state_to_lbuffer wv) /\
      B.live h (state_to_lbuffer b) /\
      B.disjoint (state_to_lbuffer wv) (state_to_lbuffer b))
    (fun () -> t) (* t *)
    (fun () h acc -> s_v h acc) (* v *)
    (fun #_ h acc -> let wv, b = acc in ()) (* invariant_loc_in_footprint *)
    (fun #_ l acc h0 h1 -> let wv, b = acc in ()) (* frame_invariant *)
    (fun #_ _ _ _ _ -> ()) (* frame_freeable *)
    (* alloca *)
    (fun () ->
      let wv = alloc_state a m in
      let b = alloc_state a m in
//      let l = B.alloca (extra_state_zero_element a) (U32.uint_to_t 1) in
      wv, b)
    (* create_in *)
    (fun () r ->
      let wv = B.malloc r (zero_element a m) U32.(4ul *^ row_len a m) in
      let b = B.malloc r (zero_element a m) U32.(4ul *^ row_len a m) in
//      let l = B.malloc r (extra_state_zero_element a) (U32.uint_to_t 1) in
      wv, b)
    (* free *)
    (fun _ acc ->
      match acc with wv, b ->
      B.free (state_to_lbuffer wv);
      B.free (state_to_lbuffer b))
    (* copy *)
    (fun _ src dst ->
      match src with src_wv, src_b ->
      match dst with src_wv, dst_b ->
      B.blit (state_to_lbuffer src_b) 0ul (state_to_lbuffer dst_b) 0ul
             U32.(4ul *^ row_len a m))

inline_for_extraction noextract
let k (key_size : nat{0 < key_size /\ key_size <= Spec.max_key a}) =
  I.stateful_buffer uint8 (U32.uint_to_t key_size) (Lib.IntTypes.u8 0)

let max_input_length (key_size : nat) : nat =
  if key_size = 0 then Spec.max_limb a
  else Spec.max_limb a - Spec.size_block a

inline_for_extraction noextract
let block = (block: S.seq uint8 { S.length block = Spec.size_block a })

inline_for_extraction noextract
let block_len = Core.size_block a

inline_for_extraction noextract
let key_size : nat = Spec.max_key a

inline_for_extraction noextract
let key_len : U32.t = U32.uint_to_t key_size

inline_for_extraction noextract
let output_size : nat = Spec.max_output a

inline_for_extraction noextract
let output_len = U32.uint_to_t output_size

/// The prevlen parameter computed by the streaming functor and given to ``update_multi``
/// or ``update_last`` is equal to the length of the data processed so far (without the
/// key). In the case of blake2, however, we also need to count the key (if it is not
/// an empty seq) in the total length of processed data.
inline_for_extraction noextract
let blake2_prevlen_nat (key_size : nat) (prevlen : nat) : nat =
  if key_size = 0 then prevlen else prevlen + Spec.size_block a

/// Same function as above but with low-level types
inline_for_extraction noextract
let blake2_prevlen_ (key_size : nat)
                    (prevlen : U64.t{ U64.v prevlen <= max_input_length key_size }) :
  x:U64.t { U64.v x = blake2_prevlen_nat key_size (U64.v prevlen) } =
  if key_size = 0 then prevlen
  else U64.(prevlen +^ FStar.Int.Cast.uint32_to_uint64 block_len)

inline_for_extraction noextract
let blake2_prevlen (key_size : nat)
                   (prevlen : U64.t{ U64.v prevlen <= max_input_length key_size }) :
  x:Spec.limb_t a {
    Lib.IntTypes.uint_v x = blake2_prevlen_nat key_size (U64.v prevlen) } =
  let open Lib.IntTypes in
  match a with
  | Spec.Blake2S -> to_u64 #U64 #PUB (blake2_prevlen_ key_size prevlen)
  | Spec.Blake2B -> FStar.Int.Cast.Full.uint64_to_uint128
                     (to_u64 #U64 #PUB (blake2_prevlen_ key_size prevlen))

let init_s () (key : Seq.lseq uint8 key_size) : Tot t =
  Spec.blake2_init a key_size key output_size

let update_multi_s () (acc : t) (prevlen : nat{prevlen % Spec.size_block a = 0})
                   (input : Seq.seq uint8{ prevlen + S.length input <= max_input_length key_size /\
                                           S.length input % Spec.size_block a = 0 }) :
  Tot t =
  let es = Hash.nat_to_extra_state (to_hash_alg a) (blake2_prevlen_nat key_size prevlen) in
  let s = (acc, es) in
  fst (Agile.update_multi (to_hash_alg a) s input)

let update_last_s () (acc : t) (prevlen : nat{prevlen % Spec.size_block a = 0})
                  (input : Seq.seq uint8{ S.length input + prevlen <= max_input_length key_size /\
                                          S.length input <= Spec.size_block a }) :
  Tot t =
  let es = Hash.nat_to_extra_state (to_hash_alg a) (blake2_prevlen_nat key_size prevlen) in
  let s = (acc, es) in
  fst (Spec.Hash.Incremental.update_last (to_hash_alg a) s prevlen input)

let finish_s () (key : Seq.lseq uint8 key_size) (acc : t) :
  output : S.seq uint8 { S.length output = U32.v output_len } =
  (* The extra state is actually not used, so we initialize it to a dummy value *)
  let s = (acc, Hash.nat_to_extra_state (to_hash_alg a) 0) in
  Spec.Hash.PadFinish.finish (to_hash_alg a) s

let spec_s ()
           (key : S.seq uint8{S.length key = key_size})
           (input : S.seq uint8{S.length input <= max_input_length key_size}) = 
  Spec.blake2 a input key_size key output_size

/// Interlude for spec proofs
/// =====================================
val update_multi_zero:
  i:index ->
  acc:t ->
  prevlen:nat{prevlen % Spec.size_block a = 0} ->
  Lemma
  (requires (prevlen <= max_input_length key_size))
  (ensures (update_multi_s i acc prevlen S.empty == acc))

let update_multi_zero () acc prevlen =
  let es = Hash.nat_to_extra_state (to_hash_alg a) (blake2_prevlen_nat key_size prevlen) in
  let s = (acc, es) in
  Spec.Hash.Lemmas.update_multi_zero (to_hash_alg a) s

val update_multi_associative:
  i:index ->
  acc: t ->
  prevlen1:nat ->
  prevlen2:nat ->
  input1:S.seq uint8 ->
  input2:S.seq uint8 ->
  Lemma
  (requires (
    prevlen1 % Spec.size_block a = 0 /\
    S.length input1 % Spec.size_block a = 0 /\
    S.length input2 % Spec.size_block a = 0 /\
    prevlen1 + S.length input1 + S.length input2 <= max_input_length key_size /\
    prevlen2 = prevlen1 + S.length input1))
  (ensures (
    let input = S.append input1 input2 in
    S.length input % Spec.size_block a = 0 /\
    prevlen2 % Spec.size_block a = 0 /\
    update_multi_s i (update_multi_s i acc prevlen1 input1) prevlen2 input2 ==
      update_multi_s i acc prevlen1 input))

let update_multi_associative () acc prevlen1 prevlen2 input1 input2 =
  let es = Hash.nat_to_extra_state (to_hash_alg a) (blake2_prevlen_nat key_size prevlen1) in
  let s = (acc, es) in
  Spec.Hash.Lemmas.update_multi_associative (to_hash_alg a) s input1 input2;
  Spec.Hash.Incremental.Lemmas.update_multi_extra_state_eq (to_hash_alg a) s input1;
  Spec.Hash.Lemmas.extra_state_add_nat_bound_lem2 #(to_hash_alg a) es (S.length input1)
 
/// A helper function: the hash incremental function defined with the functions
/// locally defined (with a signature adapted to the functor).
val blake2_hash_incremental_s :
  i:index ->
  key: I.((k key_size).t ()) ->
  input:S.seq uint8 { S.length input <= max_input_length key_size } ->
  output:S.seq uint8 { S.length output = output_size }

let blake2_hash_incremental_s i key input =
  let bs, l = Spec.Hash.Incremental.split_blocks (to_hash_alg a) input in
  let acc1 = init_s i key in
  let acc2 = update_multi_s i acc1 0 bs in
  let acc3 = update_last_s i acc2 (S.length bs) l in
  let acc4 = finish_s i key acc3 in
  acc4

/// This helper lemma proves that the blake2 specification functions defined above
/// with a signature adapted to the functor give the same result, if properly called,
/// as the original hash incremental functions.
val blake2_hash_incremental_s_is_hash_incremental :
  i:index ->
  key: I.((k key_size).t ()) ->
  input:S.seq uint8 { S.length input <= max_input_length key_size } ->
  Lemma(
    blake2_hash_incremental_s i key input ==
      Spec.Hash.Incremental.blake2_hash_incremental (to_hash_alg a) key_size key input)

/// TODO: make the proof stable
let blake2_hash_incremental_s_is_hash_incremental i key input =
  let bs, l = Spec.Hash.Incremental.split_blocks (to_hash_alg a) input in
  let acc1 = init_s i key in
  let acc2 = update_multi_s i acc1 0 bs in
  let acc3 = update_last_s i acc2 (S.length bs) l in
  let acc4 = finish_s i key acc3 in
  assert(acc4 == blake2_hash_incremental_s i key input); (* sanity check *)
  let s1 = Spec.Hash.Incremental.blake2_init (to_hash_alg a) key_size key in
  let s2 = Agile.update_multi (to_hash_alg a) s1 bs in
  let prevlen = S.length bs in (* dummy value: this variable is actually not used *)
  let s3 = Spec.Hash.Incremental.update_last (to_hash_alg a) s2 prevlen l in
  let s4 = Spec.Hash.PadFinish.finish (to_hash_alg a) s3 in
  let s4' = Spec.Hash.Incremental.blake2_hash_incremental (to_hash_alg a) key_size key input in
  assert(s4 == s4'); (* sanity check *)
  (* The proof *)
  let es1 = Hash.nat_to_extra_state (to_hash_alg a) (blake2_prevlen_nat key_size 0) in
  let s1' = (acc1, es1) in
  assert(s1' == s1);
  Spec.Hash.Incremental.Lemmas.update_multi_extra_state_eq (to_hash_alg a) s1 bs;
  Spec.Hash.Lemmas.extra_state_add_nat_bound_lem2 #(to_hash_alg a) es1 (S.length bs);
  let es2 = Hash.nat_to_extra_state (to_hash_alg a) (blake2_prevlen_nat key_size (S.length bs)) in
  let s2' = (acc2, es2) in
  assert(s2' == s2);
  let es3 = Hash.nat_to_extra_state (to_hash_alg a) 0 in
  let s3' = (acc3, es3) in
  assert(s3' == s3);
  assert(acc4 == s4)

/// TODO: make stable
val spec_is_incremental:
  i:index ->
  key: I.((k key_size).t ()) ->
  input:S.seq uint8 { S.length input <= max_input_length key_size } ->
  Lemma (
    let bs, l = Spec.Hash.Incremental.split_blocks (to_hash_alg a) input in
    let hash = update_multi_s i (init_s i key) 0 bs in
    let hash = update_last_s i hash (S.length bs) l in
    finish_s i key hash `S.equal` spec_s i key input)

let spec_is_incremental i key input =
  blake2_hash_incremental_s_is_hash_incremental i key input;
  Spec.Hash.Incremental.blake2_is_hash_incremental (to_hash_alg a) key_size key input

val update_multi_eq :
  nb : nat ->
  acc : t ->
  prevlen : nat {prevlen % Spec.size_block a = 0 } ->
  blocks : S.seq uint8 ->
  Lemma
    (requires (
      prevlen + S.length blocks <= max_input_length key_size /\
      blake2_prevlen_nat key_size prevlen + S.length blocks <= Hash.max_extra_state (to_hash_alg a) /\
      S.length blocks = Hash.block_length (to_hash_alg a) * nb))
    (ensures (
      let prevlen' = blake2_prevlen_nat key_size prevlen in
      update_multi_s () acc prevlen blocks ==
        Loops.repeati #(Hash.words_state' (to_hash_alg a)) nb
                       (Spec.blake2_update1 a prevlen' blocks) acc))

let update_multi_eq nb acc prevlen blocks =
  let blocks', _ = Seq.split blocks (nb * Hash.block_length (to_hash_alg a)) in
  assert(blocks' `Seq.equal` blocks);
  let prevlen' = blake2_prevlen_nat key_size prevlen in
  let es = Hash.nat_to_extra_state (to_hash_alg a) prevlen' in
  Spec.Hash.Incremental.repeati_blake2_update1_is_update_multi (to_hash_alg a)
                                                               nb prevlen'
                                                               blocks acc;
  Spec.Hash.Lemmas.extra_state_add_nat_bound_lem1 #(to_hash_alg a) es (S.length blocks);
  assert(
    Hash.nat_to_extra_state (to_hash_alg a) (prevlen' + S.length blocks) ==
    Hash.extra_state_add_nat #(to_hash_alg a) es (S.length blocks))

val update_last_eq :
  prevlen : nat{prevlen % Hash.block_length (to_hash_alg a) = 0} ->
  last : S.seq uint8 {S.length last <= Hash.block_length (to_hash_alg a) /\
                      prevlen + S.length last <= max_input_length key_size} ->
  acc : t ->
  Lemma
  (ensures (
    let prevlen' = blake2_prevlen_nat key_size prevlen in
    Spec.blake2_update_last a prevlen' (S.length last) last acc ==
      update_last_s () acc prevlen last))

/// TODO: make stable
let update_last_eq prevlen last acc =
  (* Checking how to unfold the ``update_last_s`` definition *)
  let prevlen' = blake2_prevlen_nat key_size prevlen in
  let es = Hash.nat_to_extra_state (to_hash_alg a) prevlen' in
  let s = acc, es in
  let s' = Spec.Hash.Incremental.update_last_blake (to_hash_alg a) s prevlen' last in
  (* TODO: if accf is defined before s', the proof loops at the definition of s' *)
  let accf = update_last_s () acc prevlen last in
  assert(accf == fst s');
  (* Make sure the blocks decomposition is what we expect *)
  let blocks, last_block, rem = Spec.Hash.Incremental.last_split_blake (to_hash_alg a) last in
  assert(blocks `S.equal` S.empty);
  assert(rem = S.length last);
  assert(last_block == Spec.get_last_padded_block a last (S.length last));
  (* Prove that the last call to ``update_multi`` does nothing (there is no call to
   * ``update_multi`` in ``blake2_update_last`` *)
  let s2 = Spec.Agile.Hash.update_multi (to_hash_alg a) s blocks in
  Spec.Hash.Lemmas.update_multi_zero (to_hash_alg a) s;
  assert(s2 == s);
  (* Prove that the extra state update computes the same total length as in ``blake2_update_last`` *)
  Spec.Hash.Lemmas.extra_state_add_nat_bound_lem1 #(to_hash_alg a) es (S.length last);
  assert(Hash.extra_state_v (Hash.extra_state_add_nat es (S.length last)) ==
         Hash.extra_state_v es + S.length last)

/// Equality between the state types defined by blake2s and the generic hash.
/// The equality is not trivial because of subtleties linked to the way types are
/// encoded for Z3.
val state_types_equalities : unit ->
  Lemma(Spec.Blake2.state a == Hash.words_state' (to_hash_alg a))

let state_types_equalities () =
  let open Lib.Sequence in
  let open Lib.IntTypes in
  assert(Spec.Blake2.state a == lseq (Spec.row a) 4);
  assert_norm(Hash.words_state' (to_hash_alg a) == m:Seq.seq (Spec.row a) {Seq.length m = 4});
  assert_norm(lseq (Spec.row a) 4 == m:Seq.seq (Spec.row a) {Seq.length m == 4});
  assert(lseq (Spec.row a) 4 == m:Seq.seq (Spec.row a) {Seq.length m = 4})

(* TODO: find a way not to duplicate the block spec *)
val update_multi: (i:G.erased index -> (
  let i = G.reveal i in
  s:s ->
  prevlen:U64.t { U64.v prevlen % U32.v (block_len) = 0 } ->
  blocks:B.buffer uint8 { B.length blocks % U32.v (block_len) = 0 } ->
  len: U32.t { U32.v len = B.length blocks /\
               U64.v prevlen + U32.v len <= max_input_length key_size } ->
  ST.Stack unit
  (requires fun h0 ->
    let state = stateful_blake2s_32 in
    state.I.invariant #i h0 s /\
    B.live h0 blocks /\
    B.(loc_disjoint (state.I.footprint #i h0 s) (loc_buffer blocks)))
  (ensures fun h0 _ h1 ->
    let state = stateful_blake2s_32 in
    B.(modifies (state.I.footprint #i h0 s) h0 h1) /\
    state.I.footprint #i h0 s == state.I.footprint #i h1 s /\
    state.I.invariant #i h1 s /\
    state.I.v i h1 s == update_multi_s i (state.I.v i h0 s) (U64.v prevlen) (B.as_seq h0 blocks) /\
    (state.I.freeable #i h0 s ==> state.I.freeable #i h1 s))))

let update_multi i acc prevlen blocks len =
  [@inline_let] let wv = get_wv acc in
  [@inline_let] let h = get_state_p acc in
  (**) let h0 = ST.get () in
  let nb = U32.(len /^ block_len) in
  [@inline_let] let prevlen' = blake2_prevlen key_size prevlen in
  Impl.blake2_update_multi #a #m #len (Impl.blake2_update_block #a #m) wv h
                           prevlen' blocks nb;
  (**) let h3 = ST.get () in
  (**) assert(s_v h3 acc ==
  (**)    Loops.repeati #(Spec.Blake2.state a) (U32.v nb)
  (**)                  (Spec.blake2_update1 a (Lib.IntTypes.uint_v prevlen')
  (**)                                       (B.as_seq h0 blocks))
  (**)                  (s_v h0 acc));
  (**) state_types_equalities ();
  (**) assert(Spec.Blake2.state a == Hash.words_state' (to_hash_alg a));
  (**) update_multi_eq (U32.v nb) (s_v h0 acc) (U64.v prevlen) (B.as_seq h0 blocks);
  (**) assert(Lib.IntTypes.uint_v prevlen' = blake2_prevlen_nat key_size (U64.v prevlen));
  (**) assert(s_v h3 acc == update_multi_s () (s_v h0 acc) (U64.v prevlen) (B.as_seq h0 blocks));
  (**) assert(B.(modifies (stateful_blake2s_32.I.footprint #() h0 acc) h0 h3))

val update_last: (
  i: G.erased index -> (
  let i = G.reveal i in
  s:s ->
  prevlen:U64.t { U64.v prevlen % U32.v (block_len) = 0 } ->
  last:B.buffer uint8 ->
  last_len:U32.t{
    last_len = B.len last /\
    U32.v last_len <= U32.v (block_len) /\
    U64.v prevlen + U32.v last_len <= max_input_length key_size} ->
  ST.Stack unit
  (requires fun h0 ->
    let state = stateful_blake2s_32 in
    state.I.invariant #i h0 s /\
    B.live h0 last /\
    B.(loc_disjoint (state.I.footprint #i h0 s) (loc_buffer last)))
  (ensures fun h0 _ h1 ->
    let state = stateful_blake2s_32 in
    state.I.invariant #i h1 s /\
    state.I.v i h1 s == update_last_s i (state.I.v i h0 s) (U64.v prevlen) (B.as_seq h0 last) /\
    B.(modifies (state.I.footprint #i h0 s) h0 h1) /\
    state.I.footprint #i h0 s == state.I.footprint #i h1 s /\
    (state.I.freeable #i h0 s ==> state.I.freeable #i h1 s))))

let update_last _ acc prevlen last last_len =
  [@inline_let] let wv = get_wv acc in
  [@inline_let] let h = get_state_p acc in
  (**) let h0 = ST.get () in
  (**) assert_norm(U64.v prevlen + U32.v last_len <= Spec.Blake2.max_limb a);
  [@inline_let]
  let prevlen' = blake2_prevlen key_size prevlen in
  assert((U64.v prevlen) % Hash.block_length (to_hash_alg a) = 0);
  assert(B.length last <= Hash.block_length (to_hash_alg a));
  assert(U64.v prevlen + B.length last <= max_input_length key_size);
  (* TODO: this call loops if moved at the end of the proof *)
  (**) update_last_eq (U64.v prevlen) (B.as_seq h0 last) (s_v h0 acc);
  Impl.blake2_update_last #a #m (Impl.blake2_update_block #a #m) #last_len
                          wv h prevlen' last_len last;
  (**) let h2 = ST.get () in
  (**) assert(
  (**)   Core.state_v h2 h ==
  (**)     Spec.blake2_update_last a (Lib.IntTypes.uint_v prevlen') (U32.v last_len)
  (**)                               (B.as_seq h0 last)
  (**)                               (Core.state_v h0 h));
  (**) assert(s_v h2 acc ==
  (**)   update_last_s () (s_v h0 acc) (U64.v prevlen) (B.as_seq h0 last))

#push-options "--ifuel 1"
inline_for_extraction noextract
let blake2s_32 (* : I.block unit *) =
  I.Block
    I.Erased (* key management *)
    
    stateful_blake2s_32 (* state *)
    (k key_size) (* key *)
    
    (fun () -> max_input_length (Spec.max_key a)) (* max_input_length *)
    (fun () -> output_len) (* output_len *)
    (fun () -> block_len) (* block_len *)
    
    (fun () k -> init_s () k) (* init_s *)
    (fun () acc prevlen input -> update_multi_s () acc prevlen input) (* update_multi_s *)
    (fun () acc prevlen input -> update_last_s () acc prevlen input) (* update_last_s *)
    (fun () k acc -> finish_s () k acc) (* finish_s *)
    (fun () -> spec_s ()) (* spec_s *)

    (fun () prevlen acc -> update_multi_zero () prevlen acc) (* update_multi_zero *)
    (* update_multi_associative *)
    (fun () acc prevlen1 prevlen2 input1 input2 ->
      update_multi_associative () acc prevlen1 prevlen2 input1 input2)
    (fun () k input -> spec_is_incremental () k input) (* spec_is_incremental *)
    (fun _ acc -> ()) (* index_of_state *)

    (* init *)
    (fun _ key acc ->
      [@inline_let] let wv = get_wv acc in
      [@inline_let] let h = get_state_p acc in
      Impl.blake2_init #a #m (Impl.blake2_update_block #a #m) wv h key_len key output_len)

    (* update_multi *)
    (fun _ acc prevlen blocks len -> update_multi () acc prevlen blocks len)

    (* update_last *)
    (fun _ acc prevlen last last_len ->
      update_last () acc prevlen last last_len)

    (* finish *)
    (fun _ k acc dst ->
      [@inline_let] let wv = get_wv acc in
      [@inline_let] let h = get_state_p acc in
      Impl.blake2_finish #a #m output_len dst h)
#pop-options

/// The incremental hash functions instantiations
let create_in = F.create_in blake2s_32 () s (I.optional_key () I.Erased (k key_size))
let init = F.init blake2s_32 (G.hide ()) s (I.optional_key () I.Erased (k key_size))
let update = F.update blake2s_32 (G.hide ()) s (I.optional_key () I.Erased (k key_size))
let finish = F.mk_finish blake2s_32 () s (I.optional_key () I.Erased (k key_size))
let free = F.free blake2s_32 (G.hide ()) s (I.optional_key () I.Erased (k key_size))
