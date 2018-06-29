module EverCrypt.Hash

open EverCrypt.Helpers
open FStar.HyperStack.ST
open FStar.Integers

module HS = FStar.HyperStack
module B = LowStar.Buffer
module M = LowStar.Modifies
module G = FStar.Ghost

open LowStar.BufferOps

let uint8_p = B.buffer UInt8.t
let bytes = Seq.seq UInt8.t

type alg =
| SHA256
| SHA384

type e_alg =
  G.erased alg

val state_s: e_alg -> Type0
let state alg = B.pointer (state_s alg)

// NS: note that the state is the first argument to the invariant so that we can
// do partial applications in pre- and post-conditions
val footprint_s: #a:e_alg -> state_s a -> GTot M.loc
let footprint (#a: e_alg) (s: state a) (m: HS.mem) =
  M.(loc_union (loc_buffer s) (footprint_s (deref m s)))

val invariant_s: (#a: e_alg) -> state_s a -> HS.mem -> Type0
let invariant (#a: e_alg) (s: state a) (m: HS.mem) =
  B.live m s /\
  M.(loc_disjoint (loc_buffer s) (footprint_s (deref m s))) /\
  invariant_s (B.get m s 0) m

let type_of alg =
  match G.reveal alg with
  | SHA256 -> uint_32
  | SHA384 -> uint_64

let size_of_k alg =
  match G.reveal alg with
  | SHA256 -> 64
  | SHA384 -> 80

type repr_t (a: e_alg) = {
  k: Seq.lseq (type_of a) (size_of_k a);
  hash: Seq.lseq (type_of a) 8;
  counter: nat;
}

val repr: #a:e_alg -> s:state a -> h:HS.mem { invariant s h } ->
  GTot (repr_t a)

// Waiting for these to land in LowStar.Modifies
let loc_in (l: M.loc) (h: HS.mem) =
  M.(loc_not_unused_in h `loc_includes` l)

let loc_unused_in (l: M.loc) (h: HS.mem) =
  M.(loc_unused_in h `loc_includes` l)

let fresh_loc (l: M.loc) (h0 h1: HS.mem) =
  loc_unused_in l h0 /\ loc_in l h1

val fresh_is_disjoint: l1:M.loc -> l2:M.loc -> h0:HS.mem -> h1:HS.mem -> Lemma
  (requires (fresh_loc l1 h0 h1 /\ l2 `loc_in` h0))
  (ensures (M.loc_disjoint l1 l2))

val frame_invariant: #a:e_alg -> l:M.loc -> s:state a -> h0:HS.mem -> h1:HS.mem -> Lemma
  (requires (
    invariant s h0 /\
    M.loc_disjoint l (footprint s h0) /\
    M.modifies l h0 h1))
  (ensures (
    invariant s h1 /\
    repr s h0 == repr s h1))

let frame_invariant_implies_footprint_preservation
  (#a: e_alg)
  (l: M.loc)
  (s: state a)
  (h0 h1: HS.mem): Lemma
  (requires (
    invariant s h0 /\
    M.loc_disjoint l (footprint s h0) /\
    M.modifies l h0 h1))
  (ensures (
    footprint s h1 == footprint s h0))
=
  ()

val create: a:alg -> ST (state (G.hide a))
  (requires fun h0 -> True)
  (ensures fun h0 s h1 ->
    invariant s h1 /\
    M.(modifies loc_none h0 h1) /\
    fresh_loc (footprint s h1) h0 h1)

let init_repr (a: e_alg): GTot (repr_t a) =
  match G.reveal a with
  | SHA256 -> {
      hash = EverCrypt.Spec.SHA2_256.h_0;
      k = EverCrypt.Spec.SHA2_256.k;
      counter = 0
    }
  | SHA384 -> {
      hash = EverCrypt.Spec.SHA2_384.h_0;
      k = EverCrypt.Spec.SHA2_384.k;
      counter = 0
    }

val init: #a:e_alg -> s:state a -> ST unit
  (requires (invariant s))
  (ensures (fun h0 _ h1 ->
    invariant s h1 /\
    M.(modifies (footprint s h0) h0 h1) /\
    footprint s h0 == footprint s h1 /\
    repr s h1 == init_repr a))

let block_size a: GTot _ =
  match G.reveal a with
  | SHA256 -> EverCrypt.Spec.SHA2_256.size_block
  | SHA384 -> EverCrypt.Spec.SHA2_384.size_block

let well_formed (#a:e_alg)
  (s: state a)
  (h: HS.mem{invariant s h}):
  GTot _
=
  let r = repr s h in
  match G.reveal a with
  | SHA256 ->
      r.k == EverCrypt.Spec.SHA2_256.k
  | SHA384 ->
      r.k == EverCrypt.Spec.SHA2_384.k

let bounded_counter (#a:e_alg)
  (s: state a)
  (h: HS.mem{invariant s h})
  (n: nat { n <= pow2 32 }):
  GTot _
=
  let r = repr s h in
  match G.reveal a with
  | SHA256 ->
      r.counter < pow2 32 - n
  | SHA384 ->
      r.counter < pow2 32 - n

let well_formed_and_counter (#a:e_alg)
  (s: state a)
  (h: HS.mem{invariant s h})
  (n: nat { n <= pow2 32 }):
  GTot _
=
  well_formed s h /\ bounded_counter s h n

let update_spec (#a:e_alg)
  (s:state a)
  (h0: HS.mem{invariant s h0})
  (h1: HS.mem{invariant s h1})
  (data: bytes{Seq.length data = block_size a}):
  GTot _
=
  let r0 = repr s h0 in
  let r1 = repr s h1 in
  match G.reveal a with
  | SHA256 ->
      r1.hash = EverCrypt.Spec.SHA2_256.update r0.hash data
  | SHA384 ->
      r1.hash = EverCrypt.Spec.SHA2_384.update r0.hash data

// Note: this function relies implicitly on the fact that we are running with
// code/lib/kremlin and that we know that machine integers and secret integers
// are the same. In the long run, we should standardize on a secret integer type
// in F*'s ulib and have evercrypt use it.
val update: #a:e_alg -> s:state a -> data:uint8_p -> Stack unit
  (requires (fun h0 ->
    invariant s h0 /\
    well_formed_and_counter s h0 1 /\
    B.live h0 data /\
    B.length data = block_size a /\
    M.(loc_disjoint (footprint s h0) (loc_buffer data))))
  (ensures (fun h0 _ h1 ->
    invariant s h1 /\
    M.(modifies (footprint s h0) h0 h1) /\
    footprint s h0 == footprint s h1 /\
    well_formed_and_counter s h1 0 /\
    update_spec s h0 h1 (B.as_seq h0 data)))

let update_multi_spec (#a:e_alg)
  (s:state a)
  (h0: HS.mem{invariant s h0})
  (h1: HS.mem{invariant s h1})
  (data: bytes{Seq.length data % block_size a = 0}):
  GTot _
=
  let r0 = repr s h0 in
  let r1 = repr s h1 in
  match G.reveal a with
  | SHA256 ->
      r1.hash = EverCrypt.Spec.SHA2_256.update_multi r0.hash data
  | SHA384 ->
      r1.hash = EverCrypt.Spec.SHA2_384.update_multi r0.hash data

val update_multi: #a:e_alg -> s:state a -> data:uint8_p -> n:UInt32.t -> Stack unit
  (requires (fun h0 ->
    invariant s h0 /\
    well_formed_and_counter s h0 (v n) /\
    B.live h0 data /\
    B.length data = block_size a * v n /\
    M.(loc_disjoint (footprint s h0) (loc_buffer data))))
  (ensures (fun h0 _ h1 ->
    invariant s h1 /\
    M.(modifies (footprint s h0) h0 h1) /\
    footprint s h0 == footprint s h1 /\
    well_formed_and_counter s h1 0 /\
    update_multi_spec s h0 h1 (B.as_seq h0 data)))

// The maximum number of bytes for the input.
let max_input_length (a: e_alg): GTot _ =
  match G.reveal a with
  | SHA256 ->
      EverCrypt.Spec.SHA2_256.max_input_len_8
  | SHA384 ->
      EverCrypt.Spec.SHA2_384.max_input_len_8

// The size, in bytes, it takes to encode the number of bytes in the message.
let size_length (a: e_alg): GTot _ =
  match G.reveal a with
  | SHA256 ->
      EverCrypt.Spec.SHA2_256.size_len_8
  | SHA384 ->
      EverCrypt.Spec.SHA2_384.size_len_8

// For the last (possibly partial) block, in so far as I understand, we
// concatenate the last chunk of data, insert a byte 0x01, then encode the length.
let last_data_fits (a: e_alg) (length: nat): GTot _ =
  length + size_length a + 1 < 2 * block_size a

// Note: conjunction of well_formed and last_data_fits allows deriving the
// specific precondition for update_last.
let update_last_spec (#a:e_alg)
  (s:state a)
  (h0: HS.mem{invariant s h0})
  (h1: HS.mem{invariant s h1})
  (data: bytes{well_formed_and_counter s h0 2 /\ last_data_fits a (Seq.length data)}):
  GTot _
=
  let r0 = repr s h0 in
  let r1 = repr s h1 in
  let counter0 = r0.counter in
  let len0 = counter0 * block_size a in
  match G.reveal a with
  | SHA256 ->
      r1.hash = EverCrypt.Spec.SHA2_256.update_last r0.hash len0 data
  | SHA384 ->
      r1.hash = EverCrypt.Spec.SHA2_384.update_last r0.hash len0 data

val update_last: #a:e_alg -> s:state a -> data:uint8_p -> len:UInt32.t -> Stack unit
  (requires (fun h0 ->
    invariant s h0 /\
    well_formed_and_counter s h0 2 /\
    B.live h0 data /\
    B.length data = v len /\
    last_data_fits a (v len) /\
    M.(loc_disjoint (footprint s h0) (loc_buffer data))))
  (ensures (fun h0 _ h1 ->
    invariant s h1 /\
    M.(modifies (footprint s h0) h0 h1) /\
    footprint s h0 == footprint s h1 /\
    well_formed s h1 /\
    update_last_spec s h0 h1 (B.as_seq h0 data)))

let hash_size a: GTot _ =
  match G.reveal a with
  | SHA256 -> EverCrypt.Spec.SHA2_256.size_hash
  | SHA384 -> EverCrypt.Spec.SHA2_384.size_hash

let finish_spec (#a:e_alg)
  (s:state a)
  (h0: HS.mem{invariant s h0})
  (dst: bytes{Seq.length dst = hash_size a}):
  GTot _
=
  let r0 = repr s h0 in
  match G.reveal a with
  | SHA256 ->
      dst = EverCrypt.Spec.SHA2_256.finish r0.hash
  | SHA384 ->
      dst = EverCrypt.Spec.SHA2_384.finish r0.hash

val finish: #a:e_alg -> s:state a -> dst:uint8_p -> Stack unit
  (requires (fun h0 ->
    invariant s h0 /\
    well_formed s h0 /\
    B.live h0 dst /\
    B.length dst = hash_size a /\
    M.(loc_disjoint (footprint s h0) (loc_buffer dst))))
  (ensures (fun h0 _ h1 ->
    invariant s h1 /\
    M.(modifies (loc_buffer dst) h0 h1) /\
    footprint s h0 == footprint s h1 /\
    finish_spec s h0 (B.as_seq h1 dst)))

let hash_spec (a: alg) (input: bytes{Seq.length input < max_input_length (G.hide a)}): GTot _ =
  match a with
  | SHA256 ->
      EverCrypt.Spec.SHA2_256.hash input
  | SHA384 ->
      EverCrypt.Spec.SHA2_384.hash input

val hash: a:alg -> dst:uint8_p -> input:uint8_p -> len:uint32_t -> Stack unit
  (requires (fun h0 ->
    B.live h0 dst /\
    B.live h0 input /\
    B.length input = v len /\
    v len < max_input_length (G.hide a) /\
    B.length dst = hash_size (G.hide a) /\
    M.(loc_disjoint (loc_buffer input) (loc_buffer dst))))
  (ensures (fun h0 _ h1 ->
    M.(modifies (loc_buffer dst) h0 h1) /\
    B.as_seq h1 dst = hash_spec a (B.as_seq h0 input)))
