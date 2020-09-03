module Hacl.Streaming.Spec

/// This module contains all of the logical reasoning, calc statement included,
/// for the streaming functor.
///
/// The functor uses a ghost variable (named ``seen``) to reason about the
/// **past**, i.e. whatever bytes have been fed into the streaming functor. In
/// other words, we capture the history of calls that have been performed on the
/// functor state, i.e. the sequence of bytes that have been accumulated via
/// previous calls to ``Functor.update``, into the ghost ``seen``
/// variable.
///
/// To make things useful, we need to relate the present to the past, i.e. we
/// need to relate the values of ``block_state`` and ``buf`` (in a given heap)
/// to the ghost value ``seen``.
///
/// The central invariant of the streaming functor is that, if you split
/// ``seen`` at the last block boundary, then:
///
/// - ``block_state`` contains the accumulated result of calling ``update`` on
///   all of the blocks, and
/// - ``buf`` contains the rest of ``seen`` that is smaller or equal to a complete
///   block and is processed lazily to make sure there is some data left when we
///   call ``last_update`` 
///
/// The function that performs this splitting is called ``split_at_last``, and
/// we need to prove various properties about it, since the streaming functor
/// distinguishes three sub-situations to make the proof tractable and we need
/// helper lemmas for all three situations.

#set-options "--max_fuel 0 --max_ifuel 0 \
  --using_facts_from '*,-LowStar.Monotonic.Buffer.unused_in_not_unused_in_disjoint_2' --z3rlimit 50"

module ST = FStar.HyperStack.ST
module HS = FStar.HyperStack
module B = LowStar.Buffer
module G = FStar.Ghost
module S = FStar.Seq
module U32 = FStar.UInt32
module U64 = FStar.UInt64

open Hacl.Streaming.Interface
open FStar.HyperStack.ST
open LowStar.BufferOps
open FStar.Mul

inline_for_extraction noextract
let uint8 = Lib.IntTypes.uint8

inline_for_extraction noextract
let uint32 = Lib.IntTypes.uint32

noextract
let bytes = S.seq uint8

/// Returns the number of blocks to process
#push-options "--z3cliopt smt.arith.nl=false"
noextract
let split_at_last_num_blocks #index (c: block index) (i: index) (b: nat):
  Pure nat
    (requires True)
    (ensures (fun n ->
      let l = U32.v (c.block_len i) in
      let blocks = n * l in
      let rest = b - blocks in
      rest <= l /\
      (rest % l = b % l) /\
      (rest =  b % l \/  rest = l) /\
      (rest = 0 <==>  b == 0) /\
      (rest = l <==> (blocks = (b / l - 1) * l)) /\
      ((rest > 0 /\ rest < l) <==>  b % l <> 0) /\
      (rest = (b % l) <==> (blocks = (b / l) * l)) /\
       blocks % l = 0 /\
      (blocks / l) * l = blocks))
=
  fst (Lib.UpdateMulti.split_at_last_lazy_nb_rem (U32.v (c.block_len i)) b)
#pop-options

#push-options "--z3cliopt smt.arith.nl=false"
noextract
let split_at_last #index (c: block index) (i: index) (b: bytes):
  Pure (bytes & bytes)
    (requires True)
    (ensures (fun (blocks, rest) ->
      let l = U32.v (c.block_len i) in
      S.length rest <= l /\
      (S.length rest % l = S.length b % l) /\
      (S.length rest = S.length b % l \/ S.length rest = l) /\
      (S.length rest = 0 <==> S.length b == 0) /\
      (S.length rest = l <==>
        (S.length blocks = (S.length b / l - 1) * l)) /\
      ((S.length rest > 0 /\ S.length rest < l) <==> S.length b % l <> 0) /\
      (S.length rest = (S.length b % l) <==>
        (S.length blocks = (S.length b / l) * l)) /\
      S.equal (S.append blocks rest) b /\
      S.length blocks % l = 0 /\
      (S.length blocks / l) * l = S.length blocks
  ))
=
  let l = U32.v (c.block_len i) in
  Lib.UpdateMulti.split_at_last_lazy l b
#pop-options

/// The following lemmas characterize [split_at_last] with conditions which are easy to
/// reason about, and is very useful for the various lemmas in this file which
/// prove properties about how to update the internal buffer so that its content
/// is actually the correct remainder of the data seen so far.

/// This first auxiliary lemma only manipulates the lengths of the sequences.
#push-options "--z3cliopt smt.arith.nl=false"
noextract
let split_at_last_num_blocks_spec #index (c: block index) (i: index)
                                  (b n rest: nat):
  Lemma
  (requires (
    let l = U32.v (c.block_len i) in
    (rest <= l /\ (rest = 0 ==> b = 0) /\ b = n * l + rest)))
  (ensures (n = split_at_last_num_blocks c i b)) =
  let l = U32.v (c.block_len i) in
  Lib.UpdateMulti.Lemmas.split_at_last_lazy_nb_rem_spec l b n rest
#pop-options

/// This second lemma is the one we will use
#push-options "--z3cliopt smt.arith.nl=false"
noextract
let split_at_last_spec #index (c: block index) (i: index)
                              (b blocks rest: bytes):
  Lemma
  (requires (
    let l = U32.v (c.block_len i) in
    (S.length blocks % l = 0 /\
     S.length rest <= l /\
     (S.length rest = 0 ==> S.length b = 0) /\
     b `Seq.equal` Seq.append blocks rest)))
  (ensures (
     (blocks, rest) == split_at_last c i b)) =
  let l = U32.v (c.block_len i) in
  Lib.UpdateMulti.Lemmas.split_at_last_lazy_spec l b blocks rest
#pop-options

/// For the initialization of the streaming state.

#push-options "--z3cliopt smt.arith.nl=false"
let split_at_last_empty #index (c: block index) (i: index): Lemma
  (ensures (
    let blocks, rest = split_at_last c i S.empty in
    S.equal blocks S.empty /\ S.equal rest S.empty))
=
  FStar.Math.Lemmas.multiple_division_lemma 0 (U32.v (c.block_len i))
#pop-options

/// "Small" case: not enough data to obtain strictly more than a complete block,
/// so it suffices to append the new input to the internal buffer. Note that we
/// don't process the resulting buffer because we have to make sure there is always
/// some data remaining in it (after the first call to update) so that [update_last]
/// is called on non-empty data at the very end.
///
/// There are many subcases that we prove in intermediate lemmas, until we can
/// get the final [split_at_last_small] theorem.
/// [b]: internal buffer
/// [d]: data to append

/// "Small" case: subcase 1: not enough data to obtain a complete block append the
/// new input to the internal buffer.

let split_at_last_small_strict #index (c: block index) (i: index) (b: bytes) (d: bytes): Lemma
  (requires (
    let _, rest = split_at_last c i b in
    S.length rest + S.length d < U32.v (c.block_len i)))
  (ensures (
    let blocks, rest = split_at_last c i b in
    let blocks', rest' = split_at_last c i (S.append b d) in
    S.equal blocks blocks' /\ S.equal (S.append rest d) rest'))
=
  let blocks, rest = split_at_last c i b in
  let blocks', rest' = split_at_last c i (S.append b d) in
  let l = U32.v (c.block_len i) in
  split_at_last_spec c i (S.append b d) blocks (S.append rest d)

/// "Small" case: subcase 2: exactly enough data to obtain a complete block, and the
/// internal buffer is empty.

#push-options "--z3cliopt smt.arith.nl=false"
let split_at_last_small_exact_empty_internal #index (c: block index) (i: index) (b: bytes) (d: bytes):
  Lemma
  (requires (
    let _, rest = split_at_last c i b in
    S.length rest + S.length d = U32.v (c.block_len i) /\
    S.length rest = 0))
  (ensures (
    let blocks, rest = split_at_last c i b in
    let blocks', rest' = split_at_last c i (S.append b d) in
    S.equal blocks blocks' /\ S.equal (S.append rest d) rest'))
=
  let blocks, rest = split_at_last c i b in
  (* The proof is trivial because [b] is empty *)
  assert(b `Seq.equal` Seq.empty);
  assert(S.append b d `Seq.equal` d);
  assert(S.append rest d `Seq.equal` d)
#pop-options

/// "Small" case 3: exactly enough data to obtain a complete block, and the data to
/// add is empty.

#push-options "--z3cliopt smt.arith.nl=false"
let split_at_last_small_exact_empty_data #index (c: block index) (i: index) (b: bytes)
                                                (d: bytes):
  Lemma
  (requires (
    let _, rest = split_at_last c i b in
    S.length rest + S.length d = U32.v (c.block_len i) /\
    S.length d = 0))
  (ensures (
    let blocks, rest = split_at_last c i b in
    let blocks', rest' = split_at_last c i (S.append b d) in
    S.equal blocks blocks' /\ S.equal (S.append rest d) rest'))
=
  let blocks, rest = split_at_last c i b in
  let blocks', rest' = split_at_last c i (S.append b d) in
  assert(S.append rest d `S.equal` rest);
  assert(S.append b d `S.equal` b)
#pop-options

/// "Small" case 4: exactly enough data to obtain a complete block, the internal
/// buffer is not empty and the data to add is not empty.

#push-options "--z3cliopt smt.arith.nl=false"
let split_at_last_small_exact #index (c: block index) (i: index) (b: bytes) (d: bytes): Lemma
  (requires (
    let _, rest = split_at_last c i b in
    S.length rest + S.length d = U32.v (c.block_len i) /\
    S.length rest > 0 /\ S.length d > 0))
  (ensures (
    let blocks, rest = split_at_last c i b in
    let blocks', rest' = split_at_last c i (S.append b d) in
    S.equal blocks blocks' /\ S.equal (S.append rest d) rest'))
=
  let blocks, rest = split_at_last c i b in
  let blocks', rest' = split_at_last c i (S.append b d) in
  let l = U32.v (c.block_len i) in
  let n = S.length blocks / l in

  assert(S.length blocks % l = 0); (* comes from the spec of [split_at_last] *)
  assert(S.length (S.append rest d) = l);  
  assert((S.append b d) `Seq.equal` Seq.append blocks (Seq.append rest d));
  split_at_last_spec c i (S.append b d) blocks (S.append rest d)
#pop-options

/// "Small" case: final theorem: not enough data to obtain strictly more than a
/// complete block, so it suffices to append the new input to the internal buffer.

let split_at_last_small #index (c: block index) (i: index) (b: bytes) (d: bytes): Lemma
  (requires (
    let _, rest = split_at_last c i b in
    S.length rest + S.length d <= U32.v (c.block_len i)))
  (ensures (
    let blocks, rest = split_at_last c i b in
    let blocks', rest' = split_at_last c i (S.append b d) in
    S.equal blocks blocks' /\ S.equal (S.append rest d) rest'))
=
  let blocks, rest = split_at_last c i b in
  let blocks', rest' = split_at_last c i (S.append b d) in
  let l = U32.v (c.block_len i) in
  
  if S.length rest + S.length d < l then
    split_at_last_small_strict c i b d
  else if S.length rest = 0 then
    split_at_last_small_exact_empty_internal c i b d
  else if S.length d = 0 then
    split_at_last_small_exact_empty_data c i b d
  else split_at_last_small_exact c i b d

/// For the initialization of the streaming state.

/// Second case: the data seen so far is empty or a multiple of the block size
/// meaning that the internal buffer is either empty or full, and the data to
/// append is not empty. This is a fast path: we can process the internal
/// buffer if it is non-empty, then process blocks without touching at the buffer
/// and finally copy the remaining data to the buffer. Of course, there must be
/// data remaining in the buffer in the end, which is why the data to append
/// musn't be empty.

#push-options "--z3rlimit 100 --z3cliopt smt.arith.nl=false"
let split_at_last_blocks #index (c: block index) (i: index) (b: bytes) (d: bytes): Lemma
  (requires (
    let blocks, rest = split_at_last c i b in
    (S.length rest = 0 \/ S.length rest = U32.v (c.block_len i)) /\
    S.length d > 0))
  (ensures (
    let blocks, rest = split_at_last c i b in
    let blocks', rest' = split_at_last c i d in
    let blocks'', rest'' = split_at_last c i (S.append b d) in
    S.equal blocks'' (S.append b blocks') /\
    S.equal rest' rest''))
=
  let blocks, rest = split_at_last c i b in
  let blocks', rest' = split_at_last c i d in
  let blocks'', rest'' = split_at_last c i (S.append b d) in
  let b' = S.append blocks rest in
  let d' = S.append blocks' rest' in
  let l = U32.v (c.block_len i) in

  (* We prove the non-trivial requirements of [split_at_last_spec] *)
  assert(S.length b % l = 0);
  Math.Lemmas.modulo_distributivity (S.length b) (S.length blocks') l;
  calc (==) {
    S.length (S.append b blocks') % l;
  (==) {}
    (S.length b + S.length blocks') % l;
  (==) { Math.Lemmas.modulo_distributivity (S.length b) (S.length blocks') l }
    ((S.length b % l) + (S.length blocks' % l)) % l;
  (==) {}
    0 % l;
  (==) { Math.Lemmas.modulo_lemma 0 l }
    0;
  };

  (* End of proof *)
  split_at_last_spec c i (S.append b d) (S.append b blocks') rest'
#pop-options
