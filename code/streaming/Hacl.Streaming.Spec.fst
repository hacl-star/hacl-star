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
/// - ``buf`` contains the rest of ``seen`` that is not big enough to form a complete block.
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

noextract
let split_at_last #index (c: block index) (i: index) (b: bytes):
  Pure (bytes & bytes)
    (requires True)
    (ensures (fun (blocks, rest) ->
      S.length rest < U32.v (c.block_len i) /\
      S.length rest = S.length b % U32.v (c.block_len i) /\
      S.equal (S.append blocks rest) b /\
      S.length blocks % U32.v (c.block_len i) = 0))
=
  let n = S.length b / U32.v (c.block_len i) in
  let blocks, rest = S.split b (n * U32.v (c.block_len i)) in
  assert (S.length blocks = n * U32.v (c.block_len i));
  FStar.Math.Lemmas.multiple_modulo_lemma n (U32.v (c.block_len i));
  assert ((n * U32.v (c.block_len i)) % U32.v (c.block_len i) = 0);
  assert (S.length rest = S.length b - n * U32.v (c.block_len i));
  assert (S.length b - n * U32.v (c.block_len i) < U32.v (c.block_len i));
  blocks, rest

/// For the initialization of the streaming state.

#push-options "--z3cliopt smt.arith.nl=false"
let split_at_last_empty #index (c: block index) (i: index): Lemma
  (ensures (
    let blocks, rest = split_at_last c i S.empty in
    S.equal blocks S.empty /\ S.equal rest S.empty))
=
  FStar.Math.Lemmas.multiple_division_lemma 0 (U32.v (c.block_len i))
#pop-options

/// "Small" case: not enough data to obtain a complete block, so it suffices to
/// append the new input to the internal buffer.

let split_at_last_small #index (c: block index) (i: index) (b: bytes) (d: bytes): Lemma
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

  (* Looking at the definition of split_at_last, blocks depends only on S.length b / l. *)
  calc (==) {
    S.length b / l;
  (==) { S.lemma_len_append blocks rest }
    (S.length blocks + S.length rest) / l;
  (==) { Math.Lemmas.lemma_div_exact (S.length blocks) l }
    (l * (S.length blocks / l) + S.length rest) / l;
  (==) { }
    (S.length rest + (S.length blocks / l) * l) / l;
  (==) { Math.Lemmas.lemma_div_plus (S.length rest) (S.length blocks / l) l }
    (S.length rest) / l + (S.length blocks / l);
  (==) { Math.Lemmas.small_div (S.length rest) l }
    S.length blocks / l;
  };

  calc (==) {
    S.length (S.append b d) / l;
  (==) { S.lemma_len_append b d; S.lemma_len_append blocks rest }
    (S.length blocks + S.length rest + S.length d) / l;
  (==) { Math.Lemmas.lemma_div_exact (S.length blocks) l }
    (l * (S.length blocks / l) + (S.length rest + S.length d)) / l;
  (==) { }
    ((S.length rest + S.length d) + (S.length blocks / l) * l) / l;
  (==) { Math.Lemmas.lemma_div_plus (S.length rest + S.length d) (S.length blocks / l) l }
    (S.length rest + S.length d) / l + (S.length blocks / l);
  (==) { Math.Lemmas.small_div (S.length rest + S.length d) l }
    S.length blocks / l;
  };

  assert (S.equal blocks blocks');

  calc (S.equal) {
    rest `S.append` d;
  (S.equal) { (* definition *) }
    S.slice b ((S.length b / l) * l) (S.length b) `S.append` d;
  (S.equal) { }
    S.slice (S.append b d) ((S.length b / l) * l) (S.length b) `S.append` d;
  (S.equal) { (* above *) }
    S.slice (S.append b d) ((S.length (S.append b d) / l) * l) (S.length b) `S.append` d;
  (S.equal) { (* ? *) }
    S.slice (S.append b d) ((S.length (S.append b d) / l) * l) (S.length b)
    `S.append`
    S.slice (S.append b d) (S.length b) (S.length (S.append b d));
  (S.equal) { S.lemma_split (S.append b d) ((S.length (S.append b d) / l) * l) }
    S.slice (S.append b d) ((S.length (S.append b d) / l) * l) (S.length b + S.length d);
  (S.equal) { S.lemma_len_append b d }
    S.slice (S.append b d) ((S.length (S.append b d) / l) * l) (S.length (S.append b d));
  (S.equal) { }
    rest';
  };

  ()

/// Second case: the buffer is empty, so this is a fast-path and we can just
/// process blocks without touching the buffer.

#push-options "--z3rlimit 100"
let split_at_last_blocks #index (c: block index) (i: index) (b: bytes) (d: bytes): Lemma
  (requires (
    let blocks, rest = split_at_last c i b in
    S.equal rest S.empty))
  (ensures (
    let blocks, rest = split_at_last c i b in
    let blocks', rest' = split_at_last c i d in
    let blocks'', rest'' = split_at_last c i (S.append b d) in
    S.equal blocks'' (S.append blocks blocks') /\
    S.equal rest' rest''))
=
  let blocks, rest = split_at_last c i b in
  let blocks', rest' = split_at_last c i d in
  let blocks'', rest'' = split_at_last c i (S.append b d) in
  let b' = S.append blocks rest in
  let d' = S.append blocks' rest' in
  let l = U32.v (c.block_len i) in
  calc (S.equal) {
    rest';
  (S.equal) { }
    snd (split_at_last c i d);
  (S.equal) { }
    S.slice d ((S.length d / l) * l) (S.length d);
  (S.equal) { }
    S.slice (S.append b d) (S.length b + (S.length d / l) * l) (S.length b + S.length d);
  (S.equal) { }
    S.slice (S.append b d) (S.length b + (S.length d / l) * l) (S.length (S.append b d));
  (S.equal) { Math.Lemmas.div_exact_r (S.length b) l }
    // For some reason this doesn't go through with the default rlimit, even
    // though this is a direct rewriting based on the application of the lemma
    // above.
    S.slice (S.append b d) ((S.length b / l) * l + (S.length d / l) * l) (S.length (S.append b d));
  (S.equal) { Math.Lemmas.distributivity_add_left (S.length b / l) (S.length d / l) l }
    S.slice (S.append b d) ((S.length b / l + S.length d / l) * l) (S.length (S.append b d));
  (S.equal) { Math.Lemmas.lemma_div_plus (S.length d) (S.length b / l) l }
    S.slice (S.append b d) (((S.length b + S.length d) / l) * l) (S.length (S.append b d));
  (S.equal) { }
    snd (S.split (S.append b d) (((S.length (S.append b d)) / l) * l));
  (S.equal) { }
    rest'';
  };

  calc (S.equal) {
    S.append blocks blocks';
  (S.equal) { (* rest = S.empty *) }
    S.append (S.append blocks rest) blocks';
  (S.equal) { }
    S.append b blocks';
  (S.equal) { }
    S.append b (fst (split_at_last c i d));
  (S.equal) { (* definition of split_at_last *) }
    S.append b (fst (S.split d ((S.length d / l) * l)));
  (S.equal) { (* definition of split *) }
    S.append b (S.slice d 0 ((S.length d / l) * l));
  (S.equal) { }
    S.slice (S.append b d) 0 (S.length b + (S.length d / l) * l);
  (S.equal) { Math.Lemmas.div_exact_r (S.length b) l }
    S.slice (S.append b d) 0 ((S.length b / l) * l + (S.length d / l) * l);
  (S.equal) { Math.Lemmas.distributivity_add_left (S.length b / l) (S.length d / l) l }
    S.slice (S.append b d) 0 ((S.length b / l + S.length d / l) * l);
  (S.equal) { Math.Lemmas.lemma_div_plus (S.length d) (S.length b / l) l }
    S.slice (S.append b d) 0 (((S.length b + S.length d) / l) * l);
  (S.equal) { }
    fst (S.split (S.append b d) (((S.length (S.append b d)) / l) * l));
  (S.equal) { }
    blocks'';
  }
#pop-options

/// Third sub-case: the amount of data we receive is exactly enough to form a
/// full block. This is an artificial case, but we need it to decompose the
/// general case into a combination of the three sub-cases!

#push-options "--z3cliopt smt.arith.nl=false"
let split_at_last_block #index (c: block index) (i: index) (b: bytes) (d: bytes): Lemma
  (requires (
    let _, rest = split_at_last c i b in
    S.length rest + S.length d = U32.v (c.block_len i)))
  (ensures (
    let blocks, rest = split_at_last c i b in
    let blocks', rest' = split_at_last c i (S.append b d) in
    S.equal (S.append b d) blocks' /\ S.equal S.empty rest'))
=
  let blocks, rest = split_at_last c i b in
    let blocks', rest' = split_at_last c i (S.append b d) in

  calc (==) {
    (S.length b + S.length d) % U32.v (c.block_len i);
  (==) { S.lemma_len_append blocks rest }
    (S.length blocks + S.length rest + S.length d) % U32.v (c.block_len i);
  (==) { Math.Lemmas.modulo_distributivity (S.length blocks) (S.length rest + S.length d) (U32.v (c.block_len i)) }
    ((S.length blocks) % U32.v (c.block_len i) + (S.length rest + S.length d) % U32.v (c.block_len i))
      % U32.v (c.block_len i);
  (==) { Math.Lemmas.multiple_modulo_lemma (U32.v (c.block_len i)) 1 }
    ((S.length blocks) % U32.v (c.block_len i)) % U32.v (c.block_len i);
  (==) { }
    0 % U32.v (c.block_len i);
  (==) { Math.Lemmas.small_modulo_lemma_1 0 (U32.v (c.block_len i)) }
    0;
  }
#pop-options
