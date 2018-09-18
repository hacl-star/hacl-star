module Hacl.Hash.Lemmas

module Endianness = FStar.Kremlin.Endianness

module S = FStar.Seq
module U8 = FStar.UInt8
module U32 = FStar.UInt32
module U64 = FStar.UInt64

(** Two sequence lemmas required for pad, among others. *)

let lemma_slice (#a: Type) (s: S.seq a) (i: nat): Lemma
  (requires (i <= S.length s))
  (ensures (S.equal (S.append (S.slice s 0 i) (S.slice s i (S.length s))) s))
  [ SMTPat (S.append (S.slice s 0 i) (S.slice s i (S.length s))) ]
=
  ()

let lemma_slice_ijk (#a: Type) (s: S.seq a) (i j k: nat): Lemma
  (requires (i <= j /\ j <= k /\ k <= S.length s))
  (ensures (S.equal (S.append (S.slice s i j) (S.slice s j k)) (S.slice s i k)))
  [ SMTPat (S.append (S.slice s i j) (S.slice s j k)) ]
=
  ()

(** Two sequence lemmas required for the pre-computation of Spec.ws *)

// Note: a similar lemma exists in FStar.Seq.Base but yields a forall in the
// ensures clauses which doesn't work, really.
let init_index (#a: Type) (j: nat) (f: (i:nat { i < j }) -> a) (i: nat):
  Lemma
    (requires (
      i < j))
    (ensures (S.index (S.init j f) i == f i))
  [ SMTPat (S.index (S.init j f) i) ]
=
  ()

let init_next (#a: Type) (s: S.seq a) (f: (i:nat { i < S.length s }) -> a) (i: nat):
  Lemma
    (requires (
      i < S.length s /\
      S.equal (S.slice s 0 i) (S.init i f) /\
      S.index s i == f i))
    (ensures (S.equal (S.slice s 0 (i + 1)) (S.init (i + 1) f)))
=
  lemma_slice_ijk s 0 i (i + 1)

(** One lemma required for the commutations of seq_uint*_of_be and append. *)

let tail_cons (#a: Type) (hd: a) (tl: S.seq a): Lemma
  (ensures (S.equal (S.tail (S.cons hd tl)) tl))
  [ SMTPat (S.tail (S.cons hd tl)) ]
=
  ()

(** One lemma needed for our for loop for padding *)

let create_next (#a: Type) (s: S.seq a) (v: a) (i: nat):
  Lemma
    (requires (
      i < S.length s /\
      S.equal (S.slice s 0 i) (S.create i v) /\
      S.index s i == v))
    (ensures (S.equal (S.slice s 0 (i + 1)) (S.create (i + 1) v)))
=
  lemma_slice_ijk s 0 i (i + 1)
