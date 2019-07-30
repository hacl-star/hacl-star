module Hacl.Impl.Store56

module ST = FStar.HyperStack.ST
open FStar.HyperStack.All
open FStar.Mul

open Lib.IntTypes
open Lib.ByteSequence
open Lib.Buffer
open Lib.ByteBuffer

module F56 = Hacl.Impl.Ed25519.Field56
module S56 = Hacl.Spec.Ed25519.Field56.Definition

#reset-options "--z3rlimit 30 --max_fuel 0 --max_ifuel 0"

val hstore56_le:
    out:lbuffer uint8 32ul
  -> off:size_t{v off <= 21}
  -> x:uint64{v x < pow2 56} ->
  Stack unit
    (requires fun h -> live h out)
    (ensures  fun h0 _ h1 -> modifies (loc (gsub out off 8ul)) h0 h1 /\
      nat_from_bytes_le (Seq.slice (as_seq h1 out) (v off) (v off + 7)) == v x
    )

let hstore56_le out off x =
  let b8 = sub out off 8ul in
  lemma_uint_to_bytes_le_preserves_value x;
  uint_to_bytes_le b8 x;
  let h1 = get() in
  calc (==) {
    v x <: nat;
    (==) { Math.Lemmas.small_mod (v x) (pow2 56) }
    (v x) % pow2 56 <: nat;
    (==) { assert (Seq.equal (as_seq h1 b8) (Seq.slice (as_seq h1 out) (v off) (v off + 8))) }
    (nat_from_bytes_le (as_seq h1 b8)) % pow2 56;
    (==) { nat_from_intseq_le_slice_lemma (as_seq h1 b8) 7 }
    (nat_from_bytes_le (Seq.slice (as_seq h1 b8) 0 7) +
    pow2 56 * nat_from_bytes_le (Seq.slice (as_seq h1 b8) 7 8)) % pow2 56;
    (==) { Math.Lemmas.lemma_mod_plus_distr_r
      (nat_from_bytes_le (Seq.slice (as_seq h1 b8) 0 7))
      (pow2 56 * nat_from_bytes_le (Seq.slice (as_seq h1 b8) 7 8))
      (pow2 56);
      Math.Lemmas.swap_mul
        (nat_from_bytes_le (Seq.slice (as_seq h1 b8) 7 8))
        (pow2 56);
      Math.Lemmas.cancel_mul_mod
        (nat_from_bytes_le (Seq.slice (as_seq h1 b8) 7 8))
        (pow2 56) }
     nat_from_bytes_le (Seq.slice (as_seq h1 b8) 0 7) % pow2 56;
     (==) {
       Math.Lemmas.small_mod (nat_from_bytes_le (Seq.slice (as_seq h1 b8) 0 7)) (pow2 56);
     assert (Seq.equal (Seq.slice (as_seq h1 b8) 0 7) (Seq.slice (as_seq h1 out) (v off) (v off + 7))) }
     nat_from_bytes_le (Seq.slice (as_seq h1 out) (v off) (v off + 7));
  }

let lemma_nat_from_bytes_le_append (k1 k2:bytes) : Lemma
  (requires Seq.length k1 + Seq.length k2 <= max_size_t)
  (ensures nat_from_bytes_le (Seq.append k1 k2) ==
  nat_from_bytes_le k1 + pow2 (Seq.length k1 * 8) * nat_from_bytes_le k2) =
  let k = Seq.append k1 k2 in
  let n = Seq.length k1 + Seq.length k2 in
  nat_from_intseq_le_slice_lemma #U8 #SEC #n k (Seq.length k1);
  assert (k1 `Seq.equal` Seq.slice k 0 (Seq.length k1));
  assert (k2 `Seq.equal` Seq.slice k (Seq.length k1) n)


let lemma_store_56_bytes (k:lbytes 32) (b0 b1 b2 b3 b4:uint64) : Lemma
  (requires
    v b0 == nat_from_bytes_le (Seq.slice k 0 7) /\
    v b1 == nat_from_bytes_le (Seq.slice k 7 14) /\
    v b2 == nat_from_bytes_le (Seq.slice k 14 21) /\
    v b3 == nat_from_bytes_le (Seq.slice k 21 28) /\
    v b4 == nat_from_bytes_le (Seq.slice k 28 32))
  (ensures S56.as_nat5 (b0, b1, b2, b3, b4) == nat_from_bytes_le k)
  =
  lemma_nat_from_bytes_le_append (Seq.slice k 0 7) (Seq.slice k 7 14);
  lemma_nat_from_bytes_le_append (Seq.slice k 0 14) (Seq.slice k 14 21);
  lemma_nat_from_bytes_le_append (Seq.slice k 0 21) (Seq.slice k 21 28);
  lemma_nat_from_bytes_le_append (Seq.slice k 0 28) (Seq.slice k 28 32);
  assert (Seq.append (Seq.slice k 0 7) (Seq.slice k 7 14) `Seq.equal` Seq.slice k 0 14);
  assert (Seq.append (Seq.slice k 0 14) (Seq.slice k 14 21) `Seq.equal` Seq.slice k 0 21);
  assert (Seq.append (Seq.slice k 0 21) (Seq.slice k 21 28) `Seq.equal` Seq.slice k 0 28);
  assert (Seq.append (Seq.slice k 0 28) (Seq.slice k 28 32) `Seq.equal` k);
  assert_norm (pow2 56 == 0x100000000000000);
  assert_norm (pow2 112 == 0x10000000000000000000000000000);
  assert_norm (pow2 168 == 0x1000000000000000000000000000000000000000000);
  assert_norm (pow2 224 == 0x100000000000000000000000000000000000000000000000000000000)

val store_56:
    out:lbuffer uint8 32ul
  -> b:lbuffer uint64 5ul ->
  Stack unit
    (requires fun h -> live h out /\ live h b /\
      (let s = as_seq h b in
        v (Seq.index s 0) < pow2 56 /\
        v (Seq.index s 1) < pow2 56 /\
        v (Seq.index s 2) < pow2 56 /\
        v (Seq.index s 3) < pow2 56 /\
        v (Seq.index s 4) < pow2 32)
    )
    (ensures  fun h0 _ h1 -> modifies (loc out) h0 h1 /\
      (assert_norm (pow2 56 < pow2 64); assert_norm (pow2 32 < pow2 64);
        assert_norm (S56.as_nat5 (u64 (pow2 56 - 1), u64 (pow2 56 - 1), u64 (pow2 56 - 1), u64 (pow2 56 - 1), u64 (pow2 32 - 1)) < pow2 256);
      nat_to_bytes_le 32 (F56.as_nat h0 b) == as_seq h1 out)
    )


let store_56 out b =
  let b0 = b.(0ul) in
  let b1 = b.(1ul) in
  let b2 = b.(2ul) in
  let b3 = b.(3ul) in
  let b4 = b.(4ul) in
  let b4' = to_u32 b4 in

  hstore56_le out 0ul b0;
  hstore56_le out 7ul b1;
  hstore56_le out 14ul b2;
  hstore56_le out 21ul b3;
  uint_to_bytes_le (sub out 28ul 4ul) b4';
  let h1 = get() in
  assert (Seq.equal (Seq.slice (as_seq h1 out) 0 7) (as_seq h1 (gsub out 0ul 7ul)));
  assert (Seq.equal (Seq.slice (as_seq h1 out) 7 14) (as_seq h1 (gsub out 7ul 7ul)));
  assert (Seq.equal (Seq.slice (as_seq h1 out) 14 21) (as_seq h1 (gsub out 14ul 7ul)));
  assert (Seq.equal (Seq.slice (as_seq h1 out) 21 28) (as_seq h1 (gsub out 21ul 7ul)));
  assert (Seq.equal (Seq.slice (as_seq h1 out) 28 32) (as_seq h1 (gsub out 28ul 4ul)));
  lemma_uint_to_bytes_le_preserves_value b4';
  lemma_store_56_bytes (as_seq h1 out) b0 b1 b2 b3 b4;
  lemma_nat_from_to_bytes_le_preserves_value (as_seq h1 out) 32
