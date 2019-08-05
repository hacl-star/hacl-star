module Hacl.Impl.Load56

module ST = FStar.HyperStack.ST
open FStar.HyperStack.All
open FStar.Mul

open Lib.IntTypes
open Lib.ByteSequence
open Lib.Buffer
open Lib.ByteBuffer

module F56 = Hacl.Impl.Ed25519.Field56
module S56 = Hacl.Spec.Ed25519.Field56.Definition

#reset-options "--z3rlimit 50 --max_fuel 0 --max_ifuel 0"

val hload56_le:
    b:lbuffer uint8 64ul
  -> off:size_t{v off <= 56} ->
  Stack uint64
    (requires fun h -> live h b)
    (ensures fun h0 z h1 -> h0 == h1 /\
      v z < 0x100000000000000 /\
      v z == nat_from_bytes_le (Seq.slice (as_seq h0 b) (v off) (v off + 7))
    )

let hload56_le b off =
  let h0 = get() in
  let b8 = sub b off 8ul in
  let z  = uint_from_bytes_le b8 in
  let z' = z &. u64 0xffffffffffffff in
  assert_norm (0xffffffffffffff == pow2 56 - 1);
  assert_norm (0x100000000000000 == pow2 56 );
  calc (==) {
    v z' <: nat;
    (==) { }
    v (z &. u64 0xffffffffffffff);
    (==) { logand_spec z (u64 0xffffffffffffff) }
    v z `logand_v` 0xffffffffffffff;
    (==) { assert_norm(pow2 56 - 1 == 0xffffffffffffff); UInt.logand_mask (UInt.to_uint_t 64 (v z)) 56 }
    (v z % pow2 56);
    (==) { lemma_reveal_uint_to_bytes_le #U64 #SEC (as_seq h0 b8) }
    nat_from_bytes_le (as_seq h0 b8) % pow2 56;
    (==) { nat_from_intseq_le_slice_lemma (as_seq h0 b8) 7 }
    (nat_from_bytes_le (Seq.slice (as_seq h0 b8) 0 7) +
      pow2 (7 * 8) * nat_from_bytes_le (Seq.slice (as_seq h0 b8) 7 8)) % pow2 56;
    (==) { FStar.Math.Lemmas.lemma_mod_plus_distr_r
      (nat_from_bytes_le (Seq.slice (as_seq h0 b8) 0 7))
      (pow2 (7 * 8) * nat_from_bytes_le (Seq.slice (as_seq h0 b8) 7 8))
      (pow2 56);
      FStar.Math.Lemmas.swap_mul (pow2 (7 * 8)) (nat_from_bytes_le (Seq.slice (as_seq h0 b8) 7 8));
        FStar.Math.Lemmas.cancel_mul_mod (nat_from_bytes_le (Seq.slice (as_seq h0 b8) 7 8)) (pow2 56) }
    nat_from_bytes_le (Seq.slice (as_seq h0 b8) 0 7) <: nat;
  };
  assert (Seq.equal
        (Seq.slice (as_seq h0 b) (v off) (v off + 7))
        (Seq.slice (as_seq h0 b8) 0 7));
  z'


let lemma_nat_from_bytes_le_append (k1 k2:bytes) : Lemma
  (requires Seq.length k1 + Seq.length k2 <= max_size_t)
  (ensures nat_from_bytes_le (Seq.append k1 k2) ==
  nat_from_bytes_le k1 + pow2 (Seq.length k1 * 8) * nat_from_bytes_le k2) =
  let k = Seq.append k1 k2 in
  let n = Seq.length k1 + Seq.length k2 in
  nat_from_intseq_le_slice_lemma #U8 #SEC #n k (Seq.length k1);
  assert (k1 `Seq.equal` Seq.slice k 0 (Seq.length k1));
  assert (k2 `Seq.equal` Seq.slice k (Seq.length k1) n)

#push-options "--z3rlimit 100"

let lemma_load_64_bytes (k:lbytes 64) (b0 b1 b2 b3 b4 b5 b6 b7 b8 b9:uint64) : Lemma
  (requires
    v b0 == nat_from_bytes_le (Seq.slice k 0 7) /\
    v b1 == nat_from_bytes_le (Seq.slice k 7 14) /\
    v b2 == nat_from_bytes_le (Seq.slice k 14 21) /\
    v b3 == nat_from_bytes_le (Seq.slice k 21 28) /\
    v b4 == nat_from_bytes_le (Seq.slice k 28 35) /\
    v b5 == nat_from_bytes_le (Seq.slice k 35 42) /\
    v b6 == nat_from_bytes_le (Seq.slice k 42 49) /\
    v b7 == nat_from_bytes_le (Seq.slice k 49 56) /\
    v b8 == nat_from_bytes_le (Seq.slice k 56 63) /\
    v b9 == v (Seq.index k 63)
    )
  (ensures S56.as_nat10 b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 == nat_from_bytes_le k)
  =
  lemma_nat_from_bytes_le_append (Seq.slice k 0 7) (Seq.slice k 7 14);
  lemma_nat_from_bytes_le_append (Seq.slice k 0 14) (Seq.slice k 14 21);
  lemma_nat_from_bytes_le_append (Seq.slice k 0 21) (Seq.slice k 21 28);
  lemma_nat_from_bytes_le_append (Seq.slice k 0 28) (Seq.slice k 28 35);
  lemma_nat_from_bytes_le_append (Seq.slice k 0 35) (Seq.slice k 35 42);
  lemma_nat_from_bytes_le_append (Seq.slice k 0 42) (Seq.slice k 42 49);
  lemma_nat_from_bytes_le_append (Seq.slice k 0 49) (Seq.slice k 49 56);
  lemma_nat_from_bytes_le_append (Seq.slice k 0 56) (Seq.slice k 56 63);
  lemma_nat_from_bytes_le_append (Seq.slice k 0 63) (Seq.create 1 (Seq.index k 63));
  assert (Seq.append (Seq.slice k 0 7) (Seq.slice k 7 14) `Seq.equal` Seq.slice k 0 14);
  assert (Seq.append (Seq.slice k 0 14) (Seq.slice k 14 21) `Seq.equal` Seq.slice k 0 21);
  assert (Seq.append (Seq.slice k 0 21) (Seq.slice k 21 28) `Seq.equal` Seq.slice k 0 28);
  assert (Seq.append (Seq.slice k 0 28) (Seq.slice k 28 35) `Seq.equal` Seq.slice k 0 35);
  assert (Seq.append (Seq.slice k 0 35) (Seq.slice k 35 42) `Seq.equal` Seq.slice k 0 42);
  assert (Seq.append (Seq.slice k 0 42) (Seq.slice k 42 49) `Seq.equal` Seq.slice k 0 49);
  assert (Seq.append (Seq.slice k 0 49) (Seq.slice k 49 56) `Seq.equal` Seq.slice k 0 56);
  assert (Seq.append (Seq.slice k 0 56) (Seq.slice k 56 63) `Seq.equal` Seq.slice k 0 63);
  assert (Seq.append (Seq.slice k 0 63) (Seq.create 1 (Seq.index k 63)) `Seq.equal` k);
  nat_from_intseq_le_lemma0 (Seq.create 1 (Seq.index k 63));
  assert_norm (pow2 56 == 0x100000000000000);
  assert_norm (pow2 112 == 0x10000000000000000000000000000);
  assert_norm (pow2 168 == 0x1000000000000000000000000000000000000000000);
  assert_norm (pow2 224 == 0x100000000000000000000000000000000000000000000000000000000);
  assert_norm (pow2 280 == 0x10000000000000000000000000000000000000000000000000000000000000000000000);
  assert_norm (pow2 336 == 0x1000000000000000000000000000000000000000000000000000000000000000000000000000000000000);
  assert_norm (pow2 392 == 0x100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000);
  assert_norm (pow2 448 == 0x10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000);
  assert_norm (pow2 504 == 0x1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)

#pop-options

val load_64_bytes:
  out:lbuffer uint64 10ul
  -> b:lbuffer uint8 64ul ->
  Stack unit
    (requires fun h -> live h out /\ live h b)
    (ensures fun h0 _ h1 -> modifies (loc out) h0 h1 /\
      F56.as_nat10 h1 out == nat_from_bytes_le (as_seq h0 b) /\
      (let t = as_seq h1 out in
      let op_String_Access = Seq.index in
      v t.[0] < 0x100000000000000
      /\ v t.[1] < 0x100000000000000
      /\ v t.[2] < 0x100000000000000
      /\ v t.[3] < 0x100000000000000
      /\ v t.[4] < 0x100000000000000
      /\ v t.[5] < 0x100000000000000
      /\ v t.[6] < 0x100000000000000
      /\ v t.[7] < 0x100000000000000
      /\ v t.[8] < 0x100000000000000
      /\ v t.[9] < 0x100000000000000)
    )

let load_64_bytes out b =
  let h0 = get() in
  let b0 = hload56_le b 0ul in
  let b1 = hload56_le b 7ul in
  let b2 = hload56_le b 14ul in
  let b3 = hload56_le b 21ul in
  let b4 = hload56_le b 28ul in
  let b5 = hload56_le b 35ul in
  let b6 = hload56_le b 42ul in
  let b7 = hload56_le b 49ul in
  let b8 = hload56_le b 56ul in
  let b63 = b.(63ul) in
  let b9 = to_u64 b63 in
  lemma_load_64_bytes (as_seq h0 b) b0 b1 b2 b3 b4 b5 b6 b7 b8 b9;
  Hacl.Bignum25519.make_u64_10 out b0 b1 b2 b3 b4 b5 b6 b7 b8 b9

val hload56_le':
    b:lbuffer uint8 32ul
  -> off:size_t{v off <= 21} ->
  Stack uint64
    (requires fun h -> live h b)
    (ensures fun h0 z h1 -> h0 == h1 /\
      v z < 0x100000000000000 /\
      v z == nat_from_bytes_le (Seq.slice (as_seq h0 b) (v off) (v off + 7))
    )

let hload56_le' b off =
  let h0 = get() in
  let b8 = sub b off 8ul in
  let z  = uint_from_bytes_le b8 in
  let z' = z &. u64 0xffffffffffffff in
  assert_norm (0xffffffffffffff == pow2 56 - 1);
  assert_norm (0x100000000000000 == pow2 56 );
  calc (==) {
    v z' <: nat;
    (==) { }
    v (z &. u64 0xffffffffffffff);
    (==) { logand_spec z (u64 0xffffffffffffff) }
    v z `logand_v` 0xffffffffffffff;
    (==) { assert_norm(pow2 56 - 1 == 0xffffffffffffff); UInt.logand_mask (UInt.to_uint_t 64 (v z)) 56 }
    (v z % pow2 56);
    (==) { lemma_reveal_uint_to_bytes_le #U64 #SEC (as_seq h0 b8) }
    nat_from_bytes_le (as_seq h0 b8) % pow2 56;
    (==) { nat_from_intseq_le_slice_lemma (as_seq h0 b8) 7 }
    (nat_from_bytes_le (Seq.slice (as_seq h0 b8) 0 7) +
      pow2 (7 * 8) * nat_from_bytes_le (Seq.slice (as_seq h0 b8) 7 8)) % pow2 56;
    (==) { FStar.Math.Lemmas.lemma_mod_plus_distr_r
      (nat_from_bytes_le (Seq.slice (as_seq h0 b8) 0 7))
      (pow2 (7 * 8) * nat_from_bytes_le (Seq.slice (as_seq h0 b8) 7 8))
      (pow2 56);
      FStar.Math.Lemmas.swap_mul (pow2 (7 * 8)) (nat_from_bytes_le (Seq.slice (as_seq h0 b8) 7 8));
        FStar.Math.Lemmas.cancel_mul_mod (nat_from_bytes_le (Seq.slice (as_seq h0 b8) 7 8)) (pow2 56) }
    nat_from_bytes_le (Seq.slice (as_seq h0 b8) 0 7) <: nat;
  };
  assert (Seq.equal
        (Seq.slice (as_seq h0 b) (v off) (v off + 7))
        (Seq.slice (as_seq h0 b8) 0 7));
  z'

let lemma_load_32_bytes (k:lbytes 32) (b0 b1 b2 b3 b4:uint64) : Lemma
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

val load_32_bytes:
  out:lbuffer uint64 5ul
  -> b:lbuffer uint8 32ul ->
  Stack unit
    (requires fun h -> live h out /\ live h b)
    (ensures  fun h0 _ h1 -> modifies (loc out) h0 h1 /\
      F56.as_nat h1 out == nat_from_bytes_le (as_seq h0 b) /\
      (let s = as_seq h1 out in
       let op_String_Access = Seq.index in
       v s.[0] < 0x100000000000000 /\
       v s.[1] < 0x100000000000000 /\
       v s.[2] < 0x100000000000000 /\
       v s.[3] < 0x100000000000000 /\
       v s.[4] < 0x100000000000000)
    )

let load_32_bytes out b =
  let h0 = get() in
  let b0 = hload56_le' b 0ul in
  let b1 = hload56_le' b 7ul in
  let b2 = hload56_le' b 14ul in
  let b3 = hload56_le' b 21ul in
  let b4 = uint_from_bytes_le #U32 (sub b 28ul 4ul) in
  let b4 = to_u64 b4 in
  lemma_reveal_uint_to_bytes_le #U32 (as_seq h0 (gsub b 28ul 4ul));
  lemma_load_32_bytes (as_seq h0 b) b0 b1 b2 b3 b4;
  Hacl.Bignum25519.make_u64_5 out b0 b1 b2 b3 b4
