module Hacl.Impl.Poly1305.Bignum128

open FStar.HyperStack
open FStar.HyperStack.All
open FStar.Mul

open Lib.IntTypes
open Lib.Buffer
open Lib.ByteBuffer

open Hacl.Impl.Poly1305.Lemmas

module ST = FStar.HyperStack.ST
module LSeq = Lib.Sequence
module BSeq = Lib.ByteSequence

friend FStar.UInt128

#set-options "--z3rlimit 50 --fuel 0 --ifuel 0"

let uints64_from_bytes_le b =
  let h0 = ST.get () in
  let lo = uint_from_bytes_le #U64 (sub b 0ul 8ul) in
  let hi = uint_from_bytes_le #U64 (sub b 8ul 8ul) in
  uint_from_bytes_le_lemma (as_seq h0 b);
  lo, hi


let uints64_to_bytes_le b r0 r1 =
  let h0 = ST.get () in
  update_sub_f h0 b 0ul 8ul
    (fun h -> BSeq.uint_to_bytes_le #U64 r0)
    (fun _ -> uint_to_bytes_le (sub b 0ul 8ul) r0);
  let h1 = ST.get () in
  update_sub_f h1 b 8ul 8ul
    (fun h -> BSeq.uint_to_bytes_le #U64 r1)
    (fun _ -> uint_to_bytes_le (sub b 8ul 8ul) r1);
  //uint_to_bytes_le (sub b 0ul 8ul) r0;
  //uint_to_bytes_le (sub b 8ul 8ul) r1;
  let h2 = ST.get () in
  uints64_to_bytes_le_lemma r0 r1;
  LSeq.eq_intro (LSeq.sub (as_seq h2 b) 0 8) (BSeq.uint_to_bytes_le #U64 r0);
  LSeq.lemma_concat2
    8 (BSeq.uint_to_bytes_le #U64 r0)
    8 (BSeq.uint_to_bytes_le #U64 r1) (as_seq h2 b)


val constant_time_carry_ok: r0:uint64 -> b0:uint64 ->
  Lemma (let c = r0 ^. ((r0 ^. b0) |. ((r0 -. b0) ^. b0)) >>. 63ul in
    v c == (if v r0 < v b0 then 1 else 0))

let constant_time_carry_ok r0 b0 =
  let c = r0 ^. ((r0 ^. b0) |. ((r0 -. b0) ^. b0)) >>. 63ul in
  let r0' = Lib.RawIntTypes.u64_to_UInt64 r0 in
  let b0' = Lib.RawIntTypes.u64_to_UInt64 b0 in
  let c' = FStar.UInt128.constant_time_carry r0' b0' in
  logxor_spec r0 b0;
  logxor_spec (r0 -. b0) b0;
  logor_spec (r0 ^. b0) ((r0 -. b0) ^. b0);
  logxor_spec r0 ((r0 ^. b0) |. ((r0 -. b0) ^. b0));
  assert (v c' == v c);
  FStar.UInt128.constant_time_carry_ok r0' b0'


val add_mod_small: a:nat -> b:nat -> n:pos -> Lemma
  (requires a % n + b % n < n)
  (ensures  a % n + b % n == (a + b) % n)

let add_mod_small a b n =
  FStar.Math.Lemmas.modulo_lemma (a % n + b % n) n;
  assert (a % n + b % n == (a % n + b % n) % n);
  FStar.Math.Lemmas.lemma_mod_plus_distr_l a (b % n) n;
  FStar.Math.Lemmas.lemma_mod_plus_distr_r a b n


val mod_add128_lemma: a:(uint64 & uint64) -> b:(uint64 & uint64) ->
  Lemma (let (a0, a1) = a in let (b0, b1) = b in
    let r0 = a0 +. b0 in let r1 = a1 +. b1 in
    let c = r0 ^. ((r0 ^. b0) |. ((r0 -. b0) ^. b0)) >>. 63ul in
    let r1 = r1 +. c in
    v r1 * pow2 64 + v r0 == ((v a1 + v b1) * pow2 64 + v a0 + v b0) % pow2 128)

let mod_add128_lemma a b =
  let (a0, a1) = a in
  let (b0, b1) = b in
  let r0 = a0 +. b0 in
  let r1 = a1 +. b1 in
  let c = r0 ^. ((r0 ^. b0) |. ((r0 -. b0) ^. b0)) >>. 63ul in
  constant_time_carry_ok r0 b0;
  assert (v c == (if v r0 < v b0 then 1 else 0));
  assert (v c == (v a0 + v b0) / pow2 64);
  let r2 = r1 +. c in

  calc (==) {
    v r2 * pow2 64 + v r0;
    (==) { }
    ((v a1 + v b1) % pow2 64 + (v a0 + v b0) / pow2 64) % pow2 64 * pow2 64 + (v a0 + v b0) % pow2 64;
    (==) { Math.Lemmas.pow2_multiplication_modulo_lemma_2 ((v a1 + v b1) % pow2 64 + (v a0 + v b0) / pow2 64) 128 64 }
    ((v a1 + v b1) % pow2 64 + (v a0 + v b0) / pow2 64) * pow2 64 % pow2 128 + (v a0 + v b0) % pow2 64;
    (==) { }
    ((v a1 + v b1) % pow2 64 * pow2 64 + (v a0 + v b0) / pow2 64 * pow2 64) % pow2 128 + (v a0 + v b0) % pow2 64;
    (==) { Math.Lemmas.pow2_multiplication_modulo_lemma_2 (v a1 + v b1) 128 64 }
    ((v a1 + v b1) * pow2 64 % pow2 128 + (v a0 + v b0) / pow2 64 * pow2 64) % pow2 128 + (v a0 + v b0) % pow2 64;
    (==) { Math.Lemmas.lemma_mod_plus_distr_l ((v a1 + v b1) * pow2 64) ((v a0 + v b0) / pow2 64 * pow2 64) (pow2 128) }
    ((v a1 + v b1) * pow2 64 + (v a0 + v b0) / pow2 64 * pow2 64) % pow2 128 + (v a0 + v b0) % pow2 64;
    (==) { Math.Lemmas.modulo_lemma ((v a0 + v b0) % pow2 64) (pow2 128) }
    ((v a1 + v b1) * pow2 64 + (v a0 + v b0) / pow2 64 * pow2 64) % pow2 128 + ((v a0 + v b0) % pow2 64) % pow2 128;
  };
  assert (v r2 * pow2 64 + v r0 ==
    ((v a1 + v b1) * pow2 64 + (v a0 + v b0) / pow2 64 * pow2 64) % pow2 128 + ((v a0 + v b0) % pow2 64) % pow2 128);
  assert (v r2 * pow2 64 + v r0 < pow2 128);
  add_mod_small ((v a1 + v b1) * pow2 64 + (v a0 + v b0) / pow2 64 * pow2 64) ((v a0 + v b0) % pow2 64) (pow2 128);
  Math.Lemmas.euclidean_division_definition (v a0 + v b0) (pow2 64);
  assert (v r2 * pow2 64 + v r0 == ((v a1 + v b1) * pow2 64 + v a0 + v b0) % pow2 128)


let mod_add128 (a0, a1) (b0, b1) =
  mod_add128_lemma (a0, a1) (b0, b1);
  let r0 = a0 +. b0 in
  let r1 = a1 +. b1 in
  let c = r0 ^. ((r0 ^. b0) |. ((r0 -. b0) ^. b0)) >>. 63ul in
  let r1 = r1 +. c in
  (r0, r1)
