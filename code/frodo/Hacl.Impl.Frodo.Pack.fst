module Hacl.Impl.Frodo.Pack

open FStar.HyperStack
open FStar.HyperStack.ST
open FStar.Mul

open Lib.IntTypes
open Lib.Buffer
open Lib.ByteBuffer

open Hacl.Impl.Matrix
open Hacl.Impl.Frodo.Params

module ST = FStar.HyperStack.ST
module Loops = Lib.LoopCombinators
module Seq = Lib.Sequence
module S = Spec.Frodo.Pack

#reset-options "--z3rlimit 100 --max_fuel 0 --max_ifuel 0 --using_facts_from '* -Spec +Spec.Frodo.Pack +Spec.Matrix'"

val lemma_split: #a:Type -> #len:size_nat -> s:Seq.lseq a len -> i:size_nat{i <= len} ->
  Lemma (s == Seq.(Seq.sub s 0 i @| Seq.sub s i (len - i)))
let lemma_split #a #len s i =
  FStar.Seq.lemma_split s i

/// Pack

inline_for_extraction noextract
val frodo_pack8:
    d:size_t{v d <= 16}
  -> a:lbuffer uint16 8ul
  -> res:lbytes d
  -> Stack unit
    (requires fun h0 -> live h0 a /\ live h0 res /\ disjoint a res)
    (ensures  fun h0 _ h1 ->
      modifies1 res h0 h1 /\
      as_seq h1 res == S.frodo_pack8 (v d) (as_seq h0 a))
let frodo_pack8 d a res =
  let h0 = ST.get() in
  push_frame();
  let maskd = to_u16 (u32 1 <<. d) -. u16 1 in
  let v16 = create (size 16) (u8 0) in
  let a0 = index a (size 0) &. maskd in
  let a1 = index a (size 1) &. maskd in
  let a2 = index a (size 2) &. maskd in
  let a3 = index a (size 3) &. maskd in
  let a4 = index a (size 4) &. maskd in
  let a5 = index a (size 5) &. maskd in
  let a6 = index a (size 6) &. maskd in
  let a7 = index a (size 7) &. maskd in
  let templong =
       to_u128 a0 <<. (size 7 *! d)
    |. to_u128 a1 <<. (size 6 *! d)
    |. to_u128 a2 <<. (size 5 *! d)
    |. to_u128 a3 <<. (size 4 *! d)
    |. to_u128 a4 <<. (size 3 *! d)
    |. to_u128 a5 <<. (size 2 *! d)
    |. to_u128 a6 <<. (size 1 *! d)
    |. to_u128 a7 <<. (size 0 *! d)
  in
  uint_to_bytes_be v16 templong;
  let src = sub v16 (size 16 -! d) d in // Skips the 1st byte when d = 15
  copy res src;
  pop_frame()

val frodo_pack:
    #n1:size_t
  -> #n2:size_t{v n1 * v n2 <= max_size_t /\ (v n1 * v n2) % 8 = 0}
  -> d:size_t{v d * ((v n1 * v n2) / 8) <= max_size_t /\ v d <= 16}
  -> a:matrix_t n1 n2
  -> res:lbytes (d *! ((n1 *! n2) /. size 8))
  -> Stack unit
    (requires fun h -> live h a /\ live h res /\ disjoint a res)
    (ensures  fun h0 _ h1 ->
      modifies1 res h0 h1 /\
      as_seq h1 res == S.frodo_pack (v d) (as_matrix h0 a))
[@"c_inline"]
let frodo_pack #n1 #n2 d a res =
  let n = (n1 *! n2) /. size 8 in
  let a_spec = S.frodo_pack_state #(v n1) #(v n2) (v d) in
  [@ inline_let]
  let refl h (i:size_nat{i <= v n}) = Seq.sub (as_seq h res) 0 (v d * i) in
  let footprint (i:size_nat{i <= v n}) = loc res in
  [@ inline_let]
  let spec h0 = S.frodo_pack_inner #(v n1) #(v n2) (v d) (as_seq h0 a) in
  let h0 = ST.get() in
  assert (Seq.equal (refl h0 0) (Seq.create 0 (u8 0)));
  loop h0 n a_spec refl footprint spec
    (fun i ->
      FStar.Math.Lemmas.lemma_mult_le_left (v d) (v i + 1) (v n);
      assert (v (d *! i +! d) <= v (d *! ((n1 *! n2) /. size 8)));
      Loops.unfold_repeat_gen (v n) a_spec (spec h0) (refl h0 0) (v i);
      let a = sub a (size 8 *! i) (size 8) in
      let r = sub res (d *! i) d in
      frodo_pack8 d a r;
      let h = ST.get() in
      lemma_split (refl h (v i + 1)) (v d * v i)
    )


/// Unpack

inline_for_extraction noextract
[@"opaque_to_smt"]
val frodo_unpack8:
    d:size_t{v d <= 16}
  -> b:lbytes d
  -> res:lbuffer uint16 8ul
  -> Stack unit
    (requires fun h0 -> live h0 b /\ live h0 res)
    (ensures  fun h0 _ h1 ->
      modifies1 res h0 h1 /\
      Seq.equal (as_seq h1 res) (S.frodo_unpack8 (v d) (as_seq h0 b)))
let frodo_unpack8 d b res =
  let h0 = ST.get() in
  push_frame();
  let maskd = to_u16 (u32 1 <<. d) -. u16 1 in
  let src = create (size 16) (u8 0) in
  update_sub src (size 16 -! d) d b;
  let templong = uint_from_bytes_be #U128 #SEC src in
  res.(size 0) <- to_u16 (templong >>. (size 7 *! d)) &. maskd;
  res.(size 1) <- to_u16 (templong >>. (size 6 *! d)) &. maskd;
  res.(size 2) <- to_u16 (templong >>. (size 5 *! d)) &. maskd;
  res.(size 3) <- to_u16 (templong >>. (size 4 *! d)) &. maskd;
  res.(size 4) <- to_u16 (templong >>. (size 3 *! d)) &. maskd;
  res.(size 5) <- to_u16 (templong >>. (size 2 *! d)) &. maskd;
  res.(size 6) <- to_u16 (templong >>. (size 1 *! d)) &. maskd;
  res.(size 7) <- to_u16 (templong >>. (size 0 *! d)) &. maskd;
  pop_frame()

// 2018.11.21 SZ: Inlining this below doesn't work. Hard to say why.
inline_for_extraction noextract
val frodo_unpack_loop:
    n1:size_t
  -> n2:size_t{v n1 * v n2 <= max_size_t /\ (v n1 * v n2) % 8 = 0}
  -> d:size_t{v d * (v n1 * v n2 / 8) <= max_size_t /\ v d <= 16}
  -> b:lbytes (d *! (n1 *! n2 /. size 8))
  -> res:matrix_t n1 n2
  -> h0:mem{live h0 b /\ live h0 res /\ disjoint b res}
  -> i:size_t{v i < v n1 * v n2 / 8}
  -> Stack unit
    (requires
      loop_inv h0 (n1 *! n2 /. size 8)
        (S.frodo_unpack_state #(v n1) #(v n2))
        (fun h i -> Seq.sub (as_seq h res) 0 (8 * i))
        (fun i -> loc res)
        (fun h0 -> S.frodo_unpack_inner #(v n1) #(v n2) (v d) (as_seq h0 b))
        (v i))
    (ensures  fun _ _ ->
      loop_inv h0 (n1 *! n2 /. size 8)
        (S.frodo_unpack_state #(v n1) #(v n2))
        (fun h i -> Seq.sub (as_seq h res) 0 (8 * i))
        (fun i -> loc res)
        (fun h0 -> S.frodo_unpack_inner #(v n1) #(v n2) (v d) (as_seq h0 b))
        (v i + 1))
let frodo_unpack_loop n1 n2 d b res h0 i =
  let n = n1 *! n2 /. size 8 in
  let a_spec = S.frodo_unpack_state #(v n1) #(v n2) in
  [@inline_let]
  let refl h (i:size_nat{i <= v n}) = Seq.sub (as_seq h res) 0 (8 * i) in
  let footprint (i:size_nat{i <= v n}) = loc res in
  [@inline_let]
  let spec h0 = S.frodo_unpack_inner #(v n1) #(v n2) (v d) (as_seq h0 b) in
  Loops.unfold_repeat_gen (v n) a_spec (spec h0) (refl h0 0) (v i);
  let b = sub b (d *! i) d in
  let r = sub res (size 8 *! i) (size 8) in
  frodo_unpack8 d b r;
  let h = ST.get() in
  lemma_split (refl h (v i + 1)) (8 * v i)

val frodo_unpack:
    n1:size_t
  -> n2:size_t{v n1 * v n2 <= max_size_t /\ (v n1 * v n2) % 8 = 0}
  -> d:size_t{v d * (v n1 * v n2 / 8) <= max_size_t /\ v d <= 16}
  -> b:lbytes (d *! (n1 *! n2 /. size 8))
  -> res:matrix_t n1 n2
  -> Stack unit
    (requires fun h -> live h b /\ live h res /\ disjoint b res)
    (ensures  fun h0 _ h1 ->
      modifies1 res h0 h1 /\
      as_seq h1 res == S.frodo_unpack #(v n1) #(v n2) (v d) (as_seq h0 b))
[@"c_inline"]
let frodo_unpack n1 n2 d b res =
  let n = n1 *! n2 /. size 8 in
  let a_spec = S.frodo_unpack_state #(v n1) #(v n2) in
  [@inline_let]
  let refl h (i:size_nat{i <= v n}) = Seq.sub (as_seq h res) 0 (8 * i) in
  let footprint (i:size_nat{i <= v n}) = loc res in
  [@inline_let]
  let spec h0 = S.frodo_unpack_inner #(v n1) #(v n2) (v d) (as_seq h0 b) in
  let h0 = ST.get() in
  loop h0 n a_spec refl footprint spec (frodo_unpack_loop n1 n2 d b res h0)
