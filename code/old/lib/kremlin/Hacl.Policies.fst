module Hacl.Policies

module ST = FStar.HyperStack.ST

open FStar.HyperStack.All

open FStar.HyperStack.ST
open FStar.Buffer

open Hacl.Types

(* Module abbreviations *)
module HS  = FStar.HyperStack
module B   = FStar.Buffer
module U8  = FStar.UInt8
module U32 = FStar.UInt32
module U64 = FStar.UInt64
module U128 = FStar.UInt128
module H8  = Hacl.UInt8
module H32  = Hacl.UInt32
module H64  = Hacl.UInt64
module H128  = Hacl.UInt128

inline_for_extraction val declassify_u8: x:H8.t -> Tot (y:U8.t{H8.v x = U8.v y})
inline_for_extraction let declassify_u8 x = x
inline_for_extraction val declassify_u32: x:H32.t -> Tot (y:U32.t{H32.v x = U32.v y})
inline_for_extraction let declassify_u32 x = x
inline_for_extraction val declassify_u64: x:H64.t -> Tot (y:U64.t{H64.v x = U64.v y})
inline_for_extraction let declassify_u64 x = x
inline_for_extraction val declassify_u128: x:H128.t -> Tot (y:U128.t{H128.v x = U128.v y})
inline_for_extraction let declassify_u128 x = x

#reset-options "--initial_fuel 0 --max_fuel 0 --initial_ifuel 0 --max_ifuel 0 --z3rlimit 50"

private val lemma_not_equal_slice: #a:Type -> b1:Seq.seq a -> b2:Seq.seq a -> i:nat -> j:nat ->
  k:nat{i <= j /\ i <= k /\ j <= k /\ k <= Seq.length b1 /\ k <= Seq.length b2 } ->
  Lemma
    (requires ~(Seq.equal (Seq.slice b1 i j) (Seq.slice b2 i j)))
    (ensures  ~(Seq.equal (Seq.slice b1 i k) (Seq.slice b2 i k)))
let lemma_not_equal_slice #a b1 b2 i j k =
  assert (forall (n:nat{n < k - i}). Seq.index (Seq.slice b1 i k) n == Seq.index b1 (n + i))

private val lemma_not_equal_last: #a:Type -> b1:Seq.seq a -> b2:Seq.seq a -> i:nat ->
  j:nat{i < j /\ j <= Seq.length b1 /\ j <= Seq.length b2} ->
  Lemma
    (requires ~(Seq.index b1 (j - 1) == Seq.index b2 (j - 1)))
    (ensures  ~(Seq.equal (Seq.slice b1 i j) (Seq.slice b2 i j)))
let lemma_not_equal_last #a b1 b2 i j =
  Seq.lemma_index_slice b1 i j (j - i - 1);
  Seq.lemma_index_slice b2 i j (j - i - 1)

val cmp_bytes_:
  b1:uint8_p ->
  b2:uint8_p ->
  len:u32{U32.v len <= length b1 /\ U32.v len <= length b2} ->
  tmp:uint8_p{length tmp == 1 /\ disjoint_2 tmp b1 b2} ->
  Stack h8
    (requires (fun h -> live h b1 /\ live h b2 /\ live h tmp /\ H8.v (get h tmp 0) == 255))
    (ensures  (fun h0 z h1 -> modifies_1 tmp h0 h1 /\
      (H8.v z == 0 \/ H8.v z == 255) /\
      (H8.v z == 255 <==> equal h0 (sub b1 0ul len) h0 (sub b2 0ul len))))

#reset-options "--z3refresh --log_queries --max_fuel 0 --max_ifuel 0 --z3rlimit 50 --query_stats"

// JP, NS: this file verifies when the dependencies are lax-checked, but not
// when the dependencies are properly checked with a cache dir. TODO fixme
#set-options "--lax"
let rec cmp_bytes_ b1 b2 len tmp =
  UInt.logand_lemma_1 #8 255;
  UInt.logand_lemma_2 #8 255;
  UInt.logand_lemma_1 #8 0;
  UInt.logand_lemma_2 #8 0;
  let h0 = ST.get() in
  let inv h (i: nat) =
    let z = get h tmp 0 in
    live h b1 /\ live h b2 /\ live h tmp /\ modifies_1 tmp h0 h /\ 0 <= i /\ i <= U32.v len /\
    (H8.v z == 255 \/ H8.v z == 0) /\
    (H8.v z == 255 <==> equal h0 (sub b1 0ul U32.(uint_to_t i)) h0 (sub b2 0ul U32.(uint_to_t i)))
  in
  let f (i:U32.t{U32.(0 <= v i /\ v i < v len)}) :
    Stack unit
      (requires (fun h -> inv h (U32.v i)))
      (ensures  (fun h0 _ h1 -> U32.(inv h0 (v i) /\ inv h1 (v i + 1)))) =
    let bi1 = b1.(i) in
    let bi2 = b2.(i) in
    let z0 = tmp.(0ul) in
    tmp.(0ul) <- H8.(eq_mask bi1 bi2 &^ z0);
    let h = ST.get() in
    if H8.v (get h tmp 0) = 255 then
      begin
      let s1  = as_seq h0 (sub b1 0ul U32.(i +^ 1ul)) in
      let s2  = as_seq h0 (sub b2 0ul U32.(i +^ 1ul)) in
      let s1' = as_seq h0 (sub b1 0ul i) in
      let s2' = as_seq h0 (sub b2 0ul i) in
      assert (Seq.equal s1' s2');
      assert FStar.Seq.(index s1 (U32.v i) == index s2 (U32.v i));
      assert (Seq.equal s1 (Seq.snoc s1' (Seq.index s1 (U32.v i))));
      assert (Seq.equal s2 (Seq.snoc s2' (Seq.index s2 (U32.v i))));
      Seq.lemma_eq_intro s1 s2
      end
    else if H8.v z0 = 0 then
      lemma_not_equal_slice (as_seq h0 b1) (as_seq h0 b2) 0 (U32.v i) (U32.v i + 1)
    else
      lemma_not_equal_last (as_seq h0 b1) (as_seq h0 b2) 0 (U32.v i + 1)
  in
  C.Compat.Loops.for 0ul len inv f;
  tmp.(0ul)


val cmp_bytes:
  b1:uint8_p ->
  b2:uint8_p ->
  len:u32{U32.v len <= length b1 /\ U32.v len <= length b2} ->
  Stack h8
    (requires (fun h -> live h b1 /\ live h b2))
    (ensures  (fun h0 z h1 -> modifies_0 h0 h1 /\
      (H8.v z == 0 <==> equal h0 (sub b1 0ul len) h0 (sub b2 0ul len))))
let cmp_bytes b1 b2 len =
  push_frame();
  let h0 = ST.get() in
  let tmp = Buffer.create (Hacl.Cast.uint8_to_sint8 255uy) 1ul in
  let h1 = ST.get() in
  let z = cmp_bytes_ b1 b2 len tmp in
  let h2 = ST.get() in
  pop_frame();
  UInt.lognot_lemma_1 #8;
  UInt.lognot_self #8 0;
  lemma_modifies_0_1' tmp h0 h1 h2;
  H8.lognot z
