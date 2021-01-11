module Hacl.Impl.Lib

open FStar.HyperStack
open FStar.HyperStack.ST
open FStar.Mul

open Lib.IntTypes
open Lib.Buffer

module ST = FStar.HyperStack.ST
module B = LowStar.Buffer
module LSeq = Lib.Sequence
module Loops = Lib.LoopCombinators

module S = Hacl.Spec.Lib

#reset-options "--z3rlimit 50 --fuel 0 --ifuel 0"

inline_for_extraction noextract
let fill_elems_st =
  #t:Type0
  -> #a:Type0
  -> h0:mem
  -> n:size_t
  -> output:lbuffer t n
  -> refl:(mem -> i:size_nat{i <= v n} -> GTot a)
  -> footprint:(i:size_nat{i <= v n} -> GTot
      (l:B.loc{B.loc_disjoint l (loc output) /\ B.address_liveness_insensitive_locs `B.loc_includes` l}))
  -> spec:(mem -> GTot (i:size_nat{i < v n} -> a -> a & t))
  -> impl:(i:size_t{v i < v n} -> Stack unit
      (requires fun h ->
	modifies (footprint (v i) |+| loc (gsub output 0ul i)) h0 h)
      (ensures  fun h1 _ h2 ->
	(let block1 = gsub output i 1ul in
	 let c, e = spec h0 (v i) (refl h1 (v i)) in
	 refl h2 (v i + 1) == c /\
	 LSeq.index (as_seq h2 block1) 0 == e /\
	 footprint (v i + 1) `B.loc_includes` footprint (v i) /\
	 modifies (footprint (v i + 1) |+| (loc block1)) h1 h2))) ->
  Stack unit
    (requires fun h -> h0 == h /\ live h output)
    (ensures  fun _ _ h1 -> modifies (footprint (v n) |+| loc output) h0 h1 /\
     (let s, o = S.generate_elems (v n) (v n) (spec h0) (refl h0 0) in
      refl h1 (v n) == s /\ as_seq #_ #t h1 output == o))


inline_for_extraction noextract
val fill_elems : fill_elems_st
let fill_elems #t #a h0 n output refl footprint spec impl =
  [@inline_let]
  let refl' h (i:nat{i <= v n}) : GTot (S.generate_elem_a t a (v n) i) =
    refl h i, as_seq h (gsub output 0ul (size i)) in
  [@inline_let]
  let footprint' i = footprint i |+| loc (gsub output 0ul (size i)) in
  [@inline_let]
  let spec' h0 = S.generate_elem_f (v n) (spec h0) in

  let h0 = ST.get () in
  loop h0 n (S.generate_elem_a t a (v n)) refl' footprint' spec'
  (fun i ->
    Loops.unfold_repeat_gen (v n) (S.generate_elem_a t a (v n)) (spec' h0) (refl' h0 0) (v i);
    impl i;
    let h = ST.get() in
    FStar.Seq.lemma_split (as_seq h (gsub output 0ul (i +! 1ul))) (v i)
  );
  let h1 = ST.get () in
  assert (refl' h1 (v n) ==
    Loops.repeat_gen (v n) (S.generate_elem_a t a (v n)) (S.generate_elem_f (v n) (spec h0)) (refl' h0 0))


inline_for_extraction noextract
val fill_blocks4:
    #t:Type0
  -> #a:Type0
  -> h0:mem
  -> n:size_t{v n % 4 = 0}
  -> output:lbuffer t n
  -> refl:(mem -> i:size_nat{i <= v n} -> GTot a)
  -> footprint:(i:size_nat{i <= v n} -> GTot
      (l:B.loc{B.loc_disjoint l (loc output) /\ B.address_liveness_insensitive_locs `B.loc_includes` l}))
  -> spec:(mem -> GTot (i:size_nat{i < v n} -> a -> a & t))
  -> impl:(i:size_t{v i < v n} -> Stack unit
      (requires fun h ->
	modifies (footprint (v i) |+| loc (gsub output 0ul i)) h0 h)
      (ensures  fun h1 _ h2 ->
	(let block1 = gsub output i 1ul in
	 let c, e = spec h0 (v i) (refl h1 (v i)) in
	 refl h2 (v i + 1) == c /\ LSeq.index (as_seq h2 block1) 0 == e /\
	 footprint (v i + 1) `B.loc_includes` footprint (v i) /\
	 modifies (footprint (v i + 1) |+| (loc block1)) h1 h2))) ->
  Stack unit
    (requires fun h -> h0 == h /\ live h output)
    (ensures  fun _ _ h1 -> modifies (footprint (v n) |+| loc output) h0 h1 /\
     (let s, o = LSeq.generate_blocks 4 (v n / 4) (v n / 4) (Loops.fixed_a a)
       (S.generate_blocks4_f #t #a (v n / 4) (spec h0)) (refl h0 0) in
      refl h1 (v n) == s /\ as_seq #_ #t h1 output == o))

let fill_blocks4 #t #a h0 n output refl footprint spec impl =
  fill_blocks h0 4ul (n /. 4ul) output (Loops.fixed_a a)
  (fun h i -> refl h (4 * i))
  (fun i -> footprint (4 * i))
  (fun h0 -> S.generate_blocks4_f #t #a (v n / 4) (spec h0))
  (fun i ->
    let h1 = ST.get () in
    impl (4ul *! i);
    impl (4ul *! i +! 1ul);
    impl (4ul *! i +! 2ul);
    impl (4ul *! i +! 3ul);
    let h2 = ST.get () in
    assert (
      let c0, e0 = spec h0 (4 * v i) (refl h1 (4 * v i)) in
      let c1, e1 = spec h0 (4 * v i + 1) c0 in
      let c2, e2 = spec h0 (4 * v i + 2) c1 in
      let c3, e3 = spec h0 (4 * v i + 3) c2 in
      let res = Lib.IntVector.create4 e0 e1 e2 e3 in
      let res1 = LSeq.sub (as_seq h2 output) (4 * v i) 4 in
      refl h2 (4 * v i + 4) == c3 /\
      (LSeq.eq_intro res res1; res1 `LSeq.equal` res))
  )


inline_for_extraction noextract
val fill_elems4: fill_elems_st
let fill_elems4 #t #a h0 n output refl footprint spec impl =
  [@inline_let] let k = n /. 4ul *! 4ul in
  let tmp = sub output 0ul k in
  fill_blocks4 #t #a h0 k tmp refl footprint spec (fun i -> impl i);
  let h1 = ST.get () in
  assert (v k + v (n -! k) = v n);
  B.modifies_buffer_elim (B.gsub #t output k (n -! k)) (footprint (v k) |+| loc tmp) h0 h1;
  assert (modifies (footprint (v k) |+| loc (gsub output 0ul k)) h0 h1);

  let inv (h:mem) (i:nat{v k <= i /\ i <= v n}) =
    modifies (footprint i |+| loc (gsub output 0ul (size i))) h0 h /\
   (let (c, res) = Loops.repeat_right (v n / 4 * 4) i (S.generate_elem_a t a (v n))
      (S.generate_elem_f (v n) (spec h0)) (refl h1 (v k), as_seq h1 (gsub output 0ul k)) in
    refl h i == c /\ as_seq h (gsub output 0ul (size i)) == res) in

  Loops.eq_repeat_right (v n / 4 * 4) (v n) (S.generate_elem_a t a (v n))
    (S.generate_elem_f (v n) (spec h0)) (refl h1 (v k), as_seq h1 (gsub output 0ul k));

  Lib.Loops.for k n inv
  (fun i ->

    impl i;
    let h = ST.get () in
    assert (v (i +! 1ul) = v i + 1);
    FStar.Seq.lemma_split (as_seq h (gsub output 0ul (i +! 1ul))) (v i);
    Loops.unfold_repeat_right (v n / 4 * 4) (v n) (S.generate_elem_a t a (v n))
      (S.generate_elem_f (v n) (spec h0)) (refl h1 (v k), as_seq h1 (gsub output 0ul k)) (v i)
    );

  S.lemma_generate_elems4 (v n) (v n) (spec h0) (refl h0 0)


inline_for_extraction noextract
val lemma_eq_disjoint:
    #a1:Type
  -> #a2:Type
  -> #a3:Type
  -> clen1:size_t
  -> clen2:size_t
  -> clen3:size_t
  -> b1:lbuffer a1 clen1
  -> b2:lbuffer a2 clen2
  -> b3:lbuffer a3 clen3
  -> n:size_t{v n < v clen2 /\ v n < v clen1}
  -> h0:mem
  -> h1:mem -> Lemma
  (requires
    live h0 b1 /\ live h0 b2 /\ live h0 b3 /\
    eq_or_disjoint b1 b2 /\ disjoint b1 b3 /\ disjoint b2 b3 /\
    modifies (loc (gsub b1 0ul n) |+| loc b3) h0 h1)
  (ensures
    (let b2s = gsub b2 n (clen2 -! n) in
    as_seq h0 b2s == as_seq h1 b2s /\
    Seq.index (as_seq h0 b2) (v n) == Seq.index (as_seq h1 b2) (v n)))

let lemma_eq_disjoint #a1 #a2 #a3 clen1 clen2 clen3 b1 b2 b3 n h0 h1 =
  let b1s = gsub b1 0ul n in
  let b2s = gsub b2 0ul n in
  assert (modifies (loc b1s |+| loc b3) h0 h1);
  assert (disjoint b1 b2 ==> Seq.equal (as_seq h0 b2) (as_seq h1 b2));
  assert (disjoint b1 b2 ==> Seq.equal (as_seq h0 b2s) (as_seq h1 b2s));
  assert (Seq.index (as_seq h1 b2) (v n) == Seq.index (as_seq h1 (gsub b2 n (clen2 -! n))) 0)


inline_for_extraction noextract
val update_sub_f_carry:
    #a:Type
  -> #b:Type
  -> #len:size_t
  -> h0:mem
  -> buf:lbuffer a len
  -> start:size_t
  -> n:size_t{v start + v n <= v len}
  -> spec:(mem -> GTot (b & Seq.lseq a (v n)))
  -> f:(unit -> Stack b
      (requires fun h -> h0 == h)
      (ensures  fun _ r h1 ->
       (let b = gsub buf start n in modifies (loc b) h0 h1 /\
       (let (c, res) = spec h0 in r == c /\ as_seq h1 b == res)))) ->
  Stack b
    (requires fun h -> h0 == h /\ live h buf)
    (ensures  fun h0 r h1 -> modifies (loc buf) h0 h1 /\
     (let (c, res) = spec h0 in r == c /\
     as_seq h1 buf == LSeq.update_sub #a #(v len) (as_seq h0 buf) (v start) (v n) res))

let update_sub_f_carry #a #b #len h0 buf start n spec f =
  let tmp = sub buf start n in
  let h0 = ST.get () in
  let r = f () in
  let h1 = ST.get () in
  assert (v (len -! (start +! n)) == v len - v (start +! n));
  B.modifies_buffer_elim (B.gsub #a buf 0ul start) (loc tmp) h0 h1;
  B.modifies_buffer_elim (B.gsub #a buf (start +! n) (len -! (start +! n))) (loc tmp) h0 h1;
  LSeq.lemma_update_sub (as_seq h0 buf) (v start) (v n) (snd (spec h0)) (as_seq h1 buf);
  r
