module Hacl.Impl.HE.Other

open FStar.Classical
open FStar.HyperStack
open FStar.HyperStack.ST
open FStar.Math.Lemmas
open FStar.Mul

open LowStar.Buffer

open Lib.IntTypes
open Lib.Buffer
open Lib.Math.Algebra
open Lib.LoopCombinators

open Hacl.Impl.Bignum

module S = Lib.Sequence
module B = Lib.Buffer
module LB = LowStar.Buffer


// 2^15 elements of 64 bits is 2^21, which should be more then enough.
type bn_len_s = s:bn_len{v s <= pow2 15}

val bn_len_s_fits: (l:bn_len_s) -> Lemma
  (
   v l * 2 < max_size_t /\
   v l * 64 < max_size_t /\
   v l * 128 < max_size_t /\
   (v l + 1) < max_size_t
  )
let bn_len_s_fits _ = ()

// small size_t
type ssize_t = s:size_t{forall (x:bn_len_s). v x * v s < pow2 32}

type bnlist (bnlen:bn_len_s) (len:ssize_t) = lbuffer uint64 (bnlen *! len)

#reset-options "--z3rlimit 100"

val gl_lemma: bnlen:bn_len_s{v bnlen > 0} -> len:ssize_t -> i:size_t{v i < v len} ->  Lemma
    (v (bnlen *! i) + v bnlen <= v (bnlen *! len))
let gl_lemma bnlen len i =
  assert (v (bnlen *! i) = v bnlen * v i);
  assert (v (bnlen *! len) = v bnlen * v len);
  distributivity_add_right (v bnlen) (v i) 1

#reset-options "--z3rlimit 100"

noextract
val bnlist_ix_g:
     #bnlen:bn_len_s
  -> #len:ssize_t
  -> h:mem
  -> x:bnlist bnlen len
  -> i:size_t{v i < v len}
  -> GTot nat
let bnlist_ix_g #bnlen #len h x i =
  gl_lemma bnlen len i;
  as_snat h (gsub x (bnlen *! i) bnlen)

noextract
val bnlist_ix_g_preserves_h:
     #bnlen:bn_len_s
  -> #len:ssize_t
  -> h0:mem
  -> h1:mem
  -> x:bnlist bnlen len
  -> i:size_t{v i < v len}
  -> Lemma
  (requires as_seq h0 x == as_seq h1 x)
  (ensures bnlist_ix_g h0 x i = bnlist_ix_g h1 x i)
let bnlist_ix_g_preserves_h #bnlen #len h0 h1 x i =
  gl_lemma bnlen len i


inline_for_extraction
val bnlist_ix:
     #bnlen:bn_len_s
  -> #len:ssize_t
  -> x:bnlist bnlen len
  -> i:size_t{v i < v len}
  -> Stack (lbignum bnlen)
           (requires fun h -> live h x)
           (ensures fun h0 r h1 ->
             (gl_lemma bnlen len i;
              h0 == h1 /\
              live h1 r /\
              r == gsub x (bnlen *! i) bnlen /\
              as_snat h1 r = bnlist_ix_g h0 x i /\
              (forall (z:LB.loc). LB.loc_disjoint z (loc x) ==> LB.loc_disjoint z (loc r))
              ))
let bnlist_ix #bnlen #len x i =
  gl_lemma bnlen len i;
  sub x (bnlen *! i) bnlen

val seq_cons_shifts_index_value: #a:eqtype -> x:a -> l:Seq.seq a -> Lemma
  (ensures (forall (i:nat{i < Seq.length l}). Seq.index (Seq.cons x l) (i+1) = Seq.index l i))
  (decreases (Seq.length l))
let rec seq_cons_shifts_index_value #a x l =
  if Seq.length l = 0 then () else seq_cons_shifts_index_value #a (Seq.head l) (Seq.tail l)


#reset-options "--z3rlimit 100"

noextract
val as_snat_bnlist_go:
     #nlen:bn_len_s
  -> #l:ssize_t
  -> h:mem
  -> x:bnlist nlen l
  -> i:size_t{v i <= v l}
  -> GTot (s:Seq.seq nat
          {(Seq.length s = v l - v i) /\
           (forall (j:size_t{v j < v l - v i}).
            Seq.index s (v j) = bnlist_ix_g h x (i +! j))})
          (decreases (v l - v i))
let rec as_snat_bnlist_go #nlen #l h x i =
  if v i = v l then Seq.empty else begin
    let e = bnlist_ix_g h x i in
    let prev = as_snat_bnlist_go h x (i +! 1ul) in
    seq_cons_shifts_index_value e prev;
    let ret = Seq.cons e prev in
    assert (Seq.index ret 0 = e);
    assert (forall (j:nat{j < v l - v i - 1}). Seq.index ret (j+1) = Seq.index prev j);
    let lemma0 (j:size_t{v j < v l - v i - 1}):
               Lemma (Seq.index prev (v j) = bnlist_ix_g h x (i +! j +! 1ul)) = () in
    let lemma1 (j:size_t{v j < v l - v i - 1}):
               Lemma (Seq.index ret (v j+1) = Seq.index prev (v j)) = () in
    let lemma2 (j:size_t{v j > 0 /\ v j < v l - v i}):
               Lemma (Seq.index ret (v j) = Seq.index prev (v j-1)) = lemma1 (j -! 1ul) in
    let lemma3 (j:size_t{v j > 0 /\ v j < v l - v i}):
               Lemma (Seq.index ret (v j) = bnlist_ix_g h x (i +! j)) =
               (lemma2 j; lemma0 (j -! 1ul)) in
    forall_intro lemma3;
    ret
  end


noextract
val as_snat_bnlist:
     #nlen:bn_len_s
  -> #l:ssize_t
  -> h:mem
  -> x:bnlist nlen l
  -> GTot (s:Seq.seq nat
          {(Seq.length s = v l) /\
           (forall (j:size_t{v j < v l}).
            Seq.index s (v j) = bnlist_ix_g h x j)})
let as_snat_bnlist #n #l h x = as_snat_bnlist_go h x 0ul

val as_snat_bnlist_preserves_h_go:
     #nlen:bn_len_s
  -> #l:ssize_t
  -> h0:mem
  -> h1:mem
  -> x:bnlist nlen l
  -> i:size_t{v i <= v l}
  -> Lemma
  (requires as_seq h0 x == as_seq h1 x)
  (ensures as_snat_bnlist_go h0 x i = as_snat_bnlist_go h1 x i)
  (decreases (v l - v i))
let rec as_snat_bnlist_preserves_h_go #nlen #l h0 h1 x i =
  if v i = v l then () else begin
    gl_lemma nlen l i;
    bnlist_ix_g_preserves_h h0 h1 x i;
    as_snat_bnlist_preserves_h_go h0 h1 x (i +! 1ul)
  end

val as_snat_bnlist_preserves_h:
     #nlen:bn_len_s
  -> #l:ssize_t
  -> h0:mem
  -> h1:mem
  -> x:bnlist nlen l
  -> Lemma
  (requires as_seq h0 x == as_seq h1 x)
  (ensures as_snat_bnlist h0 x = as_snat_bnlist h1 x)
let as_snat_bnlist_preserves_h #nlen #l h0 h1 x =
  as_snat_bnlist_preserves_h_go h0 h1 x 0ul
