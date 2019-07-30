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

val gl_lemma: bnlen:bn_len_s{v bnlen > 0} -> len:ssize_t -> i:ssize_t{v i < v len} ->  Lemma
    (v (bnlen *! i) + v bnlen <= v (bnlen *! len))
let gl_lemma bnlen len i =
  assert (v (bnlen *! i) = v bnlen * v i);
  assert (v (bnlen *! len) = v bnlen * v len);
  distributivity_add_right (v bnlen) (v i) 1

#reset-options "--z3rlimit 100"

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
              as_snat h1 r = bnlist_ix_g h0 x i
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



#reset-options "--z3rlimit 50 --max_fuel 0 --max_ifuel 0"

val as_snat_list_go:
     #a:Type0
  -> #b:eqtype
  -> #l:size_t
  -> i:size_t{v i <= v l}
  -> h:mem
  -> x:lbuffer a l
  -> extract:(mem -> a -> GTot b)
  -> GTot (s:Seq.seq b {Seq.length s = v l - v i /\
                         (forall (j:nat{j < v l - v i}).
                          Seq.index s j = extract h (S.index (as_seq h x) (v i+j)))})
          (decreases (v l - v i))
let rec as_snat_list_go #a #b #l i h x extract =
  if i =. l then Seq.empty else begin
    let x' = as_seq h x in
    let e = extract h (S.index x' (v i)) in
    let prev = (as_snat_list_go (i +! 1ul) h x extract) in
    seq_cons_shifts_index_value e prev;
    let ret = Seq.cons e prev in
    assert (Seq.index ret 0 = e);
    assert (forall (j:nat{j < v l - v i - 1}). Seq.index ret (j+1) = Seq.index prev j);
    let lemma0 (j:nat{j < v l - v i - 1}):
               Lemma (Seq.index prev j = extract h (Seq.index x' (v i+j+1))) = () in
    let lemma1 (j:nat{j < v l - v i - 1}):
               Lemma (Seq.index ret (j+1) = Seq.index prev j) = () in
    let lemma2 (j:nat{j > 0 /\ j < v l - v i}):
               Lemma (Seq.index ret j = Seq.index prev (j-1)) = lemma1 (j-1) in
    let lemma3 (j:nat{j > 0 /\ j < v l - v i}):
               Lemma (Seq.index ret j = extract h (Seq.index x' (v i + j))) =
               (lemma2 j; lemma0 (j-1)) in
    forall_intro lemma3;
    ret
  end

#reset-options // "--z3rlimit 100 --max_fuel 0 --max_ifuel 0"

val as_snat_list_preserves_stack:
     #a:Type
  -> #b:eqtype
  -> #l:size_t
  -> i:size_t{v i <= v l}
  -> x:lbuffer a l
  -> extract:(mem -> a -> GTot b)
  -> h0:mem
  -> h1:mem
  -> Lemma
  (requires (as_seq h0 x == as_seq h1 x /\
             (forall (i:nat{i < v l}).
              extract h0 (Seq.index (as_seq h0 x) i) ==
              extract h1 (Seq.index (as_seq h1 x) i))))
  (ensures (as_snat_list_go #a #b #l i h0 x extract =
            as_snat_list_go #a #b #l i h1 x extract))
  (decreases (v l - v i))
let rec as_snat_list_preserves_stack #a #b #l i x extract h0 h1 =
  if i =. l then () else
    as_snat_list_preserves_stack #a #b #l (i +! 1ul) x extract h0 h1

val as_snat_list_bn:
     #nLen:bn_len_s
  -> #l:size_t
  -> h:mem
  -> x:bnlist nLen l
  -> GTot (s:Seq.seq nat{Seq.length s = v l /\
                         (forall (j:nat{j < v l}).
                          Seq.index s j = as_snat h (S.index (as_seq h x) j))})
let as_snat_list_bn #nLen #l h x = as_snat_list_go 0ul h x (fun h v -> as_snat h v)

val as_snat_list_bn_preserves_stack:
     #nLen:bn_len_s
  -> #l:size_t
  -> x:bn_list nLen l
  -> h0:mem
  -> h1:mem
  -> Lemma
  (requires (as_seq h0 x == as_seq h1 x /\
             (forall (i:nat{i < v l}). as_seq h0 (Seq.index (as_seq h0 x) i) ==
                                       as_seq h1 (Seq.index (as_seq h1 x) i))))
  (ensures (as_snat_list_bn h0 x = as_snat_list_bn h1 x))
let as_snat_list_bn_preserves_stack #nLen #l x h0 h1 =
  as_snat_list_preserves_stack 0ul x (fun h v -> as_snat h v) h0 h1

val as_snat_list_factors:
     #nLen:bn_len_s
  -> #l:size_t
  -> h:mem
  -> x:factors_list nLen l
  -> GTot (s:Seq.seq (tuple2 nat nat)
     {Seq.length s = v l /\
     (forall (j:nat{j < v l}).
      let (p,e) = S.index (as_seq h x) j in
      let (p',e') = Seq.index s j in
      as_snat h p = p' /\ as_snat h e = e'
      )})
let as_snat_list_factors #nLen #l h x =
  as_snat_list_go 0ul h x (fun h (p,e) -> (as_snat h p,as_snat h e))

val as_snat_list_factors_preserves_stack:
     #nLen:bn_len_s
  -> #l:size_t
  -> x:factors_list nLen l
  -> h0:mem
  -> h1:mem
  -> Lemma
  (requires (as_seq h0 x == as_seq h1 x /\
             (forall (i:nat{i < v l}).
             let (p1,e1) = Seq.index (as_seq h0 x) i in
             let (p2,e2) = Seq.index (as_seq h1 x) i in
             as_seq h0 p1 == as_seq h1 p1 /\ as_seq h0 e1 == as_seq h1 e2)))
  (ensures (as_snat_list_factors h0 x = as_snat_list_factors h1 x))
let as_snat_list_factors_preserves_stack #nLen #l x h0 h1 =
  as_snat_list_preserves_stack 0ul x (fun h (p,e) -> (as_snat h p,as_snat h e)) h0 h1
