module Hacl.Impl.HE.Other

open FStar.Classical
open FStar.HyperStack
open FStar.HyperStack.ST
open FStar.Mul

open LowStar.Buffer

open Lib.IntTypes
open Lib.Buffer
open Lib.Math.Algebra
open Lib.LoopCombinators

open Hacl.Impl.Bignum

module S = Lib.Sequence
module B = Lib.Buffer

type bn_len_s = s:bn_len{v s <= pow2 22}

val bn_len_s_fits: (l:bn_len_s) -> Lemma
  (
   v l * 2 < max_size_t /\
   v l * 64 < max_size_t /\
   v l * 128 < max_size_t /\
   (v l + 1) < max_size_t
  )
let bn_len_s_fits _ = ()


let factors_list (bnlen:bn_len_s) (len:size_t) =
  lbuffer (tuple2 (lbignum bnlen) (lbignum bnlen)) len

let bn_list (bnlen:bn_len_s) (len:size_t) =
  lbuffer (lbignum bnlen) len


val seq_cons_shifts_index_value: #a:eqtype -> x:a -> l:S.seq a -> Lemma
  (ensures (forall (i:nat{i < Seq.length l}). Seq.index (Seq.cons x l) (i+1) = Seq.index l i))
  (decreases (S.length l))
let rec seq_cons_shifts_index_value #a x l =
  if Seq.length l = 0 then () else seq_cons_shifts_index_value #a (Seq.head l) (Seq.tail l)


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
  -> x:bn_list nLen l
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
