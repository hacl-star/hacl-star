module MerkleTree.Low.VectorExtras

module B = LowStar.Buffer
module S = FStar.Seq
module HS = FStar.HyperStack
module HST = FStar.HyperStack.ST
module U32 = FStar.UInt32

open LowStar.BufferOps
open Hacl.Hash.Lemmas
open FStar.Integers
open LowStar.Modifies
open LowStar.Regional

open LowStar.Vector
open LowStar.RVector
module V = LowStar.Vector
module RV = LowStar.RVector


(** Some extra functions on top of LowStar.Vector... used for Merkle Tree. *)

#set-options "--max_fuel 0 --max_ifuel 0 --z3rlimit 50"

inline_for_extraction
let move_left #a (b: B.buffer a) (dst src: U32.t) (l: U32.t): HST.Stack unit
  (requires fun h0 ->
    B.live h0 b /\
    U32.v src + U32.v l <= B.length b /\
    U32.v dst <= U32.v src)
  (ensures fun h0 _ h1 ->
    B.(modifies (loc_buffer b) h0 h1) /\ (

    let b0 = B.as_seq h0 b in
    let b1 = B.as_seq h1 b in
    let src = U32.v src in
    let dst = U32.v dst in
    let l = U32.v l in
    S.slice b1 dst (dst + l) `S.equal` S.slice b0 src (src + l)))
=
  let h0 = HST.get () in
  [@inline_let]
  let inv (h: HS.mem) (i: nat) =
    let b0 = B.as_seq h0 b in
    let b1 = B.as_seq h b in
    let src = U32.v src in
    let dst = U32.v dst in
    let l = U32.v l in
    i <= l /\
    B.(modifies (loc_buffer b) h0 h) /\
    S.slice b1 dst (dst + i) `S.equal` S.slice b0 src (src + i) /\
    S.slice b1 (src + i) (src + l) `S.equal` S.slice b0 (src + i) (src + l)
  in
  let f (i: U32.t { U32.(0 <= v i /\ v i < v l) }): HST.Stack unit
    (requires fun h0 -> inv h0 (U32.v i))
    (ensures fun h0 _ h1 -> U32.(inv h0 (v i) /\ inv h1 (v i + 1)))
  =
    let h00 = HST.get () in
    calc (==) {
      S.index (B.as_seq h0 b) U32.(v src + v i);
    (==) {}
      S.index (S.slice (B.as_seq h0 b) U32.(v src + v i) U32.(v src + v l)) 0;
    (==) {}
      S.index (S.slice (B.as_seq h00 b) U32.(v src + v i) U32.(v src + v l)) 0;
    (==) {}
      S.index (B.as_seq h00 b) U32.(v src + v i);
    };
    b.(dst `U32.add` i) <- b.(src `U32.add` i);
    let h = HST.get () in
    let b0 = B.as_seq h0 b in
    let b1 = B.as_seq h b in
    let src = U32.v src in
    let dst = U32.v dst in
    let l = U32.v l in
    let i = U32.v i in
    calc (S.equal) {
      S.slice b1 dst (dst + (i + 1));
    (S.equal) { lemma_slice_ijk b1 dst (dst + i) (dst + i + 1) }
      S.slice b1 dst (dst + i) `S.append` S.slice b1 (dst + i) (dst + i + 1);
    (S.equal) { }
      S.slice b0 src (src + i) `S.append` S.slice b1 (dst + i) (dst + i + 1);
    (S.equal) { }
      S.slice b0 src (src + i) `S.append` S.cons (S.index b1 (dst + i)) S.empty;
    (S.equal) { }
      S.slice b0 src (src + i) `S.append` S.cons (S.index b0 (src + i)) S.empty;
    (S.equal) { }
      S.slice b0 src (src + i) `S.append` S.slice b0 (src + i) (src + i + 1);
    (S.equal) { lemma_slice_ijk b0 src (src + i) (src + i + 1) }
      S.slice b0 src (src + (i + 1));
    };
    let s1 = S.slice b1 (src + (i + 1)) (src + l) in
    let s0 = S.slice b0 (src + (i + 1)) (src + l) in
    let aux (j: nat { j < S.length s0 }): Lemma (S.index s0 j == S.index s1 j)
      [ SMTPat (S.index s0 j); SMTPat (S.index s1 j) ]
    =
      calc (==) {
        S.index s0 j;
      (==) {}
        S.index (S.slice b0 (src + i) (src + l)) (j + 1);
      (==) {}
        S.index (S.slice b1 (src + i) (src + l)) (j + 1);
      (==) {}
        S.index s1 j;
      }
    in
    ()
  in
  C.Loops.for 0ul l inv f


inline_for_extraction
val shrink:
  #a:Type -> vec:vector a ->
  new_size:uint32_t{new_size <= size_of vec} ->
  HST.ST (r:vector a)
  (requires (fun h0 -> live h0 vec /\ freeable vec))
  (ensures (fun h0 r h1 ->
                live h1 vec /\ live h1 r /\ size_of r = new_size /\
                frameOf r = frameOf vec /\
                hmap_dom_eq h0 h1 /\
                freeable r /\
                modifies (loc_vector vec) h0 h1 /\
                loc_vector vec == loc_vector r /\
                S.equal (S.slice (V.as_seq h0 vec) 0 (U32.v new_size))
                        (S.slice (V.as_seq h1 r) 0 (U32.v new_size))))
let shrink #a vec new_size =
  Vec new_size (Vec?.cap vec) (Vec?.vs vec)


inline_for_extraction
val flush_inplace:
  #a:Type -> vec:vector a -> 
  i:uint32_t{i <= size_of vec} ->
  HST.ST (fvec:vector a)
    (requires (fun h0 ->
      live h0 vec /\ freeable vec /\
      HST.is_eternal_region (frameOf vec)))
    (ensures (fun h0 fvec h1 ->
      frameOf vec = frameOf fvec /\
      hmap_dom_eq h0 h1 /\
      live h1 fvec /\ freeable fvec /\
      modifies (loc_vector vec) h0 h1 /\
      loc_vector vec == loc_vector fvec /\
      size_of fvec = size_of vec - i /\
      S.equal (V.as_seq h1 fvec)
              (S.slice (V.as_seq h0 vec) (U32.v i) (U32.v (size_of vec)))))
let flush_inplace #a vec i =
  let h0 = HST.get() in
  if i >= size_of vec then
    shrink vec 0ul
  else if i = 0ul then
    vec
  else begin
    let n_shifted = size_of vec - i in
    move_left (Vec?.vs vec) 0ul i n_shifted;
    shrink vec n_shifted
  end


inline_for_extraction
val rv_flush_inplace: 
  #a:Type0 -> #rst:Type -> #rg:regional rst a ->
  rv:rvector rg -> i:uint32_t{i <= size_of rv} ->
  HST.ST (rvector rg)
    (requires (fun h0 -> rv_inv h0 rv))
    (ensures (fun h0 frv h1 ->
      V.size_of frv = V.size_of rv - i /\
      V.frameOf rv = V.frameOf frv /\
      modifies (loc_rvector rv) h0 h1 /\
      rv_inv h1 frv /\
      S.equal (as_seq h1 frv)
              (S.slice (as_seq h0 rv) (U32.v i) (U32.v (V.size_of rv)))))
let rv_flush_inplace #a #rst #rg rv i =
  let hh0 = HST.get () in
  (if i = 0ul then () else free_elems rv (i - 1ul));
  rv_loc_elems_included hh0 rv 0ul i;

  let hh1 = HST.get () in
  assert (modifies (rs_loc_elems rg (V.as_seq hh0 rv) 0 (U32.v i)) hh0 hh1);
  let frv = flush_inplace rv i in

  let hh2 = HST.get () in
  assert (modifies (loc_region_only false (V.frameOf rv)) hh1 hh2);

  // Safety
  rs_loc_elems_disj
    rg (V.as_seq hh0 rv) (V.frameOf rv) 0 (U32.v (V.size_of rv))
    0 (U32.v i) (U32.v i) (U32.v (V.size_of rv));
  rs_loc_elems_parent_disj
    rg (V.as_seq hh0 rv) (V.frameOf rv)
    (U32.v i) (U32.v (V.size_of rv));
  rs_elems_inv_preserved
    rg (V.as_seq hh0 rv) (U32.v i) (U32.v (V.size_of rv))
    (loc_union (rs_loc_elems rg (V.as_seq hh0 rv) 0 (U32.v i))
               (loc_region_only false (V.frameOf rv)))
    hh0 hh2;
  assert (rv_inv #a #rst #rg hh2 frv);

  // Correctness
  as_seq_seq_preserved
    rg (V.as_seq hh0 rv) (U32.v i) (U32.v (V.size_of rv))
    (loc_union (rs_loc_elems rg (V.as_seq hh0 rv) 0 (U32.v i))
               (loc_region_only false (V.frameOf rv)))
    hh0 hh2;
  as_seq_seq_slice
    rg hh0 (V.as_seq hh0 rv) 0 (U32.v (V.size_of rv))
    (U32.v i) (U32.v (V.size_of rv));
  assert (S.equal (S.slice (as_seq hh0 rv) (U32.v i) (U32.v (V.size_of rv)))
                  (as_seq_seq rg hh2 (V.as_seq hh0 rv)
                    (U32.v i) (U32.v (V.size_of rv))));
  as_seq_seq_eq
    rg hh2 (V.as_seq hh0 rv) (V.as_seq hh2 frv)
    (U32.v i) (U32.v (V.size_of rv)) 0 (U32.v (V.size_of frv));
  assert (S.equal (as_seq_seq rg hh2 (V.as_seq hh2 frv)
                    0 (U32.v (V.size_of frv)))
                  (as_seq_seq rg hh2 (V.as_seq hh0 rv)
                    (U32.v i) (U32.v (V.size_of rv))));
  assert (S.equal (S.slice (as_seq hh0 rv) (U32.v i) (U32.v (V.size_of rv)))
                  (as_seq hh2 frv));
  frv
