module Lib.Buffer

open FStar.HyperStack
open FStar.HyperStack.ST
open FStar.Mul

open Lib.IntTypes
open Lib.RawIntTypes

friend Lib.Sequence
friend Lib.LoopCombinators

module B = LowStar.Buffer
module IB = LowStar.ImmutableBuffer
module U32 = FStar.UInt32
module ST = FStar.HyperStack.ST
module HS = FStar.HyperStack
module Seq = Lib.Sequence
module ByteSeq = Lib.ByteSequence


#set-options "--z3rlimit 100"


let length #a b = B.length b

let ilength #a b = IB.length b

let as_seq_gsub #a #len h b start n = ()

let sub #a #len #olen b start n =
  B.sub b (size_to_UInt32 start) (size_to_UInt32 n)

let as_seq_igsub #a #len h b start n = ()

let isub #a #len #olen b start n =
  IB.isub b (size_to_UInt32 start) (size_to_UInt32 n)

let index #a #len b i =
  B.index b (size_to_UInt32 i)

let iindex #a #len b i =
  IB.index b (size_to_UInt32 i)

let upd #a #len b i v =
  B.upd b (size_to_UInt32 i) v

let bget #a #len h b i =
  FStar.Seq.index #a (B.as_seq h b) i

let ibget #a #len h b i =
  FStar.Seq.index #a (IB.as_seq h b) i

let create #a #len clen init =
  B.alloca init (normalize_term (size_to_UInt32 clen))

let createL #a init =
  B.alloca_of_list init

let recall #a #len b = B.recall b

let createL_global #a init =
  B.gcmalloc_of_list HyperStack.root init

let icreateL_global #a init =
  IB.igcmalloc_of_list #a root init

let recall_contents #a #len b s =
  B.recall_p b (cpred s)

let copy #a #len o clen i =
  let h0 = ST.get () in
  LowStar.BufferOps.blit i (size_to_UInt32 (size 0)) o (size_to_UInt32 (size 0)) (size_to_UInt32 clen);
  let h1 = ST.get () in
  assert (Seq.slice #a #len (B.as_seq h1 o) 0 len == Seq.slice #a #len (B.as_seq h0 i) 0 len)

let icopy #a #len o clen i =
  let h0 = ST.get () in
  LowStar.BufferOps.blit i (size_to_UInt32 (size 0)) o (size_to_UInt32 (size 0)) (size_to_UInt32 clen);
  let h1 = ST.get () in
  assert (Seq.slice #a #len (B.as_seq h1 o) 0 len == Seq.slice #a #len (B.as_seq h0 i) 0 len)

let memset #a #blen b init len =
  B.fill #a b init len

let update_sub #a #len dst start n src =
  let h0 = ST.get () in
  LowStar.BufferOps.blit src 0ul dst (size_to_UInt32 start) (size_to_UInt32 n);
  let h1 = ST.get () in
  assert (forall (k:nat{k < v n}). bget h1 dst (v start + k) == bget h0 src k);
  FStar.Seq.lemma_eq_intro
    (B.as_seq h1 dst)
    (Seq.update_sub #a #len (B.as_seq h0 dst) (v start) (v n) (B.as_seq h0 src))

let update_isub #a #len dst start n src =
  let h0 = ST.get () in
  LowStar.BufferOps.blit src 0ul dst (size_to_UInt32 start) (size_to_UInt32 n);
  let h1 = ST.get () in
  assert (forall (k:nat{k < v n}). bget h1 dst (v start + k) == ibget h0 src k);
  FStar.Seq.lemma_eq_intro
    (B.as_seq h1 dst)
    (Seq.update_sub #a #len (B.as_seq h0 dst) (v start) (v n) (IB.as_seq h0 src))

let update_sub_f #a #len h0 buf start n spec f =
  let h0 = ST.get () in
  let tmp = sub buf start n in
  f tmp;
  let h1 = ST.get () in
  B.modifies_buffer_elim (sub #_ #len #(v start) buf (size 0) start) (B.loc_buffer tmp) h0 h1;
  B.modifies_buffer_elim (sub #_ #len #(len - v start - v n) buf (start +! n) (size len -. start -. n)) (B.loc_buffer tmp) h0 h1;
  Sequence.lemma_update_sub #a #len (B.as_seq h0 buf) (v start) (v n) (spec h0) (B.as_seq h1 buf)

let loop_nospec #h0 #a #len n buf impl =
  let inv h1 j = B.modifies (B.loc_buffer buf) h0 h1 in
  Lib.Loops.for (size 0) n inv impl

let loop h0 n a_spec refl footprint spec impl =
  let inv h i = loop_inv h0 n a_spec refl footprint spec i h in
  Lib.Loops.for (size 0) n inv impl

let loop1 #b #blen h0 n acc spec impl =
  let inv h i = loop1_inv h0 n b blen acc spec i h in
  Lib.Loops.for (size 0) n inv impl

let loop2 #b0 #blen0 #b1 #blen1 h0 n acc0 acc1 spec impl =
  let inv h i = loop2_inv #b0 #blen0 #b1 #blen1 h0 n acc0 acc1 spec i h in
  Lib.Loops.for (size 0) n inv impl

let salloc1 #a #res h len x footprint spec spec_inv impl =
  let h0 = ST.get() in
  push_frame();
  let h1 = ST.get() in
  B.fresh_frame_modifies h0 h1;
  let b = B.alloca x len in
  let h2 = ST.get() in
  let r = impl b in
  let h3 = ST.get() in
  memset #a #(v len) b x len;
  let h4 = ST.get() in
  pop_frame();
  let h5 = ST.get() in
  B.popped_modifies h4 h5;
  spec_inv h2 h3 h5 r;
  r

inline_for_extraction noextract
val loopi_blocks_f:
    #a:Type0
  -> #b:Type0
  -> #blen:size_nat
  -> blocksize:size_t{v blocksize > 0}
  -> inpLen:size_t
  -> inp:lbuffer a (v inpLen)
  -> spec_f:(i:nat{i < v inpLen / v blocksize}
              -> Seq.lseq a (v blocksize)
              -> Seq.lseq b blen
              -> Seq.lseq b blen)
  -> f:(i:size_t{v i < v inpLen / v blocksize}
       -> inp:lbuffer a (v blocksize)
       -> w:lbuffer b blen -> Stack unit
          (requires fun h ->
            B.live h inp /\ B.live h w /\ B.disjoint inp w)
          (ensures  fun h0 _ h1 ->
            B.modifies (B.loc_buffer w) h0 h1 /\
            B.as_seq h1 w == spec_f (v i) (B.as_seq h0 inp) (B.as_seq h0 w)))
  -> nb:size_t{v nb == v inpLen / v blocksize}
  -> i:size_t{v i < v nb}
  -> w:lbuffer b blen ->
  Stack unit
    (requires fun h -> live h inp /\ live h w /\ disjoint inp w)
    (ensures  fun h0 _ h1 ->
      B.modifies (B.loc_buffer w) h0 h1 /\
      as_seq h1 w ==
      Sequence.repeati_blocks_f (v blocksize) (as_seq h0 inp) spec_f (v nb) (v i) (as_seq h0 w))

let loopi_blocks_f #a #b #blen bs inpLen inp spec_f f nb i w =
  assert ((v i + 1) * v bs <= v nb * v bs);
  let block = sub #_ #(v inpLen) inp (i *. bs) bs in
  f i block w

let loopi_blocks #a #b #blen bs inpLen inp spec_f spec_l f l w =
  let nb = inpLen /. bs in
  let rem = inpLen %. bs in
  [@ inline_let]
  let spec_fh h0 = Seq.repeati_blocks_f (v bs) (as_seq h0 inp) spec_f (v nb) in
  let h0 = ST.get () in
  loop1 #b #blen h0 nb w spec_fh
  (fun i ->
    Loop.unfold_repeati (v nb) (spec_fh h0) (as_seq h0 w) (v i);
    loopi_blocks_f #a #b #blen bs inpLen inp spec_f f nb i w);
  let last = sub #_ #(v inpLen)  inp (nb *. bs) rem in
  l nb rem last w

inline_for_extraction noextract
val loop_blocks_f:
    #a:Type0
  -> #b:Type0
  -> #blen:size_nat
  -> blocksize:size_t{v blocksize > 0}
  -> inpLen:size_t
  -> inp:lbuffer a (v inpLen)
  -> spec_f:(Seq.lseq a (v blocksize)
              -> Seq.lseq b blen
              -> Seq.lseq b blen)
  -> f:(inp:lbuffer a (v blocksize)
       -> w:lbuffer b blen -> Stack unit
          (requires fun h ->
            B.live h inp /\ B.live h w /\ B.disjoint inp w)
          (ensures  fun h0 _ h1 ->
            B.modifies (B.loc_buffer w) h0 h1 /\
            B.as_seq h1 w == spec_f (B.as_seq h0 inp) (B.as_seq h0 w)))
  -> nb:size_t{v nb == v inpLen / v blocksize}
  -> i:size_t{v i < v nb}
  -> w:lbuffer b blen ->
  Stack unit
    (requires fun h -> live h inp /\ live h w /\ disjoint inp w)
    (ensures  fun h0 _ h1 ->
      B.modifies (B.loc_buffer w) h0 h1 /\
      as_seq h1 w ==
      Sequence.repeat_blocks_f (v blocksize) (as_seq h0 inp) spec_f (v nb) (v i) (as_seq h0 w))

let loop_blocks_f #a #b #blen bs inpLen inp spec_f f nb i w =
  assert ((v i + 1) * v bs <= v nb * v bs);
  let block = sub #_ #(v inpLen) inp (i *. bs) bs in
  f block w

let loop_blocks #a #b #blen bs inpLen inp spec_f spec_l f l w =
  let nb = inpLen /. bs in
  let rem = inpLen %. bs in
  [@ inline_let]
  let spec_fh h0 = Seq.repeat_blocks_f (v bs) (as_seq h0 inp) spec_f (v nb) in
  let h0 = ST.get () in
  loop1 #b #blen h0 nb w spec_fh
  (fun i ->
    Loop.unfold_repeati (v nb) (spec_fh h0) (as_seq h0 w) (v i);
    loop_blocks_f #a #b #blen bs inpLen inp spec_f f nb i w);
  let last = sub #_ #(v inpLen)  inp (nb *. bs) rem in
  l rem last w


let mapT #a #b #len o clen f inp = 
  let h0 = ST.get () in
  loop_nospec #h0 clen o (fun i -> o.(i) <- f inp.(i));
  admit()

let imapT #a #b #len o clen f inp = 
  let h0 = ST.get () in
  loop_nospec #h0 clen o (fun i -> o.(i) <- f (iindex inp i));
  admit()

