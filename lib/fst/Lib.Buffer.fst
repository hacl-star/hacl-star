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

let concat2 #a len0 s0 len1 s1 s =
  let h0 = ST.get () in
  update_sub s (size 0) len0 s0;
  update_sub s len0 len1 s1;
  let h1 = ST.get () in
  Seq.eq_intro (Seq.sub (as_seq h1 s) 0 (v len0)) (as_seq h0 s0);
  Seq.lemma_concat2 (v len0) (as_seq h0 s0) (v len1) (as_seq h0 s1) (as_seq h1 s)

let concat3 #a len0 s0 len1 s1 len2 s2 s =
  let h0 = ST.get () in
  update_sub s (size 0) len0 s0;
  update_sub s len0 len1 s1;
  let h1 = ST.get () in
  Seq.eq_intro (Seq.sub (as_seq h1 s) 0 (v len0)) (as_seq h0 s0);
  update_sub s (len0 +! len1) len2 s2;
  let h2 = ST.get () in
  Seq.eq_intro (Seq.sub (as_seq h2 s) 0 (v len0)) (as_seq h0 s0);
  Seq.eq_intro (Seq.sub (as_seq h2 s) (v len0) (v len1)) (as_seq h0 s1);
  Seq.lemma_concat3 (v len0) (as_seq h0 s0) (v len1) (as_seq h0 s1) (v len2) (as_seq h0 s2) (as_seq h2 s)

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
let salloc1_trivial #a #res h len x footprint spec impl =
  let trivial (#res:Type) (h1 h2 h3:mem) (r:res) = () in
  salloc1 h len x footprint spec trivial impl

inline_for_extraction noextract
let salloc_nospec #a #res h len x footprint impl =
  (* BB. `a` is a random type because it is unused, is there a better solution ? *)
  let spec (z:res) (h0:mem) = a in
  let spec_inv (#res:Type) (h1 h2 h3:mem) (r:res) = () in
  salloc1 #a #res h len x footprint spec spec_inv impl

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

#reset-options "--z3rlimit 100 --max_fuel 0 --max_ifuel 0"

let fill_blocks #t h0 len n output a_spec refl footprint spec impl =
  [@inline_let]
  let a_spec' (i:nat{i <= v n}) =
    assert_spinoff (i * v len <= max_size_t);
    a_spec i & Seq.lseq t (i * v len) in
  [@inline_let]
  let refl' h (i:nat{i <= v n}) : GTot (a_spec' i) =
    refl h i, as_seq #_ #(i * v len) h (gsub output (size 0) (size i *! len))
  in
  let footprint' i = B.loc_union (footprint i) (B.loc_buffer output) in
  [@inline_let]
  let spec' h0 : GTot (i:nat{i < v n} -> a_spec' i -> a_spec' (i + 1)) =
    let f = spec h0 in
    fun i so ->
      let s, o = so <: a_spec i & Seq.lseq t (i * v len) in
      let s', block = f i s in
      let o' : Seq.lseq t ((i + 1) * v len) = Seq.(o @| block) in
      s', o'
  in
  let h0 = ST.get () in
  loop h0 n a_spec' refl' footprint' spec'
  (fun i ->
    Loop.unfold_repeat_gen (v n) a_spec' (spec' h0) (refl' h0 0) (v i);
    let block = B.sub output (i *! len) len in
    impl i block;
    let h = ST.get() in
    B.loc_includes_union_l (footprint (v i + 1)) (B.loc_buffer output) (B.loc_buffer block);
    B.loc_includes_union_l (footprint (v i + 1)) (B.loc_buffer output) (footprint (v i + 1));
    assert ((v i + 1) * v len == v i * v len + v len);
    FStar.Seq.lemma_split
      (as_seq #_ #(v i * v len + v len) h (gsub output (size 0) (i *! len +! len)))
      (v i * v len)
  );
  assert (Seq.equal
    (as_seq #_ #0 h0 (gsub output (size 0) (size 0 *! len))) FStar.Seq.empty);
  assert_norm (
    Seq.generate_blocks (v len) (v n) a_spec (spec h0) (refl h0 0) ==
    norm [delta] Seq.generate_blocks (v len) (v n) a_spec (spec h0) (refl h0 0))

#set-options "--max_fuel 1"

let fillT #a clen o spec f =
  let open Seq in
  let h0 = ST.get () in
  let a_spec = createi_a a (v clen) spec in
  let refl h i = sub (as_seq h o) 0 i in
  let footprint i = B.loc_buffer o in
  let spec h = createi_step a (v clen) spec in
  loop h0 clen a_spec refl footprint spec
    (fun i ->
      Loop.unfold_repeat_gen (v clen) a_spec (spec h0) (of_list #a []) (v i);
      o.(i) <- f i;
      let h' = ST.get () in
      FStar.Seq.lemma_split (as_seq h' o) (v i)
    )

let fill #a h0 clen o spec impl = 
  let open Seq in
  let h0 = ST.get() in
  let a_spec = createi_a a (v clen) (spec h0) in
  let refl h i = sub (as_seq h o) 0 i in
  let footprint i = B.loc_buffer o in
  let spec h = createi_step a (v clen) (spec h0) in
  loop h0 clen a_spec refl footprint spec
  (fun i ->
    Loop.unfold_repeat_gen (v clen) a_spec (spec h0) (of_list #a []) (v i);
    impl i;
    let h' = ST.get () in
    FStar.Seq.lemma_split (as_seq h' o) (v i)
  )

#set-options "--max_fuel 0"

let mapT #a #b clen out f inp = 
  let h0 = ST.get () in
  fill h0 clen out
    (fun h -> let in_seq = as_seq h inp in Seq.map_inner f in_seq)
    (fun i -> out.(i) <- f inp.(i))

let mapiT #a #b clen out spec_f f inp = 
  let h0 = ST.get () in
  fill h0 clen out
    (fun h -> let in_seq = as_seq h inp in Seq.mapi_inner spec_f in_seq)
    (fun i -> let xi = inp.(i) in out.(i) <- f i xi)

let imapT #a #b #len out clen f inp = 
  let h0 = ST.get () in
  fill h0 clen out
    (fun h -> let in_seq = ias_seq h inp in Seq.map_inner f in_seq)
    (fun i -> out.(i) <- f (iindex inp i))

// 2018.11.1 SZ: This function is unspecified in Lib.Buffer.fsti (and thus visible only to friends). Do we need this function? What's the spec?
let mapi #a #b h0 clen out inp spec impl = 
  let h0 = ST.get () in
  fill h0 clen out
    (fun h -> let in_seq = as_seq h inp in Seq.mapi_inner #a #b #(v clen) spec in_seq)
    (fun i -> impl i)
