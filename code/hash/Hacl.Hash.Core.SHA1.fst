module Hacl.Hash.Core.SHA1

open Lib.IntTypes
module B = LowStar.Buffer
module IB = LowStar.ImmutableBuffer
module HS = FStar.HyperStack
module HST = FStar.HyperStack.ST
module Spec = Spec.SHA1
module U32 = FStar.UInt32

open Hacl.Hash.Definitions
open Spec.Hash.Definitions

friend Spec.SHA1
friend Hacl.Hash.PadFinish
friend Spec.Agile.Hash

#reset-options "--max_fuel 0 --max_ifuel 0 --z3rlimit 100"

(** Top-level constant arrays for the MD5 algorithm. *)
let _h0 = IB.igcmalloc_of_list HS.root Spec.init_as_list

noextract inline_for_extraction
let legacy_alloca () =
  B.alloca_of_list Spec.init_as_list

(* We read values from constant buffers through accessors to isolate
   all recall/liveness issues away. Thus, clients will not need to
   know that their output buffers be disjoint from our constant
   immutable buffers. *)

inline_for_extraction
let h0 (i: U32.t { U32.v i < 5 } ) : HST.Stack uint32
  (requires (fun _ -> True))
  (ensures (fun h res h' ->
    B.modifies B.loc_none h h' /\
    res == Seq.index Spec.init (U32.v i)
  ))
= IB.recall_contents _h0 Spec.init;
  B.index _h0 i

let legacy_init s =
  let h = HST.get () in
  let inv (h' : HS.mem) (i: nat) : GTot Type0 =
    B.live h' s /\ B.modifies (B.loc_buffer s) h h' /\ i <= 5 /\ Seq.slice (B.as_seq h' s) 0 i == Seq.slice Spec.init 0 i
  in
  C.Loops.for 0ul 5ul inv (fun i ->
    B.upd s i (h0 i);
    let h' = HST.get () in
    Seq.snoc_slice_index (B.as_seq h' s) 0 (U32.v i);
    Seq.snoc_slice_index (Spec.init) 0 (U32.v i)
  )

inline_for_extraction
let w_t = (b: B.lbuffer (word SHA1) 80)

inline_for_extraction
let block_t = (block: B.buffer uint8 { B.length block == block_length SHA1 } )

let w_inv' (i: nat) (mi: Spec.word_block) (b: w_t) (h: HS.mem) : GTot Type0 =
  i <= 80 /\
  B.live h b /\ (
    let s = B.as_seq h b in
    (forall (j: nat) .  {:pattern (Seq.index s j) } (j < i) ==> Spec.w mi (U32.uint_to_t j) == Seq.index s j)
  )

let w_inv = w_inv' 80

let w_loop_inv (h0: Ghost.erased HS.mem) (m: block_t) (b: w_t) (h: HS.mem) (i: nat) : GTot Type0 =
  let h0 = Ghost.reveal h0 in
  i <= 80 /\
  B.disjoint m b /\
  B.live h0 m /\
  B.live h m /\
  B.live h b /\
  B.modifies (B.loc_buffer b) h0 h /\ (
    let mi = Lib.ByteSequence.uints_from_bytes_be #U32 #SEC #block_word_length (B.as_seq h m) in
    w_inv' i mi b h
  )

let w_inv_elim (h: HS.mem) (m: Spec.word_block) (b: w_t) (i: nat) (j: nat) : Lemma
  (requires (w_inv' i m b h /\ j < i))
  (ensures (Seq.index (B.as_seq h b) j == Spec.w m (U32.uint_to_t j)))
= ()

let w_loop_inv_elim (h0: Ghost.erased HS.mem) (h: HS.mem) (m: block_t) (b: w_t) (i: nat) (j: nat) : Lemma
  (requires (w_loop_inv h0 m b h i /\ j < i))
  (ensures (Seq.index (B.as_seq h b) j == Spec.w (Lib.ByteSequence.uints_from_bytes_be #U32 #SEC #block_word_length (B.as_seq h m)) (U32.uint_to_t j)))
= ()

inline_for_extraction
let index_32_be' (n: UInt32.t) (b: B.buffer uint8) (i: UInt32.t):
  HST.Stack uint32
    (requires (fun h ->
      B.live h b /\ B.length b == 4 `Prims.op_Multiply` UInt32.v n /\
      UInt32.v i < UInt32.v n))
    (ensures (fun h0 r h1 ->
      B.(modifies loc_none h0 h1) /\
      r == Seq.index (Lib.ByteSequence.uints_from_bytes_be #U32 #SEC #(v n) (B.as_seq h0 b)) (UInt32.v i)))
= Lib.ByteBuffer.uint_at_index_be #U32 #SEC #n b i

#push-options "--max_fuel 1"
inline_for_extraction
let w_body_value (h0: Ghost.erased HS.mem) (m: block_t) (b: w_t) (i: U32.t) : HST.Stack uint32
  (requires (fun h -> w_loop_inv h0 m b h (U32.v i) /\ U32.v i < 80))
  (ensures (fun h v h' -> B.modifies B.loc_none h h' /\ v == 
		       Spec.w (Lib.ByteSequence.uints_from_bytes_be #U32 #SEC #block_word_length (B.as_seq (Ghost.reveal h0) m)) i))
=
  if U32.lt i 16ul then
    index_32_be' (size block_word_length) m i
  else
    let wmit3 = B.index b (i `U32.sub` 3ul) in
    let wmit8 = B.index b (i `U32.sub` 8ul) in
    let wmit14 = B.index b (i `U32.sub` 14ul) in
    let wmit16 = B.index b (i `U32.sub` 16ul) in
    (wmit3 ^. wmit8 ^. wmit14 ^. wmit16) <<<. 1ul 
#pop-options

let lt_S_r (j i: nat) : Lemma
  (requires (j < i + 1))
  (ensures (j = i \/ j < i))
= ()

inline_for_extraction
let w_body (h0: Ghost.erased HS.mem) (m: block_t) (b: w_t) (i: U32.t { U32.v i < 80 }) : HST.Stack unit
  (requires (fun h -> w_loop_inv h0 m b h (U32.v i)))
  (ensures (fun _ _ h' -> w_loop_inv h0 m b h' (U32.v i + 1)))
= let h = HST.get () in
  let v = w_body_value h0 m b i in
  B.upd b i v;
  let h' = HST.get () in
  let f (j: nat) : Lemma
    (requires (j < U32.v i + 1))
    (ensures (j < U32.v i + 1 /\ 
	      Seq.index (B.as_seq h' b) j == 
	      Spec.w (Lib.ByteSequence.uints_from_bytes_be #U32 #SEC #block_word_length (B.as_seq (Ghost.reveal h0) m)) (U32.uint_to_t j)))
  = lt_S_r j (U32.v i);
    if j = U32.v i
    then ()
    else w_loop_inv_elim h0 h m b (U32.v i) j
  in
  Classical.forall_intro (Classical.move_requires f)

inline_for_extraction
let w (m: block_t) (b: w_t) : HST.Stack unit
  (requires (fun h -> B.live h m /\ B.live h b /\ B.disjoint m b))
  (ensures (fun h _ h' -> B.modifies (B.loc_buffer b) h h' /\ w_inv 
		       (Lib.ByteSequence.uints_from_bytes_be #U32 #SEC #block_word_length (B.as_seq h m)) b h'))
= let h = Ghost.hide (HST.get ()) in
  C.Loops.for 0ul 80ul (w_loop_inv h m b) (fun i -> w_body h m b i)

inline_for_extraction
let upd5
  (#t: Type)
  (b: B.buffer t { B.length b == 5 } )
  (x0 x1 x2 x3 x4: t)
: HST.Stack unit
  (requires (fun h -> B.live h b))
  (ensures (fun h _ h' ->
    B.modifies (B.loc_buffer b) h h' /\
    B.live h' b /\
    B.as_seq h' b `Seq.equal` Seq.seq_of_list [x0; x1; x2; x3; x4]
  ))
= B.upd b 0ul x0;
  B.upd b 1ul x1;
  B.upd b 2ul x2;
  B.upd b 3ul x3;
  B.upd b 4ul x4;
  // JP: why define this helper instead of letting callers call intro_of_list?
  let h = FStar.HyperStack.ST.get () in
  [@inline_let]
  let l = [ x0; x1; x2; x3; x4 ] in
  assert_norm (List.length l = 5);
  Seq.intro_of_list (B.as_seq h b) l

inline_for_extraction
let step3_body
  (mi: Ghost.erased Spec.word_block)
  (w: w_t)
  (gw: Ghost.erased (Spec.step3_body_w_t (Ghost.reveal mi)))
  (b: state SHA1)
  (t: U32.t {U32.v t < 80})
: HST.Stack unit
  (requires (fun h ->
    w_inv (Ghost.reveal mi) w h /\
    B.live h b /\
    B.disjoint w b
  ))
  (ensures (fun h _ h' ->
    B.modifies (B.loc_buffer b) h h' /\
    B.as_seq h' b == Spec.step3_body' (Ghost.reveal mi) (B.as_seq h b) t (Ghost.reveal gw (U32.v t))
  ))
= let _a = B.index b 0ul in
  let _b = B.index b 1ul in
  let _c = B.index b 2ul in
  let _d = B.index b 3ul in
  let _e = B.index b 4ul in
  let wmit = B.index w t in
  let _T = (_a <<<. 5ul) +. Spec.f t _b _c _d +. _e  +. Spec.k t +. wmit in
  upd5 b _T _a (_b <<<. 30ul) _c _d;
  reveal_opaque (`%Spec.step3_body') Spec.step3_body'

inline_for_extraction
let zero_out
  (b: B.buffer uint32)
  (len: U32.t { U32.v len == B.length b })
: HST.Stack unit
  (requires (fun h -> B.live h b))
  (ensures (fun h _ h' -> B.modifies (B.loc_buffer b) h h' /\ B.live h' b))
= let h0 = HST.get () in
  C.Loops.for 0ul len (fun h _ -> B.live h b /\ B.modifies (B.loc_buffer b) h0 h) (fun i -> B.upd b i (u32 0))

let spec_step3_body
  (mi: Spec.word_block)
  (gw: Ghost.erased (Spec.step3_body_w_t mi))
  (st: Ghost.erased (words_state SHA1))
  (t: nat {t < 80})
: Tot (Ghost.erased (words_state SHA1))
= Ghost.elift1 (fun h -> Spec.step3_body mi (Ghost.reveal gw) h t) st

let spec_step3_body_spec
  (mi: Spec.word_block)
  (gw: Ghost.erased (Spec.step3_body_w_t mi))
  (st: Ghost.erased (words_state SHA1)) (t: nat { t < 80 } )
: Lemma
  (Ghost.reveal (spec_step3_body mi gw st t) == Spec.step3_body mi (Ghost.reveal gw) (Ghost.reveal st) t)
  [SMTPat (Ghost.reveal (spec_step3_body mi gw st t))]
= ()

inline_for_extraction
let step3
  (m: block_t)
  (h: state SHA1)
: HST.Stack unit
  (requires (fun h0 ->
    B.live h0 m /\
    B.live h0 h /\
    B.disjoint m h
  ))
  (ensures (fun h0 _ h1 ->
    B.modifies (B.loc_buffer h) h0 h1 /\
    B.live h1 h /\
    B.as_seq h1 h == Spec.step3 
	     (Lib.ByteSequence.uints_from_bytes_be #U32 #SEC #block_word_length (B.as_seq h0 m)) (B.as_seq h0 h)
  ))
= let h0 = HST.get () in
  HST.push_frame ();
  let _w = B.alloca (u32 0) 80ul in
  w m _w;
  let mi = Ghost.hide (
      Lib.ByteSequence.uints_from_bytes_be #U32 #SEC #block_word_length (B.as_seq h0 m)) in
  let h1 = HST.get () in
  let cwt = Ghost.hide (Spec.compute_w (Ghost.reveal mi) 0 Seq.empty) in
  let gw: Ghost.erased (Spec.step3_body_w_t (Ghost.reveal mi)) =
    Ghost.elift1 (Spec.index_compute_w (Ghost.reveal mi)) cwt
  in
  let f : Ghost.erased (C.Loops.repeat_range_body_spec (words_state SHA1) 80) = Ghost.hide (Spec.step3_body (Ghost.reveal mi) (Ghost.reveal gw)) in
  let inv (h' : HS.mem) : GTot Type0 =
    B.modifies (B.loc_buffer h) h1 h' /\
    B.live h' h
  in
  let interp (h' : HS.mem { inv h' } ) : GTot (words_state SHA1) =
    B.as_seq h' h
  in
  C.Loops.repeat_range 0ul 80ul f inv interp (fun i -> step3_body mi _w gw h i);
  zero_out _w 80ul;
  HST.pop_frame ();
  reveal_opaque (`%Spec.step3) Spec.step3

inline_for_extraction
let step4
  (m: block_t)
  (h: state SHA1)
: HST.Stack unit
  (requires (fun h0 ->
    B.live h0 m /\
    B.live h0 h /\
    B.disjoint m h
  ))
  (ensures (fun h0 _ h1 ->
    B.modifies (B.loc_buffer h) h0 h1 /\
    B.live h1 h /\
      B.as_seq h1 h == Spec.step4 
	       (Lib.ByteSequence.uints_from_bytes_be #U32 #SEC #block_word_length (B.as_seq h0 m)) 
	       (B.as_seq h0 h)
  ))
= let ha = B.index h 0ul in
  let hb = B.index h 1ul in
  let hc = B.index h 2ul in
  let hd = B.index h 3ul in
  let he = B.index h 4ul in
  step3 m h;
  let sta = B.index h 0ul in
  let stb = B.index h 1ul in
  let stc = B.index h 2ul in
  let std = B.index h 3ul in
  let ste = B.index h 4ul in
  upd5
    h
    (sta +. ha)
    (stb +. hb)
    (stc +. hc)
    (std +. hd)
    (ste +. he);
  reveal_opaque (`%Spec.step4) Spec.step4

let legacy_update h l =
  step4 l h

let legacy_pad: pad_st SHA1 = Hacl.Hash.PadFinish.pad SHA1

let legacy_finish: finish_st SHA1 = Hacl.Hash.PadFinish.finish SHA1
