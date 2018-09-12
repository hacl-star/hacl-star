module Hacl.SHA1

module B = LowStar.Buffer
module IB = LowStar.ImmutableBuffer
module HS = FStar.HyperStack
module HST = FStar.HyperStack.ST
module Spec = Spec.SHA1
module U8 = FStar.UInt8
module U32 = FStar.UInt32
module E = FStar.Kremlin.Endianness
module CE = C.Endianness
module Common = Hacl.Hash.Common

friend Spec.SHA1

(** Top-level constant arrays for the MD5 algorithm. *)
let _h0 = IB.igcmalloc_of_list HS.root Spec.init_as_list

let alloca () =
  B.alloca_of_list Spec.init_as_list

(* We read values from constant buffers through accessors to isolate
   all recall/liveness issues away. Thus, clients will not need to
   know that their output buffers be disjoint from our constant
   immutable buffers. *)

inline_for_extraction
let h0 (i: U32.t { U32.v i < 5 } ) : HST.Stack U32.t
  (requires (fun _ -> True))
  (ensures (fun h res h' ->
    B.modifies B.loc_none h h' /\
    res == Seq.index Spec.init (U32.v i)
  ))
= IB.recall_contents _h0 Spec.init;
  B.index _h0 i

let init s =
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
let block_t = (block: B.buffer U8.t { B.length block == size_block SHA1 } )

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
    let mi = E.seq_uint32_of_be size_block_w (B.as_seq h m) in
    w_inv' i mi b h
  )

let w_inv_elim (h: HS.mem) (m: Spec.word_block) (b: w_t) (i: nat) (j: nat) : Lemma
  (requires (w_inv' i m b h /\ j < i))
  (ensures (Seq.index (B.as_seq h b) j == Spec.w m (U32.uint_to_t j)))
= ()

let w_loop_inv_elim (h0: Ghost.erased HS.mem) (h: HS.mem) (m: block_t) (b: w_t) (i: nat) (j: nat) : Lemma
  (requires (w_loop_inv h0 m b h i /\ j < i))
  (ensures (Seq.index (B.as_seq h b) j == Spec.w (E.seq_uint32_of_be size_block_w (B.as_seq h m)) (U32.uint_to_t j)))
= ()

inline_for_extraction
let index_32_be' (n: Ghost.erased nat) (b: B.buffer UInt8.t) (i: UInt32.t):
  HST.Stack UInt32.t
    (requires (fun h ->
      B.live h b /\ B.length b == 4 `Prims.op_Multiply` Ghost.reveal n /\
      UInt32.v i < Ghost.reveal n))
    (ensures (fun h0 r h1 ->
      B.(modifies loc_none h0 h1) /\
      r = Seq.index (E.seq_uint32_of_be (Ghost.reveal n) (B.as_seq h0 b)) (UInt32.v i)))
= CE.index_32_be b i

inline_for_extraction
let w_body_value (h0: Ghost.erased HS.mem) (m: block_t) (b: w_t) (i: U32.t) : HST.Stack U32.t
  (requires (fun h -> w_loop_inv h0 m b h (U32.v i) /\ U32.v i < 80))
  (ensures (fun h v h' -> B.modifies B.loc_none h h' /\ v == Spec.w (E.seq_uint32_of_be size_block_w (B.as_seq (Ghost.reveal h0) m)) i))
= if U32.lt i 16ul
  then
    index_32_be' (Ghost.hide size_block_w) m i
  else
    let wmit3 = B.index b (i `U32.sub` 3ul) in
    let wmit8 = B.index b (i `U32.sub` 8ul) in
    let wmit14 = B.index b (i `U32.sub` 14ul) in
    let wmit16 = B.index b (i `U32.sub` 16ul) in
    Spec.rotl 1ul (wmit3 `U32.logxor` wmit8 `U32.logxor` wmit14 `U32.logxor` wmit16)

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
    (ensures (j < U32.v i + 1 /\ Seq.index (B.as_seq h' b) j == Spec.w (E.seq_uint32_of_be size_block_w (B.as_seq (Ghost.reveal h0) m)) (U32.uint_to_t j)))
  = lt_S_r j (U32.v i);
    if j = U32.v i
    then ()
    else w_loop_inv_elim h0 h m b (U32.v i) j
  in
  Classical.forall_intro (Classical.move_requires f)

inline_for_extraction
let w (m: block_t) (b: w_t) : HST.Stack unit
  (requires (fun h -> B.live h m /\ B.live h b /\ B.disjoint m b))
  (ensures (fun h _ h' -> B.modifies (B.loc_buffer b) h h' /\ w_inv (E.seq_uint32_of_be size_block_w (B.as_seq h m)) b h'))
= let h = Ghost.hide (HST.get ()) in
  C.Loops.for 0ul 80ul (w_loop_inv h m b) (fun i -> w_body h m b i)

(*
let equal5 (#t: Type) (s1 s2: Seq.seq t) : GTot Type0 =
  Seq.length s1 == 5 /\
  Seq.length s2 == 5 /\
  Seq.index s1 0 == Seq.index s2 0 /\
  Seq.index s1 1 == Seq.index s2 1 /\
  Seq.index s1 2 == Seq.index s2 2 /\
  Seq.index s1 3 == Seq.index s2 3 /\
  Seq.index s1 4 == Seq.index s2 4

let equal5_spec (#t: Type) (s1 s2: Seq.seq t) : Lemma
  (requires (Seq.length s1 == 5 /\ Seq.length s2 == 5))
  (ensures (equal5 s1 s2 <==> s1 == s2))
  [SMTPat (equal5 s1 s2)]
= assert (equal5 s1 s2 <==> Seq.equal s1 s2)

let seq_index_upd (#a:Type) (s: Seq.seq a) (n:nat{n < Seq.length s}) (v:a) (i:nat{i < Seq.length s}) : Lemma
  (requires True)
  (ensures (Seq.index (Seq.upd s n v) i == (if i = n then v else Seq.index s i)))
  [SMTPat (Seq.index (Seq.upd s n v) i)]
= ()
*)

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
  B.upd b 4ul x4

inline_for_extraction
let step3_body
  (mi: Ghost.erased Spec.word_block)
  (w: w_t)
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
    B.as_seq h' b == Spec.step3_body' (Ghost.reveal mi) (B.as_seq h b) t
  ))
= let _a = B.index b 0ul in
  let _b = B.index b 1ul in
  let _c = B.index b 2ul in
  let _d = B.index b 3ul in
  let _e = B.index b 4ul in
  let wmit = B.index w t in
  let _T = Spec.rotl 5ul _a `U32.add_mod` Spec.f t _b _c _d `U32.add_mod` _e `U32.add_mod` Spec.k t `U32.add_mod` wmit in
  upd5 b _T _a (Spec.rotl 30ul _b) _c _d

inline_for_extraction
let zero_out
  (b: B.buffer U32.t)
  (len: U32.t { U32.v len == B.length b })
: HST.Stack unit
  (requires (fun h -> B.live h b))
  (ensures (fun h _ h' -> B.modifies (B.loc_buffer b) h h' /\ B.live h' b))
= let h0 = HST.get () in
  C.Loops.for 0ul len (fun h _ -> B.live h b /\ B.modifies (B.loc_buffer b) h0 h) (fun i -> B.upd b i 0ul)

let spec_step3_body (mi: Spec.word_block) (st: Ghost.erased (hash_w SHA1)) (t: nat {t < 80}) : Tot (Ghost.erased (hash_w SHA1)) =
  Ghost.elift1 (fun h -> Spec.step3_body mi h t) st

let spec_step3_body_spec (mi: Spec.word_block) (st: Ghost.erased (hash_w SHA1)) (t: nat { t < 80 } ) : Lemma
  (Ghost.reveal (spec_step3_body mi st t) == Spec.step3_body mi (Ghost.reveal st) t)
  [SMTPat (Ghost.reveal (spec_step3_body mi st t))]
= ()

inline_for_extraction
let repeat_range_body_spec
  (a: Type0)
  (max: nat)
: Tot Type
= (a -> i:nat{i < max} -> Tot a)

inline_for_extraction
let repeat_range_body_interp
  (a: Type0)
  (inv: (HS.mem -> GTot Type0))
: Tot Type
= (h: HS.mem { inv h } ) ->
  GTot a

inline_for_extraction
let repeat_range_body_impl
  (#a:Type0)
  (min:UInt32.t)
  (max:UInt32.t{UInt32.v min <= UInt32.v max})
  (f: Ghost.erased (repeat_range_body_spec a (U32.v max)))
  (inv: (HS.mem -> GTot Type0))
  (interp: repeat_range_body_interp a inv)
: Tot Type
= (i:UInt32.t{UInt32.v min <= UInt32.v i /\ UInt32.v i < UInt32.v max}) ->
  HST.Stack unit
  (requires (fun h -> inv h))
  (ensures (fun h0 _ h1 ->
    inv h0 /\ inv h1 /\
    interp h1 == (Ghost.reveal f) (interp h0) (UInt32.v i)
  ))

inline_for_extraction
val repeat_range:
  #a:Type0 ->
  min:UInt32.t ->
  max:UInt32.t{UInt32.v min <= UInt32.v max} ->
  f: (Ghost.erased (repeat_range_body_spec a (U32.v max))) ->
  inv: (HS.mem -> GTot Type0) ->
  interp: repeat_range_body_interp a inv ->
  fc: repeat_range_body_impl min max f inv interp ->
  HST.Stack unit
    (requires (fun h -> inv h))
    (ensures (fun h_1 _ h_2 ->
      inv h_1 /\ inv h_2 /\
      interp h_2 == Spec.Loops.repeat_range (U32.v min) (U32.v max) (Ghost.reveal f) (interp h_1)
    ))

let repeat_range #a min max f inv interp fc =
  let h0 = HST.get() in
  let inv' (h1: HS.mem) (i: nat): Type0 =
    inv h1 /\
    i <= UInt32.v max /\ UInt32.v min <= i /\
    interp h1 == Spec.Loops.repeat_range (UInt32.v min) i (Ghost.reveal f) (interp h0)
  in
  let f' (i:UInt32.t{ U32.( 0 <= v i /\ v i < v max ) }): HST.Stack unit
    (requires (fun h -> inv' h (UInt32.v i)))
    (ensures (fun h_1 _ h_2 -> U32.(inv' h_2 (v i + 1))))
  =
    fc i;
    Spec.Loops.repeat_range_induction (UInt32.v min) (UInt32.v i + 1) (Ghost.reveal f) (interp h0)
  in
  Spec.Loops.repeat_range_base (UInt32.v min) (Ghost.reveal f) (interp h0);
  C.Loops.for min max inv' f'

#set-options "--z3rlimit 32"

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
    B.as_seq h1 h == Spec.step3 (E.seq_uint32_of_be size_block_w (B.as_seq h0 m)) (B.as_seq h0 h)
  ))
= let h0 = HST.get () in
  HST.push_frame ();
  let _w = B.alloca 0ul 80ul in
  w m _w;
  let mi = Ghost.hide (E.seq_uint32_of_be size_block_w (B.as_seq h0 m)) in
  let h1 = HST.get () in
  let f : Ghost.erased (repeat_range_body_spec (hash_w SHA1) 80) = Ghost.hide (Spec.step3_body (Ghost.reveal mi)) in
  let inv (h' : HS.mem) : GTot Type0 =
    B.modifies (B.loc_buffer h) h1 h' /\
    B.live h' h
  in
  let interp (h' : HS.mem { inv h' } ) : GTot (hash_w SHA1) =
    B.as_seq h' h
  in
  repeat_range 0ul 80ul f inv interp (fun i -> step3_body mi _w h i);
  zero_out _w 80ul;
  HST.pop_frame ();
  ()

#reset-options

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
    B.as_seq h1 h == Spec.step4 (E.seq_uint32_of_be size_block_w (B.as_seq h0 m)) (B.as_seq h0 h)
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
    (sta `U32.add_mod` ha)
    (stb `U32.add_mod` hb)
    (stc `U32.add_mod` hc)
    (std `U32.add_mod` hd)
    (ste `U32.add_mod` he)

let update h l =
  step4 l h

let pad: pad_st SHA1 =
  FStar.Tactics.(synth_by_tactic (specialize (Common.pad SHA1) [`%Common.pad]))
