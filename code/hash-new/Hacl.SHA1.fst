module Hacl.SHA1

include Hacl.Hash.Common
open Spec.Hash.Helpers

module B = LowStar.Buffer
module IB = LowStar.ImmutableBuffer
module HS = FStar.HyperStack
module HST = FStar.HyperStack.ST
module Spec = Spec.SHA1
module U8 = FStar.UInt8
module U32 = FStar.UInt32
module E = FStar.Kremlin.Endianness
module CE = C.Endianness

friend Spec.SHA1

(** Top-level constant arrays for the MD5 algorithm. *)
let h0 = IB.igcmalloc_of_list HS.root Spec.init_as_list


let alloca () =
  B.alloca_of_list Spec.init_as_list

let static_fp () =
  B.loc_addr_of_buffer h0

let recall_static_fp () =
  B.recall h0

let init s =
  IB.recall_contents h0 (Seq.seq_of_list Spec.init_as_list);
  B.blit h0 0ul s 0ul 5ul

let working_state_of_seq (s: hash_w SHA1) : GTot Spec.working_state =
  {
    Spec.a = Seq.index s 0;
    Spec.b = Seq.index s 1;
    Spec.c = Seq.index s 2;
    Spec.d = Seq.index s 3;
    Spec.e = Seq.index s 4;
  }

let seq_of_working_state (s: Spec.working_state) : GTot (hash_w SHA1) =
  (Seq.seq_of_list [
    s.Spec.a;
    s.Spec.b;
    s.Spec.c;
    s.Spec.d;
    s.Spec.e;
  ])

let seq_of_working_state_of_seq (s: hash_w SHA1) : Lemma
  (seq_of_working_state (working_state_of_seq s) `Seq.equal` s)
  [SMTPat (seq_of_working_state (working_state_of_seq s))]
= ()

let working_state_of_seq_of_working_state (s: Spec.working_state) : Lemma
  (working_state_of_seq (seq_of_working_state s) == s)
  [SMTPat (working_state_of_seq (seq_of_working_state s))]
= ()

// NOTE: working_state_of_buffer MUST NOT be directly defined in terms
// of working_state_of_seq. If it is, then step3_body below will not
// typecheck

let working_state_of_buffer (h: HS.mem) (s: state SHA1) : GTot Spec.working_state =
  let s = B.as_seq h s in {
    Spec.a = Seq.index s 0;
    Spec.b = Seq.index s 1;
    Spec.c = Seq.index s 2;
    Spec.d = Seq.index s 3;
    Spec.e = Seq.index s 4;
  }

let working_state_of_buffer_eq (h: HS.mem) (s: state SHA1) : Lemma
  (working_state_of_buffer h s == working_state_of_seq (B.as_seq h s))
  [SMTPat (working_state_of_buffer h s)]
= ()

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
    working_state_of_buffer h' b == Spec.step3_body' (Ghost.reveal mi) (working_state_of_buffer h b) t
  ))
= let _a = B.index b 0ul in
  let _b = B.index b 1ul in
  let _c = B.index b 2ul in
  let _d = B.index b 3ul in
  let _e = B.index b 4ul in
  let wmit = B.index w t in
  let _T = Spec.rotl 5ul _a `U32.add_mod` Spec.f t _b _c _d `U32.add_mod` _e `U32.add_mod` Spec.k t `U32.add_mod` wmit in
  B.upd b 4ul _d;
  B.upd b 3ul _c;
  B.upd b 2ul (Spec.rotl 30ul _b);
  B.upd b 1ul _a;
  B.upd b 0ul _T

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
  Ghost.elift1 (fun h -> seq_of_working_state (Spec.step3_body mi (working_state_of_seq h) t)) st

let spec_step3_body_spec (mi: Spec.word_block) (st: Ghost.erased (hash_w SHA1)) (t: nat { t < 80 } ) : Lemma
  (working_state_of_seq (Ghost.reveal (spec_step3_body mi st t)) == Spec.step3_body mi (working_state_of_seq (Ghost.reveal st)) t)
  [SMTPat (working_state_of_seq (Ghost.reveal (spec_step3_body mi st t)))]
= ()

let repeat_range_spec_step3_body (mi: Spec.word_block) (st: Ghost.erased (hash_w SHA1)) (i j: nat) : Lemma
  (requires (i <= j /\ j < 80))
  (ensures (working_state_of_seq (Ghost.reveal (Spec.Loops.repeat_range i j (spec_step3_body mi) st)) ==
  Spec.Loops.repeat_range i j (Spec.step3_body mi) (working_state_of_seq (Ghost.reveal st))
  ))
= admit ()

inline_for_extraction
let impl_step3_body
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
    B.as_seq h' b == Ghost.reveal (spec_step3_body (Ghost.reveal mi) (Ghost.hide (B.as_seq h b)) (U32.v t))
  ))
= step3_body mi w b t

#set-options "--z3rlimit 16"

(*
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
    working_state_of_buffer h1 h == Spec.step3 (E.seq_uint32_of_be size_block_w (B.as_seq h0 m)) (B.as_seq h0 h)
  ))
= let h0 = HST.get () in
  HST.push_frame ();
  let _w = B.alloca 0ul 80ul in
  w m _w;
  let mi = Ghost.hide (E.seq_uint32_of_be size_block_w (B.as_seq h0 m)) in
  let h1 = HST.get () in
  let inv (h' : HS.mem) : GTot Type0 =
    B.modifies (B.loc_buffer h) h1 h'
  in
  let fc (i: U32.t { U32.v i < 80 } ) : HST.Stack unit
    (requires (fun h2 -> inv h2 /\ B.live h2 h))
    (ensures (fun h2 _ h3 -> B.live h2 h /\ B.live h3 h /\ B.modifies (B.loc_buffer h) h2 h3 /\ inv h3 /\ B.as_seq h3 h == Ghost.reveal (spec_step3_body (Ghost.reveal mi) (Ghost.hide (B.as_seq h2 h)) (U32.v i))
    ))
  = admit ()
  in
  let _ = C.Loops.repeat_range 5ul 0ul 80ul (spec_step3_body (Ghost.reveal mi)) h inv  fc in
  admit ();
  repeat_range_spec_step3_body (Ghost.reveal mi) (Ghost.hide (B.as_seq h1 h)) 0 80;
  zero_out _w 80ul;
  HST.pop_frame ();
  ()


(*
(fun i -> impl_step3_body mi _w h i)
