module Hacl.Hash.Core.MD5

module B = LowStar.Buffer
module IB = LowStar.ImmutableBuffer
module HS = FStar.HyperStack
module HST = FStar.HyperStack.ST
module Spec = Spec.MD5
open Lib.IntTypes

module U32 = FStar.UInt32

open Hacl.Hash.Definitions
open Spec.Hash.Definitions

friend Spec.MD5
friend Hacl.Hash.PadFinish

(** Top-level constant arrays for the MD5 algorithm. *)
let _h0 = IB.igcmalloc_of_list HS.root Spec.init_as_list
let _t = IB.igcmalloc_of_list HS.root Spec.t_as_list

noextract inline_for_extraction
let alloca () =
  B.alloca_of_list Spec.init_as_list

(* We read values from constant buffers through accessors to isolate
   all recall/liveness issues away. Thus, clients will not need to
   know that their output buffers be disjoint from our constant
   immutable buffers. *)

inline_for_extraction
let h0 (i: U32.t { U32.v i < 4 } ) : HST.Stack uint32
  (requires (fun _ -> True))
  (ensures (fun h res h' ->
    B.modifies B.loc_none h h' /\
    res == Seq.index Spec.init (U32.v i)
  ))
= IB.recall_contents _h0 Spec.init;
  B.index _h0 i

inline_for_extraction
let t (i: U32.t { U32.v i < 64 } ) : HST.Stack uint32
  (requires (fun _ -> True))
  (ensures (fun h res h' ->
    B.modifies B.loc_none h h' /\
    res == Seq.index Spec.t (U32.v i)
  ))
= IB.recall_contents _t Spec.t;
  B.index _t i

let seq_index_upd (#t: Type) (s: Seq.seq t) (i: nat) (v: t) (j: nat) : Lemma
  (requires (i < Seq.length s /\ j < Seq.length s))
  (ensures (Seq.index (Seq.upd s i v) j == (if j = i then v else Seq.index s j)))
  [SMTPat (Seq.index (Seq.upd s i v) j)]
= ()

let init s =
  let h = HST.get () in
  let inv (h' : HS.mem) (i: nat) : GTot Type0 =
    B.live h' s /\ B.modifies (B.loc_buffer s) h h' /\ i <= 4 /\ Seq.slice (B.as_seq h' s) 0 i == Seq.slice Spec.init 0 i
  in
  C.Loops.for 0ul 4ul inv (fun i ->
    B.upd s i (h0 i);
    let h' = HST.get () in
    Seq.snoc_slice_index (B.as_seq h' s) 0 (U32.v i);
    Seq.snoc_slice_index (Spec.init) 0 (U32.v i)
  )

inline_for_extraction
let abcd_t = (b: B.buffer uint32 { B.length b == 4 } )

inline_for_extraction
let abcd_idx = (n: U32.t { U32.v n < 4 } )

inline_for_extraction
let x_idx = (n: U32.t { U32.v n < 16 } )

inline_for_extraction
let x_t = (b: B.buffer uint8 { B.length b == 64 } )

inline_for_extraction
let t_idx = (n: U32.t { 1 <= U32.v n /\ U32.v n <= 64 } )

inline_for_extraction
val round_op_gen
  (f: (uint32 -> uint32 -> uint32 -> Tot uint32))
  (abcd: abcd_t)
  (x: x_t)
  (a b c d: abcd_idx)
  (k: x_idx)
  (s: Spec.rotate_idx)
  (i: t_idx)
: HST.Stack unit
  (requires (fun h ->
    B.live h abcd /\
    B.live h x /\
    B.disjoint abcd x
  ))
  (ensures (fun h _ h' ->
    B.modifies (B.loc_buffer abcd) h h' /\
    B.live h' abcd /\
    B.live h' x /\ // better to add this here also to ease chaining
    B.as_seq h' abcd == Spec.round_op_gen f (B.as_seq h abcd) 
			(Lib.ByteSequence.uints_from_bytes_le #_ #_ #16 (B.as_seq h x)) 
			(U32.v a) (U32.v b) (U32.v c) (U32.v d) (U32.v k) s (U32.v i)
  ))

#reset-options "--z3rlimit 200 --max_fuel 1 --max_ifuel 1"

let round_op_gen f abcd x a b c d k s i =
  let h = HST.get () in
  assert_norm (64 / 4 == 16);
  assert_norm (64 % 4 == 0);
  let sx = Ghost.hide (Lib.ByteSequence.uints_from_bytes_le #_ #_ #16 (B.as_seq h x)) in
  let va = B.index abcd a in
  let vb = B.index abcd b in
  let vc = B.index abcd c in
  let vd = B.index abcd d in
  let xk = Lib.ByteBuffer.uint_at_index_le #U32 #SEC #16ul x k in
  assert (xk == Seq.index (Ghost.reveal sx) (U32.v k));
  let ti = t (i `U32.sub` 1ul) in
  let v = (vb +. ((va +. f vb vc vd +. xk +. ti) <<<. s)) in
  B.upd abcd a v;
  reveal_opaque (`%Spec.round_op_gen) Spec.round_op_gen

inline_for_extraction let ia : abcd_idx = 0ul
inline_for_extraction let ib : abcd_idx = 1ul
inline_for_extraction let ic : abcd_idx = 2ul
inline_for_extraction let id : abcd_idx = 3ul

inline_for_extraction
let round1_op = round_op_gen Spec.f

#set-options "--z3rlimit 10"
inline_for_extraction
let round1
  (abcd: abcd_t)
  (x: x_t)
: HST.Stack unit
  (requires (fun h ->
    B.live h abcd /\
    B.live h x /\
    B.disjoint abcd x
  ))
  (ensures (fun h _ h' ->
    B.modifies (B.loc_buffer abcd) h h' /\
    B.live h' abcd /\
    B.live h' x /\
    B.as_seq h' abcd == Spec.round1 (B.as_seq h abcd) 
    			(Lib.ByteSequence.uints_from_bytes_le #_ #_ #16 (B.as_seq h x)) 
  ))
=
  let h = HST.get () in
  let _ = round1_op abcd x ia ib ic id  0ul  7ul  1ul in
  let _ = round1_op abcd x id ia ib ic  1ul 12ul  2ul in
  let _ = round1_op abcd x ic id ia ib  2ul 17ul  3ul in
  let _ = round1_op abcd x ib ic id ia  3ul 22ul  4ul in

  let _ = round1_op abcd x ia ib ic id 4ul 7ul 5ul in
  let _ = round1_op abcd x id ia ib ic 5ul 12ul 6ul in
  let _ = round1_op abcd x ic id ia ib 6ul 17ul 7ul in
  let _ = round1_op abcd x ib ic id ia 7ul 22ul 8ul in

  let _ = round1_op abcd x ia ib ic id 8ul 7ul 9ul in
  let _ = round1_op abcd x id ia ib ic 9ul 12ul 10ul in
  let _ = round1_op abcd x ic id ia ib 10ul 17ul 11ul in
  let _ = round1_op abcd x ib ic id ia 11ul 22ul 12ul in

  let _ = round1_op abcd x ia ib ic id 12ul 7ul 13ul in
  let _ = round1_op abcd x id ia ib ic 13ul 12ul 14ul in
  let _ = round1_op abcd x ic id ia ib 14ul 17ul 15ul in
  let _ = round1_op abcd x ib ic id ia 15ul 22ul 16ul in
  let h' = HST.get () in

  reveal_opaque (`%Spec.round1) Spec.round1;
  assert (Seq.equal (B.as_seq h' abcd) (Spec.round1 (B.as_seq h abcd) 
  		    (Lib.ByteSequence.uints_from_bytes_le #_ #_ #16 (B.as_seq h x))))


inline_for_extraction
let round2_op = round_op_gen Spec.g

inline_for_extraction
let round2
  (abcd: abcd_t)
  (x: x_t)
: HST.Stack unit
  (requires (fun h ->
    B.live h abcd /\
    B.live h x /\
    B.disjoint abcd x
  ))
  (ensures (fun h _ h' ->
    B.modifies (B.loc_buffer abcd) h h' /\
    B.live h' abcd /\
    B.live h' x /\
    B.as_seq h' abcd == Spec.round2 (B.as_seq h abcd) 
    			(Lib.ByteSequence.uints_from_bytes_le #_ #_ #16 (B.as_seq h x)))) 
=
  let h = HST.get () in
  let _ = round2_op abcd x ia ib ic id 1ul 5ul 17ul in
  let _ = round2_op abcd x id ia ib ic 6ul 9ul 18ul in
  let _ = round2_op abcd x ic id ia ib 11ul 14ul 19ul in
  let _ = round2_op abcd x ib ic id ia 0ul 20ul 20ul in

  let _ = round2_op abcd x ia ib ic id 5ul 5ul 21ul in
  let _ = round2_op abcd x id ia ib ic 10ul 9ul 22ul in
  let _ = round2_op abcd x ic id ia ib 15ul 14ul 23ul in
  let _ = round2_op abcd x ib ic id ia 4ul 20ul 24ul in

  let _ = round2_op abcd x ia ib ic id 9ul 5ul 25ul in
  let _ = round2_op abcd x id ia ib ic 14ul 9ul 26ul in
  let _ = round2_op abcd x ic id ia ib 3ul 14ul 27ul in
  let _ = round2_op abcd x ib ic id ia 8ul 20ul 28ul in

  let _ = round2_op abcd x ia ib ic id 13ul 5ul 29ul in
  let _ = round2_op abcd x id ia ib ic 2ul 9ul 30ul in
  let _ = round2_op abcd x ic id ia ib 7ul 14ul 31ul in
  let _ = round2_op abcd x ib ic id ia 12ul 20ul 32ul in
  let h' = HST.get () in

  reveal_opaque (`%Spec.round2) Spec.round2;
  assert (Seq.equal (B.as_seq h' abcd) (Spec.round2 (B.as_seq h abcd) 
         (Lib.ByteSequence.uints_from_bytes_le #_ #_ #16 (B.as_seq h x))))

inline_for_extraction
let round3_op = round_op_gen Spec.h

#set-options "--z3rlimit 100"
inline_for_extraction
let round3
  (abcd: abcd_t)
  (x: x_t)
: HST.Stack unit
  (requires (fun h ->
    B.live h abcd /\
    B.live h x /\
    B.disjoint abcd x
  ))
  (ensures (fun h _ h' ->
    B.modifies (B.loc_buffer abcd) h h' /\
    B.live h' abcd /\
    B.live h' x /\
    B.as_seq h' abcd == Spec.round3 (B.as_seq h abcd) 
      (Lib.ByteSequence.uints_from_bytes_le #_ #_ #16 (B.as_seq h x))))
=
  let h = HST.get () in
  let _ = round3_op abcd x ia ib ic id 5ul 4ul 33ul in
  let _ = round3_op abcd x id ia ib ic 8ul 11ul 34ul in
  let _ = round3_op abcd x ic id ia ib 11ul 16ul 35ul in
  let _ = round3_op abcd x ib ic id ia 14ul 23ul 36ul in

  let _ = round3_op abcd x ia ib ic id 1ul 4ul 37ul in
  let _ = round3_op abcd x id ia ib ic 4ul 11ul 38ul in
  let _ = round3_op abcd x ic id ia ib 7ul 16ul 39ul in
  let _ = round3_op abcd x ib ic id ia 10ul 23ul 40ul in

  let _ = round3_op abcd x ia ib ic id 13ul 4ul 41ul in
  let _ = round3_op abcd x id ia ib ic 0ul 11ul 42ul in
  let _ = round3_op abcd x ic id ia ib 3ul 16ul 43ul in
  let _ = round3_op abcd x ib ic id ia 6ul 23ul 44ul in

  let _ = round3_op abcd x ia ib ic id 9ul 4ul 45ul in
  let _ = round3_op abcd x id ia ib ic 12ul 11ul 46ul in
  let _ = round3_op abcd x ic id ia ib 15ul 16ul 47ul in
  let _ = round3_op abcd x ib ic id ia 2ul 23ul 48ul in
  let h' = HST.get () in

  reveal_opaque (`%Spec.round3) Spec.round3;
  assert (Seq.equal (B.as_seq h' abcd) (Spec.round3 (B.as_seq h abcd) 
      (Lib.ByteSequence.uints_from_bytes_le #_ #_ #16 (B.as_seq h x))))

inline_for_extraction
let round4_op = round_op_gen Spec.i

inline_for_extraction
let round4
  (abcd: abcd_t)
  (x: x_t)
: HST.Stack unit
  (requires (fun h ->
    B.live h abcd /\
    B.live h x /\
    B.disjoint abcd x
  ))
  (ensures (fun h _ h' ->
    B.modifies (B.loc_buffer abcd) h h' /\
    B.live h' abcd /\
    B.live h' x /\
    B.as_seq h' abcd == Spec.round4 (B.as_seq h abcd) 
          (Lib.ByteSequence.uints_from_bytes_le #_ #_ #16 (B.as_seq h x))))
=
  let h = HST.get () in
  let _ = round4_op abcd x ia ib ic id 0ul 6ul 49ul in
  let _ = round4_op abcd x id ia ib ic 7ul 10ul 50ul in
  let _ = round4_op abcd x ic id ia ib 14ul 15ul 51ul in
  let _ = round4_op abcd x ib ic id ia 5ul 21ul 52ul in

  let _ = round4_op abcd x ia ib ic id 12ul 6ul 53ul in
  let _ = round4_op abcd x id ia ib ic 3ul 10ul 54ul in
  let _ = round4_op abcd x ic id ia ib 10ul 15ul 55ul in
  let _ = round4_op abcd x ib ic id ia 1ul 21ul 56ul in

  let _ = round4_op abcd x ia ib ic id 8ul 6ul 57ul in
  let _ = round4_op abcd x id ia ib ic 15ul 10ul 58ul in
  let _ = round4_op abcd x ic id ia ib 6ul 15ul 59ul in
  let _ = round4_op abcd x ib ic id ia 13ul 21ul 60ul in

  let _ = round4_op abcd x ia ib ic id 4ul 6ul 61ul in
  let _ = round4_op abcd x id ia ib ic 11ul 10ul 62ul in
  let _ = round4_op abcd x ic id ia ib 2ul 15ul 63ul in
  let _ = round4_op abcd x ib ic id ia 9ul 21ul 64ul in
  let h' = HST.get () in

  reveal_opaque (`%Spec.round4) Spec.round4;
  assert (Seq.equal (B.as_seq h' abcd) (Spec.round4 (B.as_seq h abcd) 
            (Lib.ByteSequence.uints_from_bytes_le #_ #_ #16 (B.as_seq h x))))

inline_for_extraction
let rounds
  (abcd: abcd_t)
  (x: x_t)
: HST.Stack unit
  (requires (fun h ->
    B.live h abcd /\
    B.live h x /\
    B.disjoint abcd x
  ))
  (ensures (fun h _ h' ->
    B.modifies (B.loc_buffer abcd) h h' /\
    B.live h' abcd /\
    B.live h' x /\
    B.as_seq h' abcd == Spec.rounds (B.as_seq h abcd) 
                (Lib.ByteSequence.uints_from_bytes_le #_ #_ #16 (B.as_seq h x))))
=
  let h = HST.get () in
  round1 abcd x;
  round2 abcd x;
  round3 abcd x;
  round4 abcd x;
  let h' = HST.get () in
  reveal_opaque (`%Spec.rounds) Spec.rounds;
  assert (Seq.equal (B.as_seq h' abcd) (Spec.rounds (B.as_seq h abcd) 
                  (Lib.ByteSequence.uints_from_bytes_le #_ #_ #16 (B.as_seq h x))))

inline_for_extraction
let overwrite
  (abcd:state MD5)
  (a' b' c' d' : uint32)
: HST.Stack unit
    (requires (fun h ->
      B.live h abcd))
    (ensures (fun h0 _ h1 ->
      B.(modifies (loc_buffer abcd) h0 h1) /\
      B.live h1 abcd /\
      B.as_seq h1 abcd == Spec.overwrite (B.as_seq h0 abcd) a' b' c' d'))
= 
  let h0 = HST.get () in
  B.upd abcd ia a';
  B.upd abcd ib b';
  B.upd abcd ic c';
  B.upd abcd id d';
  let h1 = HST.get () in
  reveal_opaque (`%Spec.overwrite) Spec.overwrite;
  assert (Seq.equal (B.as_seq h1 abcd) (Spec.overwrite (B.as_seq h0 abcd) a' b' c' d'))

inline_for_extraction
let update'
  (abcd: abcd_t)
  (x: x_t)
: HST.Stack unit
    (requires (fun h ->
      B.live h abcd /\ B.live h x /\ B.disjoint abcd x))
    (ensures (fun h0 _ h1 ->
      B.(modifies (loc_buffer abcd) h0 h1) /\
      B.live h1 abcd /\
      B.as_seq h1 abcd == Spec.update (B.as_seq h0 abcd) (B.as_seq h0 x)))
=
  let h0 = HST.get () in
  assert_norm (U32.v ia == Spec.ia);
  assert_norm (U32.v ib == Spec.ib);
  assert_norm (U32.v ic == Spec.ic);
  assert_norm (U32.v id == Spec.id);
  let aa = B.index abcd ia in
  let bb = B.index abcd ib in
  let cc = B.index abcd ic in
  let dd = B.index abcd id in
  rounds abcd x;
  let a = B.index abcd ia in
  let b = B.index abcd ib in
  let c = B.index abcd ic in
  let d = B.index abcd id in
  overwrite abcd
    (a +. aa)
    (b +. bb)
    (c +. cc)
    (d +. dd);
  let h1 = HST.get () in
  reveal_opaque (`%Spec.update) Spec.update;
  assert (Seq.equal (B.as_seq h1 abcd) (Spec.update (B.as_seq h0 abcd) (B.as_seq h0 x)))

let update abcd x = update' abcd x

let pad: pad_st MD5 = Hacl.Hash.PadFinish.pad MD5

let finish: finish_st MD5 = Hacl.Hash.PadFinish.finish MD5
