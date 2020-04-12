module Lib.MultiBuffer

open FStar.Mul
module ST = FStar.HyperStack.ST
open FStar.HyperStack
open FStar.HyperStack.All
open Lib.IntTypes
open Lib.Sequence
open Lib.Buffer
open Lib.NTuple

inline_for_extraction let multibuf (lanes:flen) (len:size_t) = 
    ntuple (lbuffer uint8 len) lanes

let internally_disjoint #lanes #len (b:multibuf lanes len) =
  forall i j. (i < lanes /\ j < lanes /\ i <> j) ==> disjoint b.(|i|) b.(|j|)

let disjoint_multi #lanes #len #a #len' (b:multibuf lanes len) (b':lbuffer a len') =
  forall i. i < lanes ==> disjoint b.(|i|) b'

let rec loc_multi_ #lanes #len (b:multibuf lanes len) : GTot LowStar.Buffer.loc =
  if lanes = 1 then loc (b <: lbuffer uint8 len)
  else let b0 = fst b in
       let br = rest b in
       loc b0 |+| loc_multi_ br

let loc_multi #lanes #len b = normalize_term (loc_multi_ #lanes #len b)

let disjoint_multi_multi #lanes #len #len' (b:multibuf lanes len) (b':multibuf lanes len') =
  forall i. i < lanes ==> disjoint b.(|i|) b'.(|i|)

let live_multi #lanes #len (h:mem) (b:multibuf lanes len) =
  forall i. i < lanes ==> live h b.(|i|)

let modifies_multi #lanes #len (b:multibuf lanes len) (h0:mem) (h1:mem) =
  modifies (loc_multi b) h0 h1

let stack_allocated_multi #lanes #len (b:multibuf lanes len) (h0:mem) (h1:mem) (s:lseq uint8 (v len)) =
  forall i. i < lanes ==> stack_allocated b.(|i|) h0 h1 s

let multiseq (lanes:flen) (len:size_nat) =
    ntuple (lseq uint8 len) lanes
let as_seq_multi #lanes #len (h:mem) (b:multibuf lanes len) : GTot (multiseq lanes (v len)) =
    gmap (as_seq h) b

let as_seq_multi_lemma (#lanes:flen) #len h b (i:nat{i < lanes}):
  Lemma ((as_seq_multi #lanes #len h b).(|i|) == as_seq h b.(|i|))
        [SMTPat (as_seq_multi #lanes #len h b).(|i|)] =
        index_gmap_lemma (as_seq h) b i
  


(*
inline_for_extraction
val sub_multi: #lanes:flen -> #len:size_t -> b:multibuf lanes len -> start:size_t -> slen:size_t{v start + v slen <= v len} -> Stack (multibuf lanes slen)
    (requires (fun h0 -> live_multi h0 b))
    (ensures (fun h0 r h1 -> h0 == h1 /\ live_multi h1 r /\
                           (forall i. i < lanes ==> r.(|i|) == gsub b.(|i|) start slen)))
let sub_multi #lanes #len b start slen =
  createi lanes 
*)
unfold let op_Lens_Access #a #len = index #a #len
unfold let op_Lens_Assignment #a #len = upd #a #len

(*
unfold let multibuf (lanes:lanes_t) (len:size_t) =
  match lanes with
  | 1 -> lbuffer uint8 len
  | 4 -> lbuffer uint8 len & lbuffer uint8 len & lbuffer uint8 len & lbuffer uint8 len
  | 8 -> lbuffer uint8 len & lbuffer uint8 len & lbuffer uint8 len & lbuffer uint8 len &
         lbuffer uint8 len & lbuffer uint8 len & lbuffer uint8 len & lbuffer uint8 len
  | _ -> admit()

let disjoint_multi #lanes #len #a #len' (b:multibuf lanes len) (b':lbuffer a len') =
  match lanes with
  | 1 -> disjoint (b <: lbuffer uint8 len) b'
  | 4 -> let (b0,b1,b2,b3) = (b <: multibuf 4 len) in
         disjoint b0 b' /\ disjoint b1 b' /\ disjoint b2 b' /\ disjoint b3 b'
  | 8 -> let (b0,b1,b2,b3,b4,b5,b6,b7) = (b <: multibuf 8 len) in
         disjoint b0 b' /\ disjoint b1 b' /\ disjoint b2 b' /\ disjoint b3 b' /\
         disjoint b4 b' /\ disjoint b5 b' /\ disjoint b6 b' /\ disjoint b7 b'
  | _ -> admit()

let disjoint_multi_multi #lanes #len (b:multibuf lanes len) (b':multibuf lanes len) =
  match lanes with
  | 1 -> disjoint (b <: lbuffer uint8 len) (b' <: lbuffer uint8 len)
  | 4 -> let (b0',b1',b2',b3') = (b' <: multibuf 4 len) in
         disjoint_multi b b0' /\ disjoint_multi b b1' /\ disjoint_multi b b2' /\ disjoint_multi b b3'
  | 8 -> let (b0',b1',b2',b3',b4',b5',b6',b7') = (b' <: multibuf 8 len) in
         disjoint_multi b b0' /\ disjoint_multi b b1' /\ disjoint_multi b b2' /\ disjoint_multi b b3' /\
         disjoint_multi b b4' /\ disjoint_multi b b5' /\ disjoint_multi b b6' /\ disjoint_multi b b7'
  | _ -> admit()

let live_multi #lanes #len (h:mem) (b:multibuf lanes len) =
  match lanes with
  | 1 -> live h (b <: lbuffer uint8 len)
  | 4 -> let (b0,b1,b2,b3) = (b <: multibuf 4 len) in
         live h b0 /\ live h b1 /\ live h b2 /\ live h b3
  | 8 -> let (b0,b1,b2,b3,b4,b5,b6,b7) = (b <: multibuf 8 len) in
         live h b0 /\ live h b1 /\ live h b2 /\ live h b3 /\
         live h b4 /\ live h b5 /\ live h b6 /\ live h b7
  | _ -> admit()

let stack_allocated_multi #lanes #len (b:multibuf lanes len) (h0:mem) (h1:mem) =
  match lanes with
  | 1 -> stack_allocated (b <: lbuffer uint8 len) h0 h1 (Seq.create (v len) (u8 0))
  | 4 -> let (b0,b1,b2,b3) = (b <: multibuf 4 len) in
         stack_allocated b0 h0 h1 (Seq.create (v len) (u8 0)) /\
         stack_allocated b1 h0 h1 (Seq.create (v len) (u8 0)) /\
         stack_allocated b2 h0 h1 (Seq.create (v len) (u8 0)) /\
         stack_allocated b3 h0 h1 (Seq.create (v len) (u8 0))
  | 8 -> let (b0,b1,b2,b3,b4,b5,b6,b7) = (b <: multibuf 8 len) in
         stack_allocated b0 h0 h1 (Seq.create (v len) (u8 0)) /\
         stack_allocated b1 h0 h1 (Seq.create (v len) (u8 0)) /\
         stack_allocated b2 h0 h1 (Seq.create (v len) (u8 0)) /\
         stack_allocated b3 h0 h1 (Seq.create (v len) (u8 0)) /\
         stack_allocated b4 h0 h1 (Seq.create (v len) (u8 0)) /\
         stack_allocated b5 h0 h1 (Seq.create (v len) (u8 0)) /\
         stack_allocated b6 h0 h1 (Seq.create (v len) (u8 0)) /\
         stack_allocated b7 h0 h1 (Seq.create (v len) (u8 0))
  | _ -> admit()

let modifies_multi #lanes #len (b:multibuf lanes len) (h0:mem) (h1:mem) =
  match lanes with
  | 1 -> modifies (loc (b <: lbuffer uint8 len)) h0 h1
  | 4 -> let (b0,b1,b2,b3) = (b <: multibuf 4 len) in
         modifies (loc b0 |+| loc b1 |+| loc b2 |+| loc b3) h0 h1
  | 8 -> let (b0,b1,b2,b3,b4,b5,b6,b7) = (b <: multibuf 8 len) in
         modifies (loc b0 |+| loc b1 |+| loc b2 |+| loc b3 |+|
                   loc b4 |+| loc b5 |+| loc b6 |+| loc b7) h0 h1
  | _ -> admit()

let create_multi lanes len : StackInline (multibuf lanes len)
  (requires (fun h0 -> v len > 0 /\ 8 * v len <= max_size_t))
  (ensures (fun h0 r h1 -> live_multi h1 r /\ stack_allocated_multi r h0 h1))
  =
  admit();
  match lanes with
  | 1 -> let b: lbuffer uint8 len = create len (u8 0) in
         b
  | 4 -> let buf : lbuffer uint8 (4ul *. len)  = create (4ul *. len) (u8 0) in
         (sub buf 0ul len,
          sub buf len len,
          sub buf (2ul *. len) len,
          sub buf (3ul *. len) len)
  | 8 -> let buf : lbuffer uint8 (8ul *. len)  = create (8ul *. len) (u8 0) in
         (sub buf 0ul len,
          sub buf len len,
          sub buf (2ul *. len) len,
          sub buf (3ul *. len) len,
          sub buf (4ul *. len) len,
          sub buf (5ul *. len) len,
          sub buf (6ul *. len) len,
          sub buf (7ul *. len) len)
  | _ -> admit()

let sub_multi #lanes #len (b:multibuf lanes len) (start:size_t) (len':size_t{v start + v len' <= v len}) : Stack (multibuf lanes len')
  (requires (fun h0 -> live_multi h0 b))
  (ensures (fun h0 r h1 -> h0 == h1 /\ live_multi h1 r))
  =
  match lanes with
  | 1 -> sub (b <: lbuffer uint8 len) start len'
  | 4 -> let (b0,b1,b2,b3) = (b <: multibuf 4 len) in
         (sub b0 start len',
          sub b1 start len',
          sub b2 start len',
          sub b3 start len')
  | 8 -> let (b0,b1,b2,b3,b4,b5,b6,b7) = (b <: multibuf 8 len) in
         (sub b0 start len',
          sub b1 start len',
          sub b2 start len',
          sub b3 start len',
          sub b4 start len',
          sub b5 start len',
          sub b6 start len',
          sub b7 start len')
  | _ -> admit()

let set1_multi #lanes #len (b:multibuf lanes len) (index:size_t{v index < v len}) (v:uint8) : Stack unit
  (requires (fun h0 -> live_multi h0 b))
  (ensures (fun h0 r h1 -> modifies_multi b h0 h1))
  =
  match lanes with
  | 1 -> (b <: lbuffer uint8 len).(index) <- v
  | 4 -> let (b0,b1,b2,b3) = (b <: multibuf 4 len) in
         b0.(index) <- v;
         b1.(index) <- v;
         b2.(index) <- v;
         b3.(index) <- v
  | 8 -> let (b0,b1,b2,b3,b4,b5,b6,b7) = (b <: multibuf 8 len) in
         b0.(index) <- v;
         b1.(index) <- v;
         b2.(index) <- v;
         b3.(index) <- v;
         b4.(index) <- v;
         b5.(index) <- v;
         b6.(index) <- v;
         b7.(index) <- v
  | _ -> admit()

let copy_multi #lanes #len (b:multibuf lanes len) (b':multibuf lanes len) : Stack unit
  (requires (fun h0 -> live_multi h0 b /\ live_multi h0 b' /\ disjoint_multi_multi b b'))
  (ensures (fun h0 r h1 -> modifies_multi b h0 h1))
  =
  match lanes with
  | 1 -> copy (b <: lbuffer uint8 len) (b' <: lbuffer uint8 len)
  | 4 -> let (b0,b1,b2,b3) = (b <: multibuf 4 len) in
         let (b0',b1',b2',b3') = (b' <: multibuf 4 len) in
         copy b0 b0';
         copy b1 b1';
         copy b2 b2';
         copy b3 b3'
  | 8 -> let (b0,b1,b2,b3,b4,b5,b6,b7) = (b <: multibuf 8 len) in
         let (b0',b1',b2',b3',b4',b5',b6',b7') = (b' <: multibuf 8 len) in
         copy b0 b0';
         copy b1 b1';
         copy b2 b2';
         copy b3 b3';
         copy b4 b4';
         copy b5 b5';
         copy b6 b6';
         copy b7 b7'
  | _ -> admit()

let copy1_multi (#lanes:lanes_t) (#len:size_t) (b:multibuf lanes len) (b':lbuffer uint8 len) : Stack unit
  (requires (fun h0 -> live_multi h0 b /\ live h0 b' /\ disjoint_multi b b'))
  (ensures (fun h0 r h1 -> modifies_multi b h0 h1))
  =
  match lanes with
  | 1 -> copy (b <: lbuffer uint8 len) b'
  | 4 -> let (b0,b1,b2,b3) = (b <: multibuf 4 len) in
         copy b0 b';
         copy b1 b';
         copy b2 b';
         copy b3 b'
  | 8 -> let (b0,b1,b2,b3,b4,b5,b6,b7) = (b <: multibuf 8 len) in
         copy b0 b';
         copy b1 b';
         copy b2 b';
         copy b3 b';
         copy b4 b';
         copy b5 b';
         copy b6 b';
         copy b7 b'
  | _ -> admit()

*)
