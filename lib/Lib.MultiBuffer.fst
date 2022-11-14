module Lib.MultiBuffer

open FStar.Mul
module ST = FStar.HyperStack.ST
open FStar.HyperStack
open FStar.HyperStack.All

open Lib.IntTypes
open Lib.Sequence
open Lib.Buffer
open Lib.NTuple

#set-options "--z3rlimit 30 --fuel 0 --ifuel 0"

let live4 #a #len (h:mem) (b0 b1 b2 b3: lbuffer a len) =
  live h b0 /\ live h b1 /\ live h b2 /\ live h b3

let live8 #a #len (h:mem) (b0 b1 b2 b3 b4 b5 b6 b7: lbuffer a len) =
  live h b0 /\ live h b1 /\ live h b2 /\ live h b3 /\ live h b4 /\ live h b5 /\ live h b6 /\ live h b7

let internally_disjoint4 #len #a (b0 b1 b2 b3: lbuffer a len) =
  disjoint b0 b1 /\ disjoint b0 b2 /\ disjoint b0 b3 /\
  disjoint b1 b2 /\ disjoint b1 b3 /\ disjoint b2 b3

let internally_disjoint8 #len #a (b0 b1 b2 b3 b4 b5 b6 b7: lbuffer a len) =
  disjoint b0 b1 /\ disjoint b0 b2 /\ disjoint b0 b3 /\ disjoint b0 b4 /\ disjoint b0 b5 /\ disjoint b0 b6 /\ disjoint b0 b7 /\
  disjoint b1 b2 /\ disjoint b1 b3 /\ disjoint b1 b4 /\ disjoint b1 b5 /\ disjoint b1 b6 /\ disjoint b1 b7 /\
  disjoint b2 b3 /\ disjoint b2 b4 /\ disjoint b2 b5 /\ disjoint b2 b6 /\ disjoint b2 b7 /\
  disjoint b3 b4 /\ disjoint b3 b5 /\ disjoint b3 b6 /\ disjoint b3 b7 /\
  disjoint b4 b5 /\ disjoint b4 b6 /\ disjoint b4 b7 /\
  disjoint b5 b6 /\ disjoint b5 b7 /\
  disjoint b6 b7

inline_for_extraction let multibuf (lanes:flen) (len:size_t) =
  ntuple (lbuffer uint8 len) lanes

let internally_disjoint #lanes #len (b:multibuf lanes len) =
  forall i j. (i < lanes /\ j < lanes /\ i <> j) ==> disjoint b.(|i|) b.(|j|)

let disjoint_multi #lanes #len #a #len' (b:multibuf lanes len) (b':lbuffer a len') =
  forall i. i < lanes ==> disjoint b.(|i|) b'


let rec loc_multi_ (#lanes:flen) #len  (i:nat{i < lanes}) (b:multibuf lanes len)
                   : GTot LowStar.Buffer.loc (decreases (lanes - i)) =
  if i = lanes - 1 then loc (b.(|i|))
  else loc b.(|i|) |+| loc_multi_ (i+1) b

let loc_multi #lanes #len b = normalize_term (loc_multi_ #lanes #len 0 b)

let loc_multi1 (#lanes:flen{lanes = 1}) (#len:size_t) (b:multibuf lanes len)  :
  Lemma (loc_multi #lanes #len b == loc b.(|0|)) = ()

#push-options "--fuel 4"
let loc_multi4 (#lanes:flen{lanes = 4}) (#len:size_t) (b:multibuf lanes len)  :
  Lemma (loc_multi #lanes #len b == (loc b.(|0|) |+| (loc b.(|1|) |+| (loc b.(|2|) |+| loc b.(|3|))))) =  ()
#pop-options

#push-options "--fuel 8"
let loc_multi8 (#lanes:flen{lanes = 8}) (#len:size_t) (b:multibuf lanes len)  :
  Lemma (loc_multi #lanes #len b ==
         (loc b.(|0|) |+| (loc b.(|1|) |+| (loc b.(|2|) |+| (loc b.(|3|) |+|
          (loc b.(|4|) |+| (loc b.(|5|) |+| (loc b.(|6|) |+| loc b.(|7|))))))))) =
  ()
#pop-options

let disjoint_multi_multi #lanes #len #len' (b:multibuf lanes len) (b':multibuf lanes len') =
  forall i. i < lanes ==> disjoint b.(|i|) b'.(|i|)

let live_multi #lanes #len (h:mem) (b:multibuf lanes len) =
  forall i. i < lanes ==> live h b.(|i|)

let modifies_multi #lanes #len (b:multibuf lanes len) (h0:mem) (h1:mem) =
  modifies (loc_multi b) h0 h1

let stack_allocated_multi #lanes #len (b:multibuf lanes len) (h0:mem) (h1:mem) (s:lseq uint8 (v len)) =
  forall i. i < lanes ==> stack_allocated b.(|i|) h0 h1 s

let multiseq (lanes:flen) (len:nat) =
  ntuple (Seq.lseq uint8 len) lanes

let as_seq_multi #lanes #len (h:mem) (b:multibuf lanes len) : GTot (multiseq lanes (v len)) =
  gmap (as_seq h) b

let as_seq_multi_lemma (#lanes:flen) #len h b (i:nat{i < lanes}):
  Lemma ((as_seq_multi #lanes #len h b).(|i|) == as_seq h b.(|i|))
  [SMTPat (as_seq_multi #lanes #len h b).(|i|)]
 =
  index_gmap_lemma (as_seq h) b i

unfold let op_Lens_Access #a #len = index #a #len
unfold let op_Lens_Assignment #a #len = upd #a #len
