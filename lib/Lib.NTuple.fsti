module Lib.NTuple

open FStar.Mul
open Lib.IntTypes

#set-options "--z3rlimit 15 --max_ifuel 0 --max_fuel 0"

/// Fixed and bounded length sequences, implemented using tuples

inline_for_extraction
let flen = size_pos

inline_for_extraction noextract
let rec ntuple_ (a:Type0) (len:flen) =
  if len = 1 then a
  else a & ntuple_ a (len-1)

inline_for_extraction noextract
let ntuple (a:Type0) (len:flen) = normalize_term (ntuple_ a len)

inline_for_extraction
val fst (#a:Type0) (#len:flen) (s:ntuple a len) : a

inline_for_extraction
val rest (#a:Type0) (#len:flen{len > 1}) (s:ntuple a len) : ntuple a (len - 1)

inline_for_extraction noextract
val index (#a:Type0) (#len:flen) (s:ntuple a len) (i:nat{i < len}) : a

val index_fst_lemma (#a:Type0) (#len:flen) (s:ntuple a len) :
  Lemma (fst s == index s 0)
  [SMTPat (fst s)]

// val index_rest_lemma (#a:Type0) (#len:flen{len > 1}) (s:ntuple a len) (i:nat{i < len - 1}) :
//   Lemma (index s (i + 1) == index (rest s) i)
//   [SMTPat (index (rest s) i)]

inline_for_extraction noextract
val createi (#a:Type0) (len:flen) (f:(i:nat{i < len} -> a)) : ntuple a len

inline_for_extraction noextract
val gcreatei (#a:Type0) (len:flen) (f:(i:nat{i < len} -> GTot a)) : GTot (ntuple a len)

val createi_lemma (#a:Type0) (len:flen) (f:(i:nat{i < len} -> a)) (i:nat{i < len}) :
  Lemma (index (createi #a len f) i == f i)
  [SMTPat (index (createi #a len f) i)]

val gcreatei_lemma (#a:Type0) (len:flen) (f:(i:nat{i < len} -> GTot a)) (i:nat{i < len}) :
  Lemma (index (gcreatei #a len f) i == f i)
  [SMTPat (index (gcreatei #a len f) i)]

inline_for_extraction noextract
val to_lseq (#a:Type0) (#len:flen) (l:ntuple a len) : Lib.Sequence.lseq a len

inline_for_extraction noextract
val from_lseq (#a:Type0) (#len:flen) (s:Lib.Sequence.lseq a len) : ntuple a len

inline_for_extraction noextract
val create (#a:Type0) (len:flen) (init:a) : ntuple a len

val create_lemma (#a:Type0) (len:flen) (init:a) (i:nat{i < len}) :
  Lemma (index (create #a len init) i == init)
  [SMTPat (index (create #a len init) i)]

inline_for_extraction noextract
val concat (#a:Type0) (#len0:flen) (#len1:flen{len0 + len1 <= max_size_t})
	   (s0:ntuple a len0) (s1:ntuple a len1) : ntuple a (len0 + len1)


val concat_lemma (#a:Type0) (#len0:flen) (#len1:flen) (s0:ntuple a len0) (s1:ntuple a len1) (i:nat):
  Lemma
  (requires (len0 + len1 <= max_size_t /\ i < len0 + len1))
  (ensures ((i < len0 ==> index (concat s0 s1) i == index s0 i) /\
            (i >= len0 ==> index (concat s0 s1) i == index s1 (i-len0))))
  [SMTPat (index (concat #a #len0 #len1 s0 s1) i)]

inline_for_extraction noextract
val equal (#a:Type) (#len:flen) (s1:ntuple a len) (s2:ntuple a len) : Type0

val eq_intro: #a:Type -> #len:flen -> s1:ntuple a len -> s2:ntuple a len ->
  Lemma
  (requires forall i. {:pattern index s1 i; index s2 i} index s1 i == index s2 i)
  (ensures equal s1 s2)
  [SMTPat (equal s1 s2)]

val eq_elim: #a:Type -> #len:flen -> s1:ntuple a len -> s2:ntuple a len ->
  Lemma
  (requires equal s1 s2)
  (ensures  s1 == s2)
  [SMTPat (equal s1 s2)]

(** Updating an element of a fixed-length Sequence *)

inline_for_extraction noextract
val upd: #a:Type -> #len:flen -> s:ntuple a len -> i:nat{i < len} -> x:a -> ntuple a len

val upd_lemma (#a:Type0) (#len:flen) (s:ntuple a len) (i:nat{i < len}) (x:a) (j:nat{j < len}) :
  Lemma (index (upd #a #len s i x) j == (if i = j then x else index s j))
  [SMTPat (index (upd #a #len s i x) j)]

inline_for_extraction noextract
val sub (#a:Type) (#len:flen) (s:ntuple a len) (start:nat) (n:flen{start + n <= len}) : ntuple a n

val index_sub_lemma (#a:Type) (#len:flen) (s:ntuple a len) (start:nat) (n:flen{start + n <= len}) (i:nat{i < n}) :
  Lemma (index (sub #a #len s start n) i == index s (start + i))
  [SMTPat (index (sub #a #len s start n) i)]

inline_for_extraction noextract
val update_sub (#a:Type) (#len:flen) (s:ntuple a len) (start:nat) (n:flen{start + n <= len}) (x:ntuple a n) : ntuple a len

val index_update_sub_lemma (#a:Type) (#len:flen) (s:ntuple a len) (start:nat) (n:flen{start + n <= len}) (x:ntuple a n) (i:nat{i < n}) :
  Lemma
  (index (update_sub #a #len s start n x) i == (if i >= start && i < start + n then index x (i - start) else index s i))
  [SMTPat (index (update_sub #a #len s start n x) i)]

inline_for_extraction noextract
val mapi (#a:Type) (#b:Type) (#len:flen) (f:(i:nat{i < len} -> a -> b)) (s:ntuple a len) : ntuple b len

val index_mapi_lemma (#a:Type) (#b:Type) (#len:flen) (f:(i:nat{i < len} -> a -> b)) (s:ntuple a len) (i:nat{i < len}) :
  Lemma (index (mapi #a #b #len f s) i == f i (index s i))
  [SMTPat (index (mapi #a #b #len f s) i)]

inline_for_extraction noextract
val gmapi (#a:Type) (#b:Type) (#len:flen) (f:(i:nat{i < len} -> a -> GTot b)) (s:ntuple a len) : GTot (ntuple b len)

val index_gmapi_lemma (#a:Type) (#b:Type) (#len:flen) (f:(i:nat{i < len} -> a -> GTot b)) (s:ntuple a len) (i:nat{i < len}) :
  Lemma (index (gmapi #a #b #len f s) i == f i (index s i))
  [SMTPat (index (gmapi #a #b #len f s) i)]

inline_for_extraction noextract
val map (#a:Type) (#b:Type) (#len:flen) (f:a -> b) (s:ntuple a len) : ntuple b len

val index_map_lemma (#a:Type) (#b:Type) (#len:flen) (f:(a -> b)) (s:ntuple a len) (i:nat{i < len}) :
  Lemma (index (map #a #b #len f s) i == f (index s i))
  [SMTPat (index (map #a #b #len f s) i)]

inline_for_extraction noextract
val gmap (#a:Type) (#b:Type) (#len:flen) (f:a -> GTot b) (s:ntuple a len) : GTot (ntuple b len)

val index_gmap_lemma (#a:Type) (#b:Type) (#len:flen) (f:(a -> GTot b)) (s:ntuple a len) (i:nat{i < len}) :
  Lemma (index (gmap #a #b #len f s) i == f (index s i))
  [SMTPat (index (gmap #a #b #len f s) i)]

inline_for_extraction noextract
val map2i (#a:Type) (#b:Type) (#c:Type) (#len:flen) (f:(i:nat{i < len} -> a -> b -> c)) (s1:ntuple a len)  (s2:ntuple b len) : ntuple c len

val index_map2i_lemma (#a:Type) (#b:Type) (#c:Type) (#len:flen) (f:(i:nat{i < len} -> a -> b -> c)) (s1:ntuple a len)  (s2:ntuple b len) (i:nat{i < len}) :
  Lemma (index (map2i #a #b #c #len f s1 s2) i == f i (index s1 i) (index s2 i))
  [SMTPat (index (map2i #a #b #c #len f s1 s2) i)]

inline_for_extraction noextract
val map2 (#a:Type) (#b:Type) (#c:Type) (#len:flen) (f:(a -> b -> c)) (s1:ntuple a len)  (s2:ntuple b len) : ntuple c len

val index_map2_lemma (#a:Type) (#b:Type) (#c:Type) (#len:flen) (f:a -> b -> c) (s1:ntuple a len)  (s2:ntuple b len) (i:nat{i < len}) :
  Lemma (index (map2 #a #b #c #len f s1 s2) i == f (index s1 i) (index s2 i))
  [SMTPat (index (map2 #a #b #c #len f s1 s2) i)]

unfold let op_Lens_Access #a #len = index #a #len
unfold let op_Lens_Assignment #a #len = upd #a #len

(* The following conversions are tedious, but are needed to aid KreMLin in extracting ntuples correctly *)
inline_for_extraction noextract
let ntup1 #a (#l:flen{l = 1}) (t:a) : ntuple a l =
  assert (ntuple a l == ntuple a 1);
  t <: ntuple a 1

val ntup1_lemma (#a:Type0) (#l:flen{l == 1}) (t:a):
  Lemma (let x0 = t in let t = ntup1 #a #l t in x0 == t.(|0|))
  [SMTPat (ntup1 #a #l t)]

inline_for_extraction noextract
let tup1 #a (#l:flen{l = 1}) (t:ntuple a l) : a =
  assert (ntuple a l == ntuple a 1);
  t <: ntuple a 1

val tup1_lemma (#a:Type0) (#l:flen{l == 1}) (t:ntuple a l):
  Lemma (let x0 = tup1 t in x0 == t.(|0|))
  [SMTPat (tup1 #a #l t)]


inline_for_extraction noextract
let ntup2 #a (#l:flen{l = 2}) (t:a & a) : ntuple a l =
  assert (ntuple a l == ntuple a 2);
  (t <: ntuple a 2)

val ntup2_lemma (#a:Type0) (#l:flen{l == 2}) (t:a & a) :
  Lemma
   (let (x0,x1) = t in
    let t = ntup2 #a #l t in
    x0 == t.(|0|) /\ x1 == t.(|1|))
  [SMTPat (ntup2 #a #l t)]


inline_for_extraction noextract
let ntup4 #a (#l:flen{l = 4}) (t:a & (a & (a & a))) : ntuple a l =
  assert (ntuple a l == ntuple a 4);
  (t <: ntuple a 4)

val ntup4_lemma (#a:Type0) (#l:flen{l == 4}) (t:a & (a & (a & a))) :
  Lemma
   (let (x0,(x1,(x2,x3))) = t in
    let t = ntup4 #a #l t in
    x0 == t.(|0|) /\ x1 == t.(|1|) /\
    x2 == t.(|2|) /\ x3 == t.(|3|))
  [SMTPat (ntup4 #a #l t)]

#set-options "--fuel 8"

inline_for_extraction noextract
let tup4 #a (#l:flen{l = 4}) (t:ntuple a l) : (a & (a & (a & a))) =
  assert (ntuple a l == ntuple a 4);
  (t <: ntuple a 4)

val tup4_lemma (#a:Type0) (#l:flen{l = 4}) (t:ntuple a l) :
  Lemma
   (let (x0,(x1,(x2,x3))) = tup4 t in
    x0 == t.(|0|) /\ x1 == t.(|1|) /\
    x2 == t.(|2|) /\ x3 == t.(|3|))
  [SMTPat (tup4 t)]


inline_for_extraction noextract
let ntup8 #a (#l:flen{l = 8}) (t:a & (a & (a & (a & (a & (a & (a & a))))))) : ntuple a l =
  assert (ntuple a l == ntuple a 8);
  (t <: ntuple a 8)

val ntup8_lemma (#a:Type0) (#l:flen{l == 8}) (t:a & (a & (a & (a & (a & (a & (a & a))))))) :
  Lemma
   (let (x0,(x1,(x2,(x3,(x4,(x5,(x6,x7))))))) = t in
    let t = ntup8 #a #l t in
    x0 == t.(|0|) /\ x1 == t.(|1|) /\
    x2 == t.(|2|) /\ x3 == t.(|3|) /\
    x4 == t.(|4|) /\ x5 == t.(|5|) /\
    x6 == t.(|6|) /\ x7 == t.(|7|))
  [SMTPat (ntup8 #a #l t)]

inline_for_extraction noextract
let tup8 #a (#l:flen{l = 8}) (t:ntuple a l) : (a & (a & (a & (a & (a & (a & (a & a))))))) =
  assert (ntuple a l == ntuple a 8);
  (t <: ntuple a 8)

val tup8_lemma (#a:Type0) (#l:flen{l = 8}) (t:ntuple a l) :
  Lemma
   (let (x0,(x1,(x2,(x3,(x4,(x5,(x6,x7))))))) = tup8 t in
    x0 == t.(|0|) /\ x1 == t.(|1|) /\
    x2 == t.(|2|) /\ x3 == t.(|3|) /\
    x4 == t.(|4|) /\ x5 == t.(|5|) /\
    x6 == t.(|6|) /\ x7 == t.(|7|))
  [SMTPat (tup8 t)]


inline_for_extraction noextract
let ntup16 #a (#l:flen{l = 16}) (t:a & (a & (a & (a & (a & (a & (a & (a & (a & (a & (a & (a & (a & (a & (a & a))))))))))))))) : ntuple a l =
  assert (ntuple a l == ntuple a 16);
  (t <: ntuple a 16)

val ntup16_lemma (#a:Type0) (#l:flen{l == 16}) (t:a & (a & (a & (a & (a & (a & (a & (a & (a & (a & (a & (a & (a & (a & (a & a))))))))))))))) :
  Lemma
   (let (x0,(x1,(x2,(x3,(x4,(x5,(x6,(x7,(x8,(x9,(x10,(x11,(x12,(x13,(x14,x15))))))))))))))) = t in
    let t = ntup16 #a #l t in
    x0 == t.(|0|) /\ x1 == t.(|1|) /\
    x2 == t.(|2|) /\ x3 == t.(|3|) /\
    x4 == t.(|4|) /\ x5 == t.(|5|) /\
    x6 == t.(|6|) /\ x7 == t.(|7|) /\
    x8 == t.(|8|) /\ x9 == t.(|9|) /\
    x10 == t.(|10|) /\ x11 == t.(|11|) /\
    x12 == t.(|12|) /\ x13 == t.(|13|) /\
    x14 == t.(|14|) /\ x15 == t.(|15|))
  [SMTPat (ntup16 #a #l t)]
