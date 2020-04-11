module Lib.NTuple

open FStar.Mul
open Lib.IntTypes

#set-options "--z3rlimit 15 --max_ifuel 2 --max_fuel 2"

/// Fixed and bounded length sequences, implemented using tuples

unfold let max_ntuple_len = 16
unfold let flen = n:pos{n <= max_ntuple_len}

noextract
  let rec ntuple_ (a:Type0) (len:flen) =
  if len = 1 then a
  else a & ntuple_ a (len-1)

inline_for_extraction noextract
let ntuple (a:Type0) (len:flen) = normalize_term (ntuple_ a len)

unfold let length (#a:Type0) (#len:flen) (s: ntuple a len) : flen = len

inline_for_extraction noextract
let fst_ (#a:Type0) (#len:flen) (s:ntuple_ a len) : a =
  if len = 1 then s
  else fst (s <: a & ntuple_ a (len - 1))

inline_for_extraction
let fst #a #len (s:ntuple a len) = normalize_term (fst_ #a #len s)

inline_for_extraction noextract
let rest_ (#a:Type0) (#len:flen{len > 1}) (s:ntuple_ a len) : ntuple_ a (len - 1)=
    snd (s <: a & ntuple_ a (len - 1))

inline_for_extraction
let rest (#a:Type0) (#len:flen{len > 1}) (s:ntuple a len) : ntuple a (len - 1) =
    normalize_term (rest_ #a #len s)

inline_for_extraction noextract
let rec index_ (#a:Type0) (#len:flen) (s:ntuple a len) (i:nat{i < len}) =
  if i = 0 then fst s
  else index_ #a #(len-1) (rest s) (i-1)

inline_for_extraction
let index (#a:Type0) (#len:flen) (s:ntuple a len) (i:nat{i < len}) =
  normalize_term (index_ s i)

inline_for_extraction noextract
let rec createi_ (#a:Type0) (min:nat) (max:flen{max > min}) (f:(i:nat{i < max} -> a)) : Tot (ntuple_ a (max - min)) (decreases (max - min)) =
  if min + 1 = max then f min
  else f min, createi_ #a (min+1) max f

inline_for_extraction
let createi (#a:Type0) (len:flen) (f:(i:nat{i < len} -> a)) : ntuple a len =
  normalize_term (createi_ #a 0 len f)

inline_for_extraction noextract
let rec gcreatei_ (#a:Type0) (min:nat) (max:flen{max > min}) (f:(i:nat{i < max} -> GTot a)) : GTot (ntuple_ a (max - min)) (decreases (max - min)) =
  if min + 1 = max then f min
  else f min, gcreatei_ #a (min+1) max f

inline_for_extraction
let gcreatei (#a:Type0) (len:flen) (f:(i:nat{i < len} -> GTot a)) : GTot (ntuple a len) =
  normalize_term (gcreatei_ #a 0 len f)

inline_for_extraction noextract
let rec createi_lemma_ (#a:Type0) (min:nat) (max:flen{max > min}) (f:(i:nat{i < max} -> a)) (i:nat{i < max - min}) :
    Lemma (ensures (index #a #(max - min) (createi_ #a min max f) i == f (min+i))) (decreases i) =
    if i = 0 then ()
    else createi_lemma_ #a (min+1) max f (i-1)

inline_for_extraction noextract
let createi_lemma (#a:Type0) (len:flen) (f:(i:nat{i < len} -> a)) (i:nat{i < len}) :
    Lemma (index (createi #a len f) i == f i)
	  [SMTPat (index (createi #a len f) i)] =
    createi_lemma_ #a 0 len f i

inline_for_extraction noextract
let rec gcreatei_lemma_ (#a:Type0) (min:nat) (max:flen{max > min}) (f:(i:nat{i < max} -> GTot a)) (i:nat{i < max - min}) :
    Lemma (ensures (index #a #(max - min) (gcreatei_ #a min max f) i == f (min+i))) (decreases i) =
    if i = 0 then ()
    else gcreatei_lemma_ #a (min+1) max f (i-1)

inline_for_extraction noextract
let gcreatei_lemma (#a:Type0) (len:flen) (f:(i:nat{i < len} -> GTot a)) (i:nat{i < len}) :
    Lemma (index (gcreatei #a len f) i == f i)
	  [SMTPat (index (gcreatei #a len f) i)] =
    gcreatei_lemma_ #a 0 len f i

inline_for_extraction
let to_lseq (#a:Type0) (#len:flen) (l:ntuple a len) : Lib.Sequence.lseq a len =
    normalize_term (Lib.Sequence.createi len (index l))

inline_for_extraction
let from_lseq (#a:Type0) (#len:flen) (s:Lib.Sequence.lseq a len) : l:ntuple a len =
    normalize_term (createi #a len (Lib.Sequence.index s))

inline_for_extraction
let create (#a:Type0) (len:flen) (init:a) =
  normalize_term (createi #a len (fun i -> init))


inline_for_extraction noextract
let create_lemma (#a:Type0) (len:flen) (init:a) (i:nat{i < len}) :
    Lemma (index (create #a len init) i == init)
	  [SMTPat (index (create #a len init) i)] =
    createi_lemma_ #a 0 len (fun i -> init) i

inline_for_extraction noextract
let rec concat_ (#a:Type0) (#len0:flen) (#len1:flen{len0 + len1 <= max_ntuple_len})
		(s0:ntuple a len0) (s1:ntuple a len1) : ntuple_ a (len0 + len1) =
	if len0 = 1 then s0,s1
	else fst s0, concat_ (rest s0) s1

inline_for_extraction
let concat (#a:Type0) (#len0:flen) (#len1:flen{len0 + len1 <= max_ntuple_len})
		(s0:ntuple a len0) (s1:ntuple a len1) : ntuple a (len0 + len1) =
	concat_ s0 s1

inline_for_extraction noextract
let rec concat_lemma1 (#a:Type0) (#len0:flen) (#len1:flen{len0 + len1 <= max_ntuple_len})
		(s0:ntuple a len0) (s1:ntuple a len1) (i:nat{i < len0}) :
		Lemma (index (concat s0 s1) i == index s0 i) =
	if i = 0 then ()
	else concat_lemma1 (rest s0) s1 (i-1)

inline_for_extraction noextract
let rec concat_lemma2 (#a:Type0) (#len0:flen) (#len1:flen{len0 + len1 <= max_ntuple_len})
		(s0:ntuple a len0) (s1:ntuple a len1) (i:nat{i >= len0 /\ i < len0 + len1}) :
		Lemma (index (concat s0 s1) i == index s1 (i-len0)) =
	if i = 0 then ()
	else
	  if len0 = 1 then ()
	  else concat_lemma2 (rest s0) s1 (i-1)

inline_for_extraction noextract
let concat_lemma (#a:Type0) (#len0:flen) (#len1:flen)
		 (s0:ntuple a len0) (s1:ntuple a len1) (i:nat):
		Lemma (requires (len0 + len1 <= max_ntuple_len /\ i < len0 + len1))
		      (ensures ((i < len0 ==> index (concat s0 s1) i == index s0 i) /\
			        (i >= len0 ==> index (concat s0 s1) i == index s1 (i-len0))))
		[SMTPat (index (concat s0 s1) i)] =
		  if i < len0 then concat_lemma1 s0 s1 i
		  else concat_lemma2 s0 s1 i

abstract
type equal (#a:Type) (#len:flen) (s1:ntuple a len) (s2:ntuple a len) =
  forall (i:size_nat{i < len}).{:pattern (index s1 i); (index s2 i)} index s1 i == index s2 i

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
let rec upd_ (#a:Type) (#len:flen) (s:ntuple a len) (i:nat{i < len}) (x:a) : ntuple_ a len =
  if i = 0 then
    if len = 1 then x
    else x,rest s
  else fst s,upd_ #a #(len-1) (rest s) (i-1) x

inline_for_extraction
val upd: #a:Type -> #len:flen -> s:ntuple a len -> i:nat{i < len} -> x:a -> ntuple a len
let upd (#a:Type) (#len:flen) (s:ntuple a len) (i:nat{i < len}) (x:a) : ntuple a len = 
  normalize_term (upd_ s i x)

inline_for_extraction noextract
let rec upd_lemma (#a:Type0) (#len:flen) (s:ntuple a len) (i:nat{i < len}) (x:a) (j:nat{j < len}) :
    Lemma (index (upd #a #len s i x) j == (if i = j then x else index s j))
	  [SMTPat (index (upd #a #len s i x) j)] =
  if j = 0 then ()
  else if i = 0 then ()
       else upd_lemma #a #(len-1) (rest s) (i-1) x (j-1)

inline_for_extraction
let sub (#a:Type) (#len:flen) (s:ntuple a len) (start:nat) (n:flen{start + n <= len}) : ntuple a n =
  normalize_term (createi n (fun i -> index s (start + i)))

inline_for_extraction
let slice (#a:Type) (#len:flen) (s:ntuple a len) (start:nat) (fin:flen{start < fin /\ fin <= len}) : ntuple a (fin - start) =
  normalize_term (sub s start (fin - start))

inline_for_extraction
let update_sub (#a:Type) (#len:flen) (s:ntuple a len) (start:nat) (n:flen{start + n <= len}) (x:ntuple a n) : ntuple a len =
  normalize_term (createi len (fun i -> if i < start || i >= start+n then index s i else index x (i - start)))

inline_for_extraction
let update_slice (#a:Type) (#len:flen) (s:ntuple a len) (start:nat) (fin:flen{start < fin /\ fin <= len}) (x:ntuple a (fin - start)) : ntuple a len =
  normalize_term (update_sub s start (fin - start) x)

inline_for_extraction
let mapi (#a:Type) (#b:Type) (#len:flen) (f:(i:nat{i < len} -> a -> b)) (s:ntuple a len) : ntuple b len =
  normalize_term (createi len (fun i -> f i (index s i)))

inline_for_extraction
let gmapi (#a:Type) (#b:Type) (#len:flen) (f:(i:nat{i < len} -> a -> GTot b)) (s:ntuple a len) : GTot (ntuple b len) =
  normalize_term (gcreatei len (fun i -> f i (index s i)))

inline_for_extraction
let map (#a:Type) (#b:Type) (#len:flen) (f:a -> b) (s:ntuple a len) : ntuple b len =
  normalize_term (createi len (fun i -> f (index s i)))

inline_for_extraction
let gmap (#a:Type) (#b:Type) (#len:flen) (f:a -> GTot b) (s:ntuple a len) : GTot (ntuple b len) =
  normalize_term (gcreatei len (fun i -> f (index s i)))

inline_for_extraction
let gmap_lemma (#a:Type) (#b:Type) (#len:flen) (f:a -> GTot b) (s:ntuple a len) (i:nat{i < len}):
  Lemma (index (gmap #a #b #len f s) i == f (index s i))
        [SMTPat (index (gmap #a #b #len f s) i)] =
  gcreatei_lemma #b len (fun i -> f (index s i)) i


inline_for_extraction
let map2i (#a:Type) (#b:Type) (#c:Type) (#len:flen) (f:(i:nat{i < len} -> a -> b -> c)) (s1:ntuple a len)  (s2:ntuple b len) : ntuple c len =
  normalize_term (createi len (fun i -> f i (index s1 i) (index s2 i)))

inline_for_extraction
let map2 (#a:Type) (#b:Type) (#c:Type) (#len:flen) (f:a -> b -> c) (s1:ntuple a len)  (s2:ntuple b len) : ntuple c len =
  normalize_term (createi len (fun i -> f (index s1 i) (index s2 i)))

unfold let op_Lens_Access #a #len = index #a #len
unfold let op_Lens_Assignment #a #len = upd #a #len

