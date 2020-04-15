module Lib.NTuple

open FStar.Mul
open Lib.IntTypes

#set-options "--z3rlimit 15 --max_ifuel 0 --max_fuel 1"

let max_ntuple_len = max_size_t

unfold let length (#a:Type0) (#len:flen) (s: ntuple a len) : flen = len

inline_for_extraction noextract
let fst_ (#a:Type0) (#len:flen) (s:ntuple_ a len) : a =
  if len = 1 then s
  else fst (s <: a & ntuple_ a (len - 1))

let fst #a #len (s:ntuple a len) =
  normalize_term (fst_ #a #len s)

inline_for_extraction noextract
let rest_ (#a:Type0) (#len:flen{len > 1}) (s:ntuple_ a len) : ntuple_ a (len - 1)=
    snd (s <: a & ntuple_ a (len - 1))

let rest #a #len s =
  normalize_term (rest_ #a #len s)

inline_for_extraction noextract
let rec index_ (#a:Type0) (#len:flen) (s:ntuple a len) (i:nat{i < len}) =
  if i = 0 then fst s
  else (assert (len > 1);
        index_ #a #(len-1) (rest s) (i-1))

let index #a #len s i =
  normalize_term (index_ s i)

let index_fst_lemma #a #len s = ()

// let rec index_rest_lemma #a #len s i =
//   if len = 1 then ()
//   else admit ()

inline_for_extraction noextract
let rec createi_ (#a:Type0) (min:nat) (max:flen{max > min}) (f:(i:nat{i < max} -> a)) :
  Tot (ntuple_ a (max - min)) (decreases (max - min))
 =
  if min + 1 = max then f min
  else f min, createi_ #a (min+1) max f

let createi #a len f =
  normalize_term (createi_ #a 0 len f)

inline_for_extraction noextract
let rec gcreatei_ (#a:Type0) (min:nat) (max:flen{max > min}) (f:(i:nat{i < max} -> GTot a)) :
  GTot (ntuple_ a (max - min)) (decreases (max - min))
 =
  if min + 1 = max then f min
  else f min, gcreatei_ #a (min+1) max f

let gcreatei #a len f =
  normalize_term (gcreatei_ #a 0 len f)

let rec createi_lemma_ (#a:Type0) (min:nat) (max:flen{max > min}) (f:(i:nat{i < max} -> a)) (i:nat{i < max - min}) :
  Lemma (ensures (index #a #(max - min) (createi_ #a min max f) i == f (min+i))) (decreases i)
 =
  if i = 0 then ()
  else createi_lemma_ #a (min+1) max f (i-1)

let createi_lemma #a len f i =
  createi_lemma_ #a 0 len f i

let rec gcreatei_lemma_ (#a:Type0) (min:nat) (max:flen{max > min}) (f:(i:nat{i < max} -> GTot a)) (i:nat{i < max - min}) :
  Lemma (ensures (index #a #(max - min) (gcreatei_ #a min max f) i == f (min+i))) (decreases i)
 =
  if i = 0 then ()
  else gcreatei_lemma_ #a (min+1) max f (i-1)

let gcreatei_lemma #a len f i =
  gcreatei_lemma_ #a 0 len f i

let to_lseq #a #len l =
  normalize_term (Lib.Sequence.createi len (index l))

let from_lseq #a #len s =
  normalize_term (createi #a len (Lib.Sequence.index s))

let create #a len init =
  normalize_term (createi #a len (fun i -> init))


let create_lemma #a len init i =
  createi_lemma_ #a 0 len (fun i -> init) i

#push-options "--max_fuel 2"
inline_for_extraction noextract
let rec concat_ (#a:Type0) (#len0:flen) (#len1:flen{len0 + len1 <= max_ntuple_len})
		(s0:ntuple a len0) (s1:ntuple a len1) : ntuple_ a (len0 + len1)
 =
  if len0 = 1 then s0,s1
  else fst s0, concat_ (rest s0) s1
#pop-options

let concat #a #len0 #len1 s0 s1 = concat_ s0 s1

val concat_lemma1 (#a:Type0) (#len0:flen) (#len1:flen) (s0:ntuple a len0) (s1:ntuple a len1) (i:nat):
  Lemma
  (requires (len0 + len1 <= max_ntuple_len /\ i < len0))
  (ensures  (index (concat s0 s1) i == index s0 i))
let rec concat_lemma1 #a #len0 #len1 s0 s1 i =
  if i = 0 then ()
  else concat_lemma1 (rest s0) s1 (i-1)


val concat_lemma2 (#a:Type0) (#len0:flen) (#len1:flen) (s0:ntuple a len0) (s1:ntuple a len1) (i:nat) :
  Lemma
  (requires (len0 + len1 <= max_ntuple_len /\ i >= len0 /\ i < len0 + len1))
  (ensures  (index (concat s0 s1) i == index s1 (i-len0)))
let rec concat_lemma2 #a #len0 #len1 s0 s1 i =
  if i = 0 then ()
  else
    if len0 = 1 then ()
    else concat_lemma2 (rest s0) s1 (i-1)

let concat_lemma #a #len0 #len1 s0 s1 i =
  if i < len0 then concat_lemma1 s0 s1 i
  else concat_lemma2 s0 s1 i

let equal #a #len s1 s2 =
  (forall (i:size_nat{i < len}).{:pattern (index s1 i); (index s2 i)} index s1 i == index s2 i)

let eq_intro #a #len s1 s2 = ()

let rec eq_elim #a #len s1 s2 =
  if len = 1 then begin
    assert (s1 == index s1 0);
    assert (s2 == index s2 0) end
  else begin
    let f1 = fst s1 in
    let f2 = fst s1 in
    assert (f1 == f2);
    let r1 = rest s1 in
    let r2 = rest s2 in
    assert (forall i. i < len - 1 ==> index r1 i == index s1 (i+1));
    assert (forall i. i < len - 1 ==> index r2 i == index s2 (i+1));
    assert (forall i. i < len ==> index s1 i == index s2 i);
    eq_intro r1 r2;
    eq_elim #a #(len-1) r1 r2 end

(** Updating an element of a fixed-length Sequence *)

inline_for_extraction noextract
let rec upd_ (#a:Type) (#len:flen) (s:ntuple a len) (i:nat{i < len}) (x:a) : ntuple_ a len =
  if i = 0 then
    if len = 1 then x
    else x,rest s
  else fst s,upd_ #a #(len-1) (rest s) (i-1) x

let upd #a #len s i x =
  normalize_term (upd_ s i x)

let rec upd_lemma #a #len s i x j =
  if j = 0 then ()
  else
    if i = 0 then ()
    else upd_lemma #a #(len-1) (rest s) (i-1) x (j-1)

let sub #a #len s start n =
  normalize_term (createi n (fun i -> index s (start + i)))

let index_sub_lemma #a #len s start n i =
  createi_lemma n (fun i -> index s (start + i)) i

//TODO: add to fsti?
inline_for_extraction noextract
let slice (#a:Type) (#len:flen) (s:ntuple a len) (start:nat) (fin:flen{start < fin /\ fin <= len}) : ntuple a (fin - start) =
  normalize_term (sub s start (fin - start))

let update_sub #a #len s start n x =
  normalize_term (createi len (fun i -> if i < start || i >= start+n then index s i else index x (i - start)))

let index_update_sub_lemma #a #len s start n x i =
  createi_lemma len (fun i -> if i < start || i >= start+n then index s i else index x (i - start)) i

//TODO: add to fsti?
inline_for_extraction
let update_slice (#a:Type) (#len:flen) (s:ntuple a len) (start:nat) (fin:flen{start < fin /\ fin <= len})
  (x:ntuple a (fin - start)) : ntuple a len
 =
  normalize_term (update_sub s start (fin - start) x)

let mapi #a #b #len f s =
  normalize_term (createi len (fun i -> f i (index s i)))

let index_mapi_lemma #a #b #len f s i =
  createi_lemma len (fun i -> f i (index s i)) i

let gmapi #a #b #len f s =
  normalize_term (gcreatei len (fun i -> f i (index s i)))

let index_gmapi_lemma #a #b #len f s i =
  gcreatei_lemma len (fun i -> f i (index s i)) i

let map #a #b #len f s =
  normalize_term (createi len (fun i -> f (index s i)))

let index_map_lemma #a #b #len f s i =
  createi_lemma len (fun i -> f (index s i)) i

let gmap #a #b #len f s =
  normalize_term (gcreatei len (fun i -> f (index s i)))

let index_gmap_lemma #a #b #len f s i =
  gcreatei_lemma len (fun i -> f (index s i)) i

let map2i #a #b #c #len f s1 s2 =
  normalize_term (createi len (fun i -> f i (index s1 i) (index s2 i)))

let index_map2i_lemma #a #b #c #len f s1 s2 i =
  createi_lemma len (fun i -> f i (index s1 i) (index s2 i)) i

let map2 #a #b #c #len f s1 s2 =
  normalize_term (createi len (fun i -> f (index s1 i) (index s2 i)))

let index_map2_lemma #a #b #c #len f s1 s2 i =
  createi_lemma len (fun i -> f (index s1 i) (index s2 i)) i

#set-options "--max_fuel 4"

let ntup1_lemma #a #l t =
  assert (ntuple a l == ntuple a 1)

let tup1_lemma #a #l t =
  assert (ntuple a l == ntuple a 1)

let ntup4_lemma #a #l t =
  assert (ntuple a l == ntuple a 4)

let tup4_lemma #a #l t =
  assert (ntuple a l == ntuple a 4);
  let (x0,(x1,(x2,x3))) = tup4 t in
  let t' : ntuple a 4 = (x0,(x1,(x2,x3))) in
  assert (t == t')
