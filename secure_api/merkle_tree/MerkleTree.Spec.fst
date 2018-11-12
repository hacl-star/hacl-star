module MerkleTree.Spec

open FStar.Mul
open FStar.Seq

module List = FStar.List.Tot
module S = FStar.Seq

assume val hash_raw: eqtype
assume val hash_2_raw: hash_raw -> hash_raw -> GTot hash_raw

type hash =
| HRaw of hash_raw
| HPad // right padding to make the size of a Merkle tree be a power of 2

val hash_2: lh:hash -> rh:hash -> GTot hash
let hash_2 lh rh =
  match lh with
  | HPad -> HPad
  | HRaw lhr ->
    match rh with
    | HPad -> lh
    | HRaw rhr -> HRaw (hash_2_raw lhr rhr)

val hash_seq: Type0
let hash_seq = S.seq hash

val hash_ss: Type0
let hash_ss = S.seq hash_seq

type merkle_tree n = hs:S.seq hash{S.length hs = pow2 n}

val mt_get: #n:nat -> mt:merkle_tree n -> idx:nat{idx < pow2 n} -> GTot hash
let mt_get #n mt idx = S.index mt idx

val mt_left: #n:nat{n > 0} -> mt:merkle_tree n -> GTot (merkle_tree (n-1))
let mt_left #n mt = S.slice mt 0 (pow2 (n-1))

val mt_right: #n:nat{n > 0} -> mt:merkle_tree n -> GTot (merkle_tree (n-1))
let mt_right #n mt = S.slice mt (pow2 (n-1)) (pow2 n)

val hs_next_lv: 
  #n:nat -> hs:S.seq hash{S.length hs = 2 * n} ->
  GTot (nhs:S.seq hash{S.length nhs = n})
let rec hs_next_lv #n hs =
  if n = 0 then S.empty
  else S.cons (hash_2 (S.index hs 0) (S.index hs 1))
              (hs_next_lv #(n-1) (S.slice hs 2 (S.length hs)))

val mt_next_lv:
  #n:nat{n>0} -> mt:merkle_tree n -> GTot (merkle_tree (n-1))
let mt_next_lv #n mt = hs_next_lv #(pow2 (n-1)) mt

val mt_get_root: #n:nat -> mt:merkle_tree n -> GTot hash
let rec mt_get_root #n mt =
  if n = 0 then mt_get mt 0
  else mt_get_root (mt_next_lv mt)

type merkle_path n = p:S.seq hash{S.length p = n}

val mt_get_path:
  #n:nat -> mt:merkle_tree n -> idx:nat{idx < pow2 n} ->
  GTot (merkle_path n)
let rec mt_get_path #n mt idx =
  if n = 0 then S.empty
  else S.cons (if idx % 2 = 0 
              then S.index mt (idx + 1)
              else S.index mt (idx - 1))
              (mt_get_path (mt_next_lv mt) (idx / 2))

val mt_verify_:
  #n:nat -> p:merkle_path n -> idx:nat{idx < pow2 n} -> h:hash -> GTot (rt:hash)
let rec mt_verify_ #n p idx h =
  if n = 0 then h
  else mt_verify_ #(n-1) (S.tail p) (idx / 2)
                  (if idx % 2 = 0 
                  then hash_2 h (S.head p)
                  else hash_2 (S.head p) h)

val mt_verify:
  #n:nat -> p:merkle_path n -> idx:nat{idx < pow2 n} -> h:hash ->
  rt:hash -> GTot bool
let mt_verify #n p idx h rt =
  rt = mt_verify_ p idx h

/// Correctness

val hs_next_lv_get:
  #n:nat{n>0} -> hs:S.seq hash{S.length hs = 2 * n} -> idx:nat{idx < 2 * n} ->
  Lemma (S.index (hs_next_lv #n hs) (idx / 2) ==
        (if idx % 2 = 0
        then hash_2 (S.index hs idx) (S.index hs (idx + 1))
        else hash_2 (S.index hs (idx - 1)) (S.index hs idx)))
let rec hs_next_lv_get #n hs idx =
  if idx = 0 then ()
  else if idx = 1 then ()
  else hs_next_lv_get #(n-1) (S.slice hs 2 (S.length hs)) (idx - 2)

val mt_next_lv_get:
  #n:nat{n>0} -> mt:merkle_tree n -> idx:nat{idx < pow2 n} ->
  Lemma (mt_get (mt_next_lv mt) (idx / 2) ==
        (if idx % 2 = 0
        then hash_2 (mt_get mt idx) (mt_get mt (idx + 1))
        else hash_2 (mt_get mt (idx - 1)) (mt_get mt idx)))
let mt_next_lv_get #n mt idx =
  hs_next_lv_get #(pow2 (n-1)) mt idx

val mt_get_path_ok_:
  #n:nat -> mt:merkle_tree n -> idx:nat{idx < pow2 n} ->
  Lemma (mt_verify_ (mt_get_path mt idx) idx (mt_get mt idx) == mt_get_root mt)
let rec mt_get_path_ok_ #n mt idx =
  if n = 0 then ()
  else begin
    assert (S.head (mt_get_path mt idx) ==
           (if idx % 2 = 0 then S.index mt (idx + 1) else S.index mt (idx - 1)));
    assert (S.equal (S.tail (mt_get_path mt idx)) 
                    (mt_get_path (mt_next_lv mt) (idx / 2)));
    mt_get_path_ok_ (mt_next_lv mt) (idx / 2);
    mt_next_lv_get mt idx
  end
  
/// Security

// Two merkle trees collide when 
// 1) they have the same height (thus the same number of elements),
// 2) their contents differ, and
// 3) their roots are valid (HRaw) and same.
val mt_collide:
  #n:nat -> mt1:merkle_tree n -> mt2:merkle_tree n -> GTot bool
let mt_collide #n mt1 mt2 =
  mt1 <> mt2 && 
  HRaw? (mt_get_root mt1) &&
  mt_get_root mt1 = mt_get_root mt2

val hash_2_raw_collide:
  lh1:hash_raw -> rh1:hash_raw ->
  lh2:hash_raw -> rh2:hash_raw ->
  GTot bool
let hash_2_raw_collide lh1 rh1 lh2 rh2 =
  (lh1, rh1) <> (lh2, rh2) && 
  hash_2_raw lh1 rh1 = hash_2_raw lh2 rh2

val mt_collide_implies_hash_raw_collide:
  #n:nat -> mt1:merkle_tree n -> mt2:merkle_tree n ->
  Lemma (requires (mt_collide mt1 mt2))
        (ensures (exists lh1 rh1 lh2 rh2. hash_2_raw_collide lh1 rh1 lh2 rh2))
let mt_collide_implies_hash_raw_collide #n mt1 mt2 =
  admit ()

