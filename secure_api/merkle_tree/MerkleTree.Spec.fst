module MerkleTree.Spec

open FStar.Classical
open FStar.Mul
open FStar.Seq

open EverCrypt
open EverCrypt.Helpers

module List = FStar.List.Tot
module S = FStar.Seq

module EHS = EverCrypt.Hash // EverCrypt includes EverCrypt.Hash, so no need for this? 

inline_for_extraction noextract
let hash_alg = Spec.Hash.Definitions.SHA2_256

// fournet: hashLength would be closer to our naming conventions
// joonwonc: Some calculations
// - Spec.Hash.Definitions.word_length SHA2_256 = 4
// - Spec.Hash.Definitions.hash_word_length SHA2_256 = 8
// - Spec.Hash.Definitions.hash_length SHA2_256 = 32
inline_for_extraction noextract
val hash_size: nat
// joonwonc: KreMLin can't extract `Spec.Hash.Definitions.hash_length hash_alg`
inline_for_extraction noextract
let hash_size = 32 

// fournet: [tag] is a better name than [hash] for this
// Thus `hash_raw` is bytes of length 32
val hash_raw: eqtype
let hash_raw = b:Spec.Hash.Definitions.bytes_hash hash_alg

// joonwonc: Spec.Hash.Definitions.block_length SHA2_256 = 64
// Thus we can append `src1` and `src2` together to make it as a single block.
val hash2_raw: hash_raw -> hash_raw -> GTot hash_raw
let hash2_raw src1 src2 =
  let acc = EHS.acc0 #hash_alg in
  let acc = EHS.compress #hash_alg acc (S.append src1 src2) in
  EHS.extract #hash_alg acc

/// For simplicity, we will specify the root for a sequence of [i]
/// tags where [i <= 2^n] as the root of a full binary tree with [2^n]
/// leaves obtained by padding the sequence with dummies. This
/// requires extending the definitions of tags and hashes. Our
/// extended definition of hash justifies skipping any concrete
/// computation on dummies.

type hash =
| HRaw: hr:hash_raw -> hash
| HPad // right padding to make the size of a Merkle tree be a power of 2

val hash2: lh:hash -> rh:hash -> GTot hash
let hash2 lh rh =
  match lh with
  | HPad -> HPad
  | HRaw lhr ->
    match rh with
    | HPad -> lh
    | HRaw rhr -> HRaw (hash2_raw lhr rhr)

// fournet: [tags] a better name? 
noextract
val hash_seq: Type0
let hash_seq = S.seq hash

// fournet: systematically elide merkle_ or mt_ ?
type merkle_tree n = hs:Seq.seq hash{Seq.length hs = pow2 n}

val mt_get: #n:nat -> mt:merkle_tree n -> idx:nat{idx < pow2 n} -> GTot hash
let mt_get #n mt idx = Seq.index mt idx

// fournet: tempting, at least as a private notation? 
unfold let op_String_Access = Seq.index #hash 

val mt_left: #n:nat{n > 0} -> mt:merkle_tree n -> merkle_tree (n-1)
let mt_left #n mt = Seq.slice mt 0 (pow2 (n-1))

val mt_right: #n:nat{n > 0} -> mt:merkle_tree n -> merkle_tree (n-1)
let mt_right #n mt = Seq.slice mt (pow2 (n-1)) (pow2 n)

val mt_left_right:
  #n:nat{n > 0} -> mt:merkle_tree n ->
  Lemma (Seq.equal mt (mt_left mt @| mt_right mt))
let mt_left_right #n mt = ()

val hs_next_lv: 
  #n:nat -> hs:Seq.seq hash{Seq.length hs = 2 * n} ->
  GTot (nhs:Seq.seq hash{Seq.length nhs = n})
let rec hs_next_lv #n hs =
  if n = 0 then Seq.empty
  else Seq.cons 
    (hash2 hs.[0] hs.[1])
    (hs_next_lv #(n-1) (Seq.slice hs 2 (Seq.length hs)))

val hs_next_lv_index:
  #n:nat -> hs:Seq.seq hash{Seq.length hs = 2 * n} -> i:nat{i < n} ->
  Lemma ((hs_next_lv #n hs).[i] == hash2 hs.[2 * i] hs.[2 * i + 1])
let rec hs_next_lv_index #n hs i =
  if n = 0 || i = 0 then ()
  else hs_next_lv_index #(n - 1) (Seq.slice hs 2 (Seq.length hs)) (i - 1)

val hs_next_lv_slice:
  #n:nat -> hs:Seq.seq hash{Seq.length hs = 2 * n} ->
  i:nat -> j:nat{i <= j && j <= n} ->
  Lemma (requires True)
        (ensures (Seq.equal (hs_next_lv #(j - i) (Seq.slice hs (2 * i) (2 * j)))
                          (Seq.slice (hs_next_lv #n hs) i j)))
        (decreases (j - i))
#reset-options "--z3rlimit 10"
let rec hs_next_lv_slice #n hs i j =
  if i = j then ()
  else begin
    let x = Seq.slice hs (2 * i) (2 * j) in 
    assert (Seq.equal (hs_next_lv #(j - i) x)
                    (Seq.cons (hash2 x.[0] x.[1])
                            (hs_next_lv #(j - i - 1) (Seq.slice x 2 (Seq.length x)))));
    hs_next_lv_slice #n hs (i + 1) j;
    hs_next_lv_index #n hs i
  end

val mt_next_lv:
  #n:nat{n>0} -> mt:merkle_tree n -> GTot (merkle_tree (n-1))
let mt_next_lv #n mt = hs_next_lv #(pow2 (n-1)) mt

val mt_next_lv_mt_left:
  #n:nat{n>1} -> mt:merkle_tree n ->
  Lemma (Seq.equal (mt_next_lv (mt_left mt))
                 (mt_left (mt_next_lv mt)))
let mt_next_lv_mt_left #n mt = 
  hs_next_lv_slice #(pow2 (n-1)) mt 0 (pow2 (n-2))

val mt_next_lv_mt_right:
  #n:nat{n>1} -> mt:merkle_tree n ->
  Lemma (Seq.equal (mt_next_lv (mt_right mt))
                 (mt_right (mt_next_lv mt)))
let mt_next_lv_mt_right #n mt = 
  hs_next_lv_slice #(pow2 (n-1)) mt (pow2 (n-2)) (pow2 (n-1))

val hs_next_lv_equiv:
  j:nat -> n:nat{n > 0 && j <= 2 * n} ->
  hs1:Seq.seq hash{Seq.length hs1 = 2 * n} ->
  hs2:Seq.seq hash{Seq.length hs2 = 2 * n} ->
  Lemma (requires (Seq.equal (Seq.slice hs1 0 j) (Seq.slice hs2 0 j)))
        (ensures (Seq.equal (Seq.slice (hs_next_lv #n hs1) 0 (j / 2))
                          (Seq.slice (hs_next_lv #n hs2) 0 (j / 2))))
let hs_next_lv_equiv j n hs1 hs2 =
  forall_intro (hs_next_lv_index #n hs1);
  forall_intro (hs_next_lv_index #n hs2);
  let hs1' = hs_next_lv #n hs1 in 
  let hs2' = hs_next_lv #n hs2 in 
  assert (forall (i:nat{i < j / 2}). hs1'.[i] == hash2 hs1.[2 * i] hs1.[2 * i + 1]);
  assert (forall (i:nat{i < j / 2}). hs2'.[i] == hash2 hs2.[2 * i] hs2.[2 * i + 1]);
  assert (forall (i:nat{i < j}).     (Seq.slice hs1 0 j).[i] == (Seq.slice hs2 0 j).[i]);
  assert (forall (i:nat{i < j}).     hs1.[i] == hs2.[i]);
  assert (forall (i:nat{i < j / 2}). hs1.[2 * i] == hs2.[2 * i]);
  assert (forall (i:nat{i < j / 2}). hs1.[2 * i + 1] == hs2.[2 * i + 1]);
  assert (forall (i:nat{i < j / 2}). hs1'.[i] == hs2'.[i])

val mt_next_lv_equiv:
  j:nat -> n:nat{n > 0 && j <= pow2 n} ->
  mt1:merkle_tree n -> mt2:merkle_tree n ->
  Lemma (requires (Seq.equal (Seq.slice mt1 0 j) (Seq.slice mt2 0 j)))
        (ensures (Seq.equal (Seq.slice (mt_next_lv mt1) 0 (j / 2))
                          (Seq.slice (mt_next_lv mt2) 0 (j / 2))))
let mt_next_lv_equiv j n mt1 mt2 =
  hs_next_lv_equiv j (pow2 (n-1)) mt1 mt2

val hs_next_rel:
  n:nat ->
  hs:S.seq hash{S.length hs = 2 * n} ->
  nhs:S.seq hash{S.length nhs = n} ->
  GTot Type0
let hs_next_rel n hs nhs =
  forall (i:nat{i < n}).
    S.index nhs i ==
    hash2 (S.index hs (2 * i)) (S.index hs (2 * i + 1))

val mt_next_rel:
  n:nat{n > 0} ->
  mt:merkle_tree n ->
  nmt:merkle_tree (n - 1) ->
  GTot Type0
let mt_next_rel n mt nmt =
  hs_next_rel (pow2 (n-1)) mt nmt

val hs_next_rel_next_lv:
  n:nat ->
  hs:S.seq hash{S.length hs = 2 * n} ->
  nhs:S.seq hash{S.length nhs = n} ->
  Lemma (requires (hs_next_rel n hs nhs))
        (ensures (S.equal nhs (hs_next_lv #n hs)))
let rec hs_next_rel_next_lv n hs nhs =
  if n = 0 then ()
  else hs_next_rel_next_lv (n - 1)
         (S.slice hs 2 (S.length hs))
         (S.slice nhs 1 (S.length nhs))

val mt_next_rel_next_lv:
  n:nat{n > 0} ->
  mt:merkle_tree n ->
  nmt:merkle_tree (n - 1) ->
  Lemma (requires (mt_next_rel n mt nmt))
        (ensures (S.equal nmt (mt_next_lv mt)))
let mt_next_rel_next_lv n mt nmt =
  hs_next_rel_next_lv (pow2 (n-1)) mt nmt

val mt_next_rel_upd_even:
  n:nat{n > 0} ->
  mt:merkle_tree n ->
  nmt:merkle_tree (n - 1) ->
  i:nat{i < pow2 (n-1)} -> v:hash ->
  Lemma (requires (mt_next_rel n mt nmt))
        (ensures (mt_next_rel n
                   (S.upd mt (2 * i) v)
                   (S.upd nmt i (hash2 v (S.index mt (2 * i + 1))))))
let mt_next_rel_upd_even n mt nmt i v = ()

val mt_next_rel_upd_even_pad:
  n:nat{n > 0} ->
  mt:merkle_tree n ->
  nmt:merkle_tree (n - 1) ->
  i:nat{i < pow2 (n-1)} -> v:hash ->
  Lemma (requires (mt_next_rel n mt nmt /\
                  S.index mt (2 * i + 1) == HPad))
        (ensures (mt_next_rel n
                   (S.upd mt (2 * i) v)
                   (S.upd nmt i v)))
let mt_next_rel_upd_even_pad n mt nmt i v = ()

val mt_next_rel_upd_odd:
  n:nat{n > 0} ->
  mt:merkle_tree n ->
  nmt:merkle_tree (n - 1) ->
  i:nat{i < pow2 (n-1)} -> v:hash ->
  Lemma (requires (mt_next_rel n mt nmt))
        (ensures (mt_next_rel n
                   (S.upd mt (2 * i + 1) v)
                   (S.upd nmt i (hash2 (S.index mt (2 * i)) v))))
let mt_next_rel_upd_odd n mt nmt i v = ()

// fournet: just [root]? 
val mt_get_root: #n:nat -> mt:merkle_tree n -> GTot hash
let rec mt_get_root #n mt =
  if n = 0 then mt.[0]
  else mt_get_root (mt_next_lv mt)

val mt_get_root_step:
  #n:nat{n > 0} -> mt:merkle_tree n ->
  Lemma (mt_get_root mt =
        hash2 (mt_get_root (mt_left mt)) (mt_get_root (mt_right mt)))
let rec mt_get_root_step #n mt =
  if n = 1 then ()
  else begin
    mt_get_root_step (mt_next_lv mt);
    mt_next_lv_mt_left mt;
    mt_next_lv_mt_right mt
  end

type merkle_path n = p:Seq.seq hash{Seq.length p = n}

/// We first specify full paths, including padding.

val mt_get_path:
  #n:nat -> mt:merkle_tree n -> i:nat{i < pow2 n} -> GTot (merkle_path n)
let rec mt_get_path #n t i =
  if n = 0 then Seq.empty
  else Seq.cons 
    (if i % 2 = 0 then t.[i + 1] else t.[i - 1])
    (mt_get_path (mt_next_lv t) (i / 2))

val mt_verify_:
  #n:nat -> p:merkle_path n -> idx:nat{idx < pow2 n} -> hash -> GTot hash
let rec mt_verify_ #n p idx h =
  if n = 0 then h
  else mt_verify_ #(n-1) (Seq.tail p) (idx / 2)
                  (if idx % 2 = 0 
                  then hash2 h (Seq.head p)
                  else hash2 (Seq.head p) h)

val mt_verify:
  #n:nat -> p:merkle_path n -> idx:nat{idx < pow2 n} -> hash -> hash -> GTot bool
let mt_verify #n p idx h rt =
  rt = mt_verify_ p idx h


/// Correctness: the root of a tree is correctly recomputed from any of its paths

val hs_next_lv_get:
  #n:nat{n>0} -> hs:Seq.seq hash{Seq.length hs = 2 * n} -> idx:nat{idx < 2 * n} ->
  Lemma ((hs_next_lv #n hs).[idx / 2] ==
        (if idx % 2 = 0
        then hash2 hs.[idx] hs.[idx + 1]
        else hash2 hs.[idx - 1] hs.[idx])) 
let rec hs_next_lv_get #n hs idx =
  if idx < 2 then ()
  else hs_next_lv_get #(n-1) (Seq.slice hs 2 (Seq.length hs)) (idx - 2)

val mt_next_lv_get:
  #n:nat{n>0} -> mt:merkle_tree n -> idx:nat{idx < pow2 n} -> 
  Lemma (
    (mt_next_lv mt).[idx / 2] ==
    ( if idx % 2 = 0
      then hash2 mt.[idx] mt.[idx + 1]
      else hash2 mt.[idx - 1] mt.[idx]))
let mt_next_lv_get #n mt idx =
  hs_next_lv_get #(pow2 (n-1)) mt idx

val mt_get_path_ok_:
  #n:nat -> t:merkle_tree n -> i:nat{i < pow2 n} ->
  Lemma (mt_verify_ (mt_get_path t i) i (mt_get t i) == mt_get_root t)
let rec mt_get_path_ok_ #n mt idx =
  if n = 0 then ()
  else begin
    assert (Seq.head (mt_get_path mt idx) == (if idx % 2 = 0 then mt.[idx + 1] else mt.[idx - 1]));
    assert (Seq.equal (Seq.tail (mt_get_path mt idx)) 
                    (mt_get_path (mt_next_lv mt) (idx / 2)));
    mt_get_path_ok_ (mt_next_lv mt) (idx / 2);
    mt_next_lv_get mt idx
  end


/// Security: we reduce tree collisions to collisions on the hash
/// compression function. Such collisions yield collisions on the SHA2
/// standard (by adding the same length and padding to the
/// accumulators).
///
/// One complication addressed in the proof is the handling of
/// implicit padding.

val raw_hashes: hs:Seq.seq hash -> Tot Type0 (decreases (Seq.length hs))
let rec raw_hashes hs =
  if Seq.length hs = 0 then True
  else (HRaw? (Seq.head hs) /\ raw_hashes (Seq.tail hs))

val raw_hashes_raws: 
  hs:Seq.seq hash{raw_hashes hs} -> 
  Tot (Seq.seq hash_raw) (decreases (Seq.length hs))
let rec raw_hashes_raws hs =
  if Seq.length hs = 0 then Seq.empty
  else Seq.cons (HRaw?.hr (Seq.head hs)) (raw_hashes_raws (Seq.tail hs))

val raw_hashes_index:
  hs:Seq.seq hash -> i:nat{i < Seq.length hs} ->
  Lemma (requires (raw_hashes hs))
        (ensures (HRaw? hs.[i]))
        (decreases i)
let rec raw_hashes_index hs i =
  if i = 0 then ()
  else raw_hashes_index (Seq.tail hs) (i - 1)

val raw_hashes_slice:
  hs:Seq.seq hash -> i:nat -> j:nat{i <= j && j <= Seq.length hs} ->
  Lemma (requires (raw_hashes hs))
        (ensures (raw_hashes (Seq.slice hs i j)))
        (decreases (j - i))
let rec raw_hashes_slice hs i j =
  if i = j then ()
  else (
    raw_hashes_index hs i;
    raw_hashes_slice hs (i + 1) j)

val pad_hashes: hs:Seq.seq hash -> Type0
let rec pad_hashes hs =
  Seq.equal hs (Seq.create (Seq.length hs) HPad)

val pad_hashes_slice:
  hs:Seq.seq hash -> i:nat -> j:nat{i <= j && j <= Seq.length hs} ->
  Lemma (requires (pad_hashes hs))
        (ensures (pad_hashes (Seq.slice hs i j)))
        (decreases (j - i))
let rec pad_hashes_slice hs i j =
  if i = j then ()
  else pad_hashes_slice hs (i + 1) j

/// Right-padded Merkle tree, a tree refinement

let rpmt (n:nat) (i:nat{i <= pow2 n}) = 
  mt:merkle_tree n { 
    raw_hashes (Seq.slice mt 0 i) /\
    pad_hashes (Seq.slice mt i (Seq.length mt)) }

val rpmt_raws: #n:nat -> #i:nat{i <= pow2 n} -> mt:rpmt n i -> Seq.seq hash_raw
let rpmt_raws #n #i mt = raw_hashes_raws (Seq.slice mt 0 i)

val rpmt_i_0:
  #n:nat -> 
  mt:rpmt n 0 ->
  Lemma (Seq.equal mt (Seq.create (pow2 n) HPad))
let rpmt_i_0 #n mt = ()

val rpmt_left: 
  #n:nat{n > 0} -> #i:nat{i <= pow2 n} -> rpmt n i -> 
  rpmt (n-1) (if i <= pow2 (n-1) then i else pow2 (n-1))
let rpmt_left #n #i mt = 
  if i <= pow2 (n-1) 
  then pad_hashes_slice (Seq.slice mt i (Seq.length mt)) 0 (pow2 (n-1) - i)
  else raw_hashes_slice (Seq.slice mt 0 i) 0 (pow2 (n-1)); 
  mt_left mt
  
#reset-options "--z3rlimit 40"
val rpmt_right: 
  #n:nat{n > 0} -> #i:nat{i <= pow2 n} -> rpmt n i -> 
  rpmt (n-1) (if i <= pow2 (n-1) then 0 else i - pow2 (n-1))
let rpmt_right #n #i mt = 
  if i <= pow2 (n-1) 
  then pad_hashes_slice (Seq.slice mt i (Seq.length mt)) (pow2 (n-1) - i) (pow2 n - i)
  else raw_hashes_slice (Seq.slice mt 0 i) (pow2 (n-1)) i; 
  mt_right mt 

/// Two right-padded merkle trees collide when 
/// 1) they have the same height (`n`) and number of raw hashes (`i`),
/// 2) their contents differ, and
/// 3) their roots are same.

// fournet: we may want to work towards removing 1) using a hash prefix

type mt_collide (n:nat) (i:nat{i <= pow2 n}) = | Collision: 
  mt1:rpmt n i -> mt2:rpmt n i {
    mt1 <> mt2 && 
    mt_get_root mt1 = mt_get_root mt2 } -> mt_collide n i

type hash2_raw_collide = | Collision2:
  lh1:hash_raw -> rh1:hash_raw -> 
  lh2:hash_raw -> rh2:hash_raw { 
    (lh1 <> lh2 \/ rh1 <> rh2) /\
    hash2_raw lh1 rh1 = hash2_raw lh2 rh2 } -> hash2_raw_collide

/// Auxiliary lemmas for the proof

val rpmt_pad_hashes_0:
  #n:nat -> #i:nat{i <= pow2 n} -> mt:rpmt n i ->
  Lemma (i = 0 <==> pad_hashes mt )
let rpmt_pad_hashes_0 #n #i mt = ()

val rpmt_pad_hashes_index_0:
  #n:nat -> #i:nat{i <= pow2 n} ->
  mt:rpmt n i ->
  Lemma (pad_hashes mt <==> HPad? mt.[0])
let rec rpmt_pad_hashes_index_0 #n #i mt = ()
 
val mt_get_root_pad_index_0:
  #n:nat -> mt:merkle_tree n ->
  Lemma (HPad? mt.[0] <==> HPad? (mt_get_root mt)) 
let rec mt_get_root_pad_index_0 #n (mt:merkle_tree n) =
  if n = 0 then ()
  else 
    let mt:merkle_tree (n-1) = mt_next_lv #n mt in 
    mt_get_root_pad_index_0 #(n-1) mt
#reset-options

val rpmt_get_root_pad_hashes:
  #n:nat -> #i:nat{i <= pow2 n} -> mt:rpmt n i ->
  Lemma (pad_hashes mt <==> HPad? (mt_get_root mt))
let rpmt_get_root_pad_hashes #n #i mt = 
  rpmt_pad_hashes_index_0 mt;
  mt_get_root_pad_index_0 mt

val rpmt_get_root_pad:
  #n:nat -> #i:nat{i <= pow2 n} -> mt:rpmt n i ->
  Lemma (i = 0 <==> HPad? (mt_get_root mt))
let rpmt_get_root_pad #n #i mt =
  rpmt_get_root_pad_hashes mt;
  rpmt_pad_hashes_0 mt

val rpmt_get_root_raw:
  #n:nat -> #i:nat{i <= pow2 n} -> mt:rpmt n i ->
  Lemma (i > 0 <==> HRaw? (mt_get_root mt))
let rpmt_get_root_raw #n #i mt =
  rpmt_get_root_pad mt

val extract:
  #n:nat -> #i:nat{i <= pow2 n} -> mt_collide n i -> GTot hash2_raw_collide
#set-options "--z3rlimit 100"
let rec extract #n #i (Collision t1 t2) =
  assert(n = 0 ==> Seq.equal t1 t2); // excludes n = 0
  mt_left_right t1; mt_left_right t2;
  mt_get_root_step t1; 
  mt_get_root_step t2;
  rpmt_get_root_pad t1;
  assert(i <> 0);
  let l1 = rpmt_left t1 in 
  let l2 = rpmt_left t2 in 
  let r1 = rpmt_right t1 in 
  let r2 = rpmt_right t2 in 
  if i <= pow2 (n-1)
  then (
    rpmt_get_root_pad r1; rpmt_get_root_pad r2;
    rpmt_i_0 r1; rpmt_i_0 r2;
    extract (Collision l1 l2))
  else (
    rpmt_get_root_raw l1; rpmt_get_root_raw l2;
    rpmt_get_root_raw r1; rpmt_get_root_raw r2;
    let HRaw lh1 = mt_get_root l1 in
    let HRaw lh2 = mt_get_root l2 in
    let HRaw rh1 = mt_get_root r1 in
    let HRaw rh2 = mt_get_root r2 in
    if lh1 <> lh2 || rh1 <> rh2 
    then Collision2 lh1 rh1 lh2 rh2  
    else if l1 = l2 
      then extract (Collision r1 r2)
      else extract (Collision l1 l2))

