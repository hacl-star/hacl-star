module MerkleTree.Spec

open FStar.Classical
open FStar.Mul
open FStar.Seq

module S = FStar.Seq

#set-options "--max_fuel 0 --max_ifuel 0 --z3rlimit 10"

inline_for_extraction noextract
let hash_alg = Spec.Hash.Definitions.SHA2_256

// fournet: hashLength would be closer to our naming conventions
let hash_size = Spec.Hash.Definitions.hash_length hash_alg

// fournet: [tag] is a better name than [hash] for this
// For SHA2_256, this is is a sequence of 32 bytes
// These are secret bytes, hence not an eqtype
let hash_raw = Spec.Hash.Definitions.bytes_hash hash_alg

// joonwonc: Spec.Hash.Definitions.block_length SHA2_256 = 64
// Thus we can hash two tags together with a single call to the compression function.
val hash2_raw: hash_raw -> hash_raw -> GTot hash_raw
let hash2_raw src1 src2 =
  let acc = Spec.Agile.Hash.init hash_alg in
  let acc = Spec.Agile.Hash.update hash_alg acc (S.append src1 src2) in
  Spec.Hash.PadFinish.finish hash_alg acc

/// For simplicity, we will specify the root for a sequence of [i]
/// tags where [i <= 2^n] as the root of a full binary tree with [2^n]
/// leaves obtained by padding the sequence with dummies. This
/// requires extending the definitions of tags and hashes. Our
/// extended definition of hash justifies skipping any concrete
/// computation on dummies.
noeq
type hash =
| HRaw: hr:hash_raw -> hash
| HPad // right padding to make the size of a Merkle tree a power of 2

val hash2: lh:hash -> rh:hash -> GTot hash
let hash2 lh rh =
  allow_inversion hash;
  match lh, rh with
  | HPad    , _        -> HPad
  | _       , HPad     -> lh
  | HRaw lhr, HRaw rhr -> HRaw (hash2_raw lhr rhr)

// fournet: [tags] a better name?
noextract
val hash_seq: Type0
let hash_seq = S.seq hash

// fournet: systematically elide merkle_ or mt_ ?
type merkle_tree n = hs:hash_seq{S.length hs = pow2 n}

val mt_get: #n:nat -> mt:merkle_tree n -> idx:nat{idx < pow2 n} -> GTot hash
let mt_get #n mt idx = S.index mt idx

unfold let op_String_Access = S.index #hash

#push-options "--max_fuel 1"

val mt_left: #n:pos -> mt:merkle_tree n -> merkle_tree (n-1)
let mt_left #n mt = S.slice mt 0 (pow2 (n-1))

val mt_right: #n:pos -> mt:merkle_tree n -> merkle_tree (n-1)
let mt_right #n mt = S.slice mt (pow2 (n-1)) (pow2 n)

val mt_left_right: #n:pos -> mt:merkle_tree n ->
  Lemma (S.equal mt (mt_left mt @| mt_right mt))
let mt_left_right #n mt = ()

val hs_next_lv: #n:nat -> hs:hash_seq{S.length hs = 2 * n} ->
  GTot (nhs:hash_seq{S.length nhs = n})
let rec hs_next_lv #n hs =
  if n = 0 then S.empty
  else S.cons
    (hash2 hs.[0] hs.[1])
    (hs_next_lv #(n-1) (S.slice hs 2 (S.length hs)))

val hs_next_lv_index: #n:nat -> hs:hash_seq{S.length hs = 2 * n} -> i:nat{i < n} ->
  Lemma ((hs_next_lv #n hs).[i] == hash2 hs.[2 * i] hs.[2 * i + 1])
let rec hs_next_lv_index #n hs i =
  if n = 0 || i = 0 then ()
  else hs_next_lv_index #(n - 1) (S.slice hs 2 (S.length hs)) (i - 1)

val hs_next_lv_slice:
  #n:nat -> hs:hash_seq{S.length hs = 2 * n} ->
  i:nat -> j:nat{i <= j && j <= n} ->
  Lemma (requires True)
        (ensures  S.equal (hs_next_lv #(j - i) (S.slice hs (2 * i) (2 * j)))
                          (S.slice (hs_next_lv #n hs) i j))
        (decreases (j - i))
let rec hs_next_lv_slice #n hs i j =
  if i = j then ()
  else begin
    let x = S.slice hs (2 * i) (2 * j) in
    assert (S.equal (hs_next_lv #(j - i) x)
                    (S.cons (hash2 x.[0] x.[1])
                            (hs_next_lv #(j - i - 1) (S.slice x 2 (S.length x)))));
    hs_next_lv_slice #n hs (i + 1) j;
    hs_next_lv_index #n hs i
  end

val mt_next_lv: #n:pos -> mt:merkle_tree n -> GTot (merkle_tree (n-1))
let mt_next_lv #n mt = hs_next_lv #(pow2 (n-1)) mt

val mt_next_lv_mt_left: #n:nat{1 < n} -> mt:merkle_tree n ->
  Lemma (S.equal (mt_next_lv (mt_left mt)) (mt_left (mt_next_lv mt)))
let mt_next_lv_mt_left #n mt =
  hs_next_lv_slice #(pow2 (n-1)) mt 0 (pow2 (n-2))

val mt_next_lv_mt_right: #n:nat{1 < n} -> mt:merkle_tree n ->
  Lemma (S.equal (mt_next_lv (mt_right mt)) (mt_right (mt_next_lv mt)))
let mt_next_lv_mt_right #n mt =
  hs_next_lv_slice #(pow2 (n-1)) mt (pow2 (n-2)) (pow2 (n-1))

val hs_next_lv_equiv:
  j:nat -> n:pos{j <= 2 * n} ->
  hs1:hash_seq{S.length hs1 = 2 * n} ->
  hs2:hash_seq{S.length hs2 = 2 * n} ->
  Lemma (requires S.equal (S.slice hs1 0 j) (S.slice hs2 0 j))
        (ensures  S.equal (S.slice (hs_next_lv #n hs1) 0 (j / 2))
                          (S.slice (hs_next_lv #n hs2) 0 (j / 2)))
let hs_next_lv_equiv j n hs1 hs2 =
  forall_intro (hs_next_lv_index #n hs1);
  forall_intro (hs_next_lv_index #n hs2);
  let hs1' = hs_next_lv #n hs1 in
  let hs2' = hs_next_lv #n hs2 in
  assert (forall (i:nat{i < j / 2}). hs1'.[i] == hash2 hs1.[2 * i] hs1.[2 * i + 1]);
  assert (forall (i:nat{i < j / 2}). hs2'.[i] == hash2 hs2.[2 * i] hs2.[2 * i + 1]);
  assert (forall (i:nat{i < j}).     (S.slice hs1 0 j).[i] == (S.slice hs2 0 j).[i]);
  assert (forall (i:nat{i < j}).     hs1.[i] == hs2.[i]);
  assert (forall (i:nat{i < j / 2}). hs1.[2 * i] == hs2.[2 * i]);
  assert (forall (i:nat{i < j / 2}). hs1.[2 * i + 1] == hs2.[2 * i + 1]);
  assert (forall (i:nat{i < j / 2}). hs1'.[i] == hs2'.[i])

val mt_next_lv_equiv:
  j:nat -> n:pos{j <= pow2 n} ->
  mt1:merkle_tree n -> mt2:merkle_tree n ->
  Lemma (requires S.equal (S.slice mt1 0 j) (S.slice mt2 0 j))
        (ensures  S.equal (S.slice (mt_next_lv mt1) 0 (j / 2))
                          (S.slice (mt_next_lv mt2) 0 (j / 2)))
let mt_next_lv_equiv j n mt1 mt2 =
  hs_next_lv_equiv j (pow2 (n-1)) mt1 mt2

val hs_next_rel:
  n:nat ->
  hs:hash_seq{S.length hs = 2 * n} ->
  nhs:hash_seq{S.length nhs = n} ->
  GTot Type0
let hs_next_rel n hs nhs =
  forall (i:nat{i < n}).
    S.index nhs i ==
    hash2 (S.index hs (2 * i)) (S.index hs (2 * i + 1))

val mt_next_rel:
  n:pos ->
  mt:merkle_tree n ->
  nmt:merkle_tree (n - 1) ->
  GTot Type0
let mt_next_rel n mt nmt =
  hs_next_rel (pow2 (n-1)) mt nmt

val hs_next_rel_next_lv:
  n:nat ->
  hs:hash_seq{S.length hs = 2 * n} ->
  nhs:hash_seq{S.length nhs = n} ->
  Lemma (requires hs_next_rel n hs nhs)
        (ensures  S.equal nhs (hs_next_lv #n hs))
let rec hs_next_rel_next_lv n hs nhs =
  if n = 0 then ()
  else hs_next_rel_next_lv (n - 1)
         (S.slice hs  2 (S.length hs))
         (S.slice nhs 1 (S.length nhs))

val mt_next_rel_next_lv:
  n:pos ->
  mt:merkle_tree n ->
  nmt:merkle_tree (n - 1) ->
  Lemma (requires mt_next_rel n mt nmt)
        (ensures  S.equal nmt (mt_next_lv mt))
let mt_next_rel_next_lv n mt nmt =
  hs_next_rel_next_lv (pow2 (n-1)) mt nmt

val mt_next_rel_upd_even:
  n:pos ->
  mt:merkle_tree n ->
  nmt:merkle_tree (n - 1) ->
  i:nat{i < pow2 (n-1)} -> 
  v:hash ->
  Lemma (requires mt_next_rel n mt nmt)
        (ensures  mt_next_rel n
                   (S.upd mt (2 * i) v)
                   (S.upd nmt i (hash2 v (S.index mt (2 * i + 1)))))
let mt_next_rel_upd_even n mt nmt i v = ()

val mt_next_rel_upd_even_pad:
  n:pos ->
  mt:merkle_tree n ->
  nmt:merkle_tree (n - 1) ->
  i:nat{i < pow2 (n-1)} -> 
  v:hash ->
  Lemma (requires mt_next_rel n mt nmt /\
                  S.index mt (2 * i + 1) == HPad)
        (ensures  mt_next_rel n
                   (S.upd mt (2 * i) v)
                   (S.upd nmt i v))
let mt_next_rel_upd_even_pad n mt nmt i v = ()

val mt_next_rel_upd_odd:
  n:pos ->
  mt:merkle_tree n ->
  nmt:merkle_tree (n - 1) ->
  i:nat{i < pow2 (n-1)} -> 
  v:hash ->
  Lemma (requires mt_next_rel n mt nmt)
        (ensures  mt_next_rel n
                   (S.upd mt (2 * i + 1) v)
                   (S.upd nmt i (hash2 (S.index mt (2 * i)) v)))
let mt_next_rel_upd_odd n mt nmt i v = ()

// fournet: just [root]?
val mt_get_root: #n:nat -> mt:merkle_tree n -> GTot hash
let rec mt_get_root #n mt =
  if n = 0 then mt.[0]
  else mt_get_root (mt_next_lv mt)

#push-options "--initial_fuel 2 --max_fuel 2"

val mt_get_root_step: #n:pos -> mt:merkle_tree n ->
  Lemma (mt_get_root mt ==
         hash2 (mt_get_root (mt_left mt)) (mt_get_root (mt_right mt)))
let rec mt_get_root_step #n mt =
  if n = 1 then ()
  else begin
    mt_get_root_step (mt_next_lv mt);
    mt_next_lv_mt_left mt;
    mt_next_lv_mt_right mt
  end

#pop-options

type merkle_path n = S.lseq hash n

/// We first specify full paths, including padding.

val mt_get_path: #n:nat -> mt:merkle_tree n -> i:nat{i < pow2 n} -> GTot (merkle_path n)
let rec mt_get_path #n t i =
  if n = 0 then S.empty
  else S.cons
    (if i % 2 = 0 then t.[i + 1] else t.[i - 1])
    (mt_get_path (mt_next_lv t) (i / 2))

val mt_verify_: #n:nat -> p:merkle_path n -> idx:nat{idx < pow2 n} -> hash -> GTot hash
let rec mt_verify_ #n p idx h =
  if n = 0 then h
  else mt_verify_ #(n-1) (S.tail p) (idx / 2)
                  (if idx % 2 = 0
                   then hash2 h (S.head p)
                   else hash2 (S.head p) h)

val mt_verify: #n:nat -> p:merkle_path n -> idx:nat{idx < pow2 n} -> hash -> hash -> GTot prop
let mt_verify #n p idx h rt =
  rt == mt_verify_ p idx h


/// Correctness: the root of a tree is correctly recomputed from any of its paths

val hs_next_lv_get: #n:pos -> hs:hash_seq{S.length hs = 2 * n} -> idx:nat{idx < 2 * n} ->
  Lemma ((hs_next_lv #n hs).[idx / 2] ==
         (if idx % 2 = 0
          then hash2 hs.[idx] hs.[idx + 1]
          else hash2 hs.[idx - 1] hs.[idx]))
let rec hs_next_lv_get #n hs idx =
  if idx < 2 then ()
  else hs_next_lv_get #(n-1) (S.slice hs 2 (S.length hs)) (idx - 2)

val mt_next_lv_get: #n:pos -> mt:merkle_tree n -> idx:nat{idx < pow2 n} ->
  Lemma (
     (mt_next_lv mt).[idx / 2] ==
     (if idx % 2 = 0
      then hash2 mt.[idx] mt.[idx + 1]
      else hash2 mt.[idx - 1] mt.[idx]))
let mt_next_lv_get #n mt idx =
  hs_next_lv_get #(pow2 (n-1)) mt idx

val mt_get_path_ok_: #n:nat -> t:merkle_tree n -> i:nat{i < pow2 n} ->
  Lemma (mt_verify_ (mt_get_path t i) i (mt_get t i) == mt_get_root t)
let rec mt_get_path_ok_ #n mt idx =
  if n = 0 then ()
  else begin
    assert (S.head (mt_get_path mt idx) == 
            (if idx % 2 = 0 then mt.[idx + 1] else mt.[idx - 1]));
    assert (S.equal (S.tail (mt_get_path mt idx))
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

/// All hashes in a sequence are raw hashes, not padding
val raw_hashes: hs:hash_seq -> Tot Type0 (decreases (S.length hs))
let rec raw_hashes hs =
  if S.length hs = 0 then True
  else (HRaw? (S.head hs) /\ raw_hashes (S.tail hs))

val raw_hashes_raws: hs:hash_seq{raw_hashes hs} ->
  Tot (S.seq hash_raw) (decreases (S.length hs))
let rec raw_hashes_raws hs =
  if S.length hs = 0 then S.empty
  else S.cons (HRaw?.hr (S.head hs)) (raw_hashes_raws (S.tail hs))

val raw_hashes_index:
  hs:hash_seq -> i:nat{i < S.length hs} ->
  Lemma (requires raw_hashes hs)
        (ensures HRaw? hs.[i])
        (decreases i)
let rec raw_hashes_index hs i =
  if i = 0 then ()
  else raw_hashes_index (S.tail hs) (i - 1)

val raw_hashes_slice:
  hs:hash_seq -> i:nat -> j:nat{i <= j && j <= S.length hs} ->
  Lemma (requires raw_hashes hs)
        (ensures  raw_hashes (S.slice hs i j))
        (decreases (j - i))
let rec raw_hashes_slice hs i j =
  if i = j then ()
  else (
    raw_hashes_index hs i;
    raw_hashes_slice hs (i + 1) j)

/// All hashes in a sequence are just padding
val pad_hashes: hs:hash_seq -> Type0
let rec pad_hashes hs =
  S.equal hs (S.create (S.length hs) HPad)

val pad_hashes_slice:
  hs:hash_seq -> i:nat -> j:nat{i <= j && j <= S.length hs} ->
  Lemma (requires pad_hashes hs)
        (ensures  pad_hashes (S.slice hs i j))
        (decreases (j - i))
let rec pad_hashes_slice hs i j =
  if i = j then ()
  else pad_hashes_slice hs (i + 1) j

/// Right-padded Merkle tree, a tree refinement

let rpmt (n:nat) (i:nat{i <= pow2 n}) =
  mt:merkle_tree n {
    raw_hashes (S.slice mt 0 i) /\
    pad_hashes (S.slice mt i (S.length mt)) }

val rpmt_raws: #n:nat -> #i:nat{i <= pow2 n} -> mt:rpmt n i -> S.seq hash_raw
let rpmt_raws #n #i mt = raw_hashes_raws (S.slice mt 0 i)

val rpmt_i_0: #n:nat -> mt:rpmt n 0 ->
  Lemma (S.equal mt (S.create (pow2 n) HPad))
let rpmt_i_0 #n mt = ()

val rpmt_left: #n:pos -> #i:nat{i <= pow2 n} -> rpmt n i ->
  rpmt (n-1) (if i <= pow2 (n-1) then i else pow2 (n-1))
let rpmt_left #n #i mt =
  if i <= pow2 (n-1)
  then pad_hashes_slice (S.slice mt i (S.length mt)) 0 (pow2 (n-1) - i)
  else raw_hashes_slice (S.slice mt 0 i) 0 (pow2 (n-1));
  mt_left mt

#push-options "--z3rlimit 40"

val rpmt_right: #n:pos -> #i:nat{i <= pow2 n} -> rpmt n i ->
  rpmt (n-1) (if i <= pow2 (n-1) then 0 else i - pow2 (n-1))
let rpmt_right #n #i mt =
  if i <= pow2 (n-1)
  then pad_hashes_slice (S.slice mt i (S.length mt)) (pow2 (n-1) - i) (pow2 n - i)
  else raw_hashes_slice (S.slice mt 0 i) (pow2 (n-1)) i;
  mt_right mt

/// Two right-padded Merkle trees collide when
/// 1) they have the same height (`n`) and number of raw hashes (`i`),
/// 2) their contents differ, and
/// 3) their roots are same.

// fournet: we may want to work towards removing 1) using a hash prefix
noeq
type mt_collide (n:nat) (i:nat{i <= pow2 n}) = | Collision:
  mt1:rpmt n i -> mt2:rpmt n i {
    mt1 =!= mt2 /\
    mt_get_root mt1 == mt_get_root mt2 } -> mt_collide n i

noeq
type hash2_raw_collide = | Collision2:
  lh1:hash_raw -> rh1:hash_raw ->
  lh2:hash_raw -> rh2:hash_raw {
    (lh1 =!= lh2 \/ rh1 =!= rh2) /\
    hash2_raw lh1 rh1 == hash2_raw lh2 rh2 } -> hash2_raw_collide

/// Auxiliary lemmas for the proof

val rpmt_pad_hashes_0:
  #n:nat -> #i:nat{i <= pow2 n} -> mt:rpmt n i ->
  Lemma (i = 0 <==> pad_hashes mt )
let rpmt_pad_hashes_0 #n #i mt = ()

val rpmt_pad_hashes_index_0:
  #n:nat -> #i:nat{i <= pow2 n} ->
  mt:rpmt n i ->
  Lemma (pad_hashes mt <==> HPad? mt.[0])
let rpmt_pad_hashes_index_0 #n #i mt = ()

val mt_get_root_pad_index_0:
  #n:nat -> mt:merkle_tree n ->
  Lemma (HPad? mt.[0] <==> HPad? (mt_get_root mt))
let rec mt_get_root_pad_index_0 #n (mt:merkle_tree n) =
  if n = 0 then ()
  else
    let mt:merkle_tree (n-1) = mt_next_lv #n mt in
    mt_get_root_pad_index_0 #(n-1) mt

#pop-options

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
  allow_inversion hash;
  rpmt_get_root_pad mt

#push-options "--z3rlimit 100"

val extract: #n:nat -> #i:nat{i <= pow2 n} -> mt_collide n i -> GTot hash2_raw_collide
let rec extract #n #i (Collision t1 t2) =
  assert(n = 0 ==> S.equal t1 t2); // excludes n = 0
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
    if StrongExcludedMiddle.strong_excluded_middle (lh1 =!= lh2) ||
       StrongExcludedMiddle.strong_excluded_middle (rh1 =!= rh2)
    then Collision2 lh1 rh1 lh2 rh2
    else if StrongExcludedMiddle.strong_excluded_middle (l1 == l2)
      then extract (Collision r1 r2)
      else extract (Collision l1 l2))
