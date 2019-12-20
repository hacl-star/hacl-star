module MerkleTree.Spec

open FStar.Classical
open FStar.Mul
open FStar.Seq

module S = FStar.Seq

#set-options "--max_fuel 0 --max_ifuel 0 --z3rlimit 10"

// For SHA2_256, this is is a sequence of 32 bytes
// These are secret bytes, hence not an eqtype
type hash (#hsz:pos) = b:Spec.Hash.Definitions.bytes { Seq.length b = hsz }

type hash_fun_t (#hsz:pos) = hash #hsz -> hash #hsz -> GTot (hash #hsz)

val sha256_compress: hash_fun_t #32
let sha256_compress src1 src2 =
  let sz = Spec.Hash.Definitions.SHA2_256 in
  let hash_alg = Spec.Hash.Definitions.SHA2_256 in
  let acc = Spec.Agile.Hash.init hash_alg in
  let acc = Spec.Agile.Hash.update hash_alg acc (S.append src1 src2) in
  Spec.Hash.PadFinish.finish hash_alg acc 

/// For simplicity, we will specify the root for a sequence of [i]
/// tags where [i <= 2^n] as the root of a full binary tree with [2^n]
/// leaves obtained by padding the sequence with dummies. This
/// requires extending the definitions of hashes and hash functions. Our
/// extended definition of hash justifies skipping any concrete
/// computation on dummies.
noeq
type padded_hash #hsz =
| HRaw: hr:hash #hsz -> padded_hash #hsz
| HPad // right padding to make the size of a Merkle tree a power of 2

val padded_hash_fun: (#hsz:pos) -> (f:hash_fun_t #hsz) -> (lh:padded_hash #hsz) -> (rh:padded_hash #hsz) -> GTot (padded_hash #hsz)
let padded_hash_fun #hsz f lh rh =
  allow_inversion (padded_hash #hsz);
  match lh, rh with
  | HPad    , _        -> HPad
  | _       , HPad     -> lh
  | HRaw lhr, HRaw rhr -> HRaw (f lhr rhr)

noextract
val hashes (#hsz:pos): Type0
let hashes #hsz = S.seq (padded_hash #hsz)

type merkle_tree (#hsz:pos) n = hs:hashes #hsz {S.length hs = pow2 n}

val mt_get: #hsz:pos -> #n:nat -> mt:merkle_tree #hsz n -> idx:nat{idx < pow2 n} -> GTot (padded_hash #hsz)
let mt_get #_ #_ mt idx = S.index mt idx

unfold let op_String_Access (#hsz:pos) = S.index #(padded_hash #hsz)

#push-options "--max_fuel 1"

val mt_left: #hsz:pos -> #n:pos -> mt:merkle_tree #hsz n -> merkle_tree #hsz (n-1)
let mt_left #_ #n mt = S.slice mt 0 (pow2 (n-1))

val mt_right: #hsz:pos -> #n:pos -> mt:merkle_tree #hsz n -> merkle_tree #hsz (n-1)
let mt_right #_ #n mt = S.slice mt (pow2 (n-1)) (pow2 n)

val mt_left_right: #hsz:pos -> #n:pos -> mt:merkle_tree #hsz n ->
  Lemma (S.equal mt (mt_left mt @| mt_right mt))
let mt_left_right #_ #_ mt = ()

val hs_next_lv: #hsz:pos -> #f:hash_fun_t #hsz -> #n:nat -> hs:hashes #hsz {S.length hs = 2 * n} -> GTot (nhs:hashes #hsz {S.length nhs = n})
let rec hs_next_lv #hsz #f #n hs =
  if n = 0 then S.empty
  else S.cons
    (padded_hash_fun #hsz f hs.[0] hs.[1])
    (hs_next_lv #hsz #f #(n-1) (S.slice hs 2 (S.length hs)))

val hs_next_lv_index: #hsz:pos -> #f:hash_fun_t #hsz -> #n:nat  -> hs:hashes{S.length hs = 2 * n} -> i:nat{i < n} ->
  Lemma ((hs_next_lv #hsz #f #n hs).[i] == padded_hash_fun #hsz f hs.[2 * i] hs.[2 * i + 1])
let rec hs_next_lv_index #hsz #f #n hs i =
  if n = 0 || i = 0 then ()
  else hs_next_lv_index #hsz #f #(n - 1) (S.slice hs 2 (S.length hs)) (i - 1)

val hs_next_lv_slice:
  #hsz:pos -> #f:hash_fun_t #hsz -> #n:nat  ->
  hs:hashes{S.length hs = 2 * n} -> i:nat -> j:nat{i <= j && j <= n} ->
  Lemma (requires True)
        (ensures  S.equal (hs_next_lv #hsz #f #(j - i) (S.slice hs (2 * i) (2 * j)))
                          (S.slice (hs_next_lv #hsz #f #n hs) i j))
        (decreases (j - i))
let rec hs_next_lv_slice #hsz #f #n hs i j =
  if i = j then ()
  else begin
    let x = S.slice hs (2 * i) (2 * j) in
    assert (S.equal (hs_next_lv #hsz #f #(j - i) x)
                    (S.cons (padded_hash_fun #hsz f x.[0] x.[1])
                            (hs_next_lv #hsz #f #(j - i - 1) (S.slice x 2 (S.length x)))));
    hs_next_lv_slice #hsz #f #n hs (i + 1) j;
    hs_next_lv_index #hsz #f #n hs i
  end

val mt_next_lv: #hsz:pos -> #f:hash_fun_t #hsz -> #n:pos -> mt:merkle_tree #hsz n -> GTot (merkle_tree #hsz (n-1))
let mt_next_lv #_ #f #n mt = hs_next_lv #_ #f #(pow2 (n-1)) mt

val mt_next_lv_mt_left: #hsz:pos -> #f:hash_fun_t #hsz -> #n:nat{1 < n} -> mt:merkle_tree #hsz n ->
  Lemma (S.equal (mt_next_lv #_ #f #_ (mt_left mt)) (mt_left (mt_next_lv #_ #f #_ mt)))
let mt_next_lv_mt_left #hsz #f #n mt =
  hs_next_lv_slice #_ #f #(pow2 (n-1)) mt 0 (pow2 (n-2))

val mt_next_lv_mt_right: #hsz:pos -> #f:hash_fun_t #hsz -> #n:nat{1 < n} -> mt:merkle_tree #hsz n ->
  Lemma (S.equal (mt_next_lv #_ #f #_ (mt_right mt)) (mt_right (mt_next_lv #_ #f #_ mt)))
let mt_next_lv_mt_right #hsz #f #n mt =
  hs_next_lv_slice #hsz #f #(pow2 (n-1)) mt (pow2 (n-2)) (pow2 (n-1))

val hs_next_lv_equiv:
  #hsz:pos -> #f:hash_fun_t #hsz ->
  j:nat -> n:pos{j <= 2 * n} ->
  hs1:hashes{S.length hs1 = 2 * n} ->
  hs2:hashes{S.length hs2 = 2 * n} ->
  Lemma (requires S.equal (S.slice hs1 0 j) (S.slice hs2 0 j))
        (ensures  S.equal (S.slice (hs_next_lv #hsz #f #n hs1) 0 (j / 2))
                          (S.slice (hs_next_lv #hsz #f #n hs2) 0 (j / 2)))
let hs_next_lv_equiv #hsz #f j n hs1 hs2 =
  forall_intro (hs_next_lv_index #_ #f #n hs1);
  forall_intro (hs_next_lv_index #_ #f #n hs2);
  let hs1' = hs_next_lv #_ #f #n hs1 in
  let hs2' = hs_next_lv #_ #f #n hs2 in
  assert (forall (i:nat{i < j / 2}). hs1'.[i] == padded_hash_fun #hsz f hs1.[2 * i] hs1.[2 * i + 1]);
  assert (forall (i:nat{i < j / 2}). hs2'.[i] == padded_hash_fun #hsz f hs2.[2 * i] hs2.[2 * i + 1]);
  assert (forall (i:nat{i < j}).     (S.slice hs1 0 j).[i] == (S.slice hs2 0 j).[i]);
  assert (forall (i:nat{i < j}).     hs1.[i] == hs2.[i]);
  assert (forall (i:nat{i < j / 2}). hs1.[2 * i] == hs2.[2 * i]);
  assert (forall (i:nat{i < j / 2}). hs1.[2 * i + 1] == hs2.[2 * i + 1]);
  assert (forall (i:nat{i < j / 2}). hs1'.[i] == hs2'.[i])

val mt_next_lv_equiv:
  #hsz:pos -> #f:hash_fun_t #hsz ->
  j:nat -> n:pos{j <= pow2 n} ->
  mt1:merkle_tree #hsz n -> mt2:merkle_tree #hsz n ->
  Lemma (requires S.equal (S.slice mt1 0 j) (S.slice mt2 0 j))
        (ensures  S.equal (S.slice (mt_next_lv #_ #f #_ mt1) 0 (j / 2))
                          (S.slice (mt_next_lv #_ #f #_ mt2) 0 (j / 2)))
let mt_next_lv_equiv #hsz #f j n mt1 mt2 =
  hs_next_lv_equiv #_ #f j (pow2 (n-1)) mt1 mt2

val hs_next_rel:
  #hsz:pos -> #f:hash_fun_t #hsz ->
  n:nat ->
  hs:hashes #hsz {S.length hs = 2 * n} ->
  nhs:hashes #hsz {S.length nhs = n} ->
  GTot Type0
let hs_next_rel #hsz #f n hs nhs =
  forall (i:nat{i < n}).
    S.index nhs i ==
    padded_hash_fun #hsz f (S.index hs (2 * i)) (S.index hs (2 * i + 1))

val mt_next_rel:
  #hsz:pos -> #f:hash_fun_t #hsz ->
  n:pos ->
  mt:merkle_tree #hsz n ->
  nmt:merkle_tree #hsz (n - 1) ->
  GTot Type0
let mt_next_rel #hsz #f n mt nmt =
  hs_next_rel #hsz #f (pow2 (n-1)) mt nmt

val hs_next_rel_next_lv:
  #hsz:pos -> #f:hash_fun_t #hsz ->
  n:nat ->
  hs:hashes{S.length hs = 2 * n} ->
  nhs:hashes{S.length nhs = n} ->
  Lemma (requires hs_next_rel #_ #f n hs nhs)
        (ensures  S.equal nhs (hs_next_lv #_ #f #n hs))
let rec hs_next_rel_next_lv #hsz #f n hs nhs =
  if n = 0 then ()
  else hs_next_rel_next_lv #_ #f (n - 1)
         (S.slice hs  2 (S.length hs))
         (S.slice nhs 1 (S.length nhs))

val mt_next_rel_next_lv:
  #hsz:pos -> #f:hash_fun_t #hsz ->
  n:pos ->
  mt:merkle_tree #hsz n ->
  nmt:merkle_tree (n - 1) ->
  Lemma (requires mt_next_rel #_ #f n mt nmt)
        (ensures  S.equal nmt (mt_next_lv #_ #f mt))
let mt_next_rel_next_lv #hsz #f n mt nmt =
  hs_next_rel_next_lv #_ #f (pow2 (n-1)) mt nmt

val mt_next_rel_upd_even:
  #hsz:pos -> #f:hash_fun_t #hsz ->
  n:pos ->
  mt:merkle_tree #hsz n ->
  nmt:merkle_tree (n - 1) ->
  i:nat{i < pow2 (n-1)} -> 
  v:padded_hash ->
  Lemma (requires mt_next_rel #_ #f n mt nmt)
        (ensures  mt_next_rel #_ #f n
                   (S.upd mt (2 * i) v)
                   (S.upd nmt i (padded_hash_fun #hsz f v (S.index mt (2 * i + 1)))))
let mt_next_rel_upd_even #hsz #f n mt nmt i v = ()

#push-options "--z3rlimit 10 --initial_fuel 1 --max_fuel 1 --initial_ifuel 1 --max_ifuel 1"
val mt_next_rel_upd_even_pad:
  #hsz:pos -> #f:hash_fun_t #hsz ->
  n:pos ->
  mt:merkle_tree #hsz n ->
  nmt:merkle_tree #hsz (n - 1) ->
  i:nat{i < pow2 (n-1)} -> 
  v:padded_hash #hsz ->
  Lemma (requires (mt_next_rel #_ #f n mt nmt) /\ (S.index mt (2 * i + 1) == HPad))
        (ensures (mt_next_rel #_ #f n (S.upd mt (2 * i) v) (S.upd nmt i v)))
let mt_next_rel_upd_even_pad #hsz #f n mt nmt i v = ()
#pop-options

val mt_next_rel_upd_odd:
  #hsz:pos -> #f:hash_fun_t #hsz ->
  n:pos ->
  mt:merkle_tree #hsz n ->
  nmt:merkle_tree (n - 1) ->
  i:nat{i < pow2 (n-1)} -> 
  v:padded_hash ->
  Lemma (requires mt_next_rel #_ #f n mt nmt)
        (ensures  mt_next_rel #_ #f n
                   (S.upd mt (2 * i + 1) v)
                   (S.upd nmt i (padded_hash_fun #_ f (S.index mt (2 * i)) v)))
let mt_next_rel_upd_odd #hsz #f n mt nmt i v = ()

// fournet: just [root]?
val mt_get_root: 
  #hsz:pos -> #f:hash_fun_t #hsz ->
  #n:nat -> mt:merkle_tree #hsz n -> GTot (padded_hash #hsz)
let rec mt_get_root #hsz #f #n mt =
  if n = 0 then mt.[0]
  else mt_get_root #_ #f (mt_next_lv #_ #f mt)

#push-options "--initial_fuel 2 --max_fuel 2"

val mt_get_root_step: #hsz:pos -> #f:hash_fun_t #hsz -> #n:pos -> mt:merkle_tree #hsz n ->
  Lemma (mt_get_root #_ #f mt ==
         padded_hash_fun #_ f (mt_get_root #_ #f (mt_left mt)) (mt_get_root #_ #f (mt_right mt)))
let rec mt_get_root_step #hsz #f #n mt =
  if n = 1 then ()
  else begin
    mt_get_root_step #_ #f (mt_next_lv #_ #f mt);
    mt_next_lv_mt_left #_ #f mt;
    mt_next_lv_mt_right #_ #f mt
  end

#pop-options

type path #hsz n = S.lseq (padded_hash #hsz) n

/// We first specify full paths, including padding.

val mt_get_path: 
  #hsz:pos -> #f:hash_fun_t #hsz -> #n:nat -> 
  mt:merkle_tree #hsz n -> i:nat{i < pow2 n} -> GTot (path #hsz n)
let rec mt_get_path #hsz #f #n t i =
  if n = 0 then S.empty
  else S.cons
    (if i % 2 = 0 then t.[i + 1] else t.[i - 1])
    (mt_get_path #_ #f (mt_next_lv #_ #f t) (i / 2))

val mt_verify_: 
  #hsz:pos -> #f:hash_fun_t #hsz ->#n:nat -> 
  p:path #hsz n -> idx:nat{idx < pow2 n} -> padded_hash #hsz -> GTot (padded_hash #hsz)
let rec mt_verify_ #hsz #f #n p idx h =
  if n = 0 then h
  else mt_verify_ #_ #f #(n-1) (S.tail p) (idx / 2)
                  (if idx % 2 = 0
                   then padded_hash_fun #_ f h (S.head p)
                   else padded_hash_fun #_ f (S.head p) h)

val mt_verify: 
  #hsz:pos -> #f:hash_fun_t #hsz -> #n:nat -> 
  p:(path #hsz n) -> idx:nat{idx < pow2 n} -> padded_hash #hsz -> padded_hash #hsz -> GTot prop
let mt_verify #hsz #f #n p idx h rt =
  rt == mt_verify_ #_ #f p idx h


/// Correctness: the root of a tree is correctly recomputed from any of its paths

val hs_next_lv_get: 
  #hsz:pos -> #f:hash_fun_t #hsz -> #n:pos -> 
  hs:hashes{S.length hs = 2 * n} -> idx:nat{idx < 2 * n} ->
  Lemma ((hs_next_lv #_ #f #n hs).[idx / 2] ==
         (if idx % 2 = 0
          then padded_hash_fun #_ f hs.[idx] hs.[idx + 1]
          else padded_hash_fun #_ f hs.[idx - 1] hs.[idx]))
let rec hs_next_lv_get #hsz #f #n hs idx =
  if idx < 2 then ()
  else hs_next_lv_get #_ #f #(n-1) (S.slice hs 2 (S.length hs)) (idx - 2)

val mt_next_lv_get: 
  #hsz:pos -> #f:hash_fun_t #hsz -> #n:pos -> 
  mt:merkle_tree #hsz n -> idx:nat{idx < pow2 n} ->
  Lemma (
     (mt_next_lv #_ #f mt).[idx / 2] ==
     (if idx % 2 = 0
      then padded_hash_fun #_ f mt.[idx] mt.[idx + 1]
      else padded_hash_fun #_ f mt.[idx - 1] mt.[idx]))
let mt_next_lv_get #hsz #f #n mt idx =
  hs_next_lv_get #_ #f #(pow2 (n-1)) mt idx

val mt_get_path_ok_: 
  #hsz:pos -> #f:hash_fun_t #hsz -> #n:nat -> 
  t:merkle_tree #hsz n -> i:nat{i < pow2 n} ->
  Lemma (mt_verify_ #_ #f (mt_get_path #_ #f t i) i (mt_get t i) == mt_get_root #_ #f t)
let rec mt_get_path_ok_ #hsz #f #n mt idx =
  if n = 0 then ()
  else begin
    assert (S.head (mt_get_path #_ #f mt idx) == 
            (if idx % 2 = 0 then mt.[idx + 1] else mt.[idx - 1]));
    assert (S.equal (S.tail (mt_get_path #_ #f mt idx))
                    (mt_get_path #_ #f (mt_next_lv #_ #f mt) (idx / 2)));
    mt_get_path_ok_ #_ #f (mt_next_lv #_ #f mt) (idx / 2);
    mt_next_lv_get #_ #f mt idx
  end


/// Security: we reduce tree collisions to collisions on the hash
/// compression function. Such collisions yield collisions on the SHA2
/// standard (by adding the same length and padding to the
/// accumulators).
///
/// One complication addressed in the proof is the handling of
/// implicit padding.

/// All hashes in a sequence are raw hashes, not padding
val raw_hashes: 
  #hsz:pos -> #f:hash_fun_t #hsz ->
  hs:hashes #hsz -> Tot Type0 (decreases (S.length hs))
let rec raw_hashes #hsz #f hs =
  if S.length hs = 0 then True
  else (HRaw? (S.head hs) /\ raw_hashes #_ #f (S.tail hs))

val raw_hashes_raws: 
  #hsz:pos -> #f:hash_fun_t #hsz ->
  hs:hashes{raw_hashes #hsz #f hs} ->
  Tot (S.seq (hash #hsz)) (decreases (S.length hs))
let rec raw_hashes_raws #hsz #f hs =
  if S.length hs = 0 then S.empty
  else S.cons (HRaw?.hr (S.head hs)) (raw_hashes_raws #_ #f (S.tail hs))

val raw_hashes_index:
  #hsz:pos -> #f:hash_fun_t #hsz ->
  hs:hashes -> i:nat{i < S.length hs} ->
  Lemma (requires raw_hashes #_ #f hs)
        (ensures HRaw? #hsz hs.[i])
        (decreases i)
let rec raw_hashes_index #hsz #f hs i =
  if i = 0 then ()
  else raw_hashes_index #_ #f (S.tail hs) (i - 1)

val raw_hashes_slice:
  #hsz:pos -> #f:hash_fun_t #hsz ->
  hs:hashes -> i:nat -> j:nat{i <= j && j <= S.length hs} ->
  Lemma (requires raw_hashes #_ #f hs)
        (ensures  raw_hashes #_ #f (S.slice hs i j))
        (decreases (j - i))
let rec raw_hashes_slice #hsz #f hs i j =
  if i = j then ()
  else (
    raw_hashes_index #_ #f hs i;
    raw_hashes_slice #_ #f hs (i + 1) j)

/// All hashes in a sequence are just padding
val pad_hashes: 
  #hsz:pos -> #f:hash_fun_t #hsz ->
  hs:hashes #hsz -> Type0
let pad_hashes #hsz #f hs =
  S.equal hs (S.create (S.length hs) HPad)

val pad_hashes_slice:
  #hsz:pos -> #f:hash_fun_t #hsz ->
  hs:hashes -> i:nat -> j:nat{i <= j && j <= S.length hs} ->
  Lemma (requires pad_hashes #_ #f hs)
        (ensures  pad_hashes #_ #f (S.slice hs i j))
        (decreases (j - i))
let rec pad_hashes_slice #hsz #f hs i j =
  if i = j then ()
  else pad_hashes_slice #_ #f hs (i + 1) j

/// Right-padded Merkle tree, a tree refinement

let rpmt (#hsz:pos) (#f:hash_fun_t) (n:nat) (i:nat{i <= pow2 n}) =
  mt:merkle_tree #hsz n {
    raw_hashes #_ #f (S.slice mt 0 i) /\
    pad_hashes #_ #f (S.slice mt i (S.length mt)) }

val rpmt_raws: #hsz:pos -> #f:hash_fun_t #hsz -> #n:nat -> #i:nat{i <= pow2 n} -> mt:rpmt #hsz #f n i -> S.seq (hash #hsz)
let rpmt_raws #hsz #f #n #i mt = raw_hashes_raws #_ #f (S.slice mt 0 i)

val rpmt_i_0: #hsz:pos -> #f:hash_fun_t #hsz -> #n:nat -> mt:rpmt #hsz #f n 0 ->
  Lemma (S.equal mt (S.create (pow2 n) (HPad #hsz)))
let rpmt_i_0 #hsz #f #n mt = ()

val rpmt_left: #hsz:pos -> #f:hash_fun_t #hsz -> #n:pos -> #i:nat{i <= pow2 n} -> rpmt #hsz #f n i ->
  rpmt #hsz #f (n-1) (if i <= pow2 (n-1) then i else pow2 (n-1))
let rpmt_left #hsz #f #n #i mt =
  if i <= pow2 (n-1)
  then pad_hashes_slice #_ #f (S.slice mt i (S.length mt)) 0 (pow2 (n-1) - i)
  else raw_hashes_slice #_ #f (S.slice mt 0 i) 0 (pow2 (n-1));
  mt_left mt

#push-options "--z3rlimit 40"

val rpmt_right: #hsz:pos -> #f:hash_fun_t #hsz -> #n:pos -> #i:nat{i <= pow2 n} -> rpmt #hsz #f n i ->
  rpmt #_ #f (n-1) (if i <= pow2 (n-1) then 0 else i - pow2 (n-1))
let rpmt_right #hsz #f #n #i mt =
  if i <= pow2 (n-1)
  then pad_hashes_slice #_ #f (S.slice mt i (S.length mt)) (pow2 (n-1) - i) (pow2 n - i)
  else raw_hashes_slice #_ #f (S.slice mt 0 i) (pow2 (n-1)) i;
  mt_right mt

/// Two right-padded Merkle trees collide when
/// 1) they have the same height (`n`) and number of raw hashes (`i`),
/// 2) their contents differ, and
/// 3) their roots are same.

// fournet: we may want to work towards removing 1) using a hash prefix
noeq
type mt_collide (#hsz:pos) (#f:hash_fun_t #hsz) (n:nat) (i:nat{i <= pow2 n}) = | Collision:
  mt1:rpmt #_ #f n i -> mt2:rpmt #_ #f n i {
    mt1 =!= mt2 /\
    mt_get_root #_ #f #_ mt1 == mt_get_root #_ #f #_ mt2 } -> mt_collide #_ #f n i

noeq
type hash2_raw_collide = | Collision2:
  #hsz:pos -> #f:hash_fun_t #hsz ->
  lh1:hash -> rh1:hash ->
  lh2:hash -> rh2:hash {
    (lh1 =!= lh2 \/ rh1 =!= rh2) /\
    f lh1 rh1 == f lh2 rh2 } -> hash2_raw_collide

/// Auxiliary lemmas for the proof

val rpmt_pad_hashes_0:
  #hsz:pos -> #f:hash_fun_t #hsz ->
  #n:nat -> #i:nat{i <= pow2 n} -> mt:rpmt #_ #f n i ->
  Lemma (i = 0 <==> pad_hashes #_ #f mt )
let rpmt_pad_hashes_0 #_ #_ #n #i mt = ()

val rpmt_pad_hashes_index_0:
  #hsz:pos -> #f:hash_fun_t #hsz ->
  #n:nat -> #i:nat{i <= pow2 n} ->
  mt:rpmt #_ #f n i ->
  Lemma (pad_hashes #_ #f mt <==> HPad? mt.[0])
let rpmt_pad_hashes_index_0 #_ #_ #n #i mt = ()

val mt_get_root_pad_index_0:
  #hsz:pos -> #f:hash_fun_t #hsz ->
  #n:nat -> mt:merkle_tree #hsz n ->
  Lemma (HPad? mt.[0] <==> HPad? (mt_get_root #_ #f mt))
let rec mt_get_root_pad_index_0 #hsz #f #n (mt:merkle_tree #hsz n) =
  if n = 0 then ()
  else
    let mt:merkle_tree #hsz (n-1) = mt_next_lv #_ #f #n mt in
    mt_get_root_pad_index_0 #_ #f #(n-1) mt

#pop-options

val rpmt_get_root_pad_hashes:
  #hsz:pos -> #f:hash_fun_t #hsz ->
  #n:nat -> #i:nat{i <= pow2 n} -> mt:rpmt #_ #f n i ->
  Lemma (pad_hashes #_ #f mt <==> HPad? (mt_get_root #_ #f mt))
let rpmt_get_root_pad_hashes #_ #f #n #i mt =
  rpmt_pad_hashes_index_0 #_ #f mt;
  mt_get_root_pad_index_0 #_ #f mt

val rpmt_get_root_pad:
  #hsz:pos -> #f:hash_fun_t #hsz ->
  #n:nat -> #i:nat{i <= pow2 n} -> mt:rpmt #_ #f n i ->
  Lemma (i = 0 <==> HPad? (mt_get_root #_ #f mt))
let rpmt_get_root_pad #_ #f #n #i mt =
  rpmt_get_root_pad_hashes #_ #f mt;
  rpmt_pad_hashes_0 #_ #f mt

val rpmt_get_root_raw:
  #hsz:pos -> #f:hash_fun_t #hsz ->
  #n:nat -> #i:nat{i <= pow2 n} -> mt:rpmt #_ #f n i ->
  Lemma (i > 0 <==> HRaw? (mt_get_root #_ #f mt))
let rpmt_get_root_raw #hsz #f #n #i mt =
  allow_inversion (padded_hash #hsz);
  rpmt_get_root_pad #_ #f mt

#push-options "--z3rlimit 100"

val extract: 
  #hsz:pos -> #f:hash_fun_t #hsz ->
  #n:nat -> #i:nat{i <= pow2 n} -> mt_collide #_ #f n i -> GTot hash2_raw_collide
let rec extract #hsz #f #n #i (Collision t1 t2) =
  assert(n = 0 ==> S.equal t1 t2); // excludes n = 0
  mt_left_right t1; mt_left_right t2;
  mt_get_root_step #_ #f t1;
  mt_get_root_step #_ #f t2;
  rpmt_get_root_pad t1;
  assert(i <> 0);
  let l1 = rpmt_left t1 in
  let l2 = rpmt_left t2 in
  let r1 = rpmt_right t1 in
  let r2 = rpmt_right t2 in
  if i <= pow2 (n-1)
  then (
    rpmt_get_root_pad r1; rpmt_get_root_pad r2;
    rpmt_i_0 #_ #f r1; rpmt_i_0 #_ #f r2;
    extract (Collision l1 l2))
  else (
    rpmt_get_root_raw l1; rpmt_get_root_raw l2;
    rpmt_get_root_raw r1; rpmt_get_root_raw r2;
    let HRaw lh1 = mt_get_root #_ #f l1 in
    let HRaw lh2 = mt_get_root #_ #f l2 in
    let HRaw rh1 = mt_get_root #_ #f r1 in
    let HRaw rh2 = mt_get_root #_ #f r2 in
    if StrongExcludedMiddle.strong_excluded_middle (lh1 =!= lh2) ||
       StrongExcludedMiddle.strong_excluded_middle (rh1 =!= rh2)
    then Collision2 #_ #f lh1 rh1 lh2 rh2
    else if StrongExcludedMiddle.strong_excluded_middle (l1 == l2)
      then extract (Collision r1 r2)
      else extract (Collision l1 l2))
