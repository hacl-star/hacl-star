module MerkleTree.Spec

open FStar.Classical
open FStar.Mul
open FStar.Seq

open EverCrypt
open EverCrypt.Helpers

module List = FStar.List.Tot
module S = FStar.Seq

module EHS = EverCrypt.Hash

let hash_alg = Spec.Hash.Helpers.SHA2_256

// size_word SHA2_256 = 4
// size_hash_final_w SHA2_256 = 8
// size_hash SHA2_256 = 32
val hash_size: nat
let hash_size = Spec.Hash.Helpers.size_hash hash_alg

// Thus `hash_raw` is bytes of length 32
val hash_raw: eqtype
let hash_raw = b:Spec.Hash.Helpers.bytes_hash hash_alg

// size_block SHA2_256 = 64
// Thus we can append `src1` and `src2` together to make it as a single block.
val hash_2_raw: hash_raw -> hash_raw -> GTot hash_raw
let hash_2_raw src1 src2 =
  let acc = EHS.acc0 #hash_alg in
  let acc = EHS.compress #hash_alg acc (S.append src1 src2) in
  EHS.extract #hash_alg acc

type hash =
| HRaw: hr:hash_raw -> hash
| HPad // right padding to make the size of a Merkle tree be a power of 2

val hash_2: lh:hash -> rh:hash -> GTot hash
let hash_2 lh rh =
  match lh with
  | HPad -> HPad
  | HRaw lhr ->
    match rh with
    | HPad -> lh
    | HRaw rhr -> HRaw (hash_2_raw lhr rhr)

noextract
val hash_seq: Type0
let hash_seq = S.seq hash

noextract
val hash_ss: Type0
let hash_ss = S.seq hash_seq

type merkle_tree n = hs:S.seq hash{S.length hs = pow2 n}

val mt_get: #n:nat -> mt:merkle_tree n -> idx:nat{idx < pow2 n} -> GTot hash
let mt_get #n mt idx = S.index mt idx

val mt_left: #n:nat{n > 0} -> mt:merkle_tree n -> GTot (merkle_tree (n-1))
let mt_left #n mt = S.slice mt 0 (pow2 (n-1))

val mt_right: #n:nat{n > 0} -> mt:merkle_tree n -> GTot (merkle_tree (n-1))
let mt_right #n mt = S.slice mt (pow2 (n-1)) (pow2 n)

val mt_left_right:
  #n:nat{n > 0} -> mt:merkle_tree n ->
  Lemma (S.equal mt (S.append (mt_left mt) (mt_right mt)))
let mt_left_right #n mt = ()

val hs_next_lv: 
  #n:nat -> hs:S.seq hash{S.length hs = 2 * n} ->
  GTot (nhs:S.seq hash{S.length nhs = n})
let rec hs_next_lv #n hs =
  if n = 0 then S.empty
  else S.cons (hash_2 (S.index hs 0) (S.index hs 1))
              (hs_next_lv #(n-1) (S.slice hs 2 (S.length hs)))

val hs_next_lv_index:
  #n:nat -> hs:S.seq hash{S.length hs = 2 * n} ->
  i:nat{i < n} ->
  Lemma (requires True)
        (ensures (S.index (hs_next_lv #n hs) i ==
                 hash_2 (S.index hs (2 * i)) (S.index hs (2 * i + 1))))
let rec hs_next_lv_index #n hs i =
  if n = 0 then ()
  else if i = 0 then ()
  else hs_next_lv_index #(n - 1) (S.slice hs 2 (S.length hs)) (i - 1)

val hs_next_lv_slice:
  #n:nat -> hs:S.seq hash{S.length hs = 2 * n} ->
  i:nat -> j:nat{i <= j && j <= n} ->
  Lemma (requires True)
        (ensures (S.equal (hs_next_lv #(j - i) (S.slice hs (2 * i) (2 * j)))
                          (S.slice (hs_next_lv #n hs) i j)))
        (decreases (j - i))
#reset-options "--z3rlimit 10"
let rec hs_next_lv_slice #n hs i j =
  if i = j then ()
  else begin
    assert (S.equal (hs_next_lv #(j - i) (S.slice hs (2 * i) (2 * j)))
                    (S.cons (hash_2 (S.index (S.slice hs (2 * i) (2 * j)) 0)
                                    (S.index (S.slice hs (2 * i) (2 * j)) 1))
                            (hs_next_lv #(j - i - 1)
                              (S.slice (S.slice hs (2 * i) (2 * j))
                                2 (S.length (S.slice hs (2 * i) (2 * j)))))));
    hs_next_lv_slice #n hs (i + 1) j;
    hs_next_lv_index #n hs i
  end

val mt_next_lv:
  #n:nat{n>0} -> mt:merkle_tree n -> GTot (merkle_tree (n-1))
let mt_next_lv #n mt = hs_next_lv #(pow2 (n-1)) mt

val mt_next_lv_mt_left:
  #n:nat{n>1} -> mt:merkle_tree n ->
  Lemma (S.equal (mt_next_lv (mt_left mt))
                 (mt_left (mt_next_lv mt)))
let mt_next_lv_mt_left #n mt = 
  hs_next_lv_slice #(pow2 (n-1)) mt 0 (pow2 (n-2))

val mt_next_lv_mt_right:
  #n:nat{n>1} -> mt:merkle_tree n ->
  Lemma (S.equal (mt_next_lv (mt_right mt))
                 (mt_right (mt_next_lv mt)))
let mt_next_lv_mt_right #n mt = 
  hs_next_lv_slice #(pow2 (n-1)) mt (pow2 (n-2)) (pow2 (n-1))

val hs_next_lv_equiv:
  j:nat -> n:nat{n > 0 && j <= 2 * n} ->
  hs1:S.seq hash{S.length hs1 = 2 * n} ->
  hs2:S.seq hash{S.length hs2 = 2 * n} ->
  Lemma (requires (S.equal (S.slice hs1 0 j) (S.slice hs2 0 j)))
        (ensures (S.equal (S.slice (hs_next_lv #n hs1) 0 (j / 2))
                          (S.slice (hs_next_lv #n hs2) 0 (j / 2))))
let hs_next_lv_equiv j n hs1 hs2 =
  forall_intro (hs_next_lv_index #n hs1);
  forall_intro (hs_next_lv_index #n hs2);
  assert (forall (i:nat{i < j / 2}).
           S.index (hs_next_lv #n hs1) i ==
           hash_2 (S.index hs1 (2 * i)) (S.index hs1 (2 * i + 1)));
  assert (forall (i:nat{i < j / 2}).
           S.index (hs_next_lv #n hs2) i ==
           hash_2 (S.index hs2 (2 * i)) (S.index hs2 (2 * i + 1)));
  assert (forall (i:nat{i < j}).
           S.index (S.slice hs1 0 j) i == S.index (S.slice hs2 0 j) i);
  assert (forall (i:nat{i < j}). S.index hs1 i == S.index hs2 i);
  assert (forall (i:nat{i < j / 2}). S.index hs1 (2 * i) == S.index hs2 (2 * i));
  assert (forall (i:nat{i < j / 2}). S.index hs1 (2 * i + 1) == S.index hs2 (2 * i + 1));
  assert (forall (i:nat{i < j / 2}).
           S.index (hs_next_lv #n hs1) i == S.index (hs_next_lv #n hs2) i)

val mt_next_lv_equiv:
  j:nat -> n:nat{n > 0 && j <= pow2 n} ->
  mt1:merkle_tree n -> mt2:merkle_tree n ->
  Lemma (requires (S.equal (S.slice mt1 0 j) (S.slice mt2 0 j)))
        (ensures (S.equal (S.slice (mt_next_lv mt1) 0 (j / 2))
                          (S.slice (mt_next_lv mt2) 0 (j / 2))))
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
    hash_2 (S.index hs (2 * i)) (S.index hs (2 * i + 1))

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
                   (S.upd nmt i (hash_2 v (S.index mt (2 * i + 1))))))
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
                   (S.upd nmt i (hash_2 (S.index mt (2 * i)) v))))
let mt_next_rel_upd_odd n mt nmt i v = ()

val mt_get_root: #n:nat -> mt:merkle_tree n -> GTot hash
let rec mt_get_root #n mt =
  if n = 0 then mt_get mt 0
  else mt_get_root (mt_next_lv mt)

val mt_get_root_step:
  #n:nat{n > 0} -> mt:merkle_tree n ->
  Lemma (mt_get_root mt =
        hash_2 (mt_get_root (mt_left mt)) (mt_get_root (mt_right mt)))
let rec mt_get_root_step #n mt =
  if n = 1 then ()
  else begin
    mt_get_root_step (mt_next_lv mt);
    mt_next_lv_mt_left mt;
    mt_next_lv_mt_right mt
  end

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

val raw_hashes: hs:S.seq hash -> GTot Type0 (decreases (S.length hs))
let rec raw_hashes hs =
  if S.length hs = 0 then true
  else (HRaw? (S.head hs) /\ raw_hashes (S.tail hs))

val raw_hashes_raws: 
  hs:S.seq hash{raw_hashes hs} -> 
  GTot (S.seq hash_raw) (decreases (S.length hs))
let rec raw_hashes_raws hs =
  if S.length hs = 0 then S.empty
  else S.cons (HRaw?.hr (S.head hs)) (raw_hashes_raws (S.tail hs))

val raw_hashes_index:
  hs:S.seq hash -> i:nat{i < S.length hs} ->
  Lemma (requires (raw_hashes hs))
        (ensures (HRaw? (S.index hs i)))
        (decreases i)
let rec raw_hashes_index hs i =
  if i = 0 then ()
  else raw_hashes_index (S.tail hs) (i - 1)

val raw_hashes_slice:
  hs:S.seq hash -> i:nat -> j:nat{i <= j && j <= S.length hs} ->
  Lemma (requires (raw_hashes hs))
        (ensures (raw_hashes (S.slice hs i j)))
        (decreases (j - i))
let rec raw_hashes_slice hs i j =
  if i = j then ()
  else (raw_hashes_index hs i;
       raw_hashes_slice hs (i + 1) j)

val pad_hashes: hs:S.seq hash -> GTot Type0
let rec pad_hashes hs =
  S.equal hs (S.create (S.length hs) HPad)

val pad_hashes_slice:
  hs:S.seq hash -> i:nat -> j:nat{i <= j && j <= S.length hs} ->
  Lemma (requires (pad_hashes hs))
        (ensures (pad_hashes (S.slice hs i j)))
        (decreases (j - i))
let rec pad_hashes_slice hs i j =
  if i = j then ()
  else pad_hashes_slice hs (i + 1) j

type right_padded_merkle_tree (n:nat) =
| RP: mt:merkle_tree n ->
      i:nat{i <= pow2 n} ->
      pf:unit{
        raw_hashes (S.slice mt 0 i) /\
        pad_hashes (S.slice mt i (S.length mt))} ->
      right_padded_merkle_tree n

type rpmt n = right_padded_merkle_tree n

val rpmt_raws: #n:nat -> mt:rpmt n -> GTot (S.seq hash_raw)
let rpmt_raws #n mt =
  raw_hashes_raws (S.slice (RP?.mt mt) 0 (RP?.i mt))

val rpmt_i_0:
  #n:nat -> mt:rpmt n ->
  Lemma (requires (RP?.i mt = 0))
        (ensures (S.equal (RP?.mt mt) (S.create (pow2 n) HPad)))
let rpmt_i_0 #n mt = ()

val rpmt_left: #n:nat{n > 0} -> mt:rpmt n -> GTot (rpmt (n-1))
let rpmt_left #n mt =
  RP (mt_left (RP?.mt mt))
     (if RP?.i mt <= pow2 (n-1) then RP?.i mt else pow2 (n-1))
     (if RP?.i mt <= pow2 (n-1) 
     then begin
       pad_hashes_slice
         (S.slice (RP?.mt mt) (RP?.i mt) (S.length (RP?.mt mt)))
         0 (pow2 (n-1) - RP?.i mt)
     end
     else begin
       raw_hashes_slice
         (S.slice (RP?.mt mt) 0 (RP?.i mt))
         0 (pow2 (n-1))
     end)

#reset-options "--z3rlimit 20"
val rpmt_right: #n:nat{n > 0} -> mt:rpmt n -> GTot (rpmt (n-1))
let rpmt_right #n mt = 
  RP (mt_right (RP?.mt mt))
     (if RP?.i mt <= pow2 (n-1) then 0 else RP?.i mt - pow2 (n-1))
     (if RP?.i mt <= pow2 (n-1) 
     then begin
       pad_hashes_slice
         (S.slice (RP?.mt mt) (RP?.i mt) (S.length (RP?.mt mt)))
         (pow2 (n-1) - RP?.i mt) (pow2 n - RP?.i mt)
     end
     else begin
       raw_hashes_slice
         (S.slice (RP?.mt mt) 0 (RP?.i mt))
         (pow2 (n-1)) (RP?.i mt)
     end)
#reset-options

val rpmt_left_right:
  #n:nat{n > 0} -> mt:rpmt n ->
  Lemma (S.equal (RP?.mt mt)
                 (S.append (RP?.mt (rpmt_left mt))
                           (RP?.mt (rpmt_right mt))))
let rpmt_left_right #n mt =
  mt_left_right (RP?.mt mt)

val rpmt_get_root: #n:nat -> mt:rpmt n -> GTot hash
let rpmt_get_root #n mt = mt_get_root (RP?.mt mt)

// Two right-padded merkle trees collide when 
// 1) they have the same height (`n`) and the number of raw hashes (`RP?.i`),
// 2) their contents differ, and
// 3) their roots are valid (HRaw) and same.
val mt_collide:
  #n:nat -> mt1:rpmt n -> mt2:rpmt n -> GTot bool
let mt_collide #n mt1 mt2 =
  RP?.i mt1 = RP?.i mt2 &&
  RP?.mt mt1 <> RP?.mt mt2 &&
  HRaw? (rpmt_get_root mt1) &&
  rpmt_get_root mt1 = rpmt_get_root mt2

val hash_2_raw_collide:
  lh1:hash_raw -> rh1:hash_raw ->
  lh2:hash_raw -> rh2:hash_raw ->
  GTot bool
let hash_2_raw_collide lh1 rh1 lh2 rh2 =
  (lh1, rh1) <> (lh2, rh2) && 
  hash_2_raw lh1 rh1 = hash_2_raw lh2 rh2

val hash_2_raw_collide_helper:
  lh1:hash_raw -> rh1:hash_raw -> lh2:hash_raw -> rh2:hash_raw ->
  Lemma (requires (hash_2_raw_collide lh1 rh1 lh2 rh2))
        (ensures (exists lh1 rh1 lh2 rh2. hash_2_raw_collide lh1 rh1 lh2 rh2))
let hash_2_raw_collide_helper lh1 rh1 lh2 rh2 =
  exists_intro (fun rh2 -> hash_2_raw_collide lh1 rh1 lh2 rh2) rh2;
  exists_intro (fun lh2 -> exists rh2. hash_2_raw_collide lh1 rh1 lh2 rh2) lh2;
  exists_intro (fun rh1 -> exists lh2 rh2. hash_2_raw_collide lh1 rh1 lh2 rh2) rh1;
  exists_intro (fun lh1 -> exists rh1 lh2 rh2. hash_2_raw_collide lh1 rh1 lh2 rh2) lh1

val mt_collide_0:
  mt1:rpmt 0 -> mt2:rpmt 0 ->
  Lemma (not (mt_collide mt1 mt2))
let mt_collide_0 mt1 mt2 =
  if mt1 = mt2 then ()
  else if rpmt_get_root mt1 <> rpmt_get_root mt2 then ()
  else assert (S.equal (RP?.mt mt1) (RP?.mt mt2))

val rpmt_get_root_step:
  #n:nat{n > 0} -> mt:rpmt n ->
  Lemma (rpmt_get_root mt =
        hash_2 (rpmt_get_root (rpmt_left mt)) (rpmt_get_root (rpmt_right mt)))
let rpmt_get_root_step #n mt =
  mt_get_root_step (RP?.mt mt)

val rpmt_pad_hashes_0:
  #n:nat -> mt:rpmt n ->
  Lemma (RP?.i mt = 0 <==> pad_hashes (RP?.mt mt))
let rpmt_pad_hashes_0 #n mt = ()

val rpmt_pad_hashes_index_0:
  #n:nat -> mt:rpmt n ->
  Lemma (pad_hashes (RP?.mt mt) <==> HPad? (S.index (RP?.mt mt) 0))
let rec rpmt_pad_hashes_index_0 #n mt = ()

val mt_get_root_pad_index_0:
  #n:nat -> mt:merkle_tree n ->
  Lemma (HPad? (S.index mt 0) <==> HPad? (mt_get_root mt))
#reset-options "--z3rlimit 40"
let rec mt_get_root_pad_index_0 #n mt =
  if n = 0 then ()
  else mt_get_root_pad_index_0 (mt_next_lv mt)

val rpmt_get_root_pad_hashes:
  #n:nat -> mt:rpmt n ->
  Lemma (pad_hashes (RP?.mt mt) <==> HPad? (rpmt_get_root mt))
let rec rpmt_get_root_pad_hashes #n mt =
  rpmt_pad_hashes_index_0 mt;
  mt_get_root_pad_index_0 (RP?.mt mt)

val rpmt_get_root_pad:
  #n:nat -> mt:rpmt n ->
  Lemma (RP?.i mt = 0 <==> HPad? (rpmt_get_root mt))
let rpmt_get_root_pad #n mt =
  rpmt_get_root_pad_hashes mt;
  rpmt_pad_hashes_0 mt

val rpmt_get_root_raw:
  #n:nat -> mt:rpmt n ->
  Lemma (RP?.i mt > 0 <==> HRaw? (rpmt_get_root mt))
let rpmt_get_root_raw #n mt =
  rpmt_get_root_pad mt

val mt_collide_1:
  mt1:rpmt 1 -> mt2:rpmt 1 ->
  Lemma (requires (mt_collide mt1 mt2))
        (ensures (exists lh1 rh1 lh2 rh2. hash_2_raw_collide lh1 rh1 lh2 rh2))
let mt_collide_1 mt1 mt2 =
  if RP?.i mt1 = 0 then ()
  else begin
    rpmt_get_root_raw mt1; rpmt_get_root_raw mt2;
    rpmt_get_root_raw (rpmt_left mt1); rpmt_get_root_raw (rpmt_left mt2);
    if RP?.i mt1 = 1 
    then begin
      rpmt_get_root_pad (rpmt_right mt1); rpmt_get_root_pad (rpmt_right mt2);
      assert (S.equal (RP?.mt mt1) (RP?.mt mt2))
    end
    else begin
      rpmt_get_root_raw (rpmt_right mt1); rpmt_get_root_raw (rpmt_right mt2);
      let lrt1 = HRaw?.hr (rpmt_get_root (rpmt_left mt1)) in
      let lrt2 = HRaw?.hr (rpmt_get_root (rpmt_left mt2)) in
      let rrt1 = HRaw?.hr (rpmt_get_root (rpmt_right mt1)) in
      let rrt2 = HRaw?.hr (rpmt_get_root (rpmt_right mt2)) in
      if (lrt1, rrt1) = (lrt2, rrt2)
      then assert (S.equal (RP?.mt mt1) (RP?.mt mt2))
      else begin
        hash_2_raw_collide_helper lrt1 rrt1 lrt2 rrt2
      end
    end
  end

val mt_collide_n:
  #n:nat{n > 0} ->
  mt1:rpmt n -> mt2:rpmt n ->
  Lemma (requires (mt_collide mt1 mt2))
        (ensures (exists lh1 rh1 lh2 rh2. hash_2_raw_collide lh1 rh1 lh2 rh2))
#reset-options "--z3rlimit 40"
let rec mt_collide_n #n mt1 mt2 =
  if n = 1 then mt_collide_1 mt1 mt2
  else begin
    assert (RP?.i (rpmt_left mt1) = RP?.i (rpmt_left mt2));
    assert (RP?.i (rpmt_right mt1) = RP?.i (rpmt_right mt2));
    rpmt_left_right mt1; rpmt_left_right mt2;
    rpmt_get_root_step mt1; rpmt_get_root_step mt2;
    if RP?.i mt1 = 0 then rpmt_get_root_pad mt1
    else if RP?.i mt1 <= pow2 (n-1)
    then begin
      rpmt_get_root_raw (rpmt_left mt1); rpmt_get_root_raw (rpmt_left mt2);
      rpmt_get_root_pad (rpmt_right mt1); rpmt_get_root_pad (rpmt_right mt2);
      rpmt_i_0 (rpmt_right mt1); rpmt_i_0 (rpmt_right mt2);
      assert (RP?.mt (rpmt_left mt1) <> RP?.mt (rpmt_left mt2));
      mt_collide_n (rpmt_left mt1) (rpmt_left mt2)
    end
    else begin
      rpmt_get_root_raw (rpmt_left mt1); rpmt_get_root_raw (rpmt_left mt2);
      rpmt_get_root_raw (rpmt_right mt1); rpmt_get_root_raw (rpmt_right mt2);
      let lrt1 = HRaw?.hr (rpmt_get_root (rpmt_left mt1)) in
      let lrt2 = HRaw?.hr (rpmt_get_root (rpmt_left mt2)) in
      let rrt1 = HRaw?.hr (rpmt_get_root (rpmt_right mt1)) in
      let rrt2 = HRaw?.hr (rpmt_get_root (rpmt_right mt2)) in
      if lrt1 <> lrt2 || rrt1 <> rrt2
      then hash_2_raw_collide_helper lrt1 rrt1 lrt2 rrt2
      else begin
        if RP?.mt (rpmt_left mt1) = RP?.mt (rpmt_left mt2)
        then begin
          if RP?.mt (rpmt_right mt1) = RP?.mt (rpmt_right mt2)
          then ()
          else mt_collide_n (rpmt_right mt1) (rpmt_right mt2)
        end
        else mt_collide_n (rpmt_left mt1) (rpmt_left mt2)
      end
    end
  end

// The security property for right-padded Merkle trees
val mt_collide_implies_hash_raw_collide:
  #n:nat -> mt1:rpmt n -> mt2:rpmt n ->
  Lemma (requires (mt_collide mt1 mt2))
        (ensures (exists lh1 rh1 lh2 rh2. hash_2_raw_collide lh1 rh1 lh2 rh2))
let rec mt_collide_implies_hash_raw_collide #n mt1 mt2 =
  if n = 0 then mt_collide_0 mt1 mt2
  else mt_collide_n mt1 mt2

