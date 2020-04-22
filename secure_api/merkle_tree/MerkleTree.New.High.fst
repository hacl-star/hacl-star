module MerkleTree.New.High

open FStar.Ghost
open FStar.Seq

module S = FStar.Seq

module U32 = FStar.UInt32
module U8 = FStar.UInt8

module MTS = MerkleTree.Spec

#set-options "--z3rlimit 10 --max_fuel 0 --max_ifuel 0"

type uint32_t = U32.t
type uint8_t = U8.t

type hash (#hsz:pos) = b:Spec.Hash.Definitions.bytes{Seq.length b = hsz}
type hashes (#hsz:pos) = S.seq (hash #hsz)
type hashess (#hsz:pos) = S.seq (hashes #hsz)

noextract
let hash_init (#hsz:pos): hash #hsz =
  Seq.create hsz (Lib.IntTypes.u8 0)

val sha256_compress: src1:hash #32 -> src2:hash #32 -> GTot (hash #32)
let sha256_compress = MTS.sha256_compress


/// Facts about sequences

val seq_slice_equal_index:
  #a:Type -> s1:S.seq a -> s2:S.seq a ->
  i:nat -> j:nat{i <= j && j <= S.length s1 && j <= S.length s2} ->
  k:nat{i <= k && k < j} ->
  Lemma (requires S.equal (S.slice s1 i j) (S.slice s2 i j))
        (ensures  S.index s1 k == S.index s2 k)
        [SMTPat (S.equal (S.slice s1 i j) (S.slice s2 i j));
         SMTPat (S.index s1 k)]
let seq_slice_equal_index #a s1 s2 i j k =
  assert (S.index (S.slice s1 i j) (k - i) == S.index (S.slice s2 i j) (k - i))

private val seq_slice_more_equal:
  #a:Type -> s1:S.seq a -> s2:S.seq a ->
  n:nat -> m:nat{n <= m && m <= S.length s1 && m <= S.length s2} ->
  k:nat{n <= k} -> l:nat{k <= l && l <= m} ->
  Lemma (requires S.equal (S.slice s1 n m) (S.slice s2 n m))
        (ensures  S.equal (S.slice s1 k l) (S.slice s2 k l))
        [SMTPat (S.equal (S.slice s1 n m) (S.slice s2 n m));
         SMTPat (S.equal (S.slice s1 k l) (S.slice s2 k l))]
private let seq_slice_more_equal #a s1 s2 n m k l =
  slice_slice s1 n m (k - n) (l - n);
  slice_slice s2 n m (k - n) (l - n)

/// Facts about "2"

val remainder_2_not_1_div: n:nat ->
  Lemma (requires n % 2 <> 1)
        (ensures  n / 2 = (n + 1) / 2)
let remainder_2_not_1_div n = ()

val remainder_2_1_div: n:nat ->
  Lemma (requires n % 2 = 1)
        (ensures  n / 2 + 1 = (n + 1) / 2)
let remainder_2_1_div n = ()

/// High-level Merkle tree data structure

noeq type merkle_tree (#hsz:pos) =
| MT: i:nat -> 
      j:nat{i <= j && j < pow2 32} ->
      hs:hashess #hsz {S.length hs = 32} ->
      rhs_ok:bool -> 
      rhs:hashes #hsz {S.length rhs = 32} -> // Rightmost hashes
      mroot:hash #hsz ->
      hash_fun:MTS.hash_fun_t #hsz ->
      merkle_tree #hsz

val mt_not_full (#hsz:pos): merkle_tree #hsz -> GTot bool
let mt_not_full #hsz mt =
  MT?.j mt < pow2 32 - 1

val mt_empty (#hsz:pos): merkle_tree #hsz -> GTot bool
let mt_empty #hsz mt =
  MT?.j mt = 0

val mt_not_empty (#hsz:pos): merkle_tree #hsz -> GTot bool
let mt_not_empty #hsz mt =
  MT?.j mt > 0

/// Well-formedness w.r.t. indices of base hash elements

noextract
val offset_of: i:nat -> Tot nat
let offset_of i =
  if i % 2 = 0 then i else i - 1

val hs_wf_elts:
  #hsz:pos ->
  lv:nat{lv <= 32} ->
  hs:hashess #hsz {S.length hs = 32} ->
  i:nat -> j:nat{j >= i} ->
  GTot Type0 (decreases (32 - lv))
let rec hs_wf_elts #hsz lv hs i j =
  if lv = 32 then true
  else (let ofs = offset_of i in
       S.length (S.index hs lv) == j - ofs /\
       hs_wf_elts #hsz (lv + 1) hs (i / 2) (j / 2))

#push-options "--max_fuel 1"

val hs_wf_elts_equal:
  #hsz:pos ->
  lv:nat{lv <= 32} ->
  hs1:hashess #hsz {S.length hs1 = 32} ->
  hs2:hashess #hsz {S.length hs2 = 32} ->
  i:nat -> 
  j:nat{j >= i} ->
  Lemma (requires hs_wf_elts lv hs1 i j /\
		  S.equal (S.slice hs1 lv 32) (S.slice hs2 lv 32))
	(ensures  hs_wf_elts lv hs2 i j)
	(decreases (32 - lv))
let rec hs_wf_elts_equal #hsz lv hs1 hs2 i j =
  if lv = 32 then ()
  else (S.slice_slice hs1 lv 32 1 (32 - lv);
       S.slice_slice hs2 lv 32 1 (32 - lv);
       assert (S.equal (S.slice hs1 (lv + 1) 32)
		       (S.slice hs2 (lv + 1) 32));
       S.lemma_index_slice hs1 lv 32 0;
       S.lemma_index_slice hs2 lv 32 0;
       assert (S.index hs1 lv == S.index hs2 lv);
       hs_wf_elts_equal (lv + 1) hs1 hs2 (i / 2) (j / 2))

val mt_wf_elts (#hsz:pos): merkle_tree #hsz -> GTot Type0
let mt_wf_elts #_ (MT i j hs _ _ _ _)  =
  hs_wf_elts 0 hs i j

 /// Construction

val hs_wf_elts_empty:
  #hsz:pos ->
  lv:nat{lv <= 32} ->
  Lemma (requires True)
	(ensures  hs_wf_elts #hsz lv (S.create 32 S.empty) 0 0)
	(decreases (32 - lv))
let rec hs_wf_elts_empty #hsz lv =
  if lv = 32 then ()
  else hs_wf_elts_empty #hsz (lv + 1)

// NOTE: the public function is `create_mt` defined below, which
// builds a tree with an initial hash.
noextract inline_for_extraction
val create_empty_mt (#hsz:pos) (#f:MTS.hash_fun_t #hsz): unit -> GTot (mt:merkle_tree #hsz {mt_wf_elts #hsz mt})
let create_empty_mt #hsz #f _ =
  hs_wf_elts_empty #hsz 0;
  MT 0 0 (S.create 32 S.empty) false (S.create 32 (hash_init #hsz)) (hash_init #hsz) f

/// Insertion

val hashess_insert:
  #hsz:pos ->
  lv:nat{lv < 32} ->
  i:nat ->
  j:nat{i <= j /\ j < pow2 (32 - lv) - 1} ->
  hs:hashess #hsz {S.length hs = 32 /\ hs_wf_elts lv hs i j} ->
  v:hash #hsz ->
  GTot (ihs:hashess #hsz {S.length ihs = 32 /\ hs_wf_elts (lv + 1) ihs (i / 2) (j / 2)})
let hashess_insert #hsz lv i j hs v =
  let ihs = S.upd hs lv (S.snoc (S.index hs lv) v) in
  hs_wf_elts_equal (lv + 1) hs ihs (i / 2) (j / 2);
  ihs

val insert_:
  #hsz:pos -> #f:MTS.hash_fun_t #hsz ->
  lv:nat{lv < 32} ->
  i:nat ->
  j:nat{i <= j /\ j < pow2 (32 - lv) - 1} ->
  hs:hashess #hsz {S.length hs = 32 /\ hs_wf_elts lv hs i j} ->
  acc:hash #hsz ->
  GTot (ihs:hashess #hsz {
         S.length ihs = 32 /\
         hs_wf_elts #hsz lv ihs i (j + 1) /\
         S.equal (S.slice hs 0 lv) (S.slice ihs 0 lv)})
       (decreases j)
let rec insert_ #hsz #f lv i j hs acc =
  let ihs = hashess_insert #hsz lv i j hs acc in
  assert (S.equal (S.slice hs 0 lv) (S.slice ihs 0 lv));
  if j % 2 = 1 // S.length (S.index hs lv) > 0
  then begin
    remainder_2_1_div j;
    let nacc = f (S.last (S.index hs lv)) acc in
    let rihs = insert_ #hsz #f (lv + 1) (i / 2) (j / 2) ihs nacc in
    assert (hs_wf_elts #hsz (lv + 1) rihs (i / 2) (j / 2 + 1));
    assert (S.equal (S.slice ihs 0 (lv + 1)) (S.slice rihs 0 (lv + 1)));
    assert (S.index ihs lv == S.index rihs lv);
    assert (S.length (S.index rihs lv) = (j + 1) - offset_of i);
    assert (S.equal (S.slice ihs 0 (lv + 1)) (S.slice rihs 0 (lv + 1)));
    assert (S.equal (S.slice ihs 0 lv) (S.slice rihs 0 lv));
    rihs
  end
  else ihs

val insert_base:
  #hsz:pos -> #f:MTS.hash_fun_t #hsz ->
  lv:nat -> i:nat -> j:nat -> hs:hashess #hsz -> acc:hash #hsz ->
  Lemma (requires 
	  lv < 32 /\ i <= j /\ j < pow2 (32 - lv) - 1 /\
	  S.length hs = 32 /\ hs_wf_elts lv hs i j /\
	  j % 2 <> 1)
	(ensures S.equal (insert_ #_ #f lv i j hs acc)
		         (hashess_insert lv i j hs acc))
let insert_base #_ #_ lv i j hs acc = ()

val insert_rec:
  #hsz:pos -> #f:MTS.hash_fun_t #hsz ->
  lv:nat -> i:nat -> j:nat -> hs:hashess -> acc:hash ->
  Lemma (requires
	  lv < 32 /\ i <= j /\ j < pow2 (32 - lv) - 1 /\
	  S.length hs = 32 /\ hs_wf_elts lv hs i j /\
	  j % 2 == 1)
	(ensures 
	  (hs_wf_elts_equal (lv + 1) hs
	    (hashess_insert lv i j hs acc) (i / 2) (j / 2);
	  S.equal (insert_ #_ #f lv i j hs acc)
		  (insert_ #_ #f (lv + 1) (i / 2) (j / 2)
			   (hashess_insert lv i j hs acc)
			   (f (S.last (S.index hs lv)) acc))))
let insert_rec #_ #_ lv i j hs acc = ()

val mt_insert:
  #hsz:pos ->
  mt:merkle_tree #hsz {mt_wf_elts mt /\ mt_not_full mt} -> v:hash #hsz ->
  GTot (imt:merkle_tree #hsz{mt_wf_elts #hsz imt})
let mt_insert #hsz mt v =
  MT (MT?.i mt)
     (MT?.j mt + 1)
     (insert_ #_ #(MT?.hash_fun mt) 0 (MT?.i mt) (MT?.j mt) (MT?.hs mt) v)
     false
     (MT?.rhs mt)
     (MT?.mroot mt)
     (MT?.hash_fun mt)

val mt_create:
  hsz:pos -> f:MTS.hash_fun_t #hsz ->
  init:hash #hsz -> GTot (mt:merkle_tree{mt_wf_elts #hsz mt})
let mt_create hsz f init =
  mt_insert #_ (create_empty_mt #_ #f ()) init

/// Getting the Merkle root and path

type path (#hsz:pos) = S.seq (hash #hsz)

// Construct the rightmost hashes for a given (incomplete) Merkle tree.
// This function calculates the Merkle root as well, which is the final
// accumulator value.
val construct_rhs:
  #hsz:pos -> #f:MTS.hash_fun_t #hsz ->
  lv:nat{lv <= 32} ->
  hs:hashess #hsz {S.length hs = 32} ->
  rhs:hashes #hsz {S.length rhs = 32} ->
  i:nat ->
  j:nat{
    i <= j /\ j < pow2 (32 - lv) /\
    hs_wf_elts #hsz lv hs i j} ->
  acc:hash #hsz ->
  actd:bool ->
  GTot (crhs:hashes #hsz {S.length crhs = 32} * (hash #hsz))
       (decreases j)
let rec construct_rhs #hsz #f lv hs rhs i j acc actd =
  let ofs = offset_of i in
  if j = 0 then (rhs, acc)
  else
    (if j % 2 = 0
    then (construct_rhs #_ #f (lv + 1) hs rhs (i / 2) (j / 2) acc actd)
    else (let nrhs = if actd then S.upd rhs lv acc else rhs in
         let nacc = if actd
                    then f (S.index (S.index hs lv) (j - 1 - ofs)) acc
                    else S.index (S.index hs lv) (j - 1 - ofs) in
         construct_rhs #_ #f (lv + 1) hs nrhs (i / 2) (j / 2) nacc true))

val construct_rhs_unchanged:
  #hsz:pos -> #f:MTS.hash_fun_t #hsz ->
  lv:nat{lv <= 32} ->
  hs:hashess #hsz {S.length hs = 32} ->
  rhs:hashes #hsz {S.length rhs = 32} ->
  i:nat ->
  j:nat{
    i <= j /\ j < pow2 (32 - lv) /\
    hs_wf_elts #hsz lv hs i j} ->
  acc:hash #hsz ->
  actd:bool ->
  Lemma (requires True)
        (ensures  S.equal (S.slice rhs 0 lv)
                          (S.slice (fst (construct_rhs #_ #f lv hs rhs i j acc actd)) 0 lv))
        (decreases j)
let rec construct_rhs_unchanged #hsz #f lv hs rhs i j acc actd =
  let ofs = offset_of i in
  if j = 0 then ()
  else if j % 2 = 0
  then (construct_rhs_unchanged #_ #f (lv + 1) hs rhs (i / 2) (j / 2) acc actd;
       let rrhs = fst (construct_rhs #_ #f (lv + 1) hs rhs (i / 2) (j / 2) acc actd) in
       assert (S.equal (S.slice rhs 0 lv) (S.slice rrhs 0 lv)))
  else (let nrhs = if actd then S.upd rhs lv acc else rhs in
       let nacc = if actd
                  then f (S.index (S.index hs lv) (j - 1 - ofs)) acc
                  else S.index (S.index hs lv) (j - 1 - ofs) in
       construct_rhs_unchanged #_ #f (lv + 1) hs nrhs (i / 2) (j / 2) nacc true;
       let rrhs = fst (construct_rhs #_ #f (lv + 1) hs nrhs (i / 2) (j / 2) nacc true) in
       assert (S.equal (S.slice nrhs 0 lv) (S.slice rrhs 0 lv));
       assert (S.equal (S.slice rhs 0 lv) (S.slice nrhs 0 lv)))

val construct_rhs_even:
  #hsz:pos -> #f:MTS.hash_fun_t #hsz ->
  lv:nat{lv <= 32} ->
  hs:hashess #hsz {S.length hs = 32} ->
  rhs:hashes #hsz {S.length rhs = 32} ->
  i:nat ->
  j:nat{
    i <= j /\ j < pow2 (32 - lv) /\
    hs_wf_elts #hsz lv hs i j} ->
  acc:hash #hsz ->
  actd:bool ->
  Lemma (requires j <> 0 /\ j % 2 = 0)
        (ensures  construct_rhs #_ #f lv hs rhs i j acc actd ==
                  construct_rhs #_ #f (lv + 1) hs rhs (i / 2) (j / 2) acc actd)
let construct_rhs_even #_ #_ _ _ _ _ _ _ _ = ()

val construct_rhs_odd:
  #hsz:pos -> #f:MTS.hash_fun_t #hsz ->
  lv:nat{lv <= 32} ->
  hs:hashess #hsz {S.length hs = 32} ->
  rhs:hashes #hsz {S.length rhs = 32} ->
  i:nat ->
  j:nat{
    i <= j /\ j < pow2 (32 - lv) /\
    hs_wf_elts lv hs i j} ->
  acc:hash ->
  actd:bool ->
  Lemma (requires j % 2 = 1)
        (ensures construct_rhs #_ #f lv hs rhs i j acc actd ==
                 (let ofs = offset_of i in
                 let nrhs = if actd then S.upd rhs lv acc else rhs in
                 let nacc = if actd
                            then f (S.index (S.index hs lv) (j - 1 - ofs)) acc
                            else S.index (S.index hs lv) (j - 1 - ofs) in
                 construct_rhs #_ #f (lv + 1) hs nrhs (i / 2) (j / 2) nacc true))
let construct_rhs_odd #_ #_ _ _ _ _ _ _ _ = ()

val mt_get_root:
  #hsz:pos ->
  mt:merkle_tree #hsz {mt_wf_elts #hsz mt} -> drt:hash #hsz ->
  GTot (merkle_tree #hsz * hash #hsz)
let mt_get_root #hsz mt drt =
  if MT?.rhs_ok mt then (mt, MT?.mroot mt)
  else begin
    let (nrhs, rt) = construct_rhs #_ #(MT?.hash_fun mt) 0 (MT?.hs mt) (MT?.rhs mt) (MT?.i mt) (MT?.j mt) drt false in
    (MT (MT?.i mt) (MT?.j mt) (MT?.hs mt) true nrhs rt (MT?.hash_fun mt), rt)
  end

val mt_get_root_rhs_ok_true:
  #hsz:pos -> 
  mt:merkle_tree #hsz {mt_wf_elts mt} -> drt:hash #hsz ->
  Lemma (requires MT?.rhs_ok mt == true)
        (ensures  mt_get_root #hsz mt drt == (mt, MT?.mroot mt))
let mt_get_root_rhs_ok_true #hsz mt drt = ()

val mt_get_root_rhs_ok_false:
  #hsz:pos -> 
  mt:merkle_tree #hsz {mt_wf_elts mt} -> drt:hash ->
  Lemma (requires MT?.rhs_ok mt == false)
        (ensures  mt_get_root mt drt ==
                  (let (nrhs, rt) =
                   construct_rhs #_ #(MT?.hash_fun mt) 
                     0 (MT?.hs mt) (MT?.rhs mt) (MT?.i mt) (MT?.j mt)
	             drt false in
                   (MT (MT?.i mt) (MT?.j mt) (MT?.hs mt) true nrhs rt (MT?.hash_fun mt), rt)))
let mt_get_root_rhs_ok_false #_ _ _ = ()

val path_insert: (#hsz:pos) -> p:path #hsz -> hp:hash #hsz -> GTot (path #hsz)
let path_insert #_ p hp = S.snoc p hp

val mt_path_length_step:
  k:nat -> j:nat{k <= j} -> actd:bool -> GTot nat
let mt_path_length_step k j actd =
  if j = 0 then 0
  else (if k % 2 = 0
       then (if j = k || (j = k + 1 && not actd) then 0 else 1)
       else 1)

val mt_path_length:
  k:nat -> j:nat{k <= j} -> actd:bool -> GTot nat
let rec mt_path_length k j actd =
  if j = 0 then 0
  else (let nactd = actd || (j % 2 = 1) in
       mt_path_length_step k j actd +
       mt_path_length (k / 2) (j / 2) nactd)

val mt_make_path_step:
  #hsz:pos -> 
  lv:nat{lv <= 32} ->
  hs:hashess #hsz {S.length hs = 32} ->
  rhs:hashes #hsz {S.length rhs = 32} ->
  i:nat ->
  j:nat{
    j <> 0 /\ i <= j /\ j < pow2 (32 - lv) /\
    hs_wf_elts lv hs i j} ->
  k:nat{i <= k && k <= j} ->
  p:path #hsz ->
  actd:bool ->
  GTot (path #hsz)
let mt_make_path_step #hsz lv hs rhs i j k p actd =
  let ofs = offset_of i in
  if k % 2 = 1
  then path_insert p (S.index (S.index hs lv) (k - 1 - ofs))
  else (if k = j then p
       else if k + 1 = j
	    then (if actd
		 then path_insert p (S.index rhs lv)
		 else p)
	    else path_insert p (S.index (S.index hs lv) (k + 1 - ofs)))

// Construct a Merkle path for a given index `k`, hashes `hs`,
// and rightmost hashes `rhs`.
val mt_get_path_:
  #hsz:pos -> 
  lv:nat{lv <= 32} ->
  hs:hashess #hsz {S.length hs = 32} ->
  rhs:hashes #hsz {S.length rhs = 32} ->
  i:nat ->
  j:nat{
    i <= j /\ j < pow2 (32 - lv) /\
    hs_wf_elts lv hs i j} ->
  k:nat{i <= k && k <= j} ->
  p:path #hsz ->
  actd:bool ->
  GTot (np:path #hsz {S.length np = S.length p + mt_path_length k j actd})
       (decreases (32 - lv))
let rec mt_get_path_ #hsz lv hs rhs i j k p actd =
  let ofs = offset_of i in
  if j = 0 then p
  else
    (let np = mt_make_path_step lv hs rhs i j k p actd in
    mt_get_path_ (lv + 1) hs rhs (i / 2) (j / 2) (k / 2) np
    		 (if j % 2 = 0 then actd else true))

val mt_get_path_unchanged:
  #hsz:pos -> 
  lv:nat{lv <= 32} ->
  hs:hashess #hsz {S.length hs = 32} ->
  rhs:hashes #hsz {S.length rhs = 32} ->
  i:nat ->
  j:nat{
    i <= j /\ j < pow2 (32 - lv) /\
    hs_wf_elts #hsz lv hs i j} ->
  k:nat{i <= k && k <= j} ->
  p:path #hsz ->
  actd:bool ->
  Lemma (requires True)
        (ensures S.equal p (S.slice (mt_get_path_ lv hs rhs i j k p actd)
                                     0 (S.length p)))
        (decreases (32 - lv))
let rec mt_get_path_unchanged #hsz lv hs rhs i j k p actd =
  let ofs = offset_of i in
  if j = 0 then ()
  else
    (let np = mt_make_path_step lv hs rhs i j k p actd in
    assert (S.equal p (S.slice np 0 (S.length p)));
    mt_get_path_unchanged (lv + 1) hs rhs (i / 2) (j / 2) (k / 2) np
      (if j % 2 = 0 then actd else true))

#push-options "--z3rlimit 20"

val mt_get_path_pull:
  #hsz:pos -> 
  lv:nat{lv <= 32} ->
  hs:hashess #hsz {S.length hs = 32} ->
  rhs:hashes #hsz {S.length rhs = 32} ->
  i:nat ->
  j:nat{
    i <= j /\ j < pow2 (32 - lv) /\
    hs_wf_elts lv hs i j} ->
  k:nat{i <= k && k <= j} ->
  p:path #hsz ->
  actd:bool ->
  Lemma (requires True)
        (ensures  S.equal (mt_get_path_ lv hs rhs i j k p actd)
                          (S.append p (mt_get_path_ lv hs rhs i j k S.empty actd)))
        (decreases (32 - lv))
let rec mt_get_path_pull #hsz lv hs rhs i j k p actd =
  let ofs = offset_of i in
  if j = 0 then ()
  else
    (let np = mt_make_path_step lv hs rhs i j k p actd in
    let nactd = if j % 2 = 0 then actd else true in
    mt_get_path_pull (lv + 1) hs rhs (i / 2) (j / 2) (k / 2) np nactd;
    mt_get_path_pull (lv + 1) hs rhs (i / 2) (j / 2) (k / 2)
      (mt_make_path_step lv hs rhs i j k S.empty actd) nactd)

#pop-options

val mt_get_path_slice:
  #hsz:pos -> 
  lv:nat{lv <= 32} ->
  hs:hashess #hsz {S.length hs = 32} ->
  rhs:hashes #hsz {S.length rhs = 32} ->
  i:nat ->
  j:nat{
    i <= j /\ j < pow2 (32 - lv) /\
    hs_wf_elts lv hs i j} ->
  k:nat{i <= k && k <= j} ->
  p:path #hsz ->
  actd:bool ->
  Lemma (requires True)
        (ensures  S.equal (S.slice (mt_get_path_ lv hs rhs i j k p actd)
                            (S.length p) (S.length p + mt_path_length k j actd))
                          (mt_get_path_ lv hs rhs i j k S.empty actd))
        (decreases (32 - lv))
let mt_get_path_slice #hsz lv hs rhs i j k p actd =
  mt_get_path_pull lv hs rhs i j k p actd

val mt_get_path:
  #hsz:pos -> 
  mt:merkle_tree #hsz {mt_wf_elts mt} ->
  idx:nat{MT?.i mt <= idx /\ idx < MT?.j mt} ->
  drt:hash #hsz ->
  GTot (nat *
       (np:path #hsz {S.length np = 1 + mt_path_length idx (MT?.j mt) false}) *
       hash #hsz)
let mt_get_path #hsz mt idx drt =
  let (umt, root) = mt_get_root mt drt in
  let ofs = offset_of (MT?.i umt) in
  let np = path_insert S.empty (S.index (S.index (MT?.hs umt) 0) (idx - ofs)) in
  MT?.j umt,
  mt_get_path_ 0 (MT?.hs umt) (MT?.rhs umt)
    (MT?.i umt) (MT?.j umt) idx np false,
  root

/// Flushing

val mt_flush_to_:
  #hsz:pos -> 
  lv:nat{lv < 32} ->
  hs:hashess #hsz {S.length hs = 32} ->
  pi:nat ->
  i:nat{i >= pi} ->
  j:nat{
    j >= i /\ j < pow2 (32 - lv) /\
    hs_wf_elts #hsz lv hs pi j} ->
  GTot (fhs:hashess{
         S.length fhs = 32 /\
         S.equal (S.slice hs 0 lv) (S.slice fhs 0 lv) /\
         hs_wf_elts #hsz lv fhs i j}) 
  (decreases i)
let rec mt_flush_to_ #hsz lv hs pi i j =
  let oi = offset_of i in
  let opi = offset_of pi in
  if oi = opi then hs
  else (let ofs = oi - opi in
       let hvec = S.index hs lv in
       let flushed = S.slice hvec ofs (S.length hvec) in
       let nhs = S.upd hs lv flushed in
       hs_wf_elts_equal (lv + 1) hs nhs (pi / 2) (j / 2);
       mt_flush_to_ (lv + 1) nhs (pi / 2) (i / 2) (j / 2))

val mt_flush_to_rec:
  #hsz:pos -> 
  lv:nat{lv < 32} ->
  hs:hashess #hsz {S.length hs = 32} ->
  pi:nat ->
  i:nat{i >= pi} ->
  j:nat{
    j >= i /\ j < pow2 (32 - lv) /\
    hs_wf_elts lv hs pi j} ->
  Lemma (requires offset_of i <> offset_of pi)
        (ensures mt_flush_to_ lv hs pi i j ==
                 (let ofs = offset_of i - offset_of pi in
                 let hvec = S.index hs lv in
                 let flushed = S.slice hvec ofs (S.length hvec) in
                 let nhs = S.upd hs lv flushed in
                 hs_wf_elts_equal (lv + 1) hs nhs (pi / 2) (j / 2);
                 mt_flush_to_ #hsz (lv + 1) nhs (pi / 2) (i / 2) (j / 2)))
let mt_flush_to_rec #hsz lv hs pi i j = ()

val mt_flush_to:
  #hsz:pos -> 
  mt:merkle_tree #hsz {mt_wf_elts mt} ->
  idx:nat{idx >= MT?.i mt /\ idx < MT?.j mt} ->
  GTot (fmt:merkle_tree{mt_wf_elts #hsz fmt})
let mt_flush_to #hsz mt idx =
  let fhs = mt_flush_to_ #hsz 0 (MT?.hs mt) (MT?.i mt) idx (MT?.j mt) in
  MT idx (MT?.j mt) fhs (MT?.rhs_ok mt) (MT?.rhs mt) (MT?.mroot mt) (MT?.hash_fun mt)

val mt_flush:
  #hsz:pos -> 
  mt:merkle_tree #hsz {mt_wf_elts mt /\ MT?.j mt > MT?.i mt} ->
  GTot (fmt:merkle_tree{mt_wf_elts #hsz fmt})
let mt_flush #hsz mt =
  mt_flush_to mt (MT?.j mt - 1)

#push-options "--max_fuel 2"

/// Retraction

val mt_retract_to_:
  #hsz:pos -> 
  hs:hashess #hsz {S.length hs = 32} ->
  lv:nat{lv < S.length hs} ->
  i:nat ->
  s:nat -> // s is the first index excluded from nhs
  j:nat{ i <= s /\ s <= j /\
         j < pow2 (S.length hs - lv) /\
         hs_wf_elts lv hs i j} ->
  GTot (nhs:hashess #hsz {
         S.length nhs = S.length hs /\
         S.equal (S.slice hs 0 lv) (S.slice nhs 0 lv) /\
         hs_wf_elts #hsz lv nhs i s})
  (decreases (S.length hs - lv))
let rec mt_retract_to_ #hsz hs lv i s j =
  if lv >= S.length hs then hs
  else begin
    let hvec = S.index hs lv in
    let old_len = j - offset_of i in
    let new_len = s - offset_of i in
    assert (S.length hvec = old_len);
    assert (new_len <= old_len);
    assert (new_len <= S.length hvec);
    let retracted = S.slice hvec 0 new_len in
    let nhs = S.upd hs lv retracted in
    if lv >= S.length hs - 1 then nhs else
    begin
      hs_wf_elts_equal (lv + 1) hs nhs (i / 2) (j / 2);
      mt_retract_to_ nhs (lv + 1) (i / 2) (s / 2) (j / 2)
    end
  end

#pop-options

val mt_retract_to:
  #hsz:pos -> 
  mt:merkle_tree #hsz {mt_wf_elts mt} ->
  r:nat{MT?.i mt <= r /\ r < MT?.j mt} ->
  GTot (rmt:merkle_tree #hsz {mt_wf_elts rmt /\ MT?.i rmt = MT?.i mt /\ MT?.j rmt = r + 1})
let mt_retract_to #hsz mt r =
  let nhs = mt_retract_to_ (MT?.hs mt) 0 (MT?.i mt) (r+1) (MT?.j mt) in
  MT (MT?.i mt) (r+1) nhs false (MT?.rhs mt) (MT?.mroot mt) (MT?.hash_fun mt)


/// Verification

val mt_verify_:
  #hsz:pos -> #f:MTS.hash_fun_t #hsz ->
  k:nat ->
  j:nat{k <= j} ->
  p:path #hsz ->
  ppos:nat ->
  acc:hash #hsz ->
  actd:bool{ppos + mt_path_length k j actd <= S.length p} ->
  GTot (hash #hsz)
let rec mt_verify_ #hsz #f k j p ppos acc actd =
  if j = 0 then acc
  else (let nactd = actd || (j % 2 = 1) in
       if k % 2 = 0
       then (if j = k || (j = k + 1 && not actd)
	    then mt_verify_ #_ #f (k / 2) (j / 2) p ppos acc nactd
	    else (let nacc = f acc (S.index p ppos) in
		 mt_verify_ #_ #f (k / 2) (j / 2) p (ppos + 1) nacc nactd))
       else (let nacc = f (S.index p ppos) acc in
	    mt_verify_ #_ #f (k / 2) (j / 2) p (ppos + 1) nacc nactd))

val mt_verify:
  #hsz:pos -> #f:MTS.hash_fun_t #hsz ->
  k:nat ->
  j:nat{k < j} ->
  p:path #hsz {S.length p = 1 + mt_path_length k j false} ->
  rt:hash #hsz ->
  GTot prop
let mt_verify #_ #f k j p rt =
  let crt = mt_verify_ #_ #f k j p 1 (S.index p 0) false in
  crt == rt
