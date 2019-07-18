module Spec.Kyber2.NumericTypes

open FStar.Mul

open Spec.Kyber2.Params
open Spec.Powtwo.Lemmas
open Lib.NumericTypes

open Lib.Sequence
open Lib.IntTypes
open Lib.NumericTypes

module Seq = Lib.Sequence

type num_t = Base Group.t
type poly_t = vector_t #num_t params_n
type vec_t = vector_t #poly_t params_k
type matrix_t = matrix_t #poly_t params_k params_k

type num = Group.t
type poly = vector_i #num_t params_n
type vec = vector_i #poly_t params_k
type matrix = matrix_i #poly_t params_k params_k

#reset-options "--z3rlimit 200 --max_fuel 2 --max_ifuel 2 --using_facts_from '* -FStar.Seq'"
let ring_num = Ring.ring_t
let ring_poly = Lib.Poly.NTT2.lib_ntt_ring #num #ring_num #params_n 7 (Group.mk_t params_zeta)

let new_poly () : poly = create params_n (Group.zero_t)
let new_vec () : vec = create params_k (new_poly ())
let new_matrix () : matrix = create params_k (new_vec ())

let index_vec (v:vec) i : poly = Seq.index #_ #params_k v i

let get_line (m:matrix) i : vec = Seq.index #_ #params_k m i

let get_element (m:matrix) i j : poly = index_vec (get_line m i) j

let get_column (m:matrix) j : vec = Seq.createi params_k (fun i -> get_element m i j)

let upd_vec (v:vec) i (x:poly) : vec = upd #_ #params_k v i x

let upd_line (m:matrix) i (v:vec) : matrix = upd #_ #params_k m i v

let upd_matrix (m:matrix) (i:size_nat{i<params_k}) (j:size_nat{j<params_k}) (x:poly) : matrix = upd_line m i (upd_vec (get_line m i) j x)

let eq_vec (v1:vec) (v2:vec) : Lemma (requires forall i. {:pattern (index_vec v1 i); (index_vec v2 i)} index_vec v1 i == index_vec v2 i) (ensures v1 == v2) =
  let customprop (i:size_nat{i<params_k}) : Type0 = (Seq.index #_ #params_k v1 i == Seq.index #_ #params_k v2 i) in
  let customlemma (i:size_nat{i<params_k}) : Lemma (customprop i) = assert(index_vec v1 i == index_vec v2 i)
  in FStar.Classical.forall_intro customlemma; Seq.eq_intro #_ #params_k v1 v2

let eq_matrix_line (m1:matrix) (m2:matrix) : Lemma (requires forall i. {:pattern (get_line m1 i); (get_line m2 i)} get_line m1 i == get_line m2 i) (ensures m1 == m2) =
  let customprop (i:size_nat{i<params_k}) : Type0 = (Seq.index #_ #params_k m1 i == Seq.index #_ #params_k m2 i) in
  let customlemma (i:size_nat{i<params_k}) : Lemma (customprop i) = assert(get_line m1 i == get_line m2 i)
  in FStar.Classical.forall_intro customlemma; Seq.eq_intro #_ #params_k m1 m2

let eq_matrix_element (m1:matrix) (m2:matrix) : Lemma (requires forall i j. {:pattern (get_element m1 i j); (get_element m2 i j)} get_element m1 i j == get_element m2 i j) (ensures m1 == m2) =
  let customprop (i:size_nat{i<params_k}) : Type0 = (Seq.index #_ #params_k m1 i == Seq.index #_ #params_k m2 i) in
  let customlemma (i:size_nat{i<params_k}) : Lemma (customprop i) =
    let v1:vec = Seq.index #_ #params_k m1 i in
    let v2:vec = Seq.index #_ #params_k m2 i in
    let customprop' (j:size_nat{j<params_k}) : Type0 = (Seq.index #_ #params_k v1 j == Seq.index #_ #params_k v2 j) in
    let customlemma' (j:size_nat{j<params_k}) : Lemma (customprop' j) =
      assert(get_element m1 i j == get_element m2 i j)
    in FStar.Classical.forall_intro customlemma';
    Seq.eq_intro #_ #params_k v1 v2
  in FStar.Classical.forall_intro customlemma; Seq.eq_intro #_ #params_k m1 m2

let eq_matrix_column (m1:matrix) (m2:matrix) : Lemma (requires forall j. {:pattern (get_column m1 j); (get_column m2 j)} get_column m1 j == get_column m2 j) (ensures m1 == m2) =
  let b (i:size_nat{i<params_k}) : Type0 = (j:size_nat{j<params_k}) in
  let customprop (i:size_nat{i<params_k}) (j: b i) : Type0 = (get_element m1 i j == get_element m2 i j) in
  let customlemma (i:size_nat{i<params_k}) (j: b i) : Lemma (customprop i j) =
    assert(Seq.index #_ #params_k (get_column m1 j) i == Seq.index #_ #params_k (get_column m2 j) i)
  in FStar.Classical.forall_intro_2 customlemma; eq_matrix_element m1 m2

inline_for_extraction noextract
let rec gen_matrix_inner (m:matrix) (f: (i:nat{i<params_k}) -> (j:nat{j<params_k}) -> Tot (option poly)) (i:size_nat{i<=params_k}) (j:size_nat{j<=params_k}) : Tot (option matrix) (decreases ((params_k+1)*(params_k+1) -(params_k+1)*i-j)) =
  if (i=params_k) then Some m
  else if (j=params_k) then gen_matrix_inner m f (i+1) 0
  else
  match f i j with
  |None -> None
  |Some p -> gen_matrix_inner (upd_matrix m i j p) f i (j+1)

val gen_matrix: (f: (i:nat{i<params_k}) -> (j:nat{j<params_k}) -> Tot (option poly)) -> Tot (option matrix)

let gen_matrix f = gen_matrix_inner (new_matrix ()) f 0 0

val gen_matrix_inner_lemma0:
  (m:matrix)
  -> f: ((i:nat{i<params_k}) -> (j:nat{j<params_k}) -> Tot (option poly))
  -> (i:size_nat{i<=params_k})
  -> (j:size_nat{j<=params_k})
  -> Lemma (ensures (match gen_matrix_inner m f i j with
          |None -> True
          |Some m' -> forall (k:size_nat{k <= i /\ k < params_k}) (l:size_nat{(k < i \/ l < j) /\ l < params_k}). get_element m k l == get_element m' k l)) (decreases ((params_k+1)*(params_k+1) - (i*(params_k+1) + j)))

let rec gen_matrix_inner_lemma0 m f i j =
  if(i=params_k) then ()
  else if (j=params_k) then gen_matrix_inner_lemma0 m f (i+1) 0
  else match f i j with
    |None -> ()
    |Some p -> gen_matrix_inner_lemma0 (upd_matrix m i j p) f i (j+1)

val gen_matrix_inner_lemma:
  (m1:matrix)
  -> (m2:matrix)
  -> f: ((i:nat{i<params_k}) -> (j:nat{j<params_k}) -> Tot (option poly))
  -> (i:size_nat{i<=params_k})
  -> (j:size_nat{j<=params_k})
  -> Lemma (requires forall (k:size_nat{i <= k /\ k < params_k}) (l:size_nat{(i < k \/ j <= l) /\ l < params_k}). (get_element m2 k l) == new_poly ())
    (ensures (match (gen_matrix_inner m1 f i j), (gen_matrix_inner m2 f i j) with
      |None,None -> True
      |Some mat, Some mat' -> forall (k:size_nat{i <= k /\ k < params_k}) (l:size_nat{(i < k \/ j <= l) /\ l < params_k}). get_element mat k l == get_element mat' k l
      |_,_ -> False)) (decreases ((params_k+1)*(params_k+1) - (i*(params_k+1) + j)))

let rec gen_matrix_inner_lemma m1 m2 f i j =
  if(i = params_k) then ()
  else if (j=params_k) then gen_matrix_inner_lemma m1 m2 f (i+1) 0
  else match f i j with
  |None -> ()
  |Some p ->
    let m1' = upd_matrix m1 i j p in
    let m2' = upd_matrix m2 i j p in
    let b (k:size_nat{i <= k /\ k < params_k}) : Type0 = (l:size_nat{(i < k \/ j + 1 <= l) /\ l < params_k}) in
    let customprop (k:size_nat{i <= k /\ k < params_k}) (l:b k) : Type0 = (get_element m2' k l == new_poly ()) in
    let customlemma (k:size_nat{i <= k /\ k < params_k}) (l:b k) : Lemma (customprop k l) =
      assert(get_element m2' k l == get_element m2 k l)
    in (FStar.Classical.forall_intro_2 customlemma;
    gen_matrix_inner_lemma m1' m2' f i (j+1);
    gen_matrix_inner_lemma0 m1' f i (j+1);
    gen_matrix_inner_lemma0 m2' f i (j+1))

val gen_matrix_inner_cst_lemma:
  m:matrix
  -> f: ((i:nat{i<params_k}) -> (j:nat{j<params_k}) -> Tot (option poly))
  -> Lemma (gen_matrix_inner m f 0 0 == gen_matrix_inner (new_matrix ()) f 0 0)

let gen_matrix_inner_cst_lemma m f =
  let m0 = new_matrix () in
  gen_matrix_inner_lemma m m0 f 0 0;
  match gen_matrix_inner m f 0 0, gen_matrix_inner m0 f 0 0 with
  |None, None -> ()
  |Some mat, Some mat' -> eq_matrix_element mat mat'
  |_,_ -> ()

let dot_product (x:vec) (y:vec) = Lib.NumericTypes.dot_product x y

let matrix_vector_product (m:matrix) (v:vec) = createi params_k (fun i -> dot_product (get_line m i) v)
