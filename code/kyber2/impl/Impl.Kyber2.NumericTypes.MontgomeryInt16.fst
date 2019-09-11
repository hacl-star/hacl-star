module Impl.Kyber2.NumericTypes.MontgomeryInt16

open FStar.Mul

open Spec.Kyber2.Params
open Spec.Kyber2.NumericTypes

open FStar.HyperStack
open FStar.HyperStack.ST

module ST = FStar.HyperStack.ST

open Lib.Sequence
open Lib.Buffer
open Lib.IntTypes
//open Lib.NumericTypes

module Seq = Lib.Sequence
module Buf = Lib.Buffer

module MGroup = Impl.Kyber2.GroupMontgomery
module Group = Impl.Kyber2.Group

type num = x:int16{sint_v x > - pow2 15}
type poly = lbuffer num (size params_n)
type vec = lbuffer num ((size params_k)*!(size params_n))
type matrix = lbuffer num ((size params_k)*!(size params_k)*!(size params_n))

#reset-options "--z3rlimit 500 --max_fuel 2 --max_ifuel 2"
let to_spec_poly (h:mem) (p:poly) : Ghost (Spec.Kyber2.NumericTypes.poly) (requires T) (ensures fun p' -> p' == Seq.map MGroup.int16_to_t h.[|p|]) = Seq.map MGroup.int16_to_t h.[|p|]

let to_spec_vec (h:mem) (v:vec) : Ghost (Spec.Kyber2.NumericTypes.vec) (requires True) (ensures fun v' -> forall (i:size_nat{i<params_k}). Spec.Kyber2.NumericTypes.index_vec v' i == Seq.map MGroup.int16_to_t h.[|gsub v (size i *! size params_n) (size params_n)|]) =
  let vec_aux (j:size_nat{j<=params_k}) : Type0 = v':Spec.Kyber2.NumericTypes.vec{forall (k:size_nat{k < j}). Spec.Kyber2.NumericTypes.index_vec v' k == Seq.map MGroup.int16_to_t h.[|gsub v (size k *! size params_n) (size params_n)|]} in
  let rec aux (j:size_nat{j<=params_k}) (acc:vec_aux j) : GTot (vec_aux params_k) (decreases (params_k - j))=
    if j = params_k then acc else begin
    let p = Seq.map MGroup.int16_to_t h.[|gsub v (size j *! size params_n) (size params_n)|] in
    aux (j+1) (Spec.Kyber2.NumericTypes.upd_vec acc j p) end
  in aux 0 (Spec.Kyber2.NumericTypes.new_vec ())

let to_spec_matrix (h:mem) (m:matrix) : Ghost (Spec.Kyber2.NumericTypes.matrix) (requires True) (ensures fun m' -> forall (i:size_nat{i<params_k}). Spec.Kyber2.NumericTypes.get_line m' i == to_spec_vec h (gsub m (size i *! size params_k *! size params_n) (size params_k *! size params_n))) =
  let matrix_aux (j:size_nat{j<=params_k}) : Type0 = m':Spec.Kyber2.NumericTypes.matrix{forall (k:size_nat{k < j}). Spec.Kyber2.NumericTypes.get_line m' k == to_spec_vec h (gsub m (size k *! size params_k *! size params_n) (size params_k *! size params_n))} in
  let rec aux (j:size_nat{j<=params_k}) (acc:matrix_aux j) : GTot (matrix_aux params_k) (decreases (params_k - j))=
    if j = params_k then acc else begin
    let v = to_spec_vec h (gsub m (size j *! size params_k *! size params_n) (size params_k *! size params_n)) in
    aux (j+1) (Spec.Kyber2.NumericTypes.upd_line acc j v) end
  in aux 0 (Spec.Kyber2.NumericTypes.new_matrix ())

let to_spec_poly_lemma (h1 h2:mem) (p1 p2:vec) : Lemma (requires h1.[|p1|] == h2.[|p2|])
  (ensures to_spec_poly h1 p1 == to_spec_poly h2 p2) =
  eq_intro (to_spec_poly h1 v1) (to_spec_poly h2 v2)

let to_spec_vec_lemma (h1 h2:mem) (v1 v2:vec) : Lemma (requires h1.[|v1|] == h2.[|v2|])
  (ensures to_spec_vec h1 v1 == to_spec_vec h2 v2) =
  eq_vec (to_spec_vec h1 v1) (to_spec_vec h2 v2)

let to_spec_matrix_lemma (h1 h2:mem) (m1 m2:matrix) : Lemma (requires h1.[|m1|] == h2.[|m2|])
  (ensures to_spec_matrix h1 m1 == to_spec_matrix h2 m2) =
  let sm1 = to_spec_matrix h1 m1 in
  let sm2 = to_spec_matrix h2 m2 in
  let b (i:size_nat{i<params_k}) : Type0 = (j:size_nat{j<params_k}) in
  let customprop (k:size_nat{k<params_k}) (l: b k) : Type0 = (Spec.Kyber2.NumericTypes.get_element sm1 k l == Spec.Kyber2.NumericTypes.get_element sm2 k l) in
  let customlemma (k:size_nat{k<params_k}) (l: b k) : Lemma (customprop k l) =
    as_seq_gsub h1 m1 (size k *! size params_k *! size params_n) (size params_k *! size params_n);
    as_seq_gsub h1 (gsub m1 (size k *! size params_k *! size params_n) (size params_k *! size params_n)) (size l *! size params_n) (size params_n);
    as_seq_gsub h1 m1 (((size k *! size params_k) +! size l) *! size params_n) (size params_n);
    eq_intro h1.[|gsub (gsub m1 (size k *! size params_k *! size params_n) (size params_k *! size params_n)) (size l *! size params_n) (size params_n)|] h1.[|gsub m1 (((size k *! size params_k) +! size l) *! size params_n) (size params_n)|];
    as_seq_gsub h2 m2 (size k *! size params_k *! size params_n) (size params_k *! size params_n);
    as_seq_gsub h2 (gsub m2 (size k *! size params_k *! size params_n) (size params_k *! size params_n)) (size l *! size params_n) (size params_n);
    as_seq_gsub h2 m2 (((size k *! size params_k) +! size l) *! size params_n) (size params_n);
    eq_intro h2.[|gsub (gsub m2 (size k *! size params_k *! size params_n) (size params_k *! size params_n)) (size l *! size params_n) (size params_n)|] h2.[|gsub m2 (((size k *! size params_k) +! size l) *! size params_n) (size params_n)|]
    in FStar.Classical.forall_intro_2 customlemma;
    eq_matrix_element sm1 sm2

#reset-options "--z3rlimit 500 --max_fuel 2 --max_ifuel 2"

let new_poly () : StackInline (poly) (requires fun h0 -> True) (ensures fun h0 p h1 -> live h1 p /\ stack_allocated p h0 h1 (Seq.create params_n MGroup.zero_m) /\ Seq.map MGroup.int16_to_t h1.[|p|] == Spec.Kyber2.NumericTypes.new_poly ()) =
  assert_norm (MGroup.int16_to_t MGroup.zero_m == Group.zero_t);
  eq_intro (Seq.map MGroup.int16_to_t (Seq.create #num params_n MGroup.zero_m)) (Spec.Kyber2.NumericTypes.new_poly ());
  create (size params_n) MGroup.zero_m

let new_vec () : StackInline (vec) (requires fun h0 -> True) (ensures fun h0 v h1 -> live h1 v /\ to_spec_vec h1 v == Spec.Kyber2.NumericTypes.new_vec ()) =
  assert_norm (MGroup.int16_to_t MGroup.zero_m == Group.zero_t);
  let v = create (size params_k *! size params_n) (MGroup.zero_m) in
  let h1 = ST.get() in
  let customprop (x:size_nat{x < params_k}) : GTot Type0 = (Spec.Kyber2.NumericTypes.index_vec (to_spec_vec h1 v) x == Spec.Kyber2.NumericTypes.new_poly ()) in
  let customlemma (x:size_nat{x < params_k}) : Lemma (customprop x) =
    assert(Spec.Kyber2.NumericTypes.index_vec (to_spec_vec h1 v) x == Seq.map MGroup.int16_to_t h1.[|gsub v (size x *! size params_n) (size params_n)|]);
    as_seq_gsub h1 v (size x *! size params_n) (size params_n);
    Seq.eq_intro (Seq.map MGroup.int16_to_t (h1.[|gsub v (size x *! size params_n) (size params_n)|])) (Spec.Kyber2.NumericTypes.new_poly ())
  in FStar.Classical.forall_intro customlemma;
  Spec.Kyber2.NumericTypes.eq_vec (to_spec_vec h1 v) (Spec.Kyber2.NumericTypes.new_vec ());
  v

#reset-options "--z3rlimit 500 --max_fuel 1 --max_ifuel 1"

let new_matrix () : StackInline (matrix) (requires fun h0 -> True) (ensures fun h0 m h1 -> live h1 m /\ (forall (x:size_t{v x <params_k}) (y:size_t{v y < params_k}). to_spec_matrix h1 m == (Spec.Kyber2.NumericTypes.new_matrix ()))) =
  assert_norm (MGroup.int16_to_t MGroup.zero_m == Group.zero_t);
  let m = create (size params_k *! size params_k *! size params_n) (Group.zero_t) in
  let h1 = ST.get() in
  let b (x:size_nat{x < params_k}) : GTot Type0 = y:size_nat{y < params_k} in
  let customprop (x:size_nat{x < params_k}) (y:b x) : GTot Type0 = (Spec.Kyber2.NumericTypes.get_element (to_spec_matrix h1 m) x y == (Spec.Kyber2.NumericTypes.new_poly ())) in
  let customlemma (x:size_nat{x < params_k}) (y:b x) : Lemma (customprop x y) =
    as_seq_gsub h1 m (size x *! size params_k *! size params_n) (size params_k *! size params_n);
    as_seq_gsub h1 (gsub m (size x *! size params_k *! size params_n) (size params_k *! size params_n)) (size y *! size params_n) (size params_n);
    as_seq_gsub h1 m (((size x *!size params_k) +. size y) *! size params_n) (size params_n);
    Seq.eq_intro (h1.[|gsub (gsub m (size x *! size params_k *! size params_n) (size params_k *! size params_n)) (size y *! size params_n) (size params_n)|]) (h1.[|gsub m (((size x *!size params_k) +. size y) *! size params_n) (size params_n)|]);
    Seq.eq_intro (Seq.map MGroup.int16_to_t h1.[|gsub m (((size x *!size params_k) +. size y) *! size params_n) (size params_n)|]) (Spec.Kyber2.NumericTypes.new_poly ())
  in FStar.Classical.forall_intro_2 customlemma;
  Spec.Kyber2.NumericTypes.eq_matrix_element (to_spec_matrix h1 m) (Spec.Kyber2.NumericTypes.new_matrix ());
  m

#reset-options "--z3rlimit 1000 --max_fuel 2 --max_ifuel 2"

val get_index_vec:
  (v:vec)
  -> (i:size_t{Lib.IntTypes.v i < params_k})
  -> Stack (poly)
    (requires fun h0 -> live h0 v)
    (ensures fun h0 p h1 -> h0 == h1 /\ p == gsub v (i*!(size params_n)) (size params_n) /\ Seq.map MGroup.int16_to_t h1.[|p|] == Spec.Kyber2.NumericTypes.index_vec (to_spec_vec h0 v) (Lib.IntTypes.v i))

let get_index_vec v i = // #len v buf i =
  Buf.sub #_ #num #(size params_k *! size params_n) v (i*!(size params_n)) (size params_n)

val get_index_vec_lemma:
  h0:mem
  -> h1:mem
  -> v:vec
  -> (i:size_t{Lib.IntTypes.v i < params_k})
  -> specp:Spec.Kyber2.NumericTypes.poly
  -> Lemma (requires live h0 v /\ modifies1 (gsub v (i*!(size params_n)) (size params_n)) h0 h1 /\ Seq.map MGroup.int16_to_t h1.[|gsub v (i*!(size params_n)) (size params_n)|] == specp)
          (ensures to_spec_vec h1 v == Spec.Kyber2.NumericTypes.upd_vec (to_spec_vec h0 v) (Lib.IntTypes.v i) specp)

let get_index_vec_lemma h0 h1 v i specp =
  as_seq_gsub h1 v (i *! size params_n) (size params_n);
  assert(index_vec (to_spec_vec h1 v) (Lib.IntTypes.v i) == specp);
  let customprop (k:size_nat{k<params_k}) : GTot Type0 = (index_vec (to_spec_vec h1 v) k == index_vec (Spec.Kyber2.NumericTypes.upd_vec (to_spec_vec h0 v) (Lib.IntTypes.v i) specp) k) in
  let customlemma (k:size_nat{k<params_k}) : Lemma(customprop k) =
    if k = Lib.IntTypes.v i then () else
    as_seq_gsub h1 v (size k *! size params_n) (size params_n)
  in FStar.Classical.forall_intro customlemma;
  Spec.Kyber2.NumericTypes.eq_vec (to_spec_vec h1 v) (Spec.Kyber2.NumericTypes.upd_vec (to_spec_vec h0 v) (Lib.IntTypes.v i) specp)

val copy_index_vec:
  (v:vec)
-> (output:poly)
-> (i:size_t{Lib.IntTypes.v i < params_k})
-> Stack unit
  (requires fun h0 -> live h0 v /\ live h0 output /\ Buf.disjoint v output)
  (ensures fun h0 _ h1 -> modifies1 output h0 h1 /\ Seq.map MGroup.int16_to_t h1.[|output|] == Spec.Kyber2.NumericTypes.index_vec (to_spec_vec h0 v) (Lib.IntTypes.v i))

let copy_index_vec v output i =
  Buf.copy output (get_index_vec v i)

val get_line:
  (m:matrix)
  -> (i:size_t{v i < params_k})
  -> Stack (vec)
    (requires fun h0 -> live h0 m)
    (ensures fun h0 v' h1 -> h0 == h1 /\ v' == gsub m (i *! size params_k *! size params_n) (size params_k *! size params_n) /\ to_spec_vec h1 v' == Spec.Kyber2.NumericTypes.get_line (to_spec_matrix h0 m) (v i))

let get_line m i =
  Buf.sub #_ #num #(size params_k *! size params_k *! size params_n) m (i *! size params_k *! size params_n) (size params_k *! size params_n)

val get_line_lemma:
  h0:mem
  -> h1:mem
  -> (m:matrix)
  -> (i:size_t{v i < params_k})
  -> (specv:Spec.Kyber2.NumericTypes.vec)
  -> Lemma (requires live h0 m /\ modifies1 (gsub m (i *! size params_k *! size params_n) (size params_k *! size params_n)) h0 h1 /\ to_spec_vec h1 (gsub m (i *! size params_k *! size params_n) (size params_k *! size params_n)) == specv) (ensures to_spec_matrix h1 m == Spec.Kyber2.NumericTypes.upd_line (to_spec_matrix h0 m) (v i) specv)

let get_line_lemma h0 h1 m i specv =
  as_seq_gsub h1 m (i *! size params_k *! size params_n) (size params_k *! size params_n);
  eq_vec (Spec.Kyber2.NumericTypes.get_line (to_spec_matrix h1 m) (v i)) specv;
  let customprop (k:size_nat{k<params_k}) : GTot Type0 = (Spec.Kyber2.NumericTypes.get_line (to_spec_matrix h1 m) k == Spec.Kyber2.NumericTypes.get_line (Spec.Kyber2.NumericTypes.upd_line (to_spec_matrix h0 m) (v i) specv) k) in
  let customlemma (k:size_nat{k<params_k}) : Lemma(customprop k) =
    if k = Lib.IntTypes.v i then () else begin
    let memvect = gsub m (size k *! size params_k *! size params_n) (size params_k *! size params_n) in
    as_seq_gsub h1 m (size k *! size params_k *! size params_n) (size params_k *! size params_n);
    assert(Buf.disjoint (gsub m (i *! size params_k *! size params_n) (size params_k *! size params_n)) memvect);
    let vect0 = to_spec_vec h0 memvect in
    let vect1 = to_spec_vec h1 memvect in
    assert(h1.[|memvect|] == h0.[|memvect|]);
    assert(vect1 == Spec.Kyber2.NumericTypes.get_line (to_spec_matrix h1 m) k);
    assert(vect0 == Spec.Kyber2.NumericTypes.get_line (Spec.Kyber2.NumericTypes.upd_line (to_spec_matrix h0 m) (v i) specv) k);
    to_spec_vec_lemma h0 h1 memvect memvect end
  in FStar.Classical.forall_intro customlemma;
  Spec.Kyber2.NumericTypes.eq_matrix_line (to_spec_matrix h1 m) (Spec.Kyber2.NumericTypes.upd_line (to_spec_matrix h0 m) (v i) specv)

val copy_line:
  (m:matrix)
  -> (output:vec)
  -> (i:size_t{v i < params_k})
  -> Stack unit
    (requires fun h0 -> live h0 m /\ live h0 output /\ Buf.disjoint m output)
    (ensures fun h0 _ h1 -> live h1 output /\ modifies1 output h0 h1 /\ to_spec_vec h1 output == Spec.Kyber2.NumericTypes.get_line (to_spec_matrix h0 m) (v i))

let copy_line m output i =
  let h0 = ST.get () in
  Buf.copy output (get_line m i);
  let h1 = ST.get () in
  let spec_v = to_spec_vec h1 output in
  Spec.Kyber2.NumericTypes.eq_vec spec_v (Spec.Kyber2.NumericTypes.get_line (to_spec_matrix h0 m) (v i))

val get_element:
  m:matrix
  -> i:size_t{v i < params_k}
  -> j:size_t{v j < params_k}
  -> Stack poly
    (requires fun h0 -> live h0 m)
    (ensures fun h0 p h1 -> h0 == h1 /\ p == gsub m (((i*!size params_k) +! j) *! (size params_n)) (size params_n) /\ Seq.map MGroup.int16_to_t h1.[|p|] == Spec.Kyber2.NumericTypes.get_element (to_spec_matrix h0 m) (v i) (v j))

let get_element m i j =
  let h = ST.get () in
  as_seq_gsub h m (i *! size params_k *! size params_n) (size params_k *! size params_n);
  as_seq_gsub h (gsub m (i *! size params_k *! size params_n) (size params_k *! size params_n)) (j *! size params_n) (size params_n);
  as_seq_gsub h m (((i *! size params_k) +! j) *! size params_n) (size params_n);
  eq_intro h.[|gsub (gsub m (i *! size params_k *! size params_n) (size params_k *! size params_n)) (j *! size params_n) (size params_n)|] h.[|gsub m (((i *! size params_k) +! j) *! size params_n) (size params_n)|];
  Buf.sub #_ #num #(size params_k *! size params_k *! size params_n) m (((i*!size params_k) +! j) *! (size params_n)) (size params_n)

val get_element_lemma:
  h0:mem
  -> h1:mem
  -> m:matrix
  -> i:size_t{v i < params_k}
  -> j:size_t{v j < params_k}
  -> specp:Spec.Kyber2.NumericTypes.poly
  -> Lemma (requires live h0 m /\ modifies1 (gsub m (((i*!size params_k) +! j) *! (size params_n)) (size params_n)) h0 h1 /\ Seq.map MGroup.int16_to_t h1.[|gsub m (((i*!size params_k) +! j) *! (size params_n)) (size params_n)|] == specp) (ensures to_spec_matrix h1 m == Spec.Kyber2.NumericTypes.upd_matrix (to_spec_matrix h0 m) (v i) (v j) specp)

let get_element_lemma h0 h1 m i j specp =
  let m1 = to_spec_matrix h1 m in
  let m2 = Spec.Kyber2.NumericTypes.upd_matrix (to_spec_matrix h0 m) (v i) (v j) specp in
  let b (k:size_nat{k<params_k}) : GTot Type0 = (l:size_nat{l<params_k}) in
  as_seq_gsub h1 m (i *! size params_k *! size params_n) (size params_k *! size params_n);
  as_seq_gsub h1 (gsub m (i *! size params_k *! size params_n) (size params_k *! size params_n)) (j *! size params_n) (size params_n);
  as_seq_gsub h1 m (((i *! size params_k) +! j) *! size params_n) (size params_n);
  eq_intro h1.[|gsub (gsub m (i *! size params_k *! size params_n) (size params_k *! size params_n)) (j *! size params_n) (size params_n)|] h1.[|gsub m (((i *! size params_k) +! j) *! size params_n) (size params_n)|];
  assert(modifies1 (gsub m (((i *! size params_k) +! j) *! size params_n) (size params_n)) h0 h1);
  let customprop (k:size_nat{k<params_k}) (l: b k) : GTot Type0 = (Spec.Kyber2.NumericTypes.get_element m1 k l == Spec.Kyber2.NumericTypes.get_element m2 k l) in
  let customlemma (k:size_nat{k<params_k}) (l: b k) : Lemma (customprop k l) =
    if(k = v i && l = v j) then () else begin
    let p0 = Seq.map MGroup.int16_to_t h0.[|gsub m (((size k *! size params_k) +! size l) *! size params_n) (size params_n)|] in
    let p1 = Seq.map MGroup.int16_to_t h1.[|gsub m (((size k *! size params_k) +! size l) *! size params_n) (size params_n)|] in
    as_seq_gsub h1 m (size k *! size params_k *! size params_n) (size params_k *! size params_n);
    as_seq_gsub h1 (gsub m (size k *! size params_k *! size params_n) (size params_k *! size params_n)) (size l *! size params_n) (size params_n);
    as_seq_gsub h1 m (((size k *! size params_k) +! size l) *! size params_n) (size params_n);
    eq_intro h1.[|gsub (gsub m (size k *! size params_k *! size params_n) (size params_k *! size params_n)) (size l *! size params_n) (size params_n)|] h1.[|gsub m (((size k *! size params_k) +! size l) *! size params_n) (size params_n)|];
    as_seq_gsub h0 m (size k *! size params_k *! size params_n) (size params_k *! size params_n);
    as_seq_gsub h0 (gsub m (size k *! size params_k *! size params_n) (size params_k *! size params_n)) (size l *! size params_n) (size params_n);
    as_seq_gsub h0 m (((size k *! size params_k) +! size l) *! size params_n) (size params_n);
    eq_intro h0.[|gsub (gsub m (size k *! size params_k *! size params_n) (size params_k *! size params_n)) (size l *! size params_n) (size params_n)|] h0.[|gsub m (((size k *! size params_k) +! size l) *! size params_n) (size params_n)|];
    assert(p0 == Spec.Kyber2.NumericTypes.get_element m2 k l);
    assert(p1 == Spec.Kyber2.NumericTypes.get_element m1 k l);
    assert(Buf.disjoint (gsub m (((size k *! size params_k) +! size l) *! size params_n) (size params_n)) (gsub m (((i *! size params_k) +! j) *! size params_n) (size params_n)));
    eq_intro p0 p1
    end
  in FStar.Classical.forall_intro_2 customlemma; eq_matrix_element m1 m2

val copy_element:
  m:matrix
  -> output:poly
  -> i:size_t{v i < params_k}
  -> j:size_t{v j < params_k}
  -> Stack unit
    (requires fun h0 -> live h0 m /\ live h0 output /\ Buf.disjoint m output)
    (ensures fun h0 p h1 -> modifies1 output h0 h1 /\ Seq.map MGroup.int16_to_t h1.[|output|] == Spec.Kyber2.NumericTypes.get_element (to_spec_matrix h0 m) (v i) (v j))

let copy_element m output i j =
  Buf.copy output (get_element m i j)

val copy_column:
  (m:matrix)
  -> (output:vec)
  -> (j:size_t{v j < params_k})
  -> Stack unit
    (requires fun h0 -> live h0 m /\ live h0 output /\ Buf.disjoint m output)
    (ensures fun h0 _ h1 -> modifies1 output h0 h1 /\ live h1 output /\ to_spec_vec h1 output == Spec.Kyber2.NumericTypes.get_column (to_spec_matrix h0 m) (v j))

#reset-options "--z3rlimit 1000 --max_fuel 1 --max_ifuel 1 --print_universes"

let copy_column m output j =
  let h0 = ST.get () in
  push_frame ();
  let i = create 1ul 0ul in
  let h' = ST.get () in
  Lib.Loops.while (fun h -> v h.[|i|].[0] <= params_k /\ live h output /\ live h m /\ live h i /\ Buf.disjoint m output /\ Buf.disjoint m i /\ Buf.disjoint output i /\ modifies2 output i h' h /\ (forall (x:size_nat{x< v #U32 #PUB h.[|i|].[0]}). Spec.Kyber2.NumericTypes.index_vec (to_spec_vec h output) x == Spec.Kyber2.NumericTypes.index_vec (Spec.Kyber2.NumericTypes.get_column (to_spec_matrix h0 m) (v j)) x))
    (fun h -> v h.[|i|].[0] < params_k)
    (fun () -> i.(0ul) <. size params_k)
    (fun () -> let k = i.(0ul) in assert(v k<params_k);
       let p = get_index_vec output k in
       let h' = ST.get() in
       assert(p == gsub output (k*!size params_n) (size params_n));
       copy_element m p k j;
       let h'' = ST.get () in
       assert(Spec.Kyber2.NumericTypes.get_element (to_spec_matrix h0 m) (v k) (v j) == Spec.Kyber2.NumericTypes.index_vec (Spec.Kyber2.NumericTypes.get_column (to_spec_matrix h0 m) (v j)) (v k));
       get_index_vec_lemma h' h'' output k (Spec.Kyber2.NumericTypes.index_vec (Spec.Kyber2.NumericTypes.get_column (to_spec_matrix h0 m) (v j)) (v k));
       assert_norm(params_k < maxint U32); i.(0ul) <- k +! 1ul;
       let h = ST.get () in
       to_spec_vec_lemma h'' h output output
       );
  pop_frame ();
  let h1 = ST.get () in
  Spec.Kyber2.NumericTypes.eq_vec (to_spec_vec h1 output) (Spec.Kyber2.NumericTypes.get_column (to_spec_matrix h0 m) (v j))

val upd_vec:
  v:vec
  -> i:size_t{Lib.IntTypes.v i < params_k}
  -> p:poly
  -> Stack unit
    (requires fun h -> live h v /\ live h p /\ Buf.disjoint (gsub v (i *! size params_n) (size params_n)) p)
    (ensures fun h0 _ h1 -> modifies1 v h0 h1 /\ to_spec_vec h1 v == Spec.Kyber2.NumericTypes.upd_vec (to_spec_vec h0 v) (Lib.IntTypes.v i) (Seq.map MGroup.int16_to_t h0.[|p|]))

let upd_vec v i p =
  let h0 = ST.get () in
  Buf.copy (get_index_vec v i) p;
  let h1 = ST.get () in
  get_index_vec_lemma h0 h1 v i (Seq.map MGroup.int16_to_t h0.[|p|])

val upd_line:
  m:matrix
  -> i:size_t{v i < params_k}
  -> v':vec
  -> Stack unit
    (requires fun h -> live h m /\ live h v' /\ Buf.disjoint (gsub m (i*!size params_k*!size params_n) (size params_k*!size params_n)) v')
    (ensures fun h0 _ h1 -> modifies1 m h0 h1 /\ to_spec_matrix h1 m == Spec.Kyber2.NumericTypes.upd_line (to_spec_matrix h0 m) (v i) (to_spec_vec h0 v'))

#reset-options "--z3rlimit 1000 --max_fuel 1 --max_ifuel 1 --print_universes"

let upd_line m i v' =
  let h0 = ST.get () in
  Buf.copy (get_line m i) v';
  let h1 = ST.get () in
  to_spec_vec_lemma h0 h1 v' (gsub m (i*!size params_k*!size params_n) (size params_k*!size params_n));
  get_line_lemma h0 h1 m i (to_spec_vec h0 v')

val upd_matrix:
  m:matrix
  -> i:size_t{v i < params_k}
  -> j:size_t{v j < params_k}
  -> p:poly
  -> Stack unit
    (requires fun h -> live h m /\ live h p /\ Buf.disjoint (gsub m (((i*!size params_k) +!j)*!size params_n) (size params_n)) p)
    (ensures fun h0 _ h1 -> modifies1 m h0 h1 /\ to_spec_matrix h1 m == Spec.Kyber2.NumericTypes.upd_matrix (to_spec_matrix h0 m) (v i) (v j) (Seq.map MGroup.int16_to_t h0.[|p|]))

let upd_matrix m i j p =
  let h0 = ST.get () in
  Buf.copy (get_element m i j) p;
  let h1 = ST.get () in
  as_seq_gsub h1 m (i *! size params_k *! size params_n) (size params_k *! size params_n);
  as_seq_gsub h1 (gsub m (i *! size params_k *! size params_n) (size params_k *! size params_n)) (j *! size params_n) (size params_n);
  as_seq_gsub h1 m (((i *! size params_k) +! j) *! size params_n) (size params_n);
  eq_intro h1.[|gsub (gsub m (i *! size params_k *! size params_n) (size params_k *! size params_n)) (j *! size params_n) (size params_n)|] h1.[|gsub m (((i *! size params_k) +! j) *! size params_n) (size params_n)|];
  get_element_lemma h0 h1 m i j (Seq.map MGroup.int16_to_t h0.[|p|])

inline_for_extraction noextract
let gen_matrix_inv (h0 h:mem) (m:matrix) (spec_f: (k:nat{k < params_k}) -> (l:nat{l < params_k}) -> Tot (option Spec.Kyber2.NumericTypes.poly)) (i:lbuffer (i:size_t{v i <= params_k}) 1ul) (j:lbuffer (j:size_t{v j <= params_k}) 1ul) (b:lbuffer bool 1ul) : GTot Type0 =
  match Spec.Kyber2.NumericTypes.gen_matrix_inner (to_spec_matrix h0 m) spec_f 0 0 with
  |None -> (match Spec.Kyber2.NumericTypes.gen_matrix_inner (to_spec_matrix h m) spec_f (v h.[|i|].[0]) (v h.[|j|].[0]) with
              |None -> (v h.[|i|].[0] < params_k)
              |Some _ -> False)
  |Some mat -> match Spec.Kyber2.NumericTypes.gen_matrix_inner (to_spec_matrix h m) spec_f (v h.[|i|].[0]) (v h.[|j|].[0]) with
              |None -> False
              |Some mat' -> mat == mat' /\ h.[|b|].[0]

inline_for_extraction noextract
val gen_matrix_inner:
  (h_:mem)
  -> (m:matrix)
  -> (spec_f: ((k:nat{k < params_k}) -> (l:nat{l < params_k}) -> Tot (option Spec.Kyber2.NumericTypes.poly)))
  -> (impl_f: ((k:size_t{v k < params_k}) -> (l:size_t{v l < params_k}) -> (out:poly)
             -> Stack bool (requires fun h -> live h out)
                          (ensures fun h0 b h1 -> modifies1 out h0 h1 /\ (match spec_f (v k) (v l) with
                          |None -> b == false | Some p -> (b == true /\ Seq.map MGroup.int16_to_t h1.[|out|] == p)))))
  -> (i:lbuffer (i:size_t{v i <= params_k}) 1ul)
  -> (j:lbuffer (j:size_t{v j <= params_k}) 1ul)
  -> (b:lbuffer bool 1ul)
  -> Stack unit
    (requires fun h -> live h m /\ live h i /\ live h j /\ live h b /\
                    Buf.disjoint m i /\ Buf.disjoint m j /\ Buf.disjoint m b /\
                    Buf.disjoint i j /\ Buf.disjoint i b /\ Buf.disjoint j b
                    /\ modifies4 m i j b h_ h /\ gen_matrix_inv h_ h m spec_f i j b
                    /\ h.[|i|].[0] <. size params_k /\ h.[|b|].[0])
    (ensures fun h0 _ h1 -> (h1.[|b|].[0] = false ==> modifies2 m b h0 h1) /\ (h1.[|b|].[0] ==> modifies3 m i j h0 h1) /\ gen_matrix_inv h_ h1 m spec_f i j b)


#reset-options "--z3rlimit 200 --max_fuel 1 --max_ifuel 1 --print_universes"

let gen_matrix_inner h_ m spec_f impl_f i j b =
  let h0 = ST.get () in
  if (j.(0ul) =. size params_k) then begin
    let k = i.(0ul) in
    i.(0ul) <- k +! 1ul;
    j.(0ul) <- 0ul;
    let h1 = ST.get () in
    to_spec_matrix_lemma h0 h1 m m end
  else let b'= impl_f i.(0ul) j.(0ul) (get_element m i.(0ul) j.(0ul)) in
    if (b'= false) then b.(0ul) <- false
    else begin
      let h' = ST.get () in
      let k = j.(0ul) in
      j.(0ul) <- k +! 1ul;
      let h1 = ST.get () in
      (let i' = Buf.bget h0 i 0 in
      let j' = bget h0 j 0 in
      let j1 = bget h1 j 0 in
      bget_as_seq h0 i 0;
      bget_as_seq h0 j 0;
      bget_as_seq h1 j 0;
      let f () : GTot (bool & Spec.Kyber2.NumericTypes.poly) =
        match spec_f (v i') (v j') with
        |None -> false, Spec.Kyber2.NumericTypes.new_poly ()
        |Some p -> true, p
      in
      let b0, p = f () in
      assert (b0 = true);
      get_element_lemma h0 h' m i' j' p;
      to_spec_matrix_lemma h' h1 m m)
    end


inline_for_extraction noextract
val gen_matrix:
  (m:matrix)
  -> (spec_f: ((k:nat{k < params_k}) -> (l:nat{l < params_k}) -> Tot (option Spec.Kyber2.NumericTypes.poly)))
  -> (impl_f: ((k:size_t{v k < params_k}) -> (l:size_t{v l < params_k}) -> (out:poly)
             -> Stack bool (requires fun h -> live h out)
                          (ensures fun h0 b h1 -> modifies1 out h0 h1 /\ (match spec_f (v k) (v l) with
                          |None -> b == false | Some p -> (b == true /\ Seq.map MGroup.int16_to_t h1.[|out|] == p)))))
  -> Stack bool
    (requires fun h -> live h m)
    (ensures fun h0 res h1 -> modifies1 m h0 h1 /\ (match Spec.Kyber2.NumericTypes.gen_matrix spec_f with
      |None -> (res == false) |Some mat -> to_spec_matrix h1 m == mat /\ res == true))

let gen_matrix m spec_f impl_f =
  let h_begin = ST.get () in
  push_frame ();
  let i = create 1ul 0ul in
  let j = create 1ul 0ul in
  let b = create 1ul true in
  let h0 = ST.get () in
  to_spec_matrix_lemma h_begin h0 m m;
  Lib.Loops.while
    (fun h -> v h.[|i|].[0] <= params_k /\ v h.[|j|].[0] <= params_k /\ modifies4 m i j b h0 h /\ gen_matrix_inv h0 h m spec_f i j b)
    (fun h -> v h.[|i|].[0] < params_k && h.[|b|].[0])
    (fun () -> let a : bool = i.(0ul) <. size params_k in let b : bool = b.(0ul) in a && b)
    (fun () -> gen_matrix_inner h0 m spec_f impl_f i j b);
  let h1 = ST.get () in
  gen_matrix_inner_cst_lemma (to_spec_matrix h0 m) spec_f;
  let b = b.(0ul) in
  pop_frame ();
  let h_end = ST.get () in
  to_spec_matrix_lemma h1 h_end m m;
  b

#reset-options "--z3rlimit 400 --max_fuel 1 --max_ifuel 1 --print_universes"

let lemma_test #a #n (x:lseq a n) : Lemma (of_list (to_list x) == x) =
  FStar.Seq.Properties.lemma_seq_list_bij x

noextract
assume val zetas_list : x:(list MGroup.montgomery_t){List.length x = 128 /\ pow2 7 = 128 /\ (forall (k:size_nat{k<128}). MGroup.to_t (FStar.List.Tot.index x k) == Lib.Arithmetic.Ring.exp #Group.t #Spec.Kyber2.Ring.ring_t (Spec.Kyber2.Group.mk_t params_zeta) (Lib.Arithmetic.Sums.br 7 k))}

noextract
let zetas_seq : x:(lseq MGroup.montgomery_t 128){pow2 7 = 128 /\ (forall (k:size_nat{k<128}). MGroup.to_t x.[k] == Lib.Arithmetic.Ring.exp #Group.t #Spec.Kyber2.Ring.ring_t (Spec.Kyber2.Group.mk_t params_zeta) (Lib.Arithmetic.Sums.br 7 k))} = of_list zetas_list

#reset-options "--z3rlimit 400 --max_fuel 2 --max_ifuel 1 --print_universes"

let zetas : x:(ilbuffer MGroup.montgomery_t (size 128)){Buf.witnessed x zetas_seq /\ Buf.recallable x}
=
 Buf.createL_global zetas_list

let lemma_mod (j:size_t{v j < params_n / 4}) : Lemma ((4*(v j)) % 2 = 0 /\ (4*(v j)+1) % 2 = 1 /\ (4*(v j)+2) % 2 = 0 /\ (4*(v j)+3) % 2 = 1 /\ 4*(v j)+3 < params_n /\ (4*(v j)) / 2 = 2*(v j) /\ (4*(v j)+2) / 2 = 2*(v j)+1 /\ 4*(v j) = (4*(v j)+1)-1 /\ 4*(v j)+2 = (4*(v j)+3) - 1) =
  FStar.Math.Lemmas.paren_mul_right 2 2 (v j);
  assert(4*(v j) = 2*(2*v j));
  FStar.Math.Lemmas.swap_mul 2 (2*(v j));
  FStar.Math.Lemmas.division_definition (4*(v j)) 2 (2*(v j));
  FStar.Math.Lemmas.euclidean_division_definition (4*(v j)) 2;
  assert((4*(v j))/2 = 2*(v j));
  assert ((4*(v j)) % 2 = 0);
  FStar.Math.Lemmas.modulo_distributivity (4 * (v j)) 1 2;
  FStar.Math.Lemmas.modulo_distributivity (4 * (v j)) 2 2;
  FStar.Math.Lemmas.modulo_distributivity (4 * (v j)) 3 2;
  FStar.Math.Lemmas.modulo_distributivity 0 1 2;
  FStar.Math.Lemmas.modulo_distributivity 0 2 2;
  FStar.Math.Lemmas.modulo_distributivity 0 3 2;
  FStar.Math.Lemmas.lemma_mod_twice 1 2;
  FStar.Math.Lemmas.lemma_mod_twice 2 2;
  FStar.Math.Lemmas.lemma_mod_twice 3 2;
  assert ((4*(v j)+1) % 2 = 1);
  assert ((4*(v j)+2) % 2 = 0);
  assert ((4*(v j)+3) % 2 = 1);
  FStar.Math.Lemmas.lemma_div_plus (4*(v j)) 1 2

inline_for_extraction noextract
val poly_mul_inner_odd:
  p1:poly
  -> p2:poly
  -> output:poly
  -> j:size_t{v j < params_n / 4}
  -> Stack unit
    (requires fun h -> live h p1 /\ live h p2 /\ live h output /\ Buf.disjoint p1 output /\ Buf.disjoint p2 output
                    /\ (forall (k:nat{k<params_n}). v h.[|p1|].[k] <= params_q /\ v h.[|p1|].[k] >= - params_q) /\ (forall (k:nat{k<4*v j}). v h.[|output|].[k] <= 2 * params_q /\ v h.[|output|].[k] >= -2 * params_q /\ MGroup.int16_to_t h.[|output|].[k] == (Lib.Poly.NTT2.lib_ntt_mul #Group.t #Spec.Kyber2.Ring.ring_t #params_n 7 (Spec.Kyber2.Group.mk_t params_zeta) (Seq.map MGroup.int16_to_t h.[|p1|]) (Seq.map MGroup.int16_to_t h.[|p2|])).[k]))
    (ensures fun h0 _ h1 -> live h1 p1 /\ live h1 p2 /\ live h1 output /\ Buf.disjoint p1 output /\ Buf.disjoint p2 output
                       /\ modifies1 output h0 h1 /\ v h1.[|output|].[4*(v j)+1] <= 2 * params_q /\ v h1.[|output|].[4*(v j)+1] >= -2 * params_q /\ v h1.[|output|].[4*(v j)+3] <= 2 * params_q /\ v h1.[|output|].[4*(v j)+3] >= -2 * params_q /\ MGroup.int16_to_t h1.[|output|].[4*(v j)+1] == (Lib.Poly.NTT2.lib_ntt_mul #Group.t #Spec.Kyber2.Ring.ring_t #params_n 7 (Spec.Kyber2.Group.mk_t params_zeta) (Seq.map MGroup.int16_to_t h1.[|p1|]) (Seq.map MGroup.int16_to_t h1.[|p2|])).[4*(v j)+1] /\ MGroup.int16_to_t h1.[|output|].[4*(v j)+3] == (Lib.Poly.NTT2.lib_ntt_mul #Group.t #Spec.Kyber2.Ring.ring_t #params_n 7 (Spec.Kyber2.Group.mk_t params_zeta) (Seq.map MGroup.int16_to_t h1.[|p1|]) (Seq.map MGroup.int16_to_t h1.[|p2|])).[4*(v j)+3] /\ (forall (k:nat{k<4*v j}). v h1.[|output|].[k] <= 2 * params_q /\ v h1.[|output|].[k] >= -2 * params_q /\ MGroup.int16_to_t h1.[|output|].[k] == (Lib.Poly.NTT2.lib_ntt_mul #Group.t #Spec.Kyber2.Ring.ring_t #params_n 7 (Spec.Kyber2.Group.mk_t params_zeta) (Seq.map MGroup.int16_to_t h1.[|p1|]) (Seq.map MGroup.int16_to_t h1.[|p2|])).[k]))

let poly_mul_inner_odd p1 p2 output j =
  let h0 = ST.get () in
  assert(4*(v j) +3 < params_n);
  assert(v h0.[|p1|].[4*(v j)] <= params_q);
  assert(v h0.[|p1|].[4*(v j)+1] <= params_q);
  assert(v h0.[|p1|].[4*(v j)+2] <= params_q);
  assert(v h0.[|p1|].[4*(v j)+3] <= params_q);
  let f3 = MGroup.mul_m_int16 p2.((size 4)*!j) p1.(((size 4)*!j)+!1ul) in
  let f7 = MGroup.mul_m_int16 p2.(((size 4)*!j) +! 2ul) p1.(((size 4)*!j)+!3ul) in
  Spec.Kyber2.Ring.lemma_mul_swap_t (MGroup.int16_to_t h0.[|p2|].[4*(v j)]) (MGroup.int16_to_t h0.[|p1|].[4*(v j)+1]);
  assert(MGroup.to_t f3 == Group.mul_t (MGroup.int16_to_t h0.[|p1|].[4*(v j)+1]) (MGroup.int16_to_t h0.[|p2|].[4*(v j)]));
  output.(((size 4)*!j)+!1ul) <- f3 +! (MGroup.mul_m_int16 p2.(((size 4)*!j)+!1ul) p1.((size 4)*!j));
  Spec.Kyber2.Ring.lemma_mul_swap_t (MGroup.int16_to_t h0.[|p2|].[4*(v j)+2]) (MGroup.int16_to_t h0.[|p1|].[4*(v j)+3]);
  assert(MGroup.to_t f7 == Group.mul_t (MGroup.int16_to_t h0.[|p1|].[4*(v j)+3]) (MGroup.int16_to_t h0.[|p2|].[4*(v j)+2]));
  output.(((size 4)*!j)+!3ul) <- f7 +! (MGroup.mul_m_int16 p2.(((size 4)*!j)+!3ul) p1.(((size 4)*!j)+!2ul));
  let h_0 = ST.get () in
  Spec.Kyber2.Ring.lemma_mul_swap_t (MGroup.int16_to_t h0.[|p2|].[4*(v j)+1]) (MGroup.int16_to_t h0.[|p1|].[4*(v j)]);
  Spec.Kyber2.Ring.lemma_mul_swap_t (MGroup.int16_to_t h0.[|p2|].[4*(v j)+3]) (MGroup.int16_to_t h0.[|p1|].[4*(v j)+2]);
  MGroup.plus_lemma_int16_2 f3 (MGroup.mul_m_int16 h0.[|p2|].[4*(v j)+1] h0.[|p1|].[4*(v j)]) (h_0.[|output|].[4*(v j) + 1]);
  MGroup.plus_lemma_int16_2 f7 (MGroup.mul_m_int16 h0.[|p2|].[4*(v j)+3] h0.[|p1|].[4*(v j)+2]) (h_0.[|output|].[4*(v j) + 3]);
  assert_norm(pow2 7 = params_n / 2);
  lemma_mod j;
  Lib.Poly.NTT2.lib_ntt_mul_odd_lemma_instantiate 7 (Spec.Kyber2.Group.mk_t params_zeta) (Seq.map MGroup.int16_to_t h0.[|p1|]) (Seq.map MGroup.int16_to_t h0.[|p2|]) (Lib.Poly.NTT2.lib_ntt_mul #Group.t #Spec.Kyber2.Ring.ring_t #params_n 7 (Spec.Kyber2.Group.mk_t params_zeta) (Seq.map MGroup.int16_to_t h0.[|p1|]) (Seq.map MGroup.int16_to_t h0.[|p2|])) (4*(v j)+1);
  Lib.Poly.NTT2.lib_ntt_mul_odd_lemma_instantiate 7 (Spec.Kyber2.Group.mk_t params_zeta) (Seq.map MGroup.int16_to_t h0.[|p1|]) (Seq.map MGroup.int16_to_t h0.[|p2|]) (Lib.Poly.NTT2.lib_ntt_mul #Group.t #Spec.Kyber2.Ring.ring_t #params_n 7 (Spec.Kyber2.Group.mk_t params_zeta) (Seq.map MGroup.int16_to_t h0.[|p1|]) (Seq.map MGroup.int16_to_t h0.[|p2|])) (4*(v j)+3);
  assert(MGroup.int16_to_t h_0.[|output|].[4*(v j) + 1] == Group.plus_t (Group.mul_t (MGroup.int16_to_t h0.[|p1|].[4*(v j)+1]) (MGroup.int16_to_t h0.[|p2|].[4*(v j)])) (Group.mul_t (MGroup.int16_to_t h0.[|p1|].[4*(v j)]) (MGroup.int16_to_t h0.[|p2|].[4*(v j)+1])));
  assert((Seq.map MGroup.int16_to_t h0.[|p1|]).[4*(v j)] == MGroup.int16_to_t h0.[|p1|].[4*(v j)]);
  assert((Seq.map MGroup.int16_to_t h0.[|p1|]).[4*(v j)+1] == MGroup.int16_to_t h0.[|p1|].[4*(v j)+1]);
  assert((Seq.map MGroup.int16_to_t h0.[|p2|]).[4*(v j)] == MGroup.int16_to_t h0.[|p2|].[4*(v j)]);
  assert((Seq.map MGroup.int16_to_t h0.[|p2|]).[4*(v j)+1] == MGroup.int16_to_t h0.[|p2|].[4*(v j)+1]);
  assert (MGroup.int16_to_t h_0.[|output|].[4*(v j) + 1] == (Lib.Poly.NTT2.lib_ntt_mul #Group.t #Spec.Kyber2.Ring.ring_t #params_n 7 (Spec.Kyber2.Group.mk_t params_zeta) (Seq.map MGroup.int16_to_t h0.[|p1|]) (Seq.map MGroup.int16_to_t h0.[|p2|])).[4*(v j)+1]);
  assert(MGroup.int16_to_t h_0.[|output|].[4*(v j) + 3] == Group.plus_t (Group.mul_t (MGroup.int16_to_t h0.[|p1|].[4*(v j)+3]) (MGroup.int16_to_t h0.[|p2|].[4*(v j)+2])) (Group.mul_t (MGroup.int16_to_t h0.[|p1|].[4*(v j)+2]) (MGroup.int16_to_t h0.[|p2|].[4*(v j)+3])));
  assert((Seq.map MGroup.int16_to_t h0.[|p1|]).[4*(v j)+2] == MGroup.int16_to_t h0.[|p1|].[4*(v j)+2]);
  assert((Seq.map MGroup.int16_to_t h0.[|p1|]).[4*(v j)+3] == MGroup.int16_to_t h0.[|p1|].[4*(v j)+3]);
  assert((Seq.map MGroup.int16_to_t h0.[|p2|]).[4*(v j)+2] == MGroup.int16_to_t h0.[|p2|].[4*(v j)+2]);
  assert((Seq.map MGroup.int16_to_t h0.[|p2|]).[4*(v j)+3] == MGroup.int16_to_t h0.[|p2|].[4*(v j)+3]);
  assert (MGroup.int16_to_t h_0.[|output|].[4*(v j) + 3] == (Lib.Poly.NTT2.lib_ntt_mul #Group.t #Spec.Kyber2.Ring.ring_t #params_n 7 (Spec.Kyber2.Group.mk_t params_zeta) (Seq.map MGroup.int16_to_t h0.[|p1|]) (Seq.map MGroup.int16_to_t h0.[|p2|])).[4*(v j)+3])

val poly_mul_inner:
  p1:poly
  -> p2:poly
  -> output:poly
  -> j:size_t{v j < params_n / 4}
  -> Stack unit
    (requires fun h -> live h p1 /\ live h p2 /\ live h output /\ Buf.disjoint p1 output /\ Buf.disjoint p2 output
                    /\ (forall (k:nat{k<params_n}). v h.[|p1|].[k] <= params_q /\ v h.[|p1|].[k] >= - params_q) /\ (forall (k:nat{k<4*v j}). v h.[|output|].[k] <= 2 * params_q /\ v h.[|output|].[k] >= -2 * params_q /\ MGroup.int16_to_t h.[|output|].[k] == (Lib.Poly.NTT2.lib_ntt_mul #Group.t #Spec.Kyber2.Ring.ring_t #params_n 7 (Spec.Kyber2.Group.mk_t params_zeta) (Seq.map MGroup.int16_to_t h.[|p1|]) (Seq.map MGroup.int16_to_t h.[|p2|])).[k]))
    (ensures fun h0 _ h1 -> live h1 p1 /\ live h1 p2 /\ live h1 output /\ Buf.disjoint p1 output /\ Buf.disjoint p2 output
                       /\ modifies1 output h0 h1 /\ (forall (k:nat{k<4*(v j+1)}). v h1.[|output|].[k] <= 2 * params_q /\ v h1.[|output|].[k] >= -2 * params_q /\ MGroup.int16_to_t h1.[|output|].[k] == (Lib.Poly.NTT2.lib_ntt_mul #Group.t #Spec.Kyber2.Ring.ring_t #params_n 7 (Spec.Kyber2.Group.mk_t params_zeta) (Seq.map MGroup.int16_to_t h1.[|p1|]) (Seq.map MGroup.int16_to_t h1.[|p2|])).[k]))

#reset-options "--z3rlimit 1000 --max_fuel 1 --max_ifuel 1 --print_universes"

let poly_mul_inner p1 p2 output j =
  let h0 = ST.get () in
  poly_mul_inner_odd p1 p2 output j;
  let h_0 = ST.get () in
  assert(4*(v j) +3 < params_n);
  assert(v h0.[|p1|].[4*(v j)] <= params_q);
  assert(v h0.[|p1|].[4*(v j)+1] <= params_q);
  assert(v h0.[|p1|].[4*(v j)+2] <= params_q);
  assert(v h0.[|p1|].[4*(v j)+3] <= params_q);
  assert (MGroup.int16_to_t h_0.[|output|].[4*(v j) + 1] == (Lib.Poly.NTT2.lib_ntt_mul #Group.t #Spec.Kyber2.Ring.ring_t #params_n 7 (Spec.Kyber2.Group.mk_t params_zeta) (Seq.map MGroup.int16_to_t h0.[|p1|]) (Seq.map MGroup.int16_to_t h0.[|p2|])).[4*(v j)+1]);
  assert (MGroup.int16_to_t h_0.[|output|].[4*(v j) + 3] == (Lib.Poly.NTT2.lib_ntt_mul #Group.t #Spec.Kyber2.Ring.ring_t #params_n 7 (Spec.Kyber2.Group.mk_t params_zeta) (Seq.map MGroup.int16_to_t h0.[|p1|]) (Seq.map MGroup.int16_to_t h0.[|p2|])).[4*(v j)+3]);
  let f1 = MGroup.mul_m_int16 p2.((size 4)*!j) p1.((size 4)*!j) in
  Spec.Kyber2.Ring.lemma_mul_swap_t (MGroup.int16_to_t h0.[|p2|].[4*(v j)]) (MGroup.int16_to_t h0.[|p1|].[4*(v j)]);
  assert(MGroup.to_t f1 == Group.mul_t (MGroup.int16_to_t h0.[|p1|].[4*(v j)]) (MGroup.int16_to_t h0.[|p2|].[4*(v j)]));
  let f5 = MGroup.mul_m_int16 p2.(((size 4)*!j)+!2ul) p1.(((size 4)*!j)+!2ul) in
  Spec.Kyber2.Ring.lemma_mul_swap_t (MGroup.int16_to_t h0.[|p2|].[4*(v j)+2]) (MGroup.int16_to_t h0.[|p1|].[4*(v j)+2]);
  assert(MGroup.to_t f5 == Group.mul_t (MGroup.int16_to_t h0.[|p1|].[4*(v j)+2]) (MGroup.int16_to_t h0.[|p2|].[4*(v j)+2]));
  assert_norm(params_n / 2 = 128 /\ params_n / 4 = pow2 6 /\ params_n / 2 = pow2 7);
  Buf.recall_contents zetas zetas_seq;
  assert_norm(params_n / 4 = pow2 6 /\ pow2 6 = 64);
  assert_norm(v j < pow2 6);
  assert_norm(pow2 7 = 128);
  FStar.Math.Lemmas.pow2_double_sum 6;
  let zeta = zetas.(j+!64ul) in
  FStar.Math.Lemmas.division_definition (2*(v j)) 2 (v j);
  FStar.Math.Lemmas.euclidean_division_definition (2*(v j)) 2;
  assert((2*(v j)) % 2 = 0);
  Lib.Arithmetic.Sums.br_lemma_n2_2 6 (2*(v j));
  FStar.Math.Lemmas.pow2_double_sum 6;
  FStar.Math.Lemmas.pow2_double_mult 6;
  assert(Lib.Arithmetic.Sums.br 7 (2*(v j)) < pow2 6);
  assert(Lib.Arithmetic.Sums.br 7 (2*(v j) + 1) == Lib.Arithmetic.Sums.br 7 (2*(v j)) + pow2 6);
  FStar.Math.Lemmas.distributivity_add_right 2 (Lib.Arithmetic.Sums.br 7 (2*(v j))) (pow2 6);
  FStar.Math.Lemmas.lemma_mult_le_left 2 (Lib.Arithmetic.Sums.br 7 (2*(v j))) (pow2 6 - 1);
  FStar.Math.Lemmas.modulo_lemma (2*(Lib.Arithmetic.Sums.br 7 (2*(v j)))) (pow2 7);
  Lib.Arithmetic.Sums.br_lemma_mul 7 (v j);
  Lib.Arithmetic.Sums.br_lemma_n2_1 6 (v j);
  assert(Lib.Arithmetic.Sums.br 7 (v j + 64) = 2*(Lib.Arithmetic.Sums.br 7 (2*(v j))) + 1);
  assert(Lib.Arithmetic.Sums.br 7 (v j + 64) + 128 = 2*(Lib.Arithmetic.Sums.br 7 (2*(v j) + 1)) + 1); admit()
  //let zeta = zetas.(j +! 64ul) in
  assert(MGroup.to_t zetas_seq.[v j + 64] == Lib.Arithmetic.Ring.exp #Group.t #Spec.Kyber2.Ring.ring_t (Spec.Kyber2.Group.mk_t params_zeta) (2*(Lib.Arithmetic.Sums.br 7 (2*(v j))) +1)); admit()
  Lib.Arithmetic.Ring.lemma_exp_morphism (Spec.Kyber2.Group.mk_t params_zeta) (Lib.Arithmetic.Sums.br 7 (v j + 64)) 128;
  Spec.Kyber2.NTT.exp_correspondancy (Spec.Kyber2.Group.mk_t params_zeta) 128;
  assert_norm (Lib.ModularArithmetic.modular_exp #params_q params_zeta 128 == (-1) % params_q);
  let f2 = MGroup.mul_m_int16 p1.(((size 4) *! j) +! 1ul) (MGroup.mul_m_int16 p2.(((size 4) *!j) +! 1ul) zeta) in
  Spec.Kyber2.Group.lemma_mul_assoc_t (MGroup.int16_to_t h0.[|p1|].[4*(v j)+1]) (MGroup.int16_to_t h0.[|p2|].[4*(v j)+1]) (MGroup.to_t zeta);
  assert(MGroup.int16_to_t f2 == Group.mul_t (Group.mul_t (MGroup.int16_to_t h0.[|p1|].[4*(v j)+1])  (MGroup.int16_to_t h0.[|p2|].[4*(v j)+1])) (MGroup.to_t zeta)); admit()
  (*assert(v f1 + v f2 <= 2 * params_q /\ v f1 + v f2 >= - 2 * params_q);
  assert_norm( 2 * params_q < pow2 15);
  assert(range (v f1 + v f2) S16);
  MGroup.plus_lemma_int16 f1 f2 (f1 +! f2);
  assert(MGroup.int16_to_t (f1+!f2) == Group.plus_t (MGroup.to_t f1) (MGroup.to_t f2));
  assert(MGroup.int16_to_t (f1+!f2) == Group.plus_t (Group.mul_t (MGroup.int16_to_t h0.[|p1|].[4*(v j)]) (MGroup.int16_to_t h0.[|p2|].[4*(v j)])) (Group.mul_t (Group.mul_t (MGroup.int16_to_t h0.[|p1|].[4*(v j)+1]) (MGroup.int16_to_t h0.[|p2|].[4*(v j)+1])) (MGroup.to_t zeta)));
  assert(MGroup.int16_to_t (f1+!f2) == Group.plus_t (Group.mul_t (MGroup.int16_to_t h0.[|p1|].[4*(v j)]) (MGroup.int16_to_t h0.[|p2|].[4*(v j)])) (Group.mul_t (Group.mul_t (MGroup.int16_to_t h0.[|p1|].[4*(v j)+1]) (MGroup.int16_to_t h0.[|p2|].[4*(v j)+1])) (Lib.Arithmetic.Ring.exp #Group.t #Spec.Kyber2.Ring.ring_t (Spec.Kyber2.Group.mk_t params_zeta) (2*(Lib.Arithmetic.Sums.br 7 (2*(v j))) +1))));
  FStar.Math.Lemmas.cancel_mul_div (2*(v j)) 2;
  FStar.Math.Lemmas.swap_mul (2*(v j)) 2;
  FStar.Math.Lemmas.paren_mul_right 2 2 (v j);
  assert(2 * (2* v j) == 4 * v j);
  assert((4*(v j)) / 2 == 2*(v j));
  assert(MGroup.int16_to_t (f1+!f2) == Group.plus_t (Group.mul_t (MGroup.int16_to_t h0.[|p1|].[4*(v j)]) (MGroup.int16_to_t h0.[|p2|].[4*(v j)])) (Group.mul_t (Group.mul_t (MGroup.int16_to_t h0.[|p1|].[4*(v j)+1]) (MGroup.int16_to_t h0.[|p2|].[4*(v j)+1])) (Lib.Arithmetic.Ring.exp #Group.t #Spec.Kyber2.Ring.ring_t (Spec.Kyber2.Group.mk_t params_zeta) (2*(Lib.Arithmetic.Sums.br 7 ((4*(v j))/2)) +1))));
  Lib.Poly.NTT2.lib_ntt_mul_even_lemma_instantiate 7 (Spec.Kyber2.Group.mk_t params_zeta) (Seq.map MGroup.int16_to_t h0.[|p1|]) (Seq.map MGroup.int16_to_t h0.[|p2|]) (Lib.Poly.NTT2.lib_ntt_mul #Group.t #Spec.Kyber2.Ring.ring_t #params_n 7 (Spec.Kyber2.Group.mk_t params_zeta) (Seq.map MGroup.int16_to_t h0.[|p1|]) (Seq.map MGroup.int16_to_t h0.[|p2|])) (4*(v j));
  assert(MGroup.int16_to_t (f1+!f2) == (Lib.Poly.NTT2.lib_ntt_mul #Group.t #Spec.Kyber2.Ring.ring_t #params_n 7 (Spec.Kyber2.Group.mk_t params_zeta) (Seq.map MGroup.int16_to_t h0.[|p1|]) (Seq.map MGroup.int16_to_t h0.[|p2|])).[4*(v j)]);
  output.(4ul*!j) <- f1 +! f2
