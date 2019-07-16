module Impl.Kyber2.NumericTypes

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


type num = Group.t
type poly = lbuffer num (size params_n)
type vec = lbuffer num ((size params_n)*!(size params_k))
type matrix = lbuffer num ((size params_n)*!(size params_k)*!(size params_k))

#reset-options "--z3rlimit 500 --max_fuel 2 --max_ifuel 2"

let to_spec_vec (h:mem) (v:vec) : Ghost (Spec.Kyber2.NumericTypes.vec) (requires live h v) (ensures fun v' -> forall (i:size_nat{i<params_k}). Spec.Kyber2.NumericTypes.index_vec v' i == h.[|gsub v (size i *! size params_n) (size params_n)|]) =
  let vec_aux (j:size_nat{j<=params_k}) : Type0 = v':Spec.Kyber2.NumericTypes.vec{forall (k:size_nat{k < j}). Spec.Kyber2.NumericTypes.index_vec v' k == h.[|gsub v (size k *! size params_n) (size params_n)|]} in
  let rec aux (j:size_nat{j<=params_k}) (acc:vec_aux j) : GTot (vec_aux params_k) (decreases (params_k - j))=
    if j = params_k then acc else begin
    let p = h.[|gsub v (size j *! size params_n) (size params_n)|] in
    aux (j+1) (Spec.Kyber2.NumericTypes.upd_vec acc j p) end
  in aux 0 (Spec.Kyber2.NumericTypes.new_vec ())

let to_spec_matrix (h:mem) (m:matrix) : Ghost (Spec.Kyber2.NumericTypes.matrix) (requires live h m) (ensures fun m' -> forall (i:size_nat{i<params_k}). Spec.Kyber2.NumericTypes.get_line m' i == to_spec_vec h (gsub m (size i *! size params_k *! size params_n) (size params_k *! size params_n))) =
  assert(live h m);
  let matrix_aux (j:size_nat{j<=params_k}) : Type0 = m':Spec.Kyber2.NumericTypes.matrix{forall (k:size_nat{k < j}). Spec.Kyber2.NumericTypes.get_line m' k == to_spec_vec h (gsub m (size k *! size params_k *! size params_n) (size params_k *! size params_n))} in
  let rec aux (j:size_nat{j<=params_k}) (acc:matrix_aux j) : Ghost (matrix_aux params_k) (requires live h m) (ensures fun _ -> live h m) (decreases (params_k - j))=
    if j = params_k then acc else begin
    live_sub m (size j *! size params_k *! size params_n) (size params_k *! size params_n) h;
    let v = to_spec_vec h (gsub m (size j *! size params_k *! size params_n) (size params_k *! size params_n)) in
    aux (j+1) (Spec.Kyber2.NumericTypes.upd_line acc j v) end
  in aux 0 (Spec.Kyber2.NumericTypes.new_matrix ())

#reset-options "--z3rlimit 500 --max_fuel 2 --max_ifuel 2"

let new_poly () : StackInline (poly) (requires fun h0 -> True) (ensures fun h0 p h1 -> live h1 p /\ stack_allocated p h0 h1 (Spec.Kyber2.NumericTypes.new_poly ())) =
  create (size params_n) (Group.zero_t)

let new_vec () : StackInline (vec) (requires fun h0 -> True) (ensures fun h0 v h1 -> live h1 v /\ to_spec_vec h1 v == Spec.Kyber2.NumericTypes.new_vec ()) =
  let v = create (size params_k *! size params_n) (Group.zero_t) in
  let h1 = ST.get() in
  let customprop (x:size_nat{x < params_k}) : GTot Type0 = (Spec.Kyber2.NumericTypes.index_vec (to_spec_vec h1 v) x == (Spec.Kyber2.NumericTypes.new_poly ())) in
  let customlemma (x:size_nat{x < params_k}) : Lemma (customprop x) =
    assert(Spec.Kyber2.NumericTypes.index_vec (to_spec_vec h1 v) x == h1.[|gsub v (size x *! size params_n) (size params_n)|]);
    as_seq_gsub h1 v (size x *! size params_n) (size params_n);
    Seq.eq_intro (h1.[|gsub v (size x *! size params_n) (size params_n)|]) (Spec.Kyber2.NumericTypes.new_poly ())
  in FStar.Classical.forall_intro customlemma;
  Spec.Kyber2.NumericTypes.eq_vec (to_spec_vec h1 v) (Spec.Kyber2.NumericTypes.new_vec ());
  v

#reset-options "--z3rlimit 500 --max_fuel 1 --max_ifuel 1"

let new_matrix () : StackInline (matrix) (requires fun h0 -> True) (ensures fun h0 m h1 -> live h1 m /\ (forall (x:size_t{v x <params_k}) (y:size_t{v y < params_k}). to_spec_matrix h1 m == (Spec.Kyber2.NumericTypes.new_matrix ()))) =
  let m = create (size params_k *! size params_k *! size params_n) (Group.zero_t) in
  let h1 = ST.get() in
  let b (x:size_nat{x < params_k}) : GTot Type0 = y:size_nat{y < params_k} in
  let customprop (x:size_nat{x < params_k}) (y:b x) : GTot Type0 = (Spec.Kyber2.NumericTypes.get_element (to_spec_matrix h1 m) x y == (Spec.Kyber2.NumericTypes.new_poly ())) in
  let customlemma (x:size_nat{x < params_k}) (y:b x) : Lemma (customprop x y) =
    as_seq_gsub h1 m (size x *! size params_k *! size params_n) (size params_k *! size params_n);
    as_seq_gsub h1 (gsub m (size x *! size params_k *! size params_n) (size params_k *! size params_n)) (size y *! size params_n) (size params_n);
    as_seq_gsub h1 m (((size x *!size params_k) +. size y) *! size params_n) (size params_n);
    Seq.eq_intro (h1.[|gsub (gsub m (size x *! size params_k *! size params_n) (size params_k *! size params_n)) (size y *! size params_n) (size params_n)|]) (h1.[|gsub m (((size x *!size params_k) +. size y) *! size params_n) (size params_n)|]);
    Seq.eq_intro (h1.[|gsub m (((size x *!size params_k) +. size y) *! size params_n) (size params_n)|]) (Spec.Kyber2.NumericTypes.new_poly ())
  in FStar.Classical.forall_intro_2 customlemma;
  Spec.Kyber2.NumericTypes.eq_matrix_element (to_spec_matrix h1 m) (Spec.Kyber2.NumericTypes.new_matrix ());
  m

#reset-options "--z3rlimit 1000 --max_fuel 2 --max_ifuel 2"

val get_index_vec:
  #len:size_t
  -> (v:vec)
  -> (buf:lbuffer Group.t len)
  -> (i:size_t{Lib.IntTypes.v i < params_k})
  -> Stack (poly)
    (requires fun h0 -> live h0 v /\ live h0 buf /\ Buf.disjoint v buf)
    (ensures fun h0 p h1 -> h0 == h1 /\ Buf.disjoint p buf /\ p == gsub v (i*!(size params_n)) (size params_n) /\ h1.[|p|] == Spec.Kyber2.NumericTypes.index_vec (to_spec_vec h0 v) (Lib.IntTypes.v i))


let get_index_vec #len v buf i =
  Buf.sub #_ #Group.t #(size params_k *! size params_n) v (i*!(size params_n)) (size params_n)

val copy_index_vec:
  (v:vec)
-> (output:poly)
-> (i:size_t{Lib.IntTypes.v i < params_k})
-> Stack unit
  (requires fun h0 -> live h0 v /\ live h0 output /\ Buf.disjoint v output)
  (ensures fun h0 _ h1 -> modifies1 output h0 h1 /\ h1.[|output|] == Spec.Kyber2.NumericTypes.index_vec (to_spec_vec h0 v) (Lib.IntTypes.v i))

let copy_index_vec v output i =
  Buf.copy output (get_index_vec v output i)

val get_line:
  (m:matrix)
  -> (i:size_t{v i < params_k})
  -> Stack (vec)
    (requires fun h0 -> live h0 m)
    (ensures fun h0 v' h1 -> h0 == h1 /\ v' == gsub m (i *! size params_k *! size params_n) (size params_k *! size params_n) /\ to_spec_vec h1 v' == Spec.Kyber2.NumericTypes.get_line (to_spec_matrix h0 m) (v i))

let get_line m i =
  Buf.sub #_ #Group.t #(size params_k *! size params_k *! size params_n) m (i *! size params_k *! size params_n) (size params_k *! size params_n)

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
    (ensures fun h0 p h1 -> h0 == h1 /\ p == gsub m (((i*!size params_k) +! j) *! (size params_n)) (size params_n) /\ h1.[|p|] == Spec.Kyber2.NumericTypes.get_element (to_spec_matrix h0 m) (v i) (v j))

let get_element m i j =
  let h = ST.get () in
  as_seq_gsub h m (i *! size params_k *! size params_n) (size params_k *! size params_n);
  as_seq_gsub h (gsub m (i *! size params_k *! size params_n) (size params_k *! size params_n)) (j *! size params_n) (size params_n);
  as_seq_gsub h m (((i *! size params_k) +! j) *! size params_n) (size params_n);
  eq_intro h.[|gsub (gsub m (i *! size params_k *! size params_n) (size params_k *! size params_n)) (j *! size params_n) (size params_n)|] h.[|gsub m (((i *! size params_k) +! j) *! size params_n) (size params_n)|];
  Buf.sub #_ #Group.t #(size params_k *! size params_k *! size params_n) m (((i*!size params_k) +! j) *! (size params_n)) (size params_n)

val copy_element:
  m:matrix
  -> output:poly
  -> i:size_t{v i < params_k}
  -> j:size_t{v j < params_k}
  -> Stack unit
    (requires fun h0 -> live h0 m /\ live h0 output /\ Buf.disjoint m output)
    (ensures fun h0 p h1 -> modifies1 output h0 h1 /\ h1.[|output|] == Spec.Kyber2.NumericTypes.get_element (to_spec_matrix h0 m) (v i) (v j))

let copy_element m output i j =
  Buf.copy output (get_element m i j)

val copy_column:
  (m:matrix)
  -> (output:vec)
  -> (j:size_t{v j < params_k})
  -> Stack unit
    (requires fun h0 -> live h0 m /\ live h0 output /\ Buf.disjoint m output)
    (ensures fun h0 _ h1 -> modifies1 output h0 h1 /\ live h1 output /\ to_spec_vec h1 output == Spec.Kyber2.NumericTypes.get_column (to_spec_matrix h0 m) (v j))

#reset-options "--z3rlimit 200 --max_fuel 2 --max_ifuel 2 --print_universes"

let copy_column m output j =
  let h0 = ST.get () in
  push_frame ();
  let i = create 1ul 0ul in
  let h' = ST.get () in
  Lib.Loops.while (fun h -> v h.[|i|].[0] <= params_k /\ live h output /\ live h m /\ live h i /\ Buf.disjoint m output /\ Buf.disjoint m i /\ Buf.disjoint output i /\ modifies2 output i h' h /\ (forall (x:size_nat{x< v #U32 #PUB h.[|i|].[0]}). Spec.Kyber2.NumericTypes.index_vec (to_spec_vec h output) x == Spec.Kyber2.NumericTypes.index_vec (Spec.Kyber2.NumericTypes.get_column (to_spec_matrix h0 m) (v j)) x))
    (fun h -> v h.[|i|].[0] < params_k)
    (fun () -> i.(0ul) <. size params_k)
    (fun () -> let k = i.(0ul) in assert(v k<params_k);
       let p = get_index_vec output m k in
       assert(p == gsub output (k*!size params_n) (size params_n));
       copy_element m (get_index_vec output m k) k j;
       assert_norm(params_k < maxint U32); i.(0ul) <- k +! 1ul;
       let h = ST.get () in
       assert (h.[|p|] == Spec.Kyber2.NumericTypes.get_element (to_spec_matrix h0 m) (v k) (v j));
       (let v':Spec.Kyber2.NumericTypes.vec = (Spec.Kyber2.NumericTypes.get_column (to_spec_matrix h0 m) (v j)) in
       assert(h.[|p|] == Spec.Kyber2.NumericTypes.index_vec v' (v k));
       let output':Spec.Kyber2.NumericTypes.vec = (to_spec_vec h output) in
       assert(Spec.Kyber2.NumericTypes.index_vec output' (v k) == h.[|p|]))
       );
  pop_frame ();
  let h1 = ST.get () in
  Spec.Kyber2.NumericTypes.eq_vec (to_spec_vec h1 output) (Spec.Kyber2.NumericTypes.get_column (to_spec_matrix h0 m) (v j))
