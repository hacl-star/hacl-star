module Lib.NumericVector

open FStar.Mul
open FStar.Math.Lemmas
open Lib.IntTypes

/// Numeric types

(** A numeric type is either an inttype (a machine integer or a group of integers modulo m)
  * or a vector type.
  *)
type numeric_t =
  | Int : inttype -> numeric_t
  | Vec : numeric_t -> size_nat -> numeric_t

val dimension: numeric_t -> nat
let rec dimension = function
  | Vec t _ -> 1 + dimension t
  | _ -> 0

let numeric (m:nat) = t:numeric_t{dimension t == m}

/// Vectors over numeric types

(*
 * Some staging needed to mutually define the interpretation of numeric types
 * and the (homogeneous) vector type. The type is parameterized by the dimension
 * m and the interpretation of numeric types
 *
 * This allows for vectors whose elements are themselves vectors, which is useful
 * to define matrices and higher-dimensional arrays
 *)
noeq
type vector_ (m:nat) (t:numeric m -> Type0) : numeric m -> size_nat -> Type0 =
  | VNil  : #x:numeric m -> vector_ m t x 0
  | VCons :
    #n:size_nat{n < max_size_t} -> #x:numeric m -> t x -> vector_ m t x n -> vector_ m t x (n + 1)

(** Interpretation of numeric types *)
val uint_t: #m:nat -> a:numeric m -> Tot Type0 (decreases (dimension a))
let rec uint_t #m = function
  | Int t    -> Lib.IntTypes.uint_t t PUB
  | Vec a' n -> vector_ (m - 1) uint_t a' n

let vector_t #m t n = vector_ m uint_t t n

#set-options "--print_implicits"

/// Example
private
val v : uint_t #2 (Vec (Vec (Int U8) 1) 2)
let v = VCons (VCons 1uy VNil) (VCons (VCons 2uy VNil) VNil)

let size_pos = n:size_nat{0 < n}

val length: #m:nat -> #a:numeric m -> #n:size_nat -> v:vector_t a n -> size_nat
let length #m #a #n v = n

val hd: #m:nat -> #a:numeric m -> #n:size_pos -> v:vector_t a n -> uint_t a
let hd #m #a #n (VCons x _) = x

val tl: #m:nat -> #a:numeric m -> #n:size_pos -> v:vector_t a n -> vector_t a (n - 1)
let tl #m #a #n (VCons _ v) = v

val index: #m:nat -> #a:numeric m -> #n:size_nat -> v:vector_t a n -> i:size_nat{i < n} -> uint_t a
let rec index #m #a #n v = function
  | 0 -> hd v
  | i -> index (tl v) (i - 1)

let op_String_Access (#m:nat) (#a:numeric m) (#n:size_nat) (v:vector_t a n) i = index v i

abstract
type equal (#m:nat) (#a:numeric m) (#len:size_nat) (v1:vector_t a len) (v2:vector_t a len) =
  forall (i:size_nat{i < len}).{:pattern v1.[i]; v2.[i]} v1.[i] == v2.[i]

val eq_intro: #m:nat -> #a:numeric m -> #len:size_nat
  -> v1:vector_t a len
  -> v2:vector_t a len
  -> Lemma
    (requires forall (i:size_nat{i < len}). v1.[i] == v2.[i])
    (ensures  equal v1 v2)
let eq_intro #m #a #len v1 v2 = ()

private
val extensionality_: #m:nat -> #a:numeric m -> #len:size_nat
  -> v1:vector_t a len -> v2:vector_t a len ->
  p:((i:size_nat{i < len}) -> squash (v1.[i] == v2.[i])) -> Lemma (v1 == v2)
let rec extensionality_ #m #a #len v1 v2 p =
  match v1 with
  | VCons x1 v1' ->
    begin
    match v2 with
    | VCons x2 v2' -> p 0; extensionality_ v1' v2' (fun i -> p (i + 1))
    | _ -> ()
    end
  | _ -> ()

val eq_elim: #m:nat -> #a:numeric m -> #len:size_nat
  -> v1:vector_t a len
  -> v2:vector_t a len
  -> Lemma
    (requires equal v1 v2)
    (ensures  v1 == v2)
    [SMTPat (equal v1 v2)]
let eq_elim #m #a #len v1 v2 = extensionality_ v1 v2 (fun i -> ())

val create: #m:nat -> #a:numeric m -> n:size_nat -> init:uint_t a -> Pure (vector_t a n)
  (requires True)
  (ensures  fun v -> forall i.{:pattern (index v i)} v.[i] == init)
let rec create #m #a n init =
  match n with
  | 0 -> VNil
  | n -> let v = create (n - 1) init in VCons init v

val upd: #m:nat -> #a:numeric m -> #len:size_pos
  -> v:vector_t a len -> i:size_nat{i < len} -> x:uint_t a
  -> Pure (vector_t a len)
    (requires True)
    (ensures (fun v' ->
      v'.[i] == x /\
      (forall (j:size_nat). {:pattern (index v' j)} (j < len /\ j <> i) ==> v'.[j] == v.[j])))
let rec upd #m #a #len v i x =
  match i with
  | 0 -> VCons x (tl v)
  | n -> VCons (hd v) (upd (tl v) (i - 1) x)

let op_String_Assignment (#m:nat) (#a:numeric m) (#n:size_nat) (v:vector_t a n) i x = upd v i x

val index_tl: #m:nat -> #a:numeric m -> #n:size_pos -> v:vector_t a n ->
  Lemma (forall (i:size_pos{i < n}). v.[i] == (tl v).[i - 1])
let index_tl #m #a #n v = ()

val map2: #m:nat -> #len:size_nat -> #a:numeric m -> #b:numeric m -> #c:numeric m
  -> f:(uint_t a -> uint_t b -> uint_t c)
  -> v1:vector_t a len
  -> v2:vector_t b len ->
  Pure (vector_t c len)
    (requires True)
    (ensures  fun v -> forall i.{:pattern (index v i)} v.[i] == f (v1.[i]) (v2.[i]))
let rec map2 #m #len #a #b #c f v1 v2 =
  match v1 with
  | VNil -> VNil
  | VCons x v1' ->
    let VCons y v2' = v2 in
    index_tl v1;
    index_tl v2;
    VCons (f x y) (map2 f v1' v2')

val add: #m:nat -> #t:numeric m -> x:uint_t t -> y:uint_t t -> Tot (uint_t t) (decreases (dimension t))
let rec add #m #t x y =
  match t with
  | Int t    -> IntTypes.add_mod #t #PUB x y
  | Vec t' n ->
    let x: uint_t (Vec t' n) = x in
    let y: uint_t (Vec t' n) = y in
    let z: uint_t (Vec t' n) = map2 add x y in
    z

let ( +. ) #m #t = add #m #t

val sub: #m:nat -> #t:numeric m -> x:uint_t t -> y:uint_t t -> Tot (uint_t t) (decreases (dimension t))
let rec sub #m #t x y =
  match t with
  | Int t    -> IntTypes.sub_mod #t #PUB x y
  | Vec t' n ->
    let x: uint_t (Vec t' n) = x in
    let y: uint_t (Vec t' n) = y in
    let z: uint_t (Vec t' n) = map2 sub x y in
    z

let ( -. ) #m #t = sub #m #t

val mul: #m:nat -> #t:numeric m -> x:uint_t t -> y:uint_t t -> Tot (uint_t t) (decreases (dimension t))
let rec mul #m #t x y =
  match t with
  | Int t    -> IntTypes.sub_mod #t #PUB x y
  | Vec t' n ->
    let x: uint_t (Vec t' n) = x in
    let y: uint_t (Vec t' n) = y in
    let z: uint_t (Vec t' n) = map2 mul x y in
    z

let ( *. ) #m #t = mul #m #t

private
val vector_add: #m:nat -> #t:numeric m -> #n:size_nat -> a:vector_t t n -> b:vector_t t n
  -> Pure (vector_t t n)
  (requires True)
  (ensures  fun c -> forall (i:size_nat{i < n}). index c i == index a i +. index b i)
let vector_add #m #t #n a b = add #(m + 1) #(Vec t n) a b


/// Matrices

noeq
type matrix (a:numeric 0) =
  | M: rows:size_nat -> cols:size_nat -> m:uint_t #2 (Vec (Vec a rows) cols) -> matrix a

let rows (m:matrix 'a) = M?.rows m

let cols (m:matrix 'a) = M?.cols m

let get (m:matrix 'a) i j = ((M?.m m).[j]).[i]

let set (m:matrix 'a) (i:size_nat{i < rows m}) (j:size_nat{j < cols m}) x =
  let M rows cols m = m in
  M rows cols (m.[j] <- ((m.[j]).[i] <- x))

let op_Array_Access (#t:numeric 0) (m:matrix t) (i,j) = get m i j

let op_Array_Assignment (#t:numeric 0) (m:matrix t) (i,j) x = set m i j x

/// Example
///  [ 0   2 ]
///  [ 1   3 ]
let m:matrix (Int U16) =
  M 2 2 (
  VCons
      (VCons 0us (VCons 1us VNil))
    (VCons
      (VCons 2us (VCons 3us VNil))
      VNil))

let _ = assert_norm (m.(0,0) == 0us /\ m.(1,0) == 1us /\ m.(0,1) == 2us /\ m.(1,1) == 3us)
let _ = assert_norm (let m' = m.(0,0) <- 4us in m'.(0,0) == 4us)

val set_def1 (#a:numeric 0) (m:matrix a) (i:_) (j:_) (v:_) :
  Lemma (rows (set m i j v) == rows m)
let set_def1 #a m i j v = ()

val set_def2 (#a:numeric 0) (m:matrix a) (i:_) (j:_) (v:_) :
  Lemma (cols (set m i j v) == cols m)
let set_def2 #a m i j v = ()

val set_def3 (#a:numeric 0) (m:matrix a) (i:size_nat{i < rows m}) (j:size_nat{j < cols m}) (v:_) :
  Lemma (get (set m i j v) i j == v)
let set_def3 #a m i j v = ()

val set_def4 (#a:numeric 0) (m:matrix a) (i:size_nat{i < rows m}) (j:size_nat{j < cols m}) (v:_) :
  Lemma (forall i' j'. (i <> i' \/ j <> j') ==> get (set m i j v) i' j' == get m i' j')
let set_def4 #a m i j v = ()

(*
val matrix_create: #a:numeric 0 -> r:size_nat -> c:size_nat
  -> f:(i:size_nat{i < r} -> j:size_nat{j < c} -> uint_t a) -> matrix a
let rec matrix_create #a r c f =
  match r with
  | 0 -> M 0 c VNil
  create #0 #a c

val create_get:
    forall f: int -> int -> 'a, i j: int.
    0 <= i < r -> 0 <= j < c -> get (create f) i j = f i j

let t = Int U16

assume val sum:
  a:size_nat -> b:size_nat{a <= b} -> f:(i:size_nat{a <= i /\ i < b} -> uint_t #0 t) -> uint_t #0 t

assume val sum_def1: a:size_nat -> b:size_nat{a == b} ->
  (f:(i:size_nat{a <= i /\ i < b} -> uint_t #0 t)) -> Lemma (b <= a ==> sum a b f == u16 0)

let mul_atom #m #n (a b:matrix_t t m n) i j =
  fun k -> a.(i,k) *. b.(k,j)

let matrix_product #m #n (p a b:matrix_t t m n) =
 forall i j. 0 <= i <= m /\ 0 <= j < n ==> sum 0 n (mul_atom a b i j)
*)
