module Lib.NumericVector

open FStar.Mul
open Lib.IntTypes
open FStar.Math.Lemmas

/// Numeric types

(** A numeric type is either an inttype (a machine integer or a group of integers modulo m)
  * or a vector type
  *)
type numeric_t =
  | Int  : inttype -> numeric_t
  | Vect : numeric_t -> size_nat -> numeric_t

/// Vectors over numeric types

(*
 * Some staging needed to mutually define the interpretation of numeric types
 * and the (homogeneous) vector type.
 *
 * This allows for vectors whose elements are themselves vectors, which is useful
 * to define matrices and higher-dimensional arrays
 *)
noeq
type vector_ (#a:Type0) (t:a -> Type0) : a -> size_nat -> Type0 =
  | VNil  : #x:a -> vector_ t x 0
  | VCons : #n:size_nat{n < max_size_t} -> #x:a -> t x -> vector_ t x n -> vector_ t x (n + 1)

irreducible
val seal: #a:Type -> x:a -> a
let seal #a x = x

(** Interpretation of numeric types *)
val uint_t: numeric_t -> Type0
let rec uint_t t =
  match t with
  | Int t    -> Lib.IntTypes.uint_t t
  | Vect a n ->
    vector_ uint_t a n

type vector_t (a:numeric_t) (n:size_nat) = vector_ uint_t a n

(*
Example
val v : vector_t (Vect (Int U8) 1) 2
let v = VCons (VCons (u8 1) VNil) (VCons (VCons (u8 2) VNil) VNil)
*)

val length: #a:numeric_t -> #n:size_nat -> v:vector_t a n -> size_nat
let length #a #n v = n

val hd: #a:numeric_t -> #n:size_pos -> v:vector_t a n -> uint_t a
let hd #a #n (VCons x _) = x

val tl: #a:numeric_t -> #n:size_pos -> v:vector_t a n -> vector_t a (n - 1)
let tl #a #n (VCons _ v) = v

val index: #a:numeric_t -> #n:size_nat -> v:vector_t a n -> i:size_nat{i < n} -> uint_t a
let rec index #a #n v = function
  | 0 -> hd v
  | i -> index (tl v) (i - 1)

abstract
type equal (#a:numeric_t) (#len:size_nat) (v1:vector_t a len) (v2:vector_t a len) =
  forall (i:size_nat{i < len}).{:pattern (index v1 i); (index v2 i)} index v1 i == index v2 i

val eq_intro: #a:numeric_t -> #len:size_nat -> v1:vector_t a len -> v2:vector_t a len -> Lemma
  (requires forall (i:size_nat{i < len}). index v1 i == index v2 i)
  (ensures  equal v1 v2)
let eq_intro #a #len v1 v2 = ()

private
val extensionality_: #a:numeric_t -> #len:size_nat -> v1:vector_t a len -> v2:vector_t a len ->
  p:((i:size_nat{i < len}) -> squash (index v1 i == index v2 i)) -> Lemma (v1 == v2)
let rec extensionality_ #a #len v1 v2 p =
  match v1 with
  | VCons x1 v1' ->
    begin
    match v2 with
    | VCons x2 v2' -> p 0; extensionality_ v1' v2' (fun i -> p (i + 1))
    | _ -> ()
    end
  | _ -> ()

val eq_elim: #a:numeric_t -> #len:size_nat -> v1:vector_t a len -> v2:vector_t a len -> Lemma
  (requires equal v1 v2)
  (ensures  v1 == v2)
  [SMTPat (equal v1 v2)]
let eq_elim #a #len v1 v2 = extensionality_ #a #len v1 v2 (fun i -> ())

val create: #a:numeric_t -> n:size_nat -> init:uint_t a -> Pure (vector_t a n)
  (requires True)
  (ensures (fun v -> forall (i:size_nat).{:pattern index v i}  i < n ==> index v i == init))
let rec create #a n init =
  match n with
  | 0 -> VNil
  | n -> let v = create (n - 1) init in VCons init v

val upd: #a:numeric_t -> #len:size_pos -> v:vector_t a len -> n:size_nat{n < len} -> x:uint_t a
  -> Pure (vector_t a len)
    (requires True)
    (ensures (fun v' ->
      index v' n == x /\
      (forall (i:size_nat). {:pattern (index v' i)} (i < len /\ i <> n) ==> index v' i == index v i)))
let rec upd #a #len v i x =
  match i with
  | 0 -> VCons x (tl v)
  | n -> VCons (hd v) (upd (tl v) (i - 1) x)

val index_tl: #a:numeric_t -> #n:size_pos -> v:vector_t a n ->
  Lemma (forall (i:size_pos{i < n}). index v i == index (tl v) (i - 1))
let index_tl #a #n v = ()

val map2: #a:numeric_t -> #b:numeric_t -> #c:numeric_t -> #len:size_nat ->
  f:(uint_t a -> uint_t b -> uint_t c) -> v1:vector_t a len -> v2:vector_t b len ->
  Pure (vector_t c len)
  (requires True)
  (ensures  fun v -> forall (i:size_nat{i < len}). index v i == f (index v1 i) (index v2 i))
let rec map2 #a #b #c #len f v1 v2 =
  match v1 with
  | VNil -> VNil
  | VCons x v1' ->
    let VCons y v2' = v2 in
    index_tl v1;
    index_tl v2;
    VCons (f x y) (map2 f v1' v2')

val add: #t:numeric_t -> a:uint_t t -> b:uint_t t -> c:uint_t t
let rec add #t a b =
  match t with
  | Int t    -> add_mod #t a b
  | Vect t' n ->
    assume (uint_t (Vect t' n) == vector_ uint_t t' n);
    map2 #t' #t' #t' #n add a b

let (+.) #t = add #t

val vector_add:#t:numeric_t -> #n:size_nat -> a:vector_t t n -> b:vector_t t n
  -> Pure (vector_t t n)
  (requires True)
  (ensures  fun c -> forall (i:size_nat{i < n}). index c i == index a i +. index b i)
let vector_add #t #n a b =
  map2 #t #t #t #n add a b


(** An m-by-n matrix (m rows, n columns) *)
type matrix_t (a:numeric_t) (m:size_pos) (n:size_pos) =
  vector_t (Vect a m) n
