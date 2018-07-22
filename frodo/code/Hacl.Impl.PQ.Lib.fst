module Hacl.Impl.PQ.Lib

open FStar.HyperStack.ST
open FStar.Mul

open LowStar.BufferOps
open LowStar.Modifies
open LowStar.ModifiesPat

open Lib.IntTypes
open Lib.PQ.Buffer

module B   = LowStar.Buffer
module HS  = FStar.HyperStack
module ST  = FStar.HyperStack.ST
module Seq = Lib.Sequence
module M   = Spec.Matrix

#reset-options "--z3rlimit 50 --max_fuel 0 --max_ifuel 0"

type elem = uint16

inline_for_extraction
let lbytes len = lbuffer uint8 (v len)

inline_for_extraction noextract
let v = size_v

type matrix_t (n1:size_t) (n2:size_t{v n1 * v n2 < max_size_t}) =
  lbuffer elem (v n1 * v n2)

/// It's important to mark it as [unfold] for triggering patterns in [LowStar]
unfold
let as_matrix #n1 #n2 h (m:matrix_t n1 n2) : GTot (M.matrix (v n1) (v n2)) =
  B.as_seq h m

inline_for_extraction noextract
val matrix_create:
    n1:size_t
  -> n2:size_t{0 < v n1 * v n2 /\ v n1 * v n2 < max_size_t}
  -> StackInline (matrix_t n1 n2)
    (requires fun h0 -> True)
    (ensures  fun h0 a h1 ->
      B.alloc_post_common (HS.get_tip h0) (v n1 * v n2) a h0 h1 /\
      as_matrix h1 a == M.create (v n1) (v n2))
let matrix_create n1 n2 =
  create (n1 *. n2) (u16 0)

inline_for_extraction noextract
val mget:
    #n1:size_t
  -> #n2:size_t{v n1 * v n2 < max_size_t}
  -> a:matrix_t n1 n2
  -> i:size_t{v i < v n1}
  -> j:size_t{v j < v n2}
  -> Stack elem
    (requires fun h0 -> B.live h0 a)
    (ensures  fun h0 x h1 ->
      modifies loc_none h0 h1 /\
      x == M.mget (as_matrix h0 a) (v i) (v j))
let mget #n1 #n2 a i j =
  M.index_lt (v n1) (v n2) (v i) (v j);
  a.(i *. n2 +. j)

inline_for_extraction noextract
val mset:
    #n1:size_t
  -> #n2:size_t{v n1 * v n2 < max_size_t}
  -> a:matrix_t n1 n2
  -> i:size_t{v i < v n1}
  -> j:size_t{v j < v n2}
  -> x:elem
  -> Stack unit
    (requires fun h0 -> B.live h0 a)
    (ensures  fun h0 _ h1 ->
      modifies (loc_buffer a) h0 h1 /\
      B.live h1 a /\
      as_matrix h1 a == M.mset (as_matrix h0 a) (v i) (v j) x)
let mset #n1 #n2 a i j x =
  M.index_lt (v n1) (v n2) (v i) (v j);
  a.(i *. n2 +. j) <- x

noextract unfold
let op_String_Access #n1 #n2 (m:matrix_t n1 n2) (i, j) = mget m i j

noextract unfold
let op_String_Assignment #n1 #n2 (m:matrix_t n1 n2) (i, j) x = mset m i j x

unfold
let get #n1 #n2 h (m:matrix_t n1 n2) i j = M.mget (as_matrix h m) i j

private unfold
val map2_inner_inv:
    #n1:size_t
  -> #n2:size_t{v n1 * v n2 < max_size_t}
  -> h0:HS.mem
  -> h1:HS.mem
  -> h2:HS.mem
  -> f:(elem -> elem -> elem)
  -> a:matrix_t n1 n2
  -> b:matrix_t n1 n2
  -> c:matrix_t n1 n2
  -> i:size_t{v i < v n1}
  -> j:size_nat
  -> Type0
let map2_inner_inv #n1 #n2 h0 h1 h2 f a b c i j =
  B.live h2 a /\ B.live h2 b /\ B.live h2 c /\
  B.disjoint b c /\
  a == c /\
  modifies (loc_buffer c) h1 h2 /\
  j <= v n2 /\
  (forall (i0:nat{i0 < v i}) (j:nat{j < v n2}). get h2 c i0 j == get h1 c i0 j) /\
  (forall (j0:nat{j0 < j}). get h2 c (v i) j0 == f (get h0 a (v i) j0) (get h2 b (v i) j0)) /\
  (forall (j0:nat{j <= j0 /\ j0 < v n2}). get h2 c (v i) j0 == get h0 c (v i) j0) /\
  (forall (i0:nat{v i < i0 /\ i0 < v n1}) (j:nat{j < v n2}). get h2 c i0 j == get h0 c i0 j) /\

  (forall (i0:nat{i0 < v i}) (j:nat{j < v n2}). get h2 a i0 j == get h1 a i0 j) /\
  (forall (j0:nat{j <= j0 /\ j0 < v n2}). get h2 a (v i) j0 == get h0 a (v i) j0) /\
  (forall (i0:nat{v i < i0 /\ i0 < v n1}) (j:nat{j < v n2}). get h2 a i0 j == get h0 a i0 j)

inline_for_extraction noextract private
val map2_inner:
    #n1:size_t
  -> #n2:size_t{v n1 * v n2 < max_size_t}
  -> h0:HS.mem
  -> h1:HS.mem
  -> f:(elem -> elem -> elem)
  -> a:matrix_t n1 n2
  -> b:matrix_t n1 n2
  -> c:matrix_t n1 n2
  -> i:size_t{v i < v n1}
  -> j:size_t{v j < v n2}
  -> Stack unit
    (requires fun h2 -> map2_inner_inv h0 h1 h2 f a b c i (v j))
    (ensures  fun _ _ h2 -> map2_inner_inv h0 h1 h2 f a b c i (v j + 1))
let map2_inner #n1 #n2 h0 h1 f a b c i j =
  c.[i,j] <- f a.[i,j] b.[i,j]

inline_for_extraction
val map2:
    #n1:size_t
  -> #n2:size_t{v n1 * v n2 < max_size_t}
  -> f:(uint16 -> uint16 -> uint16)
  -> a:matrix_t n1 n2
  -> b:matrix_t n1 n2
  -> c:matrix_t n1 n2
  -> Stack unit
    (requires fun h0 -> B.live h0 a /\ B.live h0 b /\ B.live h0 c /\
      a == c /\ B.disjoint b c)
    (ensures  fun h0 _ h1 ->
      modifies (loc_buffer c) h0 h1 /\
      as_matrix h1 c == M.map2 #(v n1) #(v n2) f (as_matrix h0 a) (as_matrix h0 b) )
let map2 #n1 #n2 f a b c =
  let h0 = ST.get () in
  Lib.Loops.for (size 0) n1
    (fun h1 i -> B.live h1 a /\ B.live h1 b /\ B.live h1 c /\
      modifies (loc_buffer c) h0 h1 /\ i <= v n1 /\
      (forall (i0:nat{i0 < i}) (j:nat{j < v n2}).
        get h1 c i0 j == f (get h0 a i0 j) (get h0 b i0 j)) /\
      (forall (i0:nat{i <= i0 /\ i0 < v n1}) (j:nat{j < v n2}).
        get h1 c i0 j == get h0 c i0 j) )
    (fun i ->
      let h1 = ST.get() in
      Lib.Loops.for (size 0) n2
        (fun h2 j -> map2_inner_inv h0 h1 h2 f a b c i j)
        (fun j -> map2_inner h0 h1 f a b c i j)
    );
    let h2 = ST.get() in
    M.extensionality (as_matrix h2 c) (M.map2 f (as_matrix h0 a) (as_matrix h0 b))

inline_for_extraction
val matrix_add:
    #n1:size_t
  -> #n2:size_t{v n1 * v n2 < max_size_t}
  -> a:matrix_t n1 n2
  -> b:matrix_t n1 n2
  -> Stack unit
    (requires fun h -> B.live h a /\ B.live h b /\ B.disjoint a b)
    (ensures  fun h0 r h1 -> B.live h1 a /\ modifies (loc_buffer a) h0 h1 /\
      as_matrix h1 a == M.add (as_matrix h0 a) (as_matrix h0 b))
[@"c_inline"]
let matrix_add #n1 #n2 a b =
  map2 #n1 #n2 add_mod a b a

val matrix_sub:
   #n1:size_t
  -> #n2:size_t{v n1 * v n2 < max_size_t}
  -> a:matrix_t n1 n2
  -> b:matrix_t n1 n2
  -> Stack unit
    (requires fun h -> B.live h a /\ B.live h b /\ B.disjoint a b)
    (ensures  fun h0 r h1 -> B.live h1 b /\ modifies (loc_buffer b) h0 h1 /\
      as_matrix h1 b == M.sub (as_matrix h0 a) (as_matrix h0 b))
[@"c_inline"]
let matrix_sub #n1 #n2 a b =
  admit(); //TODO: Need another version of [map2] or to weaken its precondition
  map2 #n1 #n2 sub_mod a b b

(*
val sum:n:size_nat -> f:(j:size_nat{j < n} -> uint16) -> uint16
let sum n f = repeati n (fun j res -> res +. f j) (u16 0)

val matrix_mul:
  #n1:size_nat ->
  #n2:size_nat{n1 * n2 < max_size_t} ->
  #n3:size_nat{n1 * n3 < max_size_t /\ n2 * n3 < max_size_t} ->
  a:matrix_t n1 n2 ->
  b:matrix_t n2 n3 ->
  Tot (c:matrix_t n1 n3{ forall i k. c.(i, k) == sum n2 (fun j -> a.(i, j) *. b.(j, k))})
let matrix_mul #n1 #n2 #n3 a b =
  let c = matrix_create n1 n3 in
  repeati_inductive n1
  (fun i c -> forall (i1:size_nat{i1 < i}) (k:size_nat{k < n3}). c.(i1, k) == sum n2 (fun j -> a.(i1, j) *. b.(j, k)))
  (fun i c ->
    repeati_inductive n3
    (fun k c0 -> (forall (k1:size_nat{k1 < k}). c0.(i, k1) == sum n2 (fun j -> a.(i, j) *. b.(j, k1))) /\
               (forall (i1:size_nat{i1 < n1 /\ i <> i1}) (k:size_nat{k < n3}). c0.(i1, k) == c.(i1, k)))
    (fun k c0 ->
      c0.(i, k) <- sum n2 (fun j -> a.(i, j) *. b.(j, k))
    ) c
  ) c
*)

(*
val sum:
  n:size_t ->
  f:(j:size_nat{j < v n} -> uint16) ->
  Stack uint16
   (requires (fun h -> True))
   (ensures (fun h0 r h1 -> modifies loc_none h0 h1 /\ r == M.sum (v n) f))
let sum n f =
  push_frame();
  let res:lbuffer uint16 1 = create (size 1) (u16 0) in
  let h0 = ST.get() in
  Lib.Loops.for (size 0) n
  (fun h j -> B.live h res /\ modifies (loc_buffer res) h0 h)
  (fun j ->
    let res0 = res.(size 0) in
    res.(size 0) <- res0 +. f (v j));
  let res = res.(size 0) in
  pop_frame();
  res
*)

inline_for_extraction noextract private
val mul_inner:
  #n1:size_t ->
  #n2:size_t{v n1 * v n2 < max_size_t} ->
  #n3:size_t{v n2 * v n3 < max_size_t /\ v n1 * v n3 < max_size_t} ->
  a:matrix_t n1 n2 ->
  b:matrix_t n2 n3 ->
  c:matrix_t n1 n3 ->
  i:size_t{v i < v n1} ->
  k:size_t{v k < v n3} ->
  Stack unit
    (requires (fun h ->
      B.live h a /\ B.live h b /\ B.live h c /\ B.disjoint a c /\ B.disjoint b c))
    (ensures (fun h0 _ h1 -> B.live h1 c /\ modifies (loc_buffer c) h0 h1))
let mul_inner #n1 #n2 #n3 a b c i k =
  mset c i k (u16 0);
  let h0 = ST.get() in
  Lib.Loops.for (size 0) n2
  (fun h1 j ->
    B.live h1 a /\ B.live h1 b /\ B.live h1 c /\ B.disjoint a c /\ B.disjoint b c /\
    modifies (loc_buffer c) h0 h1)
  (fun j ->
    let abij = a.[i, j] *. b.[j, k] in
    let cik = c.[i, k] in
    c.[i, k] <- cik +. abij
  )

val matrix_mul:
  #n1:size_t ->
  #n2:size_t{v n1 * v n2 < max_size_t} ->
  #n3:size_t{v n2 * v n3 < max_size_t /\ v n1 * v n3 < max_size_t} ->
  a:matrix_t n1 n2 ->
  b:matrix_t n2 n3 ->
  c:matrix_t n1 n3 ->
  Stack unit
    (requires (fun h -> B.live h a /\ B.live h b /\
      B.live h c /\ B.disjoint a c /\ B.disjoint b c))
    (ensures (fun h0 _ h1 -> B.live h1 c /\ modifies (loc_buffer c) h0 h1))
[@"c_inline"]
let matrix_mul #n1 #n2 #n3 a b c =
  let h0 = ST.get () in
  loop_nospec #h0 n1 c
  (fun i ->
    let h1 = ST.get () in
    loop_nospec #h1 n3 c
    (fun k ->
      mul_inner #n1 #n2 #n3 a b c i k
    )
  )
