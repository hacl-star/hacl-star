module Hacl.Impl.PQ.Lib

open FStar.HyperStack.All
open Lib.IntTypes
open Lib.RawIntTypes
open Lib.Buffer
open Lib.ByteBuffer
open FStar.Mul
open FStar.Math.Lemmas

inline_for_extraction
type numeric_t = inttype

inline_for_extraction
let lbytes len = lbuffer uint8 len

inline_for_extraction
let v = size_v

inline_for_extraction
val numeric:
  #t:inttype -> x:nat{x <= maxint t} -> uint_t t
let numeric #t x =
  match t with
  | U8 -> u8 x
  | U16 -> u16 x
  | U32 -> u32 x
  | U64 -> u64 x
  | U128 -> u128 x
  | SIZE -> size x
  | NATm m -> modulo x m

inline_for_extraction
val to_numeric:
  #t:inttype -> t1:inttype -> x:uint_t t -> r:uint_t t1{uint_v r == uint_v x % modulus t1}
let to_numeric #t t1 x =
  match t, t1 with
  | U16, U16 -> x
  | U16, NATm m -> modulo ((Lib.RawIntTypes.uint_to_nat x) % m) m
  | NATm m, U16 -> u16 ((Lib.RawIntTypes.uint_to_nat x) % modulus U16)
  | _ -> admit()

inline_for_extraction
val matrix_t:
  t:numeric_t -> n1:size_t -> n2:size_t -> Type0
let matrix_t t n1 n2 = lbuffer (uint_t t) (v (n1 *. n2))

val matrix_create:
  t:numeric_t -> n1:size_t -> n2:size_t ->
  StackInline (matrix_t t n1 n2)
  (requires (fun h -> True))
  (ensures (fun h0 r h1 -> True))
  [@ "substitute"]
let matrix_create t n1 n2 =
  create (n1 *. n2) (numeric #t 0)

val mget:
  #t:numeric_t -> n1:size_t -> n2:size_t ->
  a:matrix_t t n1 n2 ->
  i:size_t{v i < v n1} -> j:size_t{v j < v n2} -> Stack (uint_t t)
  (requires (fun h -> live h a))
  (ensures (fun h0 r h1 -> True))
  [@ "substitute"]
let mget #t n1 n2 a i j =
  assume (v (i *. n2 +. j) < v (n1 *. n2));
  a.(i *. n2 +. j)

val mset:
  #t:numeric_t -> n1:size_t -> n2:size_t ->
  a:matrix_t t n1 n2 ->
  i:size_t{v i < v n1} -> j:size_t{v j < v n2} ->
  vij:uint_t t -> Stack unit
  (requires (fun h -> live h a))
  (ensures (fun h0 r h1 -> True))
  [@ "substitute"]
let mset #t n1 n2 a i j vij =
  assume (v (i *. n2 +. j) < v (n1 *. n2));
  a.(i *. n2 +. j) <- vij

//modifies a
val matrix_add:
  #t:numeric_t -> n1:size_t -> n2:size_t ->
  a:matrix_t t n1 n2 -> b:matrix_t t n1 n2 ->
  Stack unit
  (requires (fun h -> True))
  (ensures (fun h0 r h1 -> True))
  [@"c_inline"]
let matrix_add #t n1 n2 a b =
  admit();
  let h0 = FStar.HyperStack.ST.get () in
  loop_nospec #h0 n1 a
  (fun i ->
    loop_nospec #h0 n2 a
    (fun j ->
      let aij = mget n1 n2 a i j in
      let bij = mget n1 n2 b i j in
      let res = add_mod aij bij in
      mset n1 n2 a i j res
    )
  )

//modifies a
val matrix_sub:
  #t:numeric_t -> n1:size_t -> n2:size_t ->
  a:matrix_t t n1 n2 -> b:matrix_t t n1 n2 ->
  Stack unit
  (requires (fun h -> True))
  (ensures (fun h0 r h1 -> True))
  [@"c_inline"]
let matrix_sub #t n1 n2 a b =
  admit();
  let h0 = FStar.HyperStack.ST.get () in
  loop_nospec #h0 n1 a
  (fun i ->
    loop_nospec #h0 n2 a
    (fun j ->
      let aij = mget n1 n2 a i j in
      let bij = mget n1 n2 b i j in
      let res = sub_mod aij bij in
      mset n1 n2 a i j res
    )
  )

val matrix_mul:
  #t:numeric_t -> n1:size_t -> n2:size_t -> n3:size_t ->
  a:matrix_t t n1 n2 -> b:matrix_t t n2 n3 ->
  c:matrix_t t n1 n3 -> Stack unit
  (requires (fun h -> True))
  (ensures (fun h0 r h1 -> True))
  [@"c_inline"]
let matrix_mul #t n1 n2 n3 a b c =
  admit();
  let h0 = FStar.HyperStack.ST.get () in
  loop_nospec #h0 n1 c
  (fun i ->
    loop_nospec #h0 n3 c
    (fun k ->
      mset n1 n3 c i k (numeric #t 0);
      loop_nospec #h0 n2 c
      (fun j ->
	let aij = mget n1 n2 a i j in
	let bjk = mget n2 n3 b j k in
	let cik = mget n1 n3 c i k in
	let res = cik +. aij *. bjk in
	mset n1 n3 c i k res
      )
    )
  )
