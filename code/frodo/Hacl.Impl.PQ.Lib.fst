module Hacl.Impl.PQ.Lib

open FStar.HyperStack.All
open Lib.IntTypes
open Lib.PQ.Buffer
open FStar.Mul

inline_for_extraction
type numeric_t = uint16

inline_for_extraction
let lbytes len = lbuffer uint8 (v len)

inline_for_extraction noextract
let v = size_v

inline_for_extraction
type matrix_t n1 n2 = lbuffer uint16 (v (n1 *. n2))

val matrix_create:
  n1:size_t -> n2:size_t ->
  StackInline (matrix_t n1 n2)
  (requires (fun h -> True))
  (ensures (fun h0 r h1 -> True))
  [@ "substitute"]
let matrix_create n1 n2 =
  create #uint16 (n1 *. n2) (u16 0)

val mget:
  #n1:size_t -> #n2:size_t ->
  a:matrix_t n1 n2 ->
  i:size_t{v i < v n1} -> j:size_t{v j < v n2} -> Stack uint16
  (requires (fun h -> True))
  (ensures (fun h0 r h1 -> True))
  [@ "substitute"]
let mget #n1 #n2 a i j =
  assume (v (i *. n2 +. j) < v (n1 *. n2));
  a.(i *. n2 +. j)

val mset:
  #n1:size_t -> #n2:size_t ->
  a:matrix_t n1 n2 ->
  i:size_t{v i < v n1} -> j:size_t{v j < v n2} ->
  vij:uint16 -> Stack unit
  (requires (fun h -> True))
  (ensures (fun h0 r h1 -> True))
  [@ "substitute"]
let mset #n1 #n2 a i j vij =
  assume (v (i *. n2 +. j) < v (n1 *. n2));
  a.(i *. n2 +. j) <- vij

//modifies a
val matrix_add:
  #n1:size_t -> #n2:size_t ->
  a:matrix_t n1 n2 -> b:matrix_t n1 n2 ->
  Stack unit
  (requires (fun h -> True))
  (ensures (fun h0 r h1 -> True))
  [@"c_inline"]
let matrix_add #n1 #n2 a b =
  admit();
  let h0 = FStar.HyperStack.ST.get () in
  loop_nospec #h0 n1 a
  (fun i ->
    loop_nospec #h0 n2 a
    (fun j ->
      let aij = mget a i j in
      let bij = mget b i j in
      let res = add_mod aij bij in
      mset a i j res
    )
  )

//modifies b
val matrix_sub:
  #n1:size_t -> #n2:size_t ->
  a:matrix_t n1 n2 -> b:matrix_t n1 n2 ->
  Stack unit
  (requires (fun h -> True))
  (ensures (fun h0 r h1 -> True))
  [@"c_inline"]
let matrix_sub #n1 #n2 a b =
  admit();
  let h0 = FStar.HyperStack.ST.get () in
  loop_nospec #h0 n1 a
  (fun i ->
    loop_nospec #h0 n2 a
    (fun j ->
      let aij = mget a i j in
      let bij = mget b i j in
      let res = sub_mod aij bij in
      mset b i j res
    )
  )

val matrix_mul:
  #n1:size_t -> #n2:size_t -> #n3:size_t ->
  a:matrix_t n1 n2 -> b:matrix_t n2 n3 ->
  c:matrix_t n1 n3 -> Stack unit
  (requires (fun h -> True))
  (ensures (fun h0 r h1 -> True))
  [@"c_inline"]
let matrix_mul #n1 #n2 #n3 a b c =
  admit();
  let h0 = FStar.HyperStack.ST.get () in
  loop_nospec #h0 n1 c
  (fun i ->
    loop_nospec #h0 n3 c
    (fun k ->
      mset c i k (u16 0);
      loop_nospec #h0 n2 c
      (fun j ->
	let aij = mget a i j in
	let bjk = mget b j k in
	let cik = mget c i k in
	let res = cik +. aij *. bjk in
	mset c i k res
      )
    )
  )
