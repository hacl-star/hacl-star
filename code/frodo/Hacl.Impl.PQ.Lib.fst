module Hacl.Impl.PQ.Lib

open FStar.HyperStack.All
open Lib.IntTypes
open Lib.RawIntTypes
open Lib.Buffer
open Lib.ByteBuffer
open FStar.Mul
open FStar.Math.Lemmas

inline_for_extraction
type numeric_t = uint16

inline_for_extraction
let lbytes len = lbuffer uint8 len

inline_for_extraction
noextract
let v = size_v

inline_for_extraction
val matrix_t: n1:size_t -> n2:size_t -> Type0
let matrix_t n1 n2 = lbuffer uint16 (v (n1 *. n2))

val matrix_create:
  n1:size_t -> n2:size_t ->
  StackInline (matrix_t n1 n2)
  (requires (fun h -> True))
  (ensures (fun h0 r h1 -> live h1 r))
  [@ "substitute"]
let matrix_create n1 n2 =
  create #uint16 (n1 *. n2) (u16 0)

val mget:
  #n1:size_t -> #n2:size_t ->
  a:matrix_t n1 n2 ->
  i:size_t{v i < v n1} -> j:size_t{v j < v n2} -> Stack uint16
  (requires (fun h -> live h a))
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
  (requires (fun h -> live h a))
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

//modifies a
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
      mset a i j res
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


val main: unit -> St unit
let main _ =
  push_frame();
  let m1 = matrix_create (size 2) (size 2) in
  let m2 = matrix_create (size 2) (size 2) in
  admit();
  mset m1 (size 0) (size 0) (u16 0);
  mset m1 (size 0) (size 1) (u16 1);
  mset m1 (size 1) (size 0) (u16 2);
  mset m1 (size 1) (size 1) (u16 3);
  mset m2 (size 0) (size 0) (u16 0);
  mset m2 (size 0) (size 1) (u16 1);
  mset m2 (size 1) (size 0) (u16 2);
  mset m2 (size 1) (size 1) (u16 3);
  matrix_add m1 m2;
  pop_frame()
