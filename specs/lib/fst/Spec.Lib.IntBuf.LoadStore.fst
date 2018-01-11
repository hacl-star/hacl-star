module Spec.Lib.IntBuf.LoadStore

open FStar.HyperStack
open FStar.HyperStack.ST
module ST = FStar.HyperStack.ST
open Spec.Lib.IntTypes
open Spec.Lib.RawIntTypes
open Spec.Lib.IntSeq
open Spec.Lib.IntBuf

module LSeq = Spec.Lib.IntSeq

module Buf = FStar.Buffer
module U32 = FStar.UInt32 

let uints_from_bytes_le #t #len o i = admit()

inline_for_extraction
let uint32s_from_bytes_le #len clen o i = 
  let h0 = ST.get() in
  let inv (h1:mem) (j:nat) =  True in
  let f' (j:size_t{0 <= v j /\ v j <= len}) : Stack unit
      (requires (fun h -> inv h (v j)))
      (ensures (fun h1 _ h2 -> inv h2 (v j + 1))) = 
      let b32_i = sub #uint8 #(len `op_Multiply` 4) #len i (mul_mod #SIZE j (size 4)) (size 4) in
      let u32_i = Spec.Lib.Endian.uint32_from_bytes_le b32_i in
      o.(j) <- u32_i in
  Spec.Lib.Loops.for (size 0) clen inv f'

let uint32s_to_bytes_le #len o i = admit()

//let index #a #len b i = Buf.index b (U32.uint_to_t i)


(*

     x1 == update_sub (update_sub x0 x.start x.length (as_lseq h1 x)) y.start y.length (as_lseq h1 y)))


val create: #a:Type -> len:size_t -> init:a -> StackInline (lbuf a len)
		    (requires (fun _ -> True))
		    (ensures (fun h0 r h1 -> live h1 r /\ creates_1 #a r h0 h1))
let create #a len init =
  let s = salloc #(lseq a len) (create #a len init) in
  MkBuffer s 0 len

val createL: #a:Type -> l:list a {List.Tot.length l <= max_size_t} -> StackInline (lbuf a (List.Tot.length l))
		    (requires (fun _ -> True))
		    (ensures (fun h0 r h1 -> live h1 r /\ creates_1 r h0 h1))
let createL #a l = 
  let len : size_t = List.Tot.length l in
  let s = salloc #(lseq a len) (createL #a l) in
  MkBuffer s 0 len


val deref: #a:Type -> #len:size_t -> b:lbuf a len -> Stack (lseq a len) 
		     (requires (fun h -> live h b))
		     (ensures (fun h0 r h1 -> h0 == h1 /\ r == as_lseq h0 b))
let deref #a #len b = sub (!b.content) b.start b.length


val index: #a:Type -> #len:size_t{len > 0} -> b: lbuf a len -> n:size_t{n < len} -> Stack a
		     (requires (fun h -> live h b))
		     (ensures (fun h0 r h1 -> h0 == h1 /\ r == index #a #len (as_lseq #a h0 b) n))
let index #a #len b n = 
  let s = deref b in
  s.[n]
		     
val upd: #a:Type -> #len:size_t -> b:lbuf a len -> n:size_t{n < len /\ len > 0} -> x:a -> Stack unit 
		     (requires (fun h -> live h b))
		     (ensures (fun h0 _ h1 -> modifies_1 b h0 h1 /\
					   as_lseq h1 b == upd #a #len (as_lseq h0 b) n x))

let upd #a #len b n x = 
  let full = !b.content in
  let s = deref b in
  b.content := update_sub full b.start b.length (s.[n] <- x)
					   
			      
val sub: #a:Type -> #len:size_t -> b:lbuf a len -> start:size_t -> n:size_t{start + n <= len} -> b':lbuf a n{b'.max_length == b.max_length /\ b'.content == b.content /\ b'.start == b.start + start /\ b'.length == n}
let sub #a #len b s n = 
  MkBuffer b.content (b.start+s) n

val slice: #a:Type -> #len:size_t -> b:lbuf a len -> start:size_t{start < len} -> fin:size_t{start <= fin /\ fin <= len} -> b':lbuf a (fin - start){b'.max_length == b.max_length /\ b'.content == b.content /\ b'.start == b.start + start /\ b'.length == (fin - start)}
let slice #a #len b s f = 
  MkBuffer b.content (b.start + s) (f - s)


*)
