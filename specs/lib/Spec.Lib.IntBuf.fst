module Spec.Lib.IntBuf

open FStar.HyperStack
open FStar.HyperStack.ST
open Spec.Lib.IntTypes
open Spec.Lib.IntSeq

module LSeq = Spec.Lib.IntSeq

unfold type lblock' (a:Type0) (len:size_t) = reference (lseq a len)
let lblock a len = lblock' a len

let same_block #a #b #l #l' x y = 
  let _ = () in
  (a == b /\ l == l' /\ x.id == y.id)
  
let lblock_as_lseq #a #l m b = sel m b

let live_lblock #a #l h b = contains h b

let disjoint_lblock #a #b #l #l' x y = 
  x.id =!= y.id

let creates_lblock1 #a #l b h0 h1 =
    let _ = () in
    ~ (contains h0 b) /\
    contains h1 b /\
    modifies (Set.singleton b.id) h0 h1 

let modifies_lblock1 #a #l b h0 h1 = 
    let _ = () in
    live_lblock h0 b /\
    live_lblock h1 b /\
    modifies (Set.singleton b.id) h0 h1 

let modifies_lblock2 #a #b #l #l' x y h0 h1 = 
    let _ = () in
    live_lblock h0 x /\
    live_lblock h1 x /\
    live_lblock h0 y /\
    live_lblock h1 y /\
    modifies (Set.union (Set.singleton x.id) (Set.singleton y.id)) h0 h1 

noeq type buffer' (a:Type) = 
| MkBuffer: #max_length:size_t -> content:lblock a max_length -> start:size_t -> length:size_t{start+length <= max_length} -> buffer' a

let buffer = buffer'

let max_length #a b = b.max_length

let start #a b = b.start

let length #a b = b.length

let content #a b = b.content

val modifies_2: #a:Type -> #b:Type -> b1:buffer a -> b2:buffer b{disjoint b1 b2} -> h0:mem -> h1:mem -> GTot Type0
let modifies_2 #a #b x y h0 h1 = 
    let _ = () in
    live h0 x /\
    live h1 x /\
    live h0 y /\
    live h1 y /\
    (
    let x0 = sel h0 x.content in
    let x1 = sel h1 x.content in
    let y0 = sel h0 y.content in
    let y1 = sel h1 y.content in
    (x.content.id =!= y.content.id /\
     modifies (Set.union (Set.singleton x.content.id) (Set.singleton y.content.id)) h0 h1 /\
     x1 == update_sub x0 x.start x.length (as_lseq h1 x) /\
     y1 == update_sub y0 y.start y.length (as_lseq h1 y)) \/
    (x.content.id == y.content.id /\
     x.max_length == y.max_length /\
     a == b /\
     modifies (Set.singleton x.content.id) h0 h1 /\
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


