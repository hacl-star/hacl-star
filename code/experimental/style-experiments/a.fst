module A
open Lib.IntTypes
module ST = FStar.HyperStack.ST
open FStar.HyperStack
open FStar.HyperStack.All
open LowStar.Buffer
open B

inline_for_extraction
val f: #v:t -> ST unit 
	     (requires (fun h -> True)) 
	     (ensures (fun h0 _ h1 -> True))
let f #v = 
  push_frame();
  let c = alloca (elem_zero v) 10ul  in
  pop_frame()

val g: unit -> ST unit 
	     (requires (fun h -> True)) 
	     (ensures (fun h0 _ h1 -> True))
let g () = 
    f #M64
