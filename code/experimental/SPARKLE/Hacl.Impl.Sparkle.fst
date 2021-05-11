module Hacl.Impl.Sparkle

open FStar.HyperStack.All
open FStar.HyperStack
module ST = FStar.HyperStack.ST

open Lib.IntTypes
open Lib.Buffer



#set-options " --z3rlimit 200"

val arx: uint32 -> branch1: lbuffer uint32 (size 2) -> Stack unit 
  (requires fun h -> live h branch1)
  (ensures fun h0 _ h1 -> modifies (loc branch1) h0 h1)
    
let arx c b = 
  let x, y = index b (size 0), index b (size 1) in 

  let x = x +. (y >>>. 31ul) in
  let y = y ^. (x >>>. 24ul) in
  let x = x ^. c in

  let x = x +. (y >>>. 17ul) in
  let y = y ^. (x >>>. 17ul) in
  let x = x ^. c in

  let x = x +. y in
  let y = y ^. (x >>>. 31ul) in
  let x = x ^. c in

  let x = x +. (y >>>. 24ul) in
  let y = y ^. (x >>>. 16ul) in
  let x = x ^. c in

  upd b (size 0) x;
  upd b (size 1) y
