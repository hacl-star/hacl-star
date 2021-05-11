module Hacl.Impl.Sparkle

open FStar.HyperStack.All
open FStar.HyperStack
module ST = FStar.HyperStack.ST

open Lib.IntTypes
open Lib.Buffer

#set-options " --z3rlimit 200"

type branch_len =  n: size_t {v n = 1 \/ v n = 2 \/ v n = 3 \/ v n = 4 \/ v n = 6 \/ v n = 8}

type branch branch_len = lbuffer uint32 (2ul *! branch_len)


val arx: uint32 -> branch1: branch 1ul -> Stack unit 
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


val l1: x:uint32 -> Tot uint32
let l1 x = (x <<<. size 16)  ^. (x &. (u32 0xffff))


inline_for_extraction noextract
val getBranchI: #l: branch_len -> b: branch l -> i: size_t {v i < v l / 2} -> 
  Stack (tuple2 uint32 uint32)
  (requires fun h -> live h b)
  (ensures fun h0 _ h1 -> modifies0 h0 h1)

let getBranchI #l b i =  Lib.Buffer.index b i, Lib.Buffer.index b (i +! 1ul)


inline_for_extraction noextract
val xor_step: #l: branch_len -> b: branch l
  -> tx: lbuffer uint32 (size 1) 
  -> ty: lbuffer uint32 (size 1) 
   -> i: size_t {v i < v l / 2} ->
  Stack unit
    (requires fun h -> live h b /\ live h tx /\ live h ty /\ disjoint tx ty)
    (ensures fun h0 _ h1 -> modifies (loc tx |+| loc ty) h0 h1)

let xor_step #l b tx ty i = 
  let xi, yi = getBranchI b i in 
  let tx_0 = index tx (size 0) in 
  let ty_0 = index ty (size 0) in 
  upd tx (size 0) (xi ^. tx_0);
  upd tx (size 0) (yi ^. ty_0)


val xor: #l: branch_len {v l % 2 == 0} -> b: branch l -> Stack (tuple2 uint32 uint32)
    (requires fun h -> live h b)
    (ensures fun h0 _ h1 -> modifies0 h0 h1)

let xor #l b = 
  push_frame();
    let h0 = ST.get() in 
    let tx = create (size 1) (u32 0) in 
    let tu = create (size 1) (u32 0) in  
  Lib.Loops.for 0ul (l >>. 1ul) 
    (fun h i ->live h b /\ live h tu /\ live h tx /\ disjoint tx tu /\ modifies (loc tx |+| loc tu) h0 h) 
    (fun (i: size_t {v i < v l / 2}) -> 
      let h = ST.get() in 
      xor_step b tx tu i);

  let u = index #MUT #_ #1ul tx (size 0) in 
  let v = index #MUT #_ #1ul tu (size 0) in 
  pop_frame(); 
  (u, v)
    
