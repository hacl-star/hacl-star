module Hacl.Impl.Sparkle

open FStar.HyperStack.All
open FStar.HyperStack
module ST = FStar.HyperStack.ST

open Lib.IntTypes
open Lib.ByteBuffer
open Lib.Buffer

open Spec.SPARKLE2

#set-options " --z3rlimit 200"

inline_for_extraction
let size_word: size_t = 4ul

inline_for_extraction
let vsize_rcon: size_t = 8ul


let rcon: x: glbuffer uint32 vsize_rcon 
  {witnessed #uint32 #vsize_rcon x (Lib.Sequence.of_list rcon_list) /\ recallable x} =
  createL_global rcon_list


type branch_len =  n: size_t {v n = 1 \/ v n = 2 \/ v n = 3 \/ v n = 4 \/ v n = 6 \/ v n = 8}

inline_for_extraction
type branch branch_len = lbuffer uint32 (2ul *! branch_len)


val arx: uint32 -> b: branch 1ul -> Stack unit 
  (requires fun h -> live h b)
  (ensures fun h0 _ h1 -> True)
    
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


inline_for_extraction noextract
val l1: x:uint32 -> Tot uint32
let l1 x = (x <<<. size 16)  ^. (x &. (u32 0xffff))


inline_for_extraction noextract
val getBranch: #l: branch_len -> b: branch l -> i: size_t {v i <= v l / 2} -> 
  Stack (tuple2 uint32 uint32)
  (requires fun h -> live h b)
  (ensures fun h0 _ h1 -> modifies0 h0 h1)

let getBranch #l b i =  Lib.Buffer.index b (2ul *! i), Lib.Buffer.index b (2ul *! i +! 1ul)


inline_for_extraction noextract 
val setBranch: #n: branch_len -> i: size_t {v i <= v n / 2} -> branch1 -> b: branch n -> 
  Stack unit 
  (requires fun h -> live h b)
  (ensures fun h0 _ h1 -> modifies (loc b) h0 h1)  

let setBranch #n i (x, y) b =
  upd #uint32 b (2ul *. i) x;
  upd #uint32 b (2ul *. i +. 1ul) y


inline_for_extraction noextract
val xor_step: #l: branch_len -> b: branch l
  -> tx: lbuffer uint32 (size 1) 
  -> ty: lbuffer uint32 (size 1) 
   -> i: size_t {v i <= v l / 2} ->
  Stack unit
    (requires fun h -> live h b /\ live h tx /\ live h ty /\ disjoint tx ty)
    (ensures fun h0 _ h1 -> modifies (loc tx |+| loc ty) h0 h1)

let xor_step #l b tx ty i = 
  let xi, yi = getBranch b i in 
  let tx_0 = index tx (size 0) in 
  let ty_0 = index ty (size 0) in 
  upd tx (size 0) (xi ^. tx_0);
  upd ty (size 0) (yi ^. ty_0)
  

val xor: #l: branch_len -> b: branch l-> tx: lbuffer uint32 (size 1) -> ty: lbuffer uint32 (size 1) ->  
  Stack unit
    (requires fun h -> live h b /\ live h ty /\ live h tx /\ disjoint tx ty)
    (ensures fun h0 _ h1 -> modifies (loc tx |+| loc ty) h0 h1)

let xor #l b tx ty = 
  let h0 = ST.get() in 
  Lib.Loops.for 0ul (l >>. 1ul) 
    (fun h i -> live h b /\ live h ty /\ live h tx /\ disjoint tx ty /\ modifies (loc tx |+| loc ty) h0 h) 
    (fun (i: size_t {v i <= v l / 2}) -> xor_step b tx ty i)
    

inline_for_extraction noextract
val xor_x_step: #l: branch_len -> b: branch l -> lty: uint32 -> ltx: uint32 -> i: size_t {v i <= v l / 2} -> 
  Stack unit 
    (requires fun h -> live h b)
    (ensures fun h0 _ h1 -> modifies (loc b) h0 h1)

let xor_x_step #l b lty ltx i = 
  let xi, yi = getBranch #l b i in 
  let xi_n = xi ^. lty in
  let yi_n = yi ^. ltx in
  setBranch i (xi_n, yi_n) b


val xor_x: #l: branch_len -> b: branch l -> lty: uint32 -> ltx: uint32 -> Stack unit 
  (requires fun h -> live h b)
  (ensures fun h0 _ h1 -> modifies (loc b) h0 h1)
  
let xor_x #l b lty ltx = 
  let h0 = ST.get() in 
  Lib.Loops.for (0ul) (l >>. 1ul)  
    (fun h i -> live h b /\ modifies (loc b) h0 h) 
    (fun (i: size_t {v i <= v l / 2}) -> xor_x_step b lty ltx i)


val m: #l: branch_len -> b: branch l -> Stack unit 
  (requires fun h -> live h b)
  (ensures fun h0 _ h1 -> modifies (loc b) h0 h1)

let m #n b = 
  push_frame();
    let tx = create (size 1) (u32 0) in 
    let ty = create (size 1) (u32 0) in 
    
    xor #n b tx ty;
    let ltx = l1 (index tx (size 0)) in
    let lty = l1 (index ty (size 0)) in 
    xor_x #n b lty ltx;
  pop_frame()


val l_step: #n: branch_len -> perm: branch n -> i: size_t {v i <= v n / 2} -> (rightBranch : branch n) -> Stack unit 
  (requires fun h -> live h perm /\ live h rightBranch)
  (ensures fun h0 _ h1 -> modifies (loc rightBranch) h0 h1)

let l_step #n perm i rightBranch = 
  let xi, yi = getBranch rightBranch i in 
  let p0i, p1i = getBranch perm i in 
  let branchIUpd = xi ^. p0i, yi ^. p1i in
  
  let index = rotate_right n 1ul in 
  
  assume (v index  <= v n / 2);
  
  setBranch #n index branchIUpd rightBranch


val l: #n: branch_len {v n % 2 == 0} -> b: branch n -> Stack unit 
  (requires fun h -> live h b)
  (ensures fun h0 _ h1 -> modifies (loc b) h0 h1)

let l #n b = 
  let leftBranch = sub b (size 0) n in 
  let rightBranch = sub b n n in 

  let index : branch_len = (n >>. 1ul) in 
  let perm = m #index leftBranch in 

 (* assume (v (n >>. 1ul) == v n /  *)
  Lib.Loops.for 0ul (n >>. 1ul) 
  (fun h i -> live h b)
  (fun (i: size_t {v i <= v n / 2}) -> l_step #(n >>. 1ul) rightBranch i perm)



val add2: #n: branch_len {v n >= 4} -> i: size_t -> b:branch n -> Stack unit 
  (requires fun h -> live h b) 
  (ensures fun h0 _ h1 -> modifies (loc b) h0 h1)

let add2 #n i b = 

  recall_contents rcon (Lib.Sequence.of_list rcon_list); 

  let (x0, y0) = getBranch #n b (size 0) in 
  let (x1, y1) = getBranch #n b (size 1) in 

  let i0 = logand i (size 7) in 
    logand_mask i (size 7) 3; 
  let y0 = y0 ^. index rcon i0 in
  let y1 = y1 ^. (to_u32 i) in
 
  setBranch (size 0) (x0, y0) b;
  setBranch #n (size 1) (x1, y1) b


val toBranch: #n: branch_len -> i: lbuffer uint8 (size 8 *! n) -> o: branch n -> 
  Stack unit 
  (requires fun h -> True)
  (ensures fun h0 _ h1 -> True)

let toBranch #n i o = 
  uints_from_bytes_le o i 


val fromBranch: #n: branch_len -> i: branch n -> o: lbuffer uint8 (size 8 *! n) -> 
  Stack unit 
  (requires fun h -> True)
  (ensures fun h0 _ h1 -> True)

let fromBranch #n i o = 
  uints_to_bytes_le (n *! 2ul) o i


val arx_n_step: #n: branch_len -> i: size_t {v i < v n / 2} -> b: branch n -> 
  Stack unit 
  (requires fun h -> live h b)
  (ensures fun h0 _ h1 -> True)

let arx_n_step #n i b = 
  let branchI = sub b (size 2 *! i) (size 2) in 
    recall_contents rcon (Lib.Sequence.of_list rcon_list); 
  let rcon_i = index rcon i in 
  arx rcon_i branchI


val arx_n: #n: branch_len -> branch n -> 
  Stack unit 
  (requires fun h -> True)
  (ensures fun h0 _ h1 -> True)

let arx_n #n b =
  Lib.Loops.for 0ul n
  (fun h i -> live h b)
  (fun (i: size_t {v i < v n / 2}) -> arx_n_step i b)


val mainLoop_step: #n: branch_len {v n >= 4 /\ v n % 2 == 0 } ->  i: size_t -> branch n ->
  Stack unit 
  (requires fun h -> True)
  (ensures fun h0 _ h1 -> True)


let mainLoop_step #n i b = 
  add2 i b;
  arx_n #n b;
  l #n b


val mainLoop: #n: branch_len {n >= 2 /\ n % 2 == 0} -> b: branch n -> steps: size_t -> 
  Stack unit 
  (requires fun h -> True)
  (ensures fun h0 _ h1 -> True)

let mainLoop #n b steps = 
  Lib.Loops.for 0ul steps
  (fun h i -> live h b)
  (fun (i: size_t {v i < v n / 2}) -> mainLoop_step i b)


val sparkle256: steps: size_t -> i: lbuffer (uint8) (size 32) -> o: lbuffer (uint8) (size 32) ->
  Stack unit 
  (requires fun h -> True)
  (ensures fun h0 _ h1 -> True)

let sparkle256 steps i o =
  push_frame();
    let temp = create (size 4) (u32 0) in 
    toBranch #4 i temp;
    mainLoop #4 temp steps;
    fromBranch #4 steps o; 
  pop_frame()
