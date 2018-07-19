module Hacl.Impl.Matrix

open FStar.HyperStack.ST
open FStar.UInt32
open FStar.Mul
open C.Loops

module B   = LowStar.Buffer
module HS  = FStar.HyperStack
module HST = FStar.HyperStack.ST
module U32 = FStar.UInt32
module M   = Spec.Matrix

type elem = UInt16.t

type uint32_t = U32.t

type lbuffer (a:Type0) (len:uint32_t) = 
  b:B.buffer a{~(B.g_is_null #a b) /\ B.len b == len}

type lmatrix (n1:uint32_t) (n2:uint32_t{0 < (v n1 * v n2) /\ (v n1 * v n2) < pow2 32}) = 
  b:lbuffer elem (n1 *^ n2)

let as_matrix #n1 #n2 h (m:lmatrix n1 n2) : GTot (M.matrix (v n1) (v n2)) =
  B.as_seq h m


open LowStar.BufferOps
open LowStar.Modifies
open LowStar.ModifiesPat

inline_for_extraction noextract
val lcreate: 
    n1:uint32_t 
  -> n2:uint32_t{0 < (v n1 * v n2) /\ (v n1 * v n2) < pow2 32 - 1} 
  -> StackInline (lmatrix n1 n2)
    (requires fun h0 -> True)
    (ensures  fun h0 a h1 -> 
      B.alloc_post_common (HS.get_tip h0) (v n1 * v n2) a h0 h1 /\
      as_matrix h1 a == M.mcreate (v n1) (v n2))
let lcreate n1 n2 = 
  B.alloca 0us (n1 *^ n2)

inline_for_extraction noextract
val mget:
    #n1:uint32_t
  -> #n2:uint32_t{0 < (v n1 * v n2) /\ (v n1 * v n2) < pow2 32 - 1} 
  -> a:lmatrix n1 n2
  -> i:uint32_t{i <^ n1}
  -> j:uint32_t{j <^ n2}
  -> StackInline elem
    (requires fun h0 -> B.live h0 a)
    (ensures  fun h0 x h1 -> 
      modifies loc_none h0 h1 /\
      x == M.mget (as_matrix h0 a) (v i) (v j))
let mget #n1 #n2 a i j =
  M.lemma_matrix_index (v n1) (v n2) (v i) (v j);
  a.(i *^ n2 +^ j)

inline_for_extraction noextract
val mset:
    #n1:uint32_t
  -> #n2:uint32_t{0 < (v n1 * v n2) /\ (v n1 * v n2) < pow2 32 - 1} 
  -> a:lmatrix n1 n2
  -> i:uint32_t{i <^ n1}
  -> j:uint32_t{j <^ n2}
  -> x:elem
  -> StackInline unit
    (requires fun h0 -> B.live h0 a)
    (ensures  fun h0 _ h1 -> 
      modifies (loc_buffer a) h0 h1 /\
      as_matrix h1 a == M.mset (as_matrix h0 a) (v i) (v j) x)
let mset #n1 #n2 a i j x =
  M.lemma_matrix_index (v n1) (v n2) (v i) (v j);
  a.(i *^ n2 +^ j) <- x

noextract unfold
let op_Array_Access #n1 #n2 (m:lmatrix n1 n2) (i,j) = mget m i j

noextract unfold
let op_Array_Assignment #n1 #n2 (m:lmatrix n1 n2) (i,j) x = mset m i j x

private
val inv:
    #n1:uint32_t 
  -> #n2:uint32_t{0 < (v n1 * v n2) /\ (v n1 * v n2) < pow2 32 - 1} 
  -> h0:HS.mem
  -> h1:HS.mem
  -> h2:HS.mem
  -> f:(elem -> elem -> Tot elem)
  -> a:lmatrix n1 n2
  -> b:lmatrix n1 n2
  -> c:lmatrix n1 n2 
  -> i:uint32_t{i <^ n1}
  -> j:nat
  -> Type0
let inv #n1 #n2 h0 h1 h2 f a b c i j =
  B.live h2 a /\ B.live h2 b /\ B.live h2 c /\ modifies (loc_buffer c) h0 h2 /\ j <= v n2 /\
  B.disjoint a c /\ B.disjoint b c /\ 
  (forall (i0:nat{i0 < v i}) (j:nat{j < v n2}).
    M.mget (as_matrix h2 c) i0 j == M.mget (as_matrix h1 c) i0 j) /\
  (forall (j0:nat{j0 < j}). 
    M.mget (as_matrix h2 c) (v i) j0 == 
    f (M.mget (as_matrix h0 a) (v i) j0) (M.mget (as_matrix h0 b) (v i) j0)) /\
  as_matrix h0 a == as_matrix h2 a /\ as_matrix h0 b == as_matrix h2 b

inline_for_extraction noextract private
val lmap2_inner:
    #n1:uint32_t 
  -> #n2:uint32_t{0 < (v n1 * v n2) /\ (v n1 * v n2) < pow2 32 - 1} 
  -> h0:HS.mem
  -> h1:HS.mem
  -> f:(elem -> elem -> Tot elem)
  -> a:lmatrix n1 n2
  -> b:lmatrix n1 n2
  -> c:lmatrix n1 n2 
  -> i:uint32_t{i <^ n1}
  -> j:uint32_t{v j < v n2}
  -> Stack unit
    (requires fun h2 -> inv h0 h1 h2 f a b c i (v j))
    (ensures  fun _ _ h2 -> inv h0 h1 h2 f a b c i (v j+1))
let lmap2_inner #n1 #n2 h0 h1 f a b c i j =
  let h0' = HST.get() in
  push_frame(); 
  c.(i,j) <- f a.(i,j) b.(i,j); 
  pop_frame();
  let h1' = HST.get() in
  assert (modifies (loc_buffer c) h0' h1')
  
inline_for_extraction
val lmap2:
    #n1:uint32_t 
  -> #n2:uint32_t{0 < (v n1 * v n2) /\ (v n1 * v n2) < pow2 32 - 1} 
  -> f:(elem -> elem -> elem)
  -> a:lmatrix n1 n2
  -> b:lmatrix n1 n2
  -> c:lmatrix n1 n2 
  -> StackInline unit
    (requires fun h0 -> B.live h0 a /\ B.live h0 b /\ B.live h0 c /\
      B.disjoint a c /\ B.disjoint b c)
    (ensures  fun h0 _ h1 -> 
      modifies (loc_buffer c) h0 h1 /\
      as_matrix h1 c == M.mmap2 #(v n1) #(v n2) f (as_matrix h0 a) (as_matrix h0 b) )
let lmap2 #n1 #n2 f a b c =
  let h0 = HST.get () in
  C.Loops.for 0ul n1
    (fun h1 i -> B.live h1 a /\ B.live h1 b /\ B.live h1 c /\ 
      B.disjoint a c /\ B.disjoint b c /\ modifies (loc_buffer c) h0 h1 /\ i <= v n1 /\
      (forall (i0:nat{i0 < i}) (j:nat{j < v n2}). 
        M.mget (as_matrix h1 c) i0 j == 
        f (M.mget (as_matrix h0 a) i0 j) (M.mget (as_matrix h0 b) i0 j)))
    (fun i -> 
      let h1 = HST.get() in
      C.Loops.for 0ul n2
        (fun h2 j -> inv #n1 #n2 h0 h1 h2 f a b c i j)
        U32.(fun j -> lmap2_inner #n1 #n2 h0 h1 f a b c i j)
    );
    let h2 = HST.get() in
    M.extensionality (as_matrix h2 c) 
      (M.mmap2 #(v n1) #(v n2) f (as_matrix h0 a) (as_matrix h0 b))

inline_for_extraction
let ladd #n1 #n2 a b c =
  lmap2 #n1 #n2 UInt16.add_mod a b c

val main: unit -> St unit
let main () =
  push_frame();
  let a = lcreate 2ul 2ul in
  let b = lcreate 2ul 2ul in
  let c = lcreate 2ul 2ul in
  ladd a b c;
  pop_frame()

