module Hacl.Impl.SHA2_256

open FStar.Mul
open FStar.HyperStack
open FStar.HyperStack.ST

open Lib.IntTypes
open Lib.Buffer
open Lib.ByteBuffer
open Lib.LoopCombinators

module ST = FStar.HyperStack.ST
module Seq = Lib.Sequence
module Loops = Lib.LoopCombinators
module Spec = Spec.SHA2


///
/// SHA-256
///

#set-options "--z3rlimit 50"


type word_t = Spec.word_t Spec.SHA2_256
type limb_t = Spec.limb_t Spec.SHA2_256

type block_wp = lbuffer word_t (size Spec.size_block_w)
type hash_wp  = lbuffer word_t (size Spec.size_hash_w)
type ws_wp    = lbuffer word_t (size (Spec.size_kTable Spec.SHA2.SHA2_256))

type block_p  = lbuffer uint8 (size (Spec.size_block Spec.SHA2_256))



let const_kTable: x:ilbuffer uint32 64ul{witnessed x (Spec.SHA2.kTable Spec.SHA2.SHA2_256) /\ recallable x} =
  createL_global Spec.kTable_list_224_256

let const_h0Table: x:ilbuffer uint32 8ul{witnessed x (Spec.SHA2.h0Table Spec.SHA2.SHA2_256) /\ recallable x} =
  createL_global Spec.h0Table_list_256

let const_opTable: x:ilbuffer (rotval U32) 12ul{witnessed x (Spec.SHA2.opTable Spec.SHA2.SHA2_256) /\ recallable x} =
  createL_global Spec.opTable_list_224_256


val get_kTable:
  s:size_t{size_v s < Spec.size_kTable Spec.SHA2_256} ->
  Stack uint32
    (requires (fun h -> True))
    (ensures  (fun h0 z h1 -> h0 == h1 /\
      uint_v z == uint_v (Seq.index (Spec.kTable Spec.SHA2_256) (size_v s))))

[@ Substitute ]
let get_kTable s =
  recall_contents const_kTable (Spec.kTable Spec.SHA2_256);
  index const_kTable s

val set_h0Table:
  buf: lbuffer word_t (size Spec.size_hash_w) ->
  Stack unit
    (requires (fun h -> live h buf))
    (ensures  (fun h0 z h1 -> modifies1 buf h0 h1
                         /\ h1.[buf] == Spec.h0Table Spec.SHA2_256))

[@ Substitute ]
let set_h0Table s =
  recall_contents const_h0Table (Spec.h0Table Spec.SHA2_256);
  assume(disjoint s const_h0Table);
  copy s const_h0Table


val get_opTable:
  s:size_t{size_v s < Spec.size_opTable} ->
  Stack size_t
    (requires (fun h -> True))
    (ensures  (fun h0 z h1 -> h0 == h1 /\
      uint_v z == uint_v (Seq.index (Spec.opTable Spec.SHA2_256) (size_v s))))

[@ Substitute ]
let get_opTable s =
  recall_contents const_opTable (Spec.opTable Spec.SHA2_256);
  index const_opTable s



val _Ch: x: uint32 -> y: uint32 -> z: uint32 ->
  Tot (r: uint32{r == Spec._Ch Spec.SHA2_256 x y z})

let _Ch x y z = ((x &. y) ^. ((~. x) &. z))


val _Maj: x: uint32 -> y: uint32 -> z: uint32 ->
  Tot (r: uint32{r == Spec._Maj Spec.SHA2_256 x y z})

let _Maj x y z = (x &. y) ^. ((x &. z) ^. (y &. z))


val _Sigma0: x:uint32 ->
  Stack uint32
  (requires (fun h -> True))
  (ensures  (fun h0 r h1 -> modifies0 h0 h1 /\ r == Spec._Sigma0 Spec.SHA2_256 x))

let _Sigma0 x = (x >>>. (get_opTable 0ul)) ^. ((x >>>. get_opTable 1ul) ^. (x >>>. get_opTable 2ul))

val _Sigma1: x:uint32 ->
  Stack uint32
  (requires (fun h -> True))
  (ensures  (fun h0 r h1 -> modifies0 h0 h1 /\ r == Spec._Sigma1 Spec.SHA2_256 x))

let _Sigma1 x = (x >>>. get_opTable 3ul) ^. ((x >>>. get_opTable 4ul) ^. (x >>>. get_opTable 5ul))

val _sigma0: x:uint32 ->
  Stack uint32
  (requires (fun h -> True))
  (ensures  (fun h0 r h1 -> modifies0 h0 h1 /\ r == Spec._sigma0 Spec.SHA2_256 x))

let _sigma0 x =
  let n = get_opTable 3ul in
  (x >>>. get_opTable 6ul) ^. ((x >>>. get_opTable 7ul) ^. (x >>. n))

val _sigma1: x: uint32 ->
  Stack uint32
  (requires (fun h -> True))
  (ensures  (fun h0 r h1 -> modifies0 h0 h1 /\ r == Spec._sigma1 Spec.SHA2_256 x))

let _sigma1 x =
  let n = get_opTable 11ul in
  (x >>>. get_opTable 9ul) ^. ((x >>>. get_opTable 10ul) ^. (x >>. n))

val step_ws0:
    s: ws_wp
  -> b: block_wp
  -> i: size_t{v i < 16} ->
  Stack unit
  (requires (fun h -> live h b /\ live h s /\ disjoint b s))
  (ensures  (fun h0 _ h1 -> modifies1 s h0 h1
                       /\ h1.[s] == Spec.step_ws0 Spec.SHA2_256 h0.[b] (v i) h0.[s]))

let step_ws0 s b i = s.(i) <- b.(i)


#reset-options "--z3rlimit 50"

val step_ws1:
    s: ws_wp
  -> i: size_t{16 <= v i /\ v i < Spec.size_kTable Spec.SHA2_256} ->
  Stack unit
  (requires (fun h -> live h s))
  (ensures  (fun h0 _ h1 -> modifies1 s h0 h1
                       /\ h1.[s] == Spec.step_ws1 Spec.SHA2_256 (v i) h0.[s]))

let step_ws1 s i =
  let t16 = s.(i -. 16ul) in
  let t15 = s.(i -. 15ul) in
  let t7  = s.(i -. 7ul) in
  let t2  = s.(i -. 2ul) in
  let s1 = _sigma1 t2 in
  let s0 = _sigma0 t15 in
  s.(i) <- s1 +. (t7 +. (s0 +. t16))


val loop_ws0: s:ws_wp -> b:block_wp ->
  Stack unit
  (requires (fun h -> live h s /\ live h b /\ disjoint s b))
  (ensures  (fun h0 _ h1 -> modifies1 s h0 h1))
                       (* /\ h1.[s] == Spec.loop_ws0 Spec.SHA2_256 h0.[b] h0.[s])) *)
let loop_ws0 s b =
  let h0 = ST.get () in
  loop_nospec #h0 (size 16) s
  (fun i -> step_ws0 s b i)


val loop_ws1: s: ws_wp ->
  Stack unit
  (requires (fun h -> live h s))
  (ensures  (fun h0 _ h1 -> modifies1 s h0 h1))
                       (* /\ h1.[s] == Spec.loop_ws1 Spec.SHA2_256 h0.[s])) *)
let loop_ws1 s =
  let h0 = ST.get () in
  loop_nospec #h0 (size (Spec.size_kTable Spec.SHA2_256) -. (size 16)) s
  (fun i -> step_ws1 s (i +. size 16))


val ws:
    s: ws_wp
  -> b: block_wp ->
  Stack unit
  (requires (fun h -> live h s /\ live h b /\ disjoint s b))
  (ensures  (fun h0 _ h1 -> modifies1 s h0 h1))

let ws s b =
  loop_ws0 s b;
  loop_ws1 s


val shuffle_core:
    s: hash_wp
  -> wsTable: ws_wp
  -> t: size_t{v t < Spec.size_kTable Spec.SHA2_256} ->
  Stack unit
  (requires (fun h -> live h s /\ live h wsTable /\ disjoint s wsTable))
  (ensures  (fun h0 _ h1 -> modifies1 s h0 h1))
                       (* /\ h1.[s] == Spec.shuffle_core Spec.SHA2_256 h0.[wsTable] (v t) h0.[s])) *)

let shuffle_core hash wsTable i =
  let a0 = hash.(0ul) in
  let b0 = hash.(1ul) in
  let c0 = hash.(2ul) in
  let d0 = hash.(3ul) in
  let e0 = hash.(4ul) in
  let f0 = hash.(5ul) in
  let g0 = hash.(6ul) in
  let h0 = hash.(7ul) in

  let ws_i: uint32 = wsTable.(i) in
  let k_i: uint32 = get_kTable i in
  let r =  k_i +. ws_i in
  let s0 = _Sigma0 a0 in
  let s1 = _Sigma1 e0 in
  let t1 = h0 +. s1 +. ((_Ch e0 f0 g0) +. r) in
  let t2 = s0 +. (_Maj a0 b0 c0) in

  hash.(0ul) <- (t1 +. t2);
  hash.(1ul) <- a0;
  hash.(2ul) <- b0;
  hash.(3ul) <- c0;
  hash.(4ul) <- (d0 +. t1);
  hash.(5ul) <- e0;
  hash.(6ul) <- f0;
  hash.(7ul) <- g0


val shuffle: hash:hash_wp -> wsTable: ws_wp ->
  Stack unit
  (requires (fun h -> live h hash /\ live h wsTable /\ disjoint hash wsTable))
  (ensures  (fun h0 _ h1 -> modifies1 hash h0 h1))
                       (* /\ h1.[hash] == Spec.shuffle Spec.SHA2_256 h0.[wsTable] h0.[hash])) *)

let shuffle hash wsTable =
  let h0 = ST.get () in
  loop_nospec #h0 (size (Spec.size_kTable Spec.SHA2_256)) hash
  (fun i -> shuffle_core hash wsTable i)


val compress: hash:hash_wp -> block:block_wp ->
  Stack unit
  (requires (fun h -> live h hash /\ live h block /\ disjoint hash block))
  (ensures  (fun h0 _ h1 -> modifies1 hash h0 h1))
                       (* /\ h1.[hash] == Spec.compress Spec.SHA2_256 h0.[block] h0.[hash])) *)

let compress hash block =
  push_frame();
  let wsTable = create (size (Spec.size_kTable Spec.SHA2_256)) (u32 0) in
  let hash0 = create (size Spec.size_hash_w) (u32 0) in
  ws wsTable block;
  copy hash0 hash;
  shuffle hash wsTable;
  let h0 = ST.get () in
  loop_nospec #h0 (size Spec.size_hash_w) hash
  (fun i ->
    let x0 = hash0.(i) in
    let x1 = hash.(i) in
    hash.(i) <- x0 +. x1);
  pop_frame ()


val truncate: hash:lbuffer uint8 (size (Spec.size_hash Spec.SHA2_256)) -> hw:hash_wp ->
  Stack unit
  (requires (fun h -> live h hash /\ live h hw /\ disjoint hash hw))
  (ensures  (fun h0 _ h1 -> modifies1 hash h0 h1))
                       (* /\ h1.[hash] == Spec.truncate Spec.SHA2_256 h0.[hw])) *)

let truncate hash hw =
  let h0 = ST.get () in
  salloc_nospec h0 (size Spec.size_hash_w *. size (Spec.size_word Spec.SHA2_256)) (u8 0) (Ghost.hide (loc hash))
  (fun hash_full ->
    uints_to_bytes_be (size Spec.size_hash_w) hash_full hw;
    let hash_final = sub hash_full (size 0) (size (Spec.size_hash Spec.SHA2_256)) in
    copy hash hash_final)


(* Definition of the function returning the number of padding blocks for a single input block *)
let number_blocks_padding (len:size_t{v len <= Spec.size_block Spec.SHA2_256}) :
  Tot (r:size_t{v r == Spec.number_blocks_padding Spec.SHA2_256 (v len)}) =
  if len <. (size (Spec.size_block Spec.SHA2_256) -. 8ul) then 1ul else 2ul


(* Definition of the padding function for a single input block *)
val pad:
    blocks: lbuffer uint8 (size (2 * Spec.size_block Spec.SHA2_256))
  -> prev: uint64
  -> last: buffer uint8
  -> len: size_t{ v len == length last
               /\ v len <= Spec.size_block Spec.SHA2_256
               /\ v len + uint_v prev <= Spec.max_input Spec.SHA2_256} ->
  Stack unit
  (requires (fun h -> live h blocks /\ live h last /\ disjoint blocks last))
  (ensures  (fun h0 _ h1 -> modifies1 blocks h0 h1))

let pad blocks prev last len =
  let nr = number_blocks_padding len in
  // Create the padding and copy the partial block inside
  let h0 = ST.get () in
  loop_nospec #h0 len blocks
  (fun i ->
    let x = index #MUT #uint8 #len last i in
    blocks.(i) <- x);
  // Write the 0x80 byte and the zeros in the padding
  blocks.(len) <- u8 0x80;
  // Encode and write the total length in bits at the end of the padding
  let tlen = prev +. (to_u64 len) in
  let tlenbits = tlen *. (u64 8) in
  let encodedlen = sub blocks (nr *. size (Spec.size_block Spec.SHA2_256) -. 8ul) 8ul in
  uint_to_bytes_be encodedlen tlenbits


val update_block: hash:hash_wp -> block:block_p ->
  Stack unit
  (requires (fun h -> live h hash /\ live h block /\ disjoint hash block))
  (ensures  (fun h0 _ h1 -> modifies1 hash h0 h1))

let update_block hash block =
  let h0 = ST.get () in
  salloc_nospec h0 (size Spec.size_block_w) (u32 0) (Ghost.hide (loc hash))
  (fun blockw ->
    uints_from_bytes_be blockw block;
    compress hash blockw)


val init: hash:hash_wp ->
  Stack unit
  (requires (fun h -> live h hash))
  (ensures  (fun h0 _ h1 -> modifies1 hash h0 h1
                       /\ h1.[hash] == Spec.init Spec.SHA2_256))

let init hash = set_h0Table hash


val update_last:
    hash: hash_wp
  -> prev: uint64
  -> last: buffer uint8
  -> len: size_t{ v len == length last
               /\ v len <= Spec.size_block Spec.SHA2_256
               /\ v len + uint_v prev <= Spec.max_input Spec.SHA2_256} ->
  Stack unit
  (requires (fun h -> live h hash /\ live h last /\ disjoint hash last))
  (ensures  (fun h0 _ h1 -> modifies1 hash h0 h1))

let update_last hash prev last len =
  let h0 = ST.get () in
  salloc_nospec h0 (2ul *. size (Spec.size_block Spec.SHA2_256)) (u8 0) (Ghost.hide (loc hash))
  (fun blocks ->
    pad blocks prev last len;
    let block0 = sub blocks (size 0) (size (Spec.size_block Spec.SHA2_256)) in
    let block1 = sub blocks (size (Spec.size_block Spec.SHA2_256)) (size (Spec.size_block Spec.SHA2_256)) in
    if number_blocks_padding len =. 1ul then (
      update_block hash block0)
    else (
      update_block hash block0;
      update_block hash block1))


val update:
    hash: hash_wp
  -> input: buffer uint8
  -> len: size_t{ v len == length input
               /\ v len <= Spec.max_input Spec.SHA2_256} ->
  Stack unit
  (requires (fun h -> live h hash /\ live h input /\ disjoint hash input))
  (ensures  (fun h0 _ h1 -> modifies1 hash h0 h1))

let update hash input len =
  let h0 = ST.get() in
  loopi_blocks_nospec (size (Spec.size_block Spec.SHA2_256)) len input
    (fun i block hash -> update_block hash block)
    (fun i len last hash -> update_last hash (to_u64 i *. u64 (Spec.size_block Spec.SHA2_256)) last len)
    hash


val finish: hash:lbuffer uint8 (size (Spec.size_hash Spec.SHA2_256)) -> hw:hash_wp ->
  Stack unit
  (requires (fun h -> live h hash /\ live h hw /\ disjoint hash hw))
  (ensures  (fun h0 _ h1 -> modifies1 hash h0 h1))

let finish hash hw = truncate hash hw


val hash:
    output: lbuffer uint8 (size (Spec.size_hash Spec.SHA2_256))
  -> input: buffer uint8
  -> len: size_t{length input == v len /\ v len <= Spec.max_input Spec.SHA2_256} ->
  Stack unit
  (requires (fun h -> live h output /\ live h input /\ disjoint output input))
  (ensures  (fun h0 _ h1 -> modifies1 output h0 h1))

let hash output input len =
  let h0 = ST.get () in
  salloc_nospec h0 (size Spec.size_hash_w) (u32 0) (Ghost.hide (loc output))
  (fun hash ->
    init hash;
    update hash input len;
    finish output hash)
