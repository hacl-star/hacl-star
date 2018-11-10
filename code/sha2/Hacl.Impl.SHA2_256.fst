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

#set-options "--admit_smt_queries true"


type word_t = Spec.word_t Spec.SHA2_256
type limb_t = Spec.limb_t Spec.SHA2_256

type block_wp = lbuffer word_t Spec.size_block_w
type hash_wp  = lbuffer word_t Spec.size_hash_w
type ws_wp    = lbuffer word_t (Spec.size_kTable Spec.SHA2.SHA2_256)

type block_p  = lbuffer uint8 (Spec.size_block Spec.SHA2_256)



let const_kTable = icreateL_global Spec.kTable_list_224_256
let const_h0Table = icreateL_global Spec.h0Table_list_256



val get_kTable:
  s:size_t{size_v s < Spec.size_kTable Spec.SHA2_256} ->
  Stack uint32
    (requires (fun h -> True))
    (ensures  (fun h0 z h1 -> h0 == h1 /\
      uint_v z == uint_v (Seq.index (Spec.kTable Spec.SHA2_256) (size_v s))))

[@ Substitute ]
let get_kTable s =
  recall_contents const_kTable (Spec.kTable Spec.SHA2_256);
  iindex const_kTable s

val set_h0Table:
  buf: lbuffer word_t Spec.size_hash_w ->
  Stack unit
    (requires (fun h -> live h buf))
    (ensures  (fun h0 z h1 -> h0 == h1))

[@ Substitute ]
let set_h0Table s =
  recall_contents const_h0Table (Spec.h0Table Spec.SHA2_256);
  let h0 = ST.get () in
  loop_nospec #h0 Spec.size_hash_w s
  (fun i -> s.(i) <- iindex const_h0Table i)

val step_ws0:
    s: ws_wp
  -> b: block_wp
  -> i: size_t{v i < 16} ->
  Stack unit
  (requires (fun h -> live h b /\ live h s /\ disjoint b s))
  (ensures  (fun h0 _ h1 -> modifies1 s h0 h1))

let step_ws0 s b i = s.(i) <- b.(i)


val step_ws1:
    s: ws_wp
  -> i: size_t{16 <= v i /\ v i < Spec.size_kTable Spec.SHA2_256} ->
  Stack unit
  (requires (fun h -> live h s))
  (ensures  (fun h0 _ h1 -> modifies1 s h0 h1))

let step_ws1 s i =
  let t16 = s.(i - 16) in
  let t15 = s.(i - 15) in
  let t7  = s.(i - 7) in
  let t2  = s.(i - 2) in
  let s1 = Spec._sigma1 Spec.SHA2_256 t2 in
  let s0 = Spec._sigma0 Spec.SHA2_256 t15 in
  s.(i) <- s1 +. (t7 +. (s0 +. t16))


val loop_ws0: s:ws_wp -> b:block_wp ->
  Stack unit
  (requires (fun h -> live h s /\ live h b /\ disjoint s b))
  (ensures  (fun h0 _ h1 -> modifies1 s h0 h1))

let loop_ws0 b s =
  let h0 = ST.get () in
  loop_nospec #h0 (size 16) s
  (fun i -> step_ws0 s b i)


val loop_ws1: s: ws_wp ->
  Stack unit
  (requires (fun h -> live h s))
  (ensures  (fun h0 _ h1 -> modifies1 s h0 h1))

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
  loop_ws0 b s;
  loop_ws1 s


val shuffle_core:
    s: hash_wp
  -> wsTable: ws_wp
  -> t: size_t{v t < Spec.size_kTable Spec.SHA2_256} ->
  Stack unit
  (requires (fun h -> live h s /\ live h wsTable /\ disjoint s wsTable))
  (ensures  (fun h0 _ h1 -> modifies1 s h0 h1))

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
  let t1 = h0 +. (Spec._Sigma1 Spec.SHA2_256 e0) +. ((Spec._Ch Spec.SHA2_256 e0 f0 g0) +. r) in
  let t2 = (Spec._Sigma0 Spec.SHA2_256 a0) +. (Spec._Maj Spec.SHA2_256 a0 b0 c0) in

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

let shuffle hash wsTable =
  let h0 = ST.get () in
  loop_nospec #h0 (size (Spec.size_kTable Spec.SHA2_256)) hash
  (fun i -> shuffle_core hash wsTable i)



val compress: hash:hash_wp -> block:block_wp ->
  Stack unit
  (requires (fun h -> live h hash /\ live h block /\ disjoint hash block))
  (ensures  (fun h0 _ h1 -> modifies1 hash h0 h1))

let compress hash block =
  push_frame();
  let wsTable = create (size (Spec.size_kTable Spec.SHA2_256)) (u32 0) in
  let hash0 = create (size Spec.size_hash_w) (u32 0) in
  copy hash0 (size 0) hash;
  shuffle hash wsTable;
  let h0 = ST.get () in
  loop_nospec #h0 Spec.size_hash_w hash
  (fun i -> hash.(i) <- hash.(i) ^. hash0.(i))



val truncate: hash:lbuffer uint8 (Spec.size_hash Spec.SHA2_256) -> hw:hash_wp ->
  Stack unit
  (requires (fun h -> live h hash /\ live h hw /\ disjoint hash hw))
  (ensures  (fun h0 _ h1 -> modifies1 hash h0 h1))

let truncate hash hw =
  let h0 = ST.get () in
  salloc_nospec h0 (size Spec.size_hash_w *. size (Spec.size_word Spec.SHA2_256)) (u8 0) (Ghost.hide (LowStar.Buffer.loc_buffer hash))
  (fun hash_full ->
    uints_to_bytes_be hash_full Spec.size_hash_w hw;
    let hash_final = sub #uint8 #(Spec.size_hash_w * (Spec.size_word Spec.SHA2_256)) #(Spec.size_hash Spec.SHA2_256) hash_full (size 0) (size (Spec.size_hash Spec.SHA2_256)) in
    copy hash (size 0) hash_final)


(* Definition of the function returning the number of padding blocks for a single input block *)
let number_blocks_padding (len:size_t{v len <= Spec.size_block Spec.SHA2_256}) : Tot size_t =
  if len <. (size (Spec.size_block Spec.SHA2_256) -. 8ul) then 1ul else 2ul

(* Definition of the padding function for a single input block *)
val pad:
    #vlen: size_nat
  -> blocks: lbuffer uint8 (2 * Spec.size_block Spec.SHA2_256)
  -> prev: uint64
  -> last: lbuffer uint8 vlen
  -> len: size_t{ v len == vlen
               /\ v len <= Spec.size_block Spec.SHA2_256
               /\ v len + v prev <= Spec.max_input Spec.SHA2_256} ->
  Stack unit
  (requires (fun h -> live h blocks /\ live h last /\ disjoint blocks last))
  (ensures  (fun h0 _ h1 -> modifies1 blocks h0 h1))

let pad #vlen blocks prev last len =
  let nr = number_blocks_padding len in
  // Create the padding and copy the partial block inside
  let h0 = ST.get () in
  loop_nospec #h0 len blocks
  (fun i -> blocks.(i) <- last.(i));
  // Write the 0x80 byte and the zeros in the padding
  blocks.(len) <- u8 0x80;
  // Encode and write the total length in bits at the end of the padding
  let tlen = prev +. (to_u64 len) in
  let tlenbits = tlen *. (u64 8) in
  let encodedlen = sub blocks len (size 8) in
  uint_to_bytes_be encodedlen tlenbits


val update_block: hash:hash_wp -> block:block_p ->
  Stack unit
  (requires (fun h -> live h hash /\ live h block /\ disjoint hash block))
  (ensures  (fun h0 _ h1 -> modifies1 hash h0 h1))

let update_block hash block =
  let h0 = ST.get () in
  salloc_nospec h0 (size Spec.size_block_w) (u32 0) (Ghost.hide (LowStar.Buffer.loc_buffer hash))
  (fun blockw ->
    uints_from_bytes_be blockw (size Spec.size_block_w) block;
    compress hash blockw)


val init: hash:hash_wp ->
  Stack unit
  (requires (fun h -> live h hash))
  (ensures  (fun h0 _ h1 -> modifies1 hash h0 h1))

let init hash = set_h0Table hash


val update_last:
    #vlen: size_nat
  -> hash: hash_wp
  -> prev: uint64
  -> last: lbuffer uint8 vlen
  -> len: size_t{ v len == vlen
               /\ v len <= Spec.size_block Spec.SHA2_256
               /\ v len + v prev <= Spec.max_input Spec.SHA2_256} ->
  Stack unit
  (requires (fun h -> live h hash /\ live h last /\ disjoint hash last))
  (ensures  (fun h0 _ h1 -> modifies1 hash h0 h1))

let update_last #vlen hash prev last len =
  let h0 = ST.get () in
  salloc_nospec h0 (2ul *. size Spec.size_block_w) (u8 0) (Ghost.hide (LowStar.Buffer.loc_buffer hash))
  (fun blocks ->
    pad blocks prev last len;
    let block0 = sub blocks (size 0) (Spec.size_block Spec.SHA2_256) in
    let block1 = sub blocks (Spec.size_block Spec.SHA2_256) (Spec.size_block Spec.SHA2_256) in
    if number_blocks_padding len = 1ul then (
      update_block hash block0)
    else (
      update_block hash block0;
      update_block hash block1))


val update:
    #vlen: size_nat
  -> hash: hash_wp
  -> input: lbuffer uint8 vlen
  -> len: size_t{ v len == vlen
               /\ v len <= Spec.max_input Spec.SHA2_256} ->
  Stack unit
  (requires (fun h -> live h hash /\ live h input /\ disjoint hash input))
  (ensures  (fun h0 _ h1 -> modifies1 hash h0 h1))

let update #vlen hash input len =
  let h0 = ST.get() in
  loopi_blocks_nospec (size (Spec.size_block Spec.SHA2_256)) len hash
    (fun i block hash -> update_block hash block)
    (fun i len last hash -> update_last #(len %. size (Spec.size_block Spec.SHA2_256)) hash (len /. (size (Spec.size_block Spec.SHA2_256))) last len)
    hash


val finish: hash:lbuffer uint8 (Spec.size_hash Spec.SHA2_256) -> hw:hash_wp ->
  Stack unit
  (requires (fun h -> live h hash /\ live h hw /\ disjoint hash hw))
  (ensures  (fun h0 _ h1 -> modifies1 hash h0 h1))

let finish hash hw = truncate hash hw


val hash: output: lbuffer uint8 (Spec.size_hash Spec.SHA2_256) -> input: buffer uint8 -> len: size_t{length input == v len} ->
  Stack unit
  (requires (fun h -> live h output /\ live h input /\ disjoint output input))
  (ensures  (fun h0 _ h1 -> modifies1 output h0 h1))

let hash output input len =
  let h0 = ST.get () in
  salloc_nospec h0 Spec.size_hash_w (u32 0) (Ghost.hide (LowStar.Buffer.loc_buffer output))
  (fun hash ->
    init hash;
    update #(v len) hash input len;
    finish output hash)
