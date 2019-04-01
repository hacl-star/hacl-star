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
                         /\ h1.[|buf|] == Spec.h0Table Spec.SHA2_256))

[@ Substitute ]
let set_h0Table s =
  recall_contents const_h0Table (Spec.h0Table Spec.SHA2_256);
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



val _Ch: x: word_t -> y: word_t -> z: word_t ->
  Tot (r: word_t{r == Spec._Ch Spec.SHA2_256 x y z})

let _Ch x y z = ((x &. y) ^. ((~. x) &. z))


val _Maj: x: word_t -> y: word_t -> z: word_t ->
  Tot (r: word_t{r == Spec._Maj Spec.SHA2_256 x y z})

let _Maj x y z = (x &. y) ^. ((x &. z) ^. (y &. z))


val _Sigma0: x:word_t ->
  Stack word_t
  (requires (fun h -> True))
  (ensures  (fun h0 r h1 -> modifies0 h0 h1 /\ r == Spec._Sigma0 Spec.SHA2_256 x))

let _Sigma0 x = (x >>>. (get_opTable 0ul)) ^. ((x >>>. get_opTable 1ul) ^. (x >>>. get_opTable 2ul))

val _Sigma1: x:word_t ->
  Stack word_t
  (requires (fun h -> True))
  (ensures  (fun h0 r h1 -> modifies0 h0 h1 /\ r == Spec._Sigma1 Spec.SHA2_256 x))

let _Sigma1 x = (x >>>. get_opTable 3ul) ^. ((x >>>. get_opTable 4ul) ^. (x >>>. get_opTable 5ul))

val _sigma0: x:word_t ->
  Stack word_t
  (requires (fun h -> True))
  (ensures  (fun h0 r h1 -> modifies0 h0 h1 /\ r == Spec._sigma0 Spec.SHA2_256 x))

let _sigma0 x =
  let n = get_opTable 8ul in
  (x >>>. get_opTable 6ul) ^. ((x >>>. get_opTable 7ul) ^. (x >>. n))

val _sigma1: x: word_t ->
  Stack word_t
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
                       /\ h1.[|s|] == Spec.step_ws0 Spec.SHA2_256 h0.[|b|] (v i) h0.[|s|]))

let step_ws0 s b i = s.(i) <- b.(i)


#reset-options "--z3rlimit 150"

val step_ws1:
    s: ws_wp
  -> i: size_t{16 <= v i /\ v i < Spec.size_kTable Spec.SHA2_256} ->
  Stack unit
  (requires (fun h -> live h s))
  (ensures  (fun h0 _ h1 -> modifies1 s h0 h1
                       /\ h1.[|s|] == Spec.step_ws1 Spec.SHA2_256 (v i) h0.[|s|]))

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
  (ensures  (fun h0 _ h1 -> modifies1 s h0 h1
                       /\ h1.[|s|] == Spec.loop_ws0 Spec.SHA2_256 h0.[|b|] h0.[|s|]))
let loop_ws0 s b =
  let h0 = ST.get () in
  [@inline_let]
  let spec h = Spec.step_ws0 Spec.SHA2_256 h.[|b|] in
  loop1 h0 (size 16) s spec
  (fun i ->
    Loops.unfold_repeati 16 (spec h0) h0.[|s|] (v i);
    step_ws0 s b i)


val loop_ws1: s: ws_wp ->
  Stack unit
  (requires (fun h -> live h s))
  (ensures  (fun h0 _ h1 -> modifies1 s h0 h1
                       /\ h1.[|s|] == Spec.loop_ws1 Spec.SHA2_256 h0.[|s|]))
let loop_ws1 s =
  let h0 = ST.get () in
  [@inline_let]
  let spec h = Spec.step_ws1 Spec.SHA2_256 in
  [@inline_let]
  let rounds = Spec.size_kTable Spec.SHA2_256 - 16 in
  assert(rounds + 16 >= 16 /\ rounds < Spec.size_kTable Spec.SHA2_256);
  assert(v (size rounds) + 16 >= 16 /\ v (size rounds) < Spec.size_kTable Spec.SHA2_256);
  admit();
  loop1 h0 (size rounds) s spec
  (fun i ->
    Loops.unfold_repeati rounds (spec h0) h0.[|s|] (v i);
    step_ws1 s (i +. size 16))


val ws:
    s: ws_wp
  -> b: block_wp ->
  Stack unit
  (requires (fun h -> live h s /\ live h b /\ disjoint s b
                 /\ h.[|s|] == Seq.create (Spec.size_kTable Spec.SHA2.SHA2_256) (u32 0)))
  (ensures  (fun h0 _ h1 -> modifies1 s h0 h1
                       /\ h1.[|s|] == Spec.ws Spec.SHA2_256 h0.[|b|]))

let ws s b =
  loop_ws0 s b;
  loop_ws1 s


val shuffle_core:
    s: hash_wp
  -> wsTable: ws_wp
  -> t: size_t{v t < Spec.size_kTable Spec.SHA2_256} ->
  Stack unit
  (requires (fun h -> live h s /\ live h wsTable /\ disjoint s wsTable))
  (ensures  (fun h0 _ h1 -> modifies1 s h0 h1
                       /\ h1.[|s|] == Spec.shuffle_core Spec.SHA2_256 h0.[|wsTable|] (v t) h0.[|s|]))

let shuffle_core hash wsTable i =
  let a0 = hash.(0ul) in
  let b0 = hash.(1ul) in
  let c0 = hash.(2ul) in
  let d0 = hash.(3ul) in
  let e0 = hash.(4ul) in
  let f0 = hash.(5ul) in
  let g0 = hash.(6ul) in
  let h0 = hash.(7ul) in

  let ws_i: word_t = wsTable.(i) in
  let k_i: word_t = get_kTable i in
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
  (ensures  (fun h0 _ h1 -> modifies1 hash h0 h1
                       /\ h1.[|hash|] == Spec.shuffle Spec.SHA2_256 h0.[|wsTable|] h0.[|hash|]))

let shuffle hash wsTable =
  let h0 = ST.get () in
  [@inline_let]
  let spec h = Spec.shuffle_core Spec.SHA2_256 h.[|wsTable|] in
  loop1 h0 (size (Spec.size_kTable Spec.SHA2_256)) hash spec
  (fun i ->
    Loops.unfold_repeati (Spec.size_kTable Spec.SHA2_256) (spec h0) h0.[|hash|] (v i);
    shuffle_core hash wsTable i)


val compress: hash:hash_wp -> block:block_wp ->
  Stack unit
  (requires (fun h -> live h hash /\ live h block /\ disjoint hash block))
  (ensures  (fun h0 _ h1 -> modifies1 hash h0 h1
                       /\ h1.[|hash|] == Spec.compress Spec.SHA2_256 h0.[|block|] h0.[|hash|]))

#reset-options "--z3rlimit 150"

let compress hash block =
  (**) let h0 = ST.get () in
  push_frame();
  let wsTable = create (size (Spec.size_kTable Spec.SHA2_256)) (u32 0) in
  let hash1 = create (size Spec.size_hash_w) (u32 0) in
  ws wsTable block;
  copy hash1 hash;
  shuffle hash1 wsTable;
  [@inline_let]
  (**) let f = (fun x0 x1 -> add_mod #U32 #SEC x0 x1) in
  map2T (size Spec.size_hash_w) hash f hash hash1;
  (**) let h5 = ST.get () in
  (**) Seq.eq_intro (h5.[|hash|]) (Spec.compress Spec.SHA2_256 h0.[|block|] h0.[|hash|]);
  pop_frame ()


val truncate: hash:lbuffer uint8 (size (Spec.size_hash Spec.SHA2_256)) -> hw:hash_wp ->
  Stack unit
  (requires (fun h -> live h hash /\ live h hw /\ disjoint hash hw))
  (ensures  (fun h0 _ h1 -> modifies1 hash h0 h1
                       /\ h1.[|hash|] == Spec.truncate Spec.SHA2_256 h0.[|hw|]))

let truncate hash hw =
  push_frame ();
  let hash_full = create (size Spec.size_hash_w *. size (Spec.size_word Spec.SHA2_256)) (u8 0) in
  uints_to_bytes_be (size Spec.size_hash_w) hash_full hw;
  let hash_final = sub hash_full (size 0) (size (Spec.size_hash Spec.SHA2_256)) in
  copy hash hash_final;
  pop_frame ()


(* Definition of the function returning the number of padding blocks for a single input block *)
let number_blocks_padding (len:size_t{v len <= Spec.size_block Spec.SHA2_256}) :
  Tot (r:size_t{v r == Spec.number_blocks_padding Spec.SHA2_256 (v len)}) =
  if len <. (size (Spec.size_block Spec.SHA2_256) -. 8ul) then 1ul else 2ul

#reset-options "--z3rlimit 150 --max_fuel 0"

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
  (ensures  (fun h0 _ h1 -> modifies1 blocks h0 h1
                       /\ h1.[|blocks|] == Spec.pad Spec.SHA2_256 (v prev) (v len) (as_seq #MUT #uint8 #len h0 last)))
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
  uint_to_bytes_be encodedlen tlenbits;
  admit()


val update_block: hash:hash_wp -> block:block_p ->
  Stack unit
  (requires (fun h -> live h hash /\ live h block /\ disjoint hash block))
  (ensures  (fun h0 _ h1 -> modifies1 hash h0 h1
                       /\ h1.[|hash|] == Spec.update_block Spec.SHA2_256 h0.[|block|] h0.[|hash|]))

let update_block hash block =
  push_frame ();
  let blockw = create (size Spec.size_block_w) (u32 0) in
  uints_from_bytes_be blockw block;
  compress hash blockw;
  pop_frame ()


val init: hash:hash_wp ->
  Stack unit
  (requires (fun h -> live h hash))
  (ensures  (fun h0 _ h1 -> modifies1 hash h0 h1
                       /\ h1.[|hash|] == Spec.init Spec.SHA2_256))

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
  (ensures  (fun h0 _ h1 -> modifies1 hash h0 h1
                       /\ h1.[|hash|] == Spec.update_last Spec.SHA2_256 (v prev) (v len) (as_seq #MUT #uint8 #len h0 last) (as_seq h0 hash)))

let update_last hash prev last len =
  push_frame ();
  let blocks = create (2ul *. size (Spec.size_block Spec.SHA2_256)) (u8 0) in
  pad blocks prev last len;
  let block0 = sub blocks (size 0) (size (Spec.size_block Spec.SHA2_256)) in
  let block1 = sub blocks (size (Spec.size_block Spec.SHA2_256)) (size (Spec.size_block Spec.SHA2_256)) in
  if number_blocks_padding len =. 1ul then (
     update_block hash block0)
  else (
    update_block hash block0;
    update_block hash block1);
  pop_frame ()


(* Definition of the single block update function *)
let spec_update_block (p:Spec.alg) (len:size_nat) (i:size_nat{i < len / Spec.size_block p}) (block:Lib.ByteSequence.lbytes (Spec.size_block p)) (hash:Spec.hash_w p): Tot (hf:Spec.hash_w p{hf == Spec.update_block p block hash}) =
  let bw = Lib.ByteSequence.uints_from_bytes_be block in
  Spec.compress p bw hash

(* Definition of the function for the partial block compression *)
let spec_update_last
  (p:Spec.alg)
  (flen: size_nat)
  (i: size_nat{i = flen % Spec.size_block p})
  (rlen:nat{rlen <= Spec.size_block p /\ rlen + (i * Spec.size_block p) <= Spec.max_input p})
  (last:Lib.ByteSequence.lbytes rlen)
  (hash:Spec.hash_w p):
  Tot (Spec.hash_w p) =

  let prev = i * Spec.size_block p in
  let blocks = Spec.pad p i rlen last in
  if Spec.number_blocks_padding p rlen = 1 then
    Spec.update_block p blocks hash
  else (
    let block1 = Lib.Sequence.sub blocks 0 (Spec.size_block p) in
    let block2 = Lib.Sequence.sub blocks (Spec.size_block p) (Spec.size_block p) in
    let hash = Spec.update_block p block1 hash in
    Spec.update_block p block2 hash)


(* Definition of the update function *)
let spec_update (p:Spec.alg) (input:Lib.Sequence.seq uint8) (hash:Spec.hash_w p): Tot (Spec.hash_w p) =
  admit();
  assume(Lib.Sequence.length input <= max_size_t);
  Lib.Sequence.repeati_blocks #uint8 #(hash:Spec.hash_w p) (Spec.size_block p) input
    (spec_update_block p (Lib.Sequence.length input))
    (spec_update_last p (Lib.Sequence.length input)) hash

val update:
    hash: hash_wp
  -> input: buffer uint8
  -> len: size_t{ v len == length input
               /\ v len <= Spec.max_input Spec.SHA2_256} ->
  Stack unit
  (requires (fun h -> live h hash /\ live h input /\ disjoint hash input))
  (ensures  (fun h0 _ h1 -> modifies1 hash h0 h1
                       /\ h1.[|hash|] == Spec.update Spec.SHA2_256 (as_seq #MUT #uint8 #len h0 input) h0.[|hash|]))

let update hash input len =
  admit();
  let h0 = ST.get() in
  loopi_blocks (size (Spec.size_block Spec.SHA2_256)) len input
    (spec_update_block Spec.SHA2_256 (v len))
    (spec_update_last Spec.SHA2_256 (v len))
    (fun i block hash -> update_block hash len)
    (fun i len last hash -> update_last hash len len last)
    hash


val finish: hash:lbuffer uint8 (size (Spec.size_hash Spec.SHA2_256)) -> hw:hash_wp ->
  Stack unit
  (requires (fun h -> live h hash /\ live h hw /\ disjoint hash hw))
  (ensures  (fun h0 _ h1 -> modifies1 hash h0 h1
                       /\ h1.[|hash|] == Spec.finish Spec.SHA2_256 h0.[|hw|]))

let finish hash hw = truncate hash hw


val hash:
    output: lbuffer uint8 (size (Spec.size_hash Spec.SHA2_256))
  -> input: buffer uint8
  -> len: size_t{length input == v len /\ v len <= Spec.max_input Spec.SHA2_256} ->
  Stack unit
  (requires (fun h -> live h output /\ live h input /\ disjoint output input))
  (ensures  (fun h0 _ h1 -> modifies1 output h0 h1
                       /\ h1.[|output|] == Spec.hash Spec.SHA2_256 (as_seq #MUT #uint8 #len h0 input)))

let hash output input len =
  let h0 = ST.get () in
  push_frame ();
  let hash = create (size Spec.size_hash_w) (u32 0) in
  init hash;
  update hash input len;
  finish output hash;
  pop_frame ()
