module Hacl.Impl.HMAC_SHA2_256

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

module SpecSHA2 = Spec.SHA2
module SpecHash = Spec.Hash
module SpecHMAC = Spec.HMAC

module Hash = Hacl.Hash.SHA2



inline_for_extraction noextract
let a = Spec.Hash.Definitions.SHA2_256


(* Key wrapping function *)
val wrap_key:
    output: lbuffer uint8 (size (Spec.Hash.Definitions.block_length a))
  -> key: buffer uint8
  -> len: size_t{v len == length key /\ v len < Spec.Hash.Definitions.max_input_length a} ->
  Stack unit
  (requires (fun h -> live h output /\ live h key /\ disjoint output key))
  (ensures  (fun h0 _ h1 -> modifies1 output h0 h1))

let wrap_key output key len =
  if len <=. size (Spec.Hash.Definitions.block_length a) then
    update_sub #MUT output (size 0) len key
  else begin
    let output' = sub output (size 0) (size (Spec.Hash.Definitions.hash_length a)) in
    Hash.hash_256 key len output'
  end


#reset-options "--z3rlimit 25"

val init:
    state: lbuffer uint32 (size (Spec.Hash.Definitions.hash_word_length a))
  -> key: lbuffer uint8 (size (Spec.Hash.Definitions.block_length a)) ->
  Stack unit
  (requires (fun h -> live h state /\ live h key /\ disjoint state key))
  (ensures  (fun h0 _ h1 -> modifies1 state h0 h1))

let init state key =
  push_frame ();
  let ipad = create (size (Spec.Hash.Definitions.block_length a)) (u8 0x36) in
  let state' = create (size (Spec.Hash.Definitions.hash_word_length a)) (u32 0) in
  let h0 = ST.get () in
  loop_nospec #h0 (size (Spec.Hash.Definitions.block_length a)) ipad
  (fun i -> ipad.(i) <- ipad.(i) ^. key.(i));
  Hacl.Hash.Core.SHA2.init_256 state';
  Hacl.Hash.Core.SHA2.update_256 state' ipad;
  copy state state';
  pop_frame ()


val update_block:
    state: lbuffer uint32 (size (Spec.Hash.Definitions.hash_word_length a))
  -> block: lbuffer uint8 (size (Spec.Hash.Definitions.block_length a)) ->
  Stack unit
  (requires (fun h -> live h state /\ live h block /\ disjoint state block))
  (ensures  (fun h0 _ h1 -> modifies1 state h0 h1))

let update_block state block =  Hacl.Hash.Core.SHA2.update_256 state block


val update_last:
    state: lbuffer uint32 (size (Spec.Hash.Definitions.hash_word_length a))
  -> prev: uint_t U64 PUB{ v prev % Spec.Hash.Definitions.block_length a = 0 }
  -> last: buffer uint8
  -> len: size_t{ v len == length last
               /\ v len <= Spec.Hash.Definitions.block_length a
               /\ v len + uint_v prev < Spec.Hash.Definitions.max_input_length a} ->
  Stack unit
  (requires (fun h -> live h state /\ live h last /\ disjoint state last))
  (ensures  (fun h0 _ h1 -> modifies1 state h0 h1))

let update_last state prev last len =
  Hash.update_last_256 state prev last len

#set-options "--z3rlimit 50"

val finish:
    hash: lbuffer uint8 (size (Spec.Hash.Definitions.hash_length a))
  -> state: lbuffer uint32 (size (Spec.Hash.Definitions.hash_word_length a))
  -> key: lbuffer uint8 (size (Spec.Hash.Definitions.block_length a)) ->
  Stack unit
  (requires (fun h -> live h hash /\ live h key /\ live h state
                 /\ disjoint hash key /\ disjoint hash state))
  (ensures  (fun h0 _ h1 -> modifies1 hash h0 h1))

let finish hash state key =
  push_frame();
  let scratch = create (size (Spec.Hash.Definitions.block_length a) +.
    size (Spec.Hash.Definitions.hash_length a)) (u8 0x5c)
  in
  let state2 = Hacl.Hash.Core.SHA2.alloca_256 () in
  let opad = sub scratch (size 0) (size (Spec.Hash.Definitions.block_length a)) in
  let s4 = sub scratch (size (Spec.Hash.Definitions.block_length a))
    (size (Spec.Hash.Definitions.hash_length a)) in
  Hacl.Hash.PadFinish.finish a state s4; (* s4 = hash *)
  let h0 = ST.get () in
  loop_nospec #h0 (size (Spec.Hash.Definitions.block_length a)) opad
  (fun i -> opad.(i) <- opad.(i) ^. key.(i)); (* s5 = opad *)
    let s5 = opad in
  Hacl.Hash.Core.SHA2.init_256 state2;
  Hacl.Hash.Core.SHA2.update_256 state2 s5;
  Hash.update_last_256 state2 (uint (Spec.Hash.Definitions.block_length a)) s4
    (size (Spec.Hash.Definitions.hash_length a));
  Hacl.Hash.PadFinish.finish a state2 hash;
  pop_frame ()


val hmac:
    mac: lbuffer uint8 (size (Spec.Hash.Definitions.hash_length a))
  -> key: buffer uint8{length key <= Spec.Hash.Definitions.max_input_length a}
  -> klen: size_t{v klen == length key}
  -> input: buffer uint8{length key + length input + Spec.Hash.Definitions.block_length a <= Spec.Hash.Definitions.max_input_length a}
  -> len: size_t{v len == length input} ->
  Stack unit
  (requires (fun h -> live h mac /\ live h key /\ live h input
                 /\ disjoint mac key /\ disjoint mac input))
  (ensures  (fun h0 _ h1 -> modifies1 mac h0 h1))

let hmac mac key klen input len =
  push_frame ();
  let okey = create (size (Spec.Hash.Definitions.block_length a)) (u8 0) in
  let state = create (size (Spec.Hash.Definitions.hash_word_length a)) (u32 0) in
  wrap_key okey key klen;
  init state okey;
  loopi_blocks_nospec (size (Spec.Hash.Definitions.block_length a)) len input
  (fun i block state -> update_block state block)
  (fun i len last state -> update_last state ((cast U64 PUB i +. (uint 1)) *. uint (Spec.Hash.Definitions.block_length a)) last len) state;
  finish mac state okey;
  pop_frame ()
