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

module Hash = Hacl.Impl.SHA2_256



inline_for_extraction noextract
let a = Spec.SHA2.SHA2_256


(* Key wrapping function *)
val wrap_key:
    output: lbuffer uint8 (size (Spec.SHA2.size_block a))
  -> key: buffer uint8
  -> len: size_t{v len == length key /\ v len <= Spec.SHA2.max_input a} ->
  Stack unit
  (requires (fun h -> live h output /\ live h key /\ disjoint output key))
  (ensures  (fun h0 _ h1 -> modifies1 output h0 h1))

let wrap_key output key len =
  if len <=. size (Spec.SHA2.size_block a) then
    update_sub #MUT output (size 0) len key
  else begin
    let output' = sub output (size 0) (size (Spec.SHA2.size_hash a)) in
    Hash.hash output' key len
  end


#reset-options "--z3rlimit 25"

val init:
    state: lbuffer uint32 (size Spec.SHA2.size_hash_w)
  -> key: lbuffer uint8 (size (Spec.SHA2.size_block a)) ->
  Stack unit
  (requires (fun h -> live h state /\ live h key /\ disjoint state key))
  (ensures  (fun h0 _ h1 -> modifies1 state h0 h1))

let init state key =
  push_frame ();
  let ipad = create (size (Spec.SHA2.size_block a)) (u8 0x36) in
  let state' = create (size (Spec.SHA2.size_hash_w)) (u32 0) in
  let h0 = ST.get () in
  loop_nospec #h0 (size (Spec.SHA2.size_block a)) ipad
  (fun i -> ipad.(i) <- ipad.(i) ^. key.(i));
  Hash.init state';
  Hash.update_block state' ipad;
  copy state state';
  pop_frame ()


val update_block:
    state: lbuffer uint32 (size Spec.SHA2.size_hash_w)
  -> block: lbuffer uint8 (size (Spec.SHA2.size_block a)) ->
  Stack unit
  (requires (fun h -> live h state /\ live h block /\ disjoint state block))
  (ensures  (fun h0 _ h1 -> modifies1 state h0 h1))

let update_block state block = Hacl.Impl.SHA2_256.update_block state block


val update_last:
    state: lbuffer uint32 (size Spec.SHA2.size_hash_w)
  -> prev: uint64
  -> last: buffer uint8
  -> len: size_t{ v len == length last
               /\ v len <= Spec.SHA2.size_block a
               /\ v len + uint_v prev <= Spec.SHA2.max_input a} ->
  Stack unit
  (requires (fun h -> live h state /\ live h last /\ disjoint state last))
  (ensures  (fun h0 _ h1 -> modifies1 state h0 h1))

let update_last state prev last len = Hacl.Impl.SHA2_256.update_last state prev last len


val update:
    state: lbuffer uint32 (size Spec.SHA2.size_hash_w)
  -> input: buffer uint8
  -> len: size_t{ v len == length input
               /\ v len <= Spec.SHA2.max_input a} ->
  Stack unit
  (requires (fun h -> live h state /\ live h input /\ disjoint state input))
  (ensures  (fun h0 _ h1 -> modifies1 state h0 h1))

let update state input len = Hacl.Impl.SHA2_256.update state input len


#set-options "--z3rlimit 50"

val finish:
    hash: lbuffer uint8 (size (Spec.SHA2.size_hash a))
  -> state: lbuffer uint32 (size Spec.SHA2.size_hash_w)
  -> key: lbuffer uint8 (size (Spec.SHA2.size_block a)) ->
  Stack unit
  (requires (fun h -> live h hash /\ live h key /\ live h state
                 /\ disjoint hash key /\ disjoint hash state))
  (ensures  (fun h0 _ h1 -> modifies1 hash h0 h1))

let finish hash state key =
  push_frame();
  let scratch = create (size (Spec.SHA2.size_block a) +. size (Spec.SHA2.size_hash a)) (u8 0x5c) in
  let state2 = create (size Spec.SHA2.size_hash_w) (u32 0x00) in
  let opad = sub scratch (size 0) (size (Spec.SHA2.size_block a)) in
  let s4 = sub scratch (size (Spec.SHA2.size_block a)) (size (Spec.SHA2.size_hash a)) in
  Hacl.Impl.SHA2_256.finish s4 state; (* s4 = hash *)
  let h0 = ST.get () in
  loop_nospec #h0 (size (Spec.SHA2.size_block a)) opad
  (fun i -> opad.(i) <- opad.(i) ^. key.(i)); (* s5 = opad *)
    let s5 = opad in
  Hacl.Impl.SHA2_256.init state2;
  Hacl.Impl.SHA2_256.update_block state2 s5;
  Hacl.Impl.SHA2_256.update_last state2 (u64 (Spec.SHA2.size_block a)) s4 (size (Spec.SHA2.size_hash a));
  Hacl.Impl.SHA2_256.finish hash state2;
  pop_frame ()


val hmac:
    mac: lbuffer uint8 (size (Spec.SHA2.size_hash a))
  -> key: buffer uint8{length key <= Spec.SHA2.max_input a}
  -> klen: size_t{v klen == length key}
  -> input: buffer uint8{length key + length input + Spec.SHA2.size_block a <= Spec.SHA2.max_input a}
  -> len: size_t{v len == length input} ->
  Stack unit
  (requires (fun h -> live h mac /\ live h key /\ live h input
                 /\ disjoint mac key /\ disjoint mac input))
  (ensures  (fun h0 _ h1 -> modifies1 mac h0 h1))

let hmac mac key klen input len =
  push_frame ();
  let okey = create (size (Spec.SHA2.size_block a)) (u8 0) in
  let state = create (size Spec.SHA2.size_hash_w) (u32 0) in
  wrap_key okey key klen;
  init state okey;
  loopi_blocks_nospec (size (Spec.SHA2.size_block a)) len input
  (fun i block state -> update_block state block)
  (fun i len last state -> update_last state ((to_u64 i +. (u64 1)) *. u64 (Spec.SHA2.size_block a)) last len) state;
  finish mac state okey;
  pop_frame ()
