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


#set-options "--admit_smt_queries true"


inline_for_extraction noextract
let a = Spec.SHA2.SHA2_256


(* Key wrapping function *)
val wrap_key:
    output: lbuffer uint8 (Spec.SHA2.size_block a)
  -> key: buffer uint8
  -> len: size_t{v len == length key /\ v len <= Spec.SHA2.max_input a} ->
  Stack unit
  (requires (fun h -> live h output /\ live h key /\ disjoint output key))
  (ensures  (fun h0 _ h1 -> modifies1 output h0 h1))

let wrap_key output key len =
  if len <=. size (Spec.SHA2.size_block a) then
    update_sub output (size 0) len key
  else begin
    let output' = sub output (size 0) (size (Spec.SHA2.size_hash a)) in
    Hash.hash output' key len
  end


val init:
    hash: lbuffer uint32 Spec.SHA2.size_hash_w
  -> key: lbuffer uint8 (Spec.SHA2.size_block a) ->
  Stack unit
  (requires (fun h -> live h hash /\ live h key /\ disjoint hash key))
  (ensures  (fun h0 _ h1 -> modifies1 key h0 h1))

let init hash key =
  let h0 = ST.get () in
  salloc_nospec h0 (size (Spec.SHA2.size_block a)) (u8 0x36) (Ghost.hide (LowStar.Buffer.loc_buffer hash))
  (fun ipad ->
    let h0 = ST.get () in
    loop_nospec #h0 (size (Spec.SHA2.size_block a)) key
    (fun i ->
      let a = ipad.(i) in
      let b = key.(i) in
      ipad.(i) <- a ^. b);
    Hash.update_block hash ipad)


val update_block:
    hash: lbuffer uint32 Spec.SHA2.size_hash_w
  -> block: lbuffer uint8 (Spec.SHA2.size_block a) ->
  Stack unit
  (requires (fun h -> live h hash /\ live h block /\ disjoint hash block))
  (ensures  (fun h0 _ h1 -> modifies1 hash h0 h1))

let update_block hash block = Hacl.Impl.SHA2_256.update_block hash block


val update_last:
    hash: lbuffer uint32 Spec.SHA2.size_hash_w
  -> prev: uint64
  -> last: buffer uint8
  -> len: size_t{ v len == length last
               /\ v len <= Spec.SHA2.size_block a
               /\ v len + v prev <= Spec.SHA2.max_input a} ->
  Stack unit
  (requires (fun h -> live h hash /\ live h last /\ disjoint hash last))
  (ensures  (fun h0 _ h1 -> modifies1 hash h0 h1))

let update_last hash prev last len = Hacl.Impl.SHA2_256.update_last hash prev last len


val update:
    hash: lbuffer uint32 Spec.SHA2.size_hash_w
  -> input: buffer uint8
  -> len: size_t{ v len == length input
               /\ v len <= Spec.SHA2.max_input a} ->
  Stack unit
  (requires (fun h -> live h hash /\ live h input /\ disjoint hash input))
  (ensures  (fun h0 _ h1 -> modifies1 hash h0 h1))

let update hash input len = Hacl.Impl.SHA2_256.update hash input len


val finish:
    hash: lbuffer uint8 (Spec.SHA2.size_hash a)
  -> hw: lbuffer uint32 Spec.SHA2.size_hash_w
  -> key: lbuffer uint8 (Spec.SHA2.size_block a) ->
  Stack unit
  (requires (fun h -> live h hash /\ live h key /\ disjoint hash key))
  (ensures  (fun h0 _ h1 -> modifies1 key h0 h1))

let finish hash hw key =
  let h0 = ST.get () in
  salloc_nospec h0 (size (Spec.SHA2.size_block a) +. size (Spec.SHA2.size_hash a)) (u8 0x5c) (Ghost.hide (LowStar.Buffer.loc_buffer hash))
  (fun scratch ->

    let h1 = ST.get () in
    salloc_nospec h1 (size Spec.SHA2.size_hash_w) (u32 0) (Ghost.hide (LowStar.Buffer.loc_union
                                                                      (LowStar.Buffer.loc_buffer hash)
                                                                      (LowStar.Buffer.loc_buffer scratch)))
    (fun hw2 ->
      let opad = sub scratch (size 0) (size (Spec.SHA2.size_block a)) in
      let s4 = sub scratch (size (Spec.SHA2.size_block a)) (size (Spec.SHA2.size_hash a)) in
      Hacl.Impl.SHA2_256.finish s4 hw; (* s4 = hash *)
      let h0 = ST.get () in
      loop_nospec #h0 (size (Spec.SHA2.size_block a)) key
      (fun i -> opad.(i) <- opad.(i) ^. key.(i)); (* s5 = opad *)
      let s5 = opad in
      Hacl.Impl.SHA2_256.init hw2;
      Hacl.Impl.SHA2_256.update_block hw2 s5;
      Hacl.Impl.SHA2_256.update_last hw2 (u64 (Spec.SHA2.size_block a)) s4 (size (Spec.SHA2.size_hash a));
      Hacl.Impl.SHA2_256.finish hash hw2))


val hmac:
    mac: lbuffer uint8 (Spec.SHA2.size_hash a)
  -> key: buffer uint8{length key <= Spec.SHA2.max_input a}
  -> klen: size_t{v klen == length key}
  -> input: buffer uint8{length key + length input + Spec.SHA2.size_block a <= Spec.SHA2.max_input a}
  -> len: size_t{v len == length input} ->
  Stack unit
  (requires (fun h -> live h mac /\ live h key /\ live h input
                 /\ disjoint mac key /\ disjoint mac input))
  (ensures  (fun h0 _ h1 -> modifies1 mac h0 h1))

let hmac mac key klen input len =
  let h0 = ST.get () in
  salloc_nospec h0 (size (Spec.SHA2.size_block a)) (u8 0) (Ghost.hide (LowStar.Buffer.loc_buffer mac))
  (fun okey ->
    let h1 = ST.get () in
    salloc_nospec h1 (size Spec.SHA2.size_hash_w) (u32 0) (Ghost.hide (LowStar.Buffer.loc_union
                                                                      (LowStar.Buffer.loc_buffer mac)
                                                                      (LowStar.Buffer.loc_buffer okey)))
    (fun hash ->
      wrap_key okey key len;
      init hash okey;
//      update hash input len;
      finish mac okey hash))
