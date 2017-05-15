module Hacl.HMAC.SHA2_256

open FStar.Mul
open FStar.Ghost
open FStar.HyperStack
open FStar.ST
open FStar.Buffer

open C.Loops

open Hacl.Cast
open Hacl.UInt8
open Hacl.UInt32
open FStar.UInt32


(* Definition of aliases for modules *)
module U8 = FStar.UInt8
module U32 = FStar.UInt32
module U64 = FStar.UInt64

module H8 = Hacl.UInt8
module H32 = Hacl.UInt32
module H64 = Hacl.UInt64

module Spec_Hash = Spec.SHA2_256
module Hash = Hacl.Hash.SHA2_256
module Spec = Spec.HMAC.SHA2_256


(* Definition of base types *)
private let uint8_t   = FStar.UInt8.t
private let uint32_t  = FStar.UInt32.t
private let uint64_t  = FStar.UInt64.t

private let uint8_ht  = Hacl.UInt8.t
private let uint32_ht = Hacl.UInt32.t
private let uint64_ht = Hacl.UInt64.t

private let uint32_p = Buffer.buffer uint32_ht
private let uint8_p  = Buffer.buffer uint8_ht


(* Definitions of aliases for functions *)
[@"substitute"]
private let u8_to_h8 = Hacl.Cast.uint8_to_sint8
[@"substitute"]
private let u32_to_h32 = Hacl.Cast.uint32_to_sint32
[@"substitute"]
private let u32_to_h64 = Hacl.Cast.uint32_to_sint64
[@"substitute"]
private let h32_to_h8  = Hacl.Cast.sint32_to_sint8
[@"substitute"]
private let h32_to_h64 = Hacl.Cast.sint32_to_sint64
[@"substitute"]
private let u64_to_h64 = Hacl.Cast.uint64_to_sint64


//
// HMAC-SHA2-256
//

#reset-options "--max_fuel 0  --z3rlimit 10"

let xor_bytes_inplace a b len = C.Loops.in_place_map2 a b len (fun x y -> H8.logxor x y)


#reset-options "--max_fuel 0  --z3rlimit 10"

val wrap_key:
  output :uint8_p  {length output = v Hash.size_block} ->
  key    :uint8_p  {disjoint output key} ->
  len    :uint32_t {v len = length key /\ v len < Spec_Hash.max_input_len_8} ->
  Stack unit
        (requires (fun h -> live h output /\ live h key))
        (ensures  (fun h0 _ h1 -> live h1 output /\ modifies_1 output h0 h1))

#reset-options "--max_fuel 0  --z3rlimit 10"

let wrap_key output key len =
  if len <=^ Hash.size_block  then
    Buffer.blit key 0ul output 0ul len
  else begin
    let nkey = Buffer.sub output 0ul Hash.size_hash in
    Hash.hash nkey key len
  end


#reset-options "--max_fuel 0  --z3rlimit 10"

val hmac_core:
  mac  :uint8_p  {length mac = v Hash.size_hash} ->
  key  :uint8_p  {length key = v Hash.size_block /\ disjoint key mac} ->
  data :uint8_p  {length data + v Hash.size_block < Spec_Hash.max_input_len_8 /\ disjoint data mac /\ disjoint data key} ->
  len  :uint32_t {length data = v len} ->
  Stack unit
        (requires (fun h -> live h mac /\ live h key /\ live h data))
        (ensures  (fun h0 _ h1 -> live h1 mac /\ modifies_1 mac h0 h1))

#reset-options "--max_fuel 0  --z3rlimit 25"

let hmac_core mac key data len =

  (* Push a new memory frame *)
  (**) push_frame ();

  (* Initialize constants *)
  let ipad = Buffer.create (u8_to_h8 0x36uy) Hash.size_block in
  let opad = Buffer.create (u8_to_h8 0x5cuy) Hash.size_block in

  (* Allocate memory for the Hash states *)
  let state0 = Hash.alloc () in
  let state1 = Hash.alloc () in

  (* Step 2: xor "result of step 1" with ipad *)
  xor_bytes_inplace ipad key Hash.size_block;

  (* Step 3: append data to "result of step 2" *)
  (* Step 4: apply Hash to "result of step 3" *)
  let n0 = U32.div len Hash.size_block in
  let r0 = U32.rem len Hash.size_block in
  let last0 = Buffer.offset data (n0 *^ Hash.size_block) in
  Hash.init state0;
  Hash.update state0 ipad; (* s2 = ipad *)
  Hash.update_multi state0 data n0;
  Hash.update_last state0 last0 r0;

  let hash0 = Buffer.sub ipad 0ul Hash.size_hash in (* Salvage memory *)
  Hash.finish state0 hash0; (* s4 = hash (s2 @| data) *)

  (* Step 5: xor "result of step 1" with opad *)
  xor_bytes_inplace opad key Hash.size_block;

  (* Step 6: append "result of step 4" to "result of step 5" *)
  (* Step 7: apply H to "result of step 6" *)
  let n1 = 2ul in (* Hash.size_block + Hash.size_hash fits in 2 blocks *)
  let r1 = Hash.size_block -^ Hash.size_hash in
  Hash.init state1;
  Hash.update state1 opad; (* s5 = opad *)
  Hash.update_last state1 hash0 r1;
  Hash.finish state1 mac; (* s7 = hash (s5 @| s4) *)

  (* Pop the memory frame *)
  (**) pop_frame ()
