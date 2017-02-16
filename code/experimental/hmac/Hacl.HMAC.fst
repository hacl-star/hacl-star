module Hacl.HMAC

open FStar.Mul
open FStar.Ghost
open FStar.HyperStack
open FStar.ST
open FStar.Buffer

open Hacl.Cast
open Hacl.UInt8
open Hacl.UInt32
open FStar.UInt32

open Hacl.Utils.Experimental


(* Definition of aliases for modules *)
module U8 = FStar.UInt8
module U32 = FStar.UInt32
module U64 = FStar.UInt64

module S8 = Hacl.UInt8
module S32 = Hacl.UInt32
module S64 = Hacl.UInt64

module Buffer = FStar.Buffer
module Cast = Hacl.Cast
module Utils = Hacl.Utils.Experimental

module Hash = Hacl.Hash.SHA2.L256


(* Definition of base types *)
let uint8_t   = FStar.UInt8.t
let uint32_t  = FStar.UInt32.t
let uint64_t  = FStar.UInt64.t

let suint8_t  = Hacl.UInt8.t
let suint32_t = Hacl.UInt32.t
let suint64_t = Hacl.UInt64.t

let suint32_p = Buffer.buffer suint32_t
let suint8_p  = Buffer.buffer suint8_t


(* Definitions of aliases for functions *)
let u8_to_s8 = Cast.uint8_to_sint8
let u32_to_s32 = Cast.uint32_to_sint32
let u32_to_s64 = Cast.uint32_to_sint64
let s32_to_s8  = Cast.sint32_to_sint8
let s32_to_s64 = Cast.sint32_to_sint64
let u64_to_s64 = Cast.uint64_to_sint64



//
// HMAC
//

(* Define parameters *)
inline_for_extraction let hashsize = Hash.hashsize
inline_for_extraction let hashsize_32 = Hash.hashsize_32
inline_for_extraction let blocksize = Hash.blocksize
inline_for_extraction let blocksize_32 = Hash.blocksize_32


(* Size and positions of objects in the state *)
inline_for_extraction let size_ipad = blocksize
inline_for_extraction let size_opad = blocksize
inline_for_extraction let size_okey_32 = blocksize /^ 4ul
inline_for_extraction let size_state = size_okey_32 +^ Hash.size_state

inline_for_extraction let pos_okey = 0ul
inline_for_extraction let pos_state_hash_0 = pos_okey +^ size_okey_32



(* Define a function to wrap the key length after blocksize *)
[@"c_inline"]
private val hmac_wrap_key:
  okey :suint8_p{length okey = U32.v blocksize} ->
  key  :suint8_p ->
  len  :uint32_t{U32.v len <= length key /\ U32.v len + 8 < pow2 32} ->
  Stack unit
        (requires (fun h0 -> live h0 okey /\ live h0 key))
        (ensures  (fun h0 _ h1 -> live h1 okey /\ live h1 key /\ modifies_1 okey h0 h1))

[@"c_inline"]
let hmac_wrap_key okey key len =
  if U32.(len >^ blocksize) then
    Hash.hash okey key len
  else
    Buffer.blit key 0ul okey 0ul len



val init:
  state :suint32_p{length state = U32.v size_state} ->
  key   :suint8_p ->
  len   :uint32_t {U32.v len = length key} ->
  Stack unit
        (requires (fun h0 -> live h0 state))
        (ensures  (fun h0 r h1 -> live h1 state /\ modifies_1 state h0 h1))

let init state key len =

  (* Push a new memory frame *)
  (**) push_frame();

  (* Allocate and set initial values for ipad *)
  let ipad = Buffer.create (uint8_to_sint8 0x36uy) size_ipad in

  (* Retrive and allocate memory for the wrapped key location *)
  let okey_32 = Buffer.sub state pos_okey size_okey_32 in
  let okey_8 = Buffer.create (uint8_to_sint8 0x00uy) blocksize in

  (* Retreive memory for the inner hash state *)
  let ctx_hash_0 = Buffer.sub state pos_state_hash_0 Hash.size_state in

  (* Initialize the inner hash state *)
  Hash.init ctx_hash_0;

  (* Step 1: make sure the key has the proper length *)
  hmac_wrap_key okey_8 key len;
  Hacl.Utils.Experimental.load32s_be okey_32 okey_8 (size_okey_32 *^ 4ul);

  (* Step 2: xor "result of step 1" with ipad *)
  Utils.xor_bytes ipad okey_8 blocksize;
  let s2 = ipad in

  (* Step 3a: feed s2 to the inner hash function *)
  Hash.update ctx_hash_0 s2;

  (* Pop the memory frame *)
  (**) pop_frame()



val update :
  state :suint32_p{length state = U32.v size_state} ->
  data  :suint8_p {length data = U32.v blocksize} ->
  Stack unit
        (requires (fun h0 -> live h0 state /\ live h0 data))
        (ensures  (fun h0 r h1 -> live h1 state /\ modifies_1 state h0 h1))

let update state data =

  (* Select the part of the state used by the inner hash function *)
  let ctx_hash_0 = Buffer.sub state pos_state_hash_0 Hash.size_state in

  (* Process the rest of the data *)
  Hash.update ctx_hash_0 data



val update_multi:
  state :suint32_p{length state = v size_state} ->
  data  :suint8_p ->
  max   :uint32_t ->
  idx   :uint32_t ->
  Stack unit
        (requires (fun h0 -> live h0 state))
        (ensures  (fun h0 _ h1 -> live h1 state /\ modifies_1 state h0 h1))

let rec update_multi state data max idx =

  if (idx =^ max) then ()
  else

    (* Get the current block for the data *)
    let b = Buffer.sub data (mul_mod idx blocksize) blocksize in

    (* Call the update function on the current block *)
    update state b;

    (* Recursive call *)
    update_multi state data max (idx +^ 1ul)



val update_last:
  state :suint32_p{length state = U32.v size_state} ->
  data  :suint8_p {length data = U32.v blocksize} ->
  len   :uint32_t {U32.v len <= U32.v blocksize} ->
  Stack unit
        (requires (fun h0 -> live h0 state /\ live h0 data))
        (ensures  (fun h0 r h1 -> live h1 state /\ modifies_1 state h0 h1))

let update_last state data len =

  (* Select the part of the state used by the inner hash function *)
  let ctx_hash_0 = Buffer.sub state pos_state_hash_0 Hash.size_state in

  (* Process the rest of the data *)
  Hash.update_last ctx_hash_0 data len



val finish:
  state :suint32_p{length state = U32.v size_state} ->
  mac   :suint8_p {length mac = U32.v hashsize} ->
  Stack unit
        (requires (fun h0 -> live h0 state /\ live h0 mac))
        (ensures  (fun h0 _ h1 -> live h1 state /\ live h1 mac /\ modifies_2 state mac h0 h1))

let finish state mac =

  (* Push a new memory frame *)
  (**) push_frame();

  (* Allocate and set initial values for ipad and opad *)
  let opad = Buffer.create (uint8_to_sint8 0x5cuy) size_opad in

  (* Allocate memory to store the output of the inner hash *)
  let s4 = Buffer.create (uint8_to_sint8 0x00uy) hashsize in

  (* Allocate memory for the outer hash state *)
  let ctx_hash_1 = Buffer.create (uint32_to_sint32 0ul) Hash.size_state in

  (* Retrieve the state of the inner hash *)
  let ctx_hash_0 = Buffer.sub state pos_state_hash_0 Hash.size_state in

  (* Retrive and allocate memory for the wrapped key location *)
  let okey_32 = Buffer.sub state pos_okey size_okey_32 in
  let okey_8 = Buffer.create (uint8_to_sint8 0x00uy) blocksize in
  Hacl.Utils.Experimental.store32s_be okey_8 okey_32 blocksize;

  (* Step 4: apply H to "result of step 3" *)
  Hash.finish ctx_hash_0 s4;

  (* Step 5: xor "result of step 1" with opad *)
  Utils.xor_bytes opad okey_8 blocksize;
  let s5 = opad in

  (* Initialize outer hash state *)
  Hash.init ctx_hash_1;

  (* Step 6: append "result of step 4" to "result of step 5" *)
  (* Step 7: apply H to "result of step 6" *)
  Hash.update ctx_hash_1 s5;
  Hash.update_last ctx_hash_1 s4 hashsize;
  Hash.finish ctx_hash_1 mac;

  (* Pop memory frame *)
  (**) pop_frame()



val hmac:
  mac     :suint8_p{length mac = U32.v hashsize} ->
  key     :suint8_p ->
  keylen  :uint32_t{U32.v keylen <= length key} ->
  data    :suint8_p ->
  datalen :uint32_t{U32.v datalen <= length data /\ U32.v datalen + U32.v blocksize <= pow2 32} ->
  Stack unit
        (requires (fun h -> live h mac /\ live h key /\ live h data ))
        (ensures  (fun h0 r h1 -> live h1 mac /\ modifies_1 mac h0 h1))

let hmac mac key keylen data datalen =

  (* Push a new memory frame *)
  (**) push_frame();

  (* Allocate memory for the mac state *)
  let ctx = Buffer.create (u32_to_s32 0ul) size_state in

  (* Compute the number of blocks to process *)
  let n = U32.div datalen blocksize in
  let r = U32.rem datalen blocksize in

  (* Initialize the mac state *)
  init ctx key keylen;

  (* Update the state with data blocks *)
  update_multi ctx data n 0ul;

  (* Get the last block *)
  let input_last = Buffer.sub data (mul_mod n blocksize) r in

  (* Process the last block of data *)
  update_last ctx input_last r;

  (* Finalize the mac output *)
  finish ctx mac;

  (* Pop the memory frame *)
  (**) pop_frame()
