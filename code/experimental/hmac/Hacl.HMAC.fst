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
inline_for_extraction let hash = Hash.sha256
inline_for_extraction let hashsize = Hash.hashsize
inline_for_extraction let blocksize = Hash.blocksize


(* Size and positions of objects in memb *)
inline_for_extraction let size_ipad = blocksize
inline_for_extraction let size_opad = blocksize
inline_for_extraction let size_okey = blocksize
inline_for_extraction let size_s3   = blocksize +^ blocksize
inline_for_extraction let size_s6   = blocksize +^ blocksize
inline_for_extraction let size_memb = size_ipad +^ size_opad +^ size_okey +^ size_s3 +^ size_s6

inline_for_extraction let pos_ipad  = 0ul
inline_for_extraction let pos_opad  = pos_ipad +^ blocksize
inline_for_extraction let pos_okey  = pos_opad +^ blocksize
inline_for_extraction let pos_s3    = pos_okey +^ blocksize
inline_for_extraction let pos_s6    = pos_s3 +^ blocksize


(* Define a function to wrap the key length after bl bits *)
private val hmac_wrap_key:
  okey   :suint8_p{length okey = U32.v blocksize} ->
  key    :suint8_p ->
  keylen :uint32_t{U32.v keylen <= length key /\ U32.v keylen + 8 < pow2 32} ->
  Stack unit
        (requires (fun h0 -> live h0 okey /\ live h0 key))
        (ensures  (fun h0 _ h1 -> live h1 okey /\ live h1 key /\ modifies_1 okey h0 h1))

let hmac_wrap_key okey key keylen =
  if U32.(keylen >^ blocksize) then
    hash okey key keylen
  else
    blit key 0ul okey 0ul keylen



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

  (* Allocate memory for the padding *)
  let memb = Buffer.create (uint8_to_sint8 0uy) size_memb in

  (* Allocate and set initial values for ipad and opad *)
  let ipad = Buffer.create (uint8_to_sint8 0x36uy) size_ipad in
  let opad = Buffer.create (uint8_to_sint8 0x5cuy) size_opad in

  (* Allocate memory for the wrapped key location *)
  let okey = Buffer.create (uint8_to_sint8 0uy) size_okey in

  (* Allocate memory for working emplacements *)
  let s3 = Buffer.create (uint8_to_sint8 0uy) size_s3 in
  let s6 = Buffer.create (uint8_to_sint8 0uy) size_s6 in

  (* Step 1: make sure the key has the proper length *)
  hmac_wrap_key okey key keylen;

  (* Step 2: xor "result of step 1" with ipad *)
  Utils.xor_bytes ipad okey blocksize;
  let s2 = ipad in

  (* Step 3: append data to "result of step 2" *)
  Buffer.blit s2 0ul s3 0ul blocksize;
  Buffer.blit data 0ul s3 blocksize blocksize;

  (* Step 4: apply H to "result of step 3" *)
  let s4 = s2 in
  hash s4 s3 (blocksize +^ datalen);

  (* Step 5: xor "result of step 1" with opad *)
  Utils.xor_bytes okey opad blocksize;
  let s5 = okey in

  (* Step 6: append "result of step 4" to "result of step 5" *)
  Buffer.blit s5 0ul s6 0ul blocksize;
  Buffer.blit s4 0ul s6 blocksize blocksize;

  (* Step 7: apply H to "result of step 6" *)
  hash mac s6 (blocksize +^ hashsize);

  (* Pop the memory frame *)
  (**) pop_frame()
