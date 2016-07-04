module HMAC.Sha256

open FStar.Mul
open FStar.Ghost
open FStar.HyperStack
open FStar.HST
open FStar.UInt32
open Hacl.Cast
open Hacl.UInt8
open Hacl.UInt32
open Hacl.SBuffer

open Hash.Sha256


module HH = FStar.HyperHeap
module HS = FStar.HyperStack
module U8 = Hacl.UInt8
module U32 = Hacl.UInt32

let u32 = FStar.UInt32.t
let u64 = FStar.UInt64.t
let s32 = Hacl.UInt32.t
let s8 = Hacl.UInt8.t
let uint32s = u32s
let bytes = u8s


#set-options "--lax"


// Define missing function
assume val xor_bytes: bytes -> bytes -> bytes -> u32 -> St unit 


(* Define parameters *)
let hash = sha256
let hl = 32ul
let bl = 64ul


(* Define a function to wrap the key length after bl bits *)
// BB.TODO: Uncomment the specification
//val wrap_key : (key    :bytes) ->
//               (keylen :u32 { length key = v keylen })
//               -> St (okey:bytes * okeylen:u32)
let wrap_key key keylen =
  if gt keylen bl then
    let nkey = create 0uy hl in
    hash nkey key keylen;
    nkey,hl
  else
    key,keylen


(* Define the main function *)
val hmac_sha256 : (mac     :bytes { length mac = v hl }) ->
                  (key     :bytes { disjoint key mac }) ->
                  (keylen  :u32   { length key = v keylen }) ->
                  (data    :bytes { disjoint mac data /\ disjoint key data }) ->
                  (datalen :u32   { length data = v datalen })
                  -> STL unit
                        (requires (fun h -> live h mac /\ live h data /\ live h key))
                        (ensures  (fun h0 r h1 -> live h1 mac /\ live h1 data /\ live h1 key /\ modifies_1 mac h0 h1))

let hmac_sha256 mac key keylen data datalen =
  (* Define ipad and opad *)
  let ipad = create 0x36uy bl in
  let opad = create 0x5cuy bl in

  (* Step 1: make sure the key has the proper length *)
  let okey,okeylen = wrap_key key keylen in
  let s1 = create 0uy bl in
  blit okey 0ul s1 0ul okeylen;

  (* Step 2: xor "result of step 1" with ipad *)
  let s2 = create 0uy bl in
  xor_bytes s2 s1 ipad bl;

  (* Step 3: append data to "result of step 2" *)
  let s3 = create 0uy (bl +^ datalen) in
  blit s2 0ul s3 0ul bl;
  blit data 0ul s3 bl datalen;

  (* Step 4: apply H to "result of step 3" *)
  let s4 = create 0uy hl in
  hash s4 s3 (bl +^ datalen);

  (* Step 5: xor "result of step 1" with opad *)
  let s5 = create 0uy bl in
  xor_bytes s5 s1 opad bl;

  (* Step 6: append "result of step 4" to "result of step 5" *)
  let s6 = create 0uy (hl +^ bl) in
  blit s5 0ul s6 0ul bl;
  blit s4 0ul s6 bl hl;

  (* Step 7: apply H to "result of step 6" *)
  hash mac s6 (hl +^ bl)
