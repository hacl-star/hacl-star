module Hacl.HMAC.Incremental.Masked.WIP
  
open FStar.Mul
open FStar.Ghost
open FStar.HyperStack
open FStar.ST
open FStar.Buffer
open FStar.UInt32
open Hacl.Cast
open Hacl.UInt8
open Hacl.UInt32
open Hacl.SBuffer
open Hacl.Operations
open Hacl.Conversions

module U8 = FStar.UInt8
module S8 = Hacl.UInt8
module U32 = FStar.UInt32
module S32 = Hacl.UInt32
module U64 = FStar.UInt64
module S64 = Hacl.UInt64
module SB = Hacl.SBuffer
module HC = Hacl.Cast


(* Define base types *)
let s8 = Hacl.UInt8.t
let u32 = FStar.UInt32.t
let s32 = Hacl.UInt32.t
let u64 = FStar.UInt64.t
let s64 = Hacl.UInt64.t
let uint32s = Hacl.SBuffer.u32s
let bytes = Hacl.SBuffer.u8s

#set-options "--lax"

(* Define operators *)
let ( +@ ) = U32.add
let ( +@% ) = U32.add_mod
let ( /@ ) = U32.div

(* Aliases *)
let u32_to_s32 = HC.uint32_to_sint32


(* Define parameters *)
module HF = Hash.SHA2.L256
module HFM = Hash.SHA2.L256.Masked

let hash = HF.sha256
let hash_masked = HFM.sha256

(* Get parameters *)
let hash_init = HF.init
let hash_update = HF.update
let hash_finish = HF.finish
let hash_init_masked = HFM.init
let hash_update_masked = HFM.update
let hash_finish_masked = HFM.finish

let hashsize = HF.hashsize
let blocksize = HF.blocksize
let hl = hashsize
let bl = blocksize


(* Define size of objects in the state_hmac *)
let size_key = bl // Bytes
let size_ipad = bl // Bytes
let size_opad = bl // Bytes
let size_final_hash_1 = hl // Bytes
let size_state_hmac_flat = size_key +@ size_ipad +@ size_opad +@ size_final_hash_1 // Bytes

(* Define size of objects in the state *)
let size_state_hash_1 = HFM.size_state // UInt32s
let size_state_hash_2 = HF.size_state // UInt32s
let size_state_hmac = size_state_hmac_flat // Bytes -> UInt32s
let size_state = size_state_hash_1 +@ size_state_hash_2 +@ size_state_hmac // UInt32s

(* Define position of objects in the state *)
let pos_state_hash_1 = 0ul
let pos_state_hash_2 = pos_state_hash_1 +@ size_state_hash_1
let pos_state_hmac  = pos_state_hash_2 +@ size_state_hash_2

(* Define position of objects in state_hmac *)
let pos_key         = 0ul
let pos_ipad        = pos_key +@ size_key
let pos_opad        = pos_ipad +@ size_ipad
let pos_final_hash_1 = pos_opad +@ size_opad


(* Define a function to wrap the key length after bl bits *)
val wrap_key : (okey   :bytes{length okey = U32.v bl}) ->
               (key    :bytes{length key % (U32.v bl) = 0 /\ disjoint okey key}) ->
               (keylen :s32{S32.v keylen <= length key}) ->
               (rounds_mask:u32{U32.v rounds_mask * U32.v blocksize = length key})
  -> STL unit
        (requires (fun h -> live h okey /\ live h key))
        (ensures  (fun h0 _ h1 -> live h1 okey /\ live h1 key /\ modifies_1 okey h0 h1))

let wrap_key okey key keylen rounds_mask =
  let mask = S32.gt_mask keylen (u32_to_s32 bl) in
  let p = branch_s32_mask (u32_to_s32 0ul) keylen mask in
  hash_masked okey key keylen rounds_mask;
  copymask key (u32_to_s32 0ul) p okey (U32.mul rounds_mask blocksize)


(* Define the initial hmac state *)
val init' :(memb   :bytes) -> 
           (state  :uint32s{length state = U32.v size_state}) ->
           (key    :bytes  {length key % (U32.v bl) = 0 /\ disjoint key state}) -> 
           (keylen :s32    {S32.v keylen <= length key}) ->
           (rounds_mask:u32{U32.v rounds_mask * U32.v blocksize = length key})
  -> STL unit
        (requires (fun h -> live h state))
        (ensures  (fun h0 r h1 -> live h1 state /\ modifies_1 state h0 h1))

let init' memb state key keylen rounds_mask =
  (* Select the part of the state used by the inner hash function *)
  let state_hash_1 = sub state pos_state_hash_1 size_state_hash_1 in
  let state_hash_2 = sub state pos_state_hash_2 size_state_hash_2 in

  (* Initialize the underlying hash functions *)
  hash_init_masked state_hash_1;
  hash_init state_hash_2;

  (* Select the part of the state used for HMAC *)
  let state_hmac = sub state pos_state_hmac size_state_hmac in
  let state_hmac_flat = sub memb 0ul size_state_hmac_flat in

  (* Conversion of the hmac state back to be flatten as bytes *)
  (**) be_bytes_of_uint32s state_hmac_flat state_hmac size_state_hmac_flat;
  
  (* Set initial values for ipad *)
  let ipad = sub state_hmac_flat pos_ipad size_ipad in
  setall ipad (uint8_to_sint8 0x36uy) size_ipad;

  (* Set initial values for ipad *)
  let opad = sub state_hmac_flat pos_opad size_opad in
  setall opad (uint8_to_sint8 0x5cuy) size_opad;

  (* Set initial values for  *)
  let okey = sub state_hmac_flat pos_key size_key in

  (* Step 1: make sure the key has the proper length *)
  wrap_key okey key keylen rounds_mask;

  (* Step 2: xor "result of step 1" with ipad *)
  xor_bytes ipad okey bl;
  xor_bytes opad okey bl;

  (* Step 3': feed ipad ^ okey to the inner hash function *)
  hash_update_masked state_hash_1 ipad (u32_to_s32 bl) 2ul;
  hash_update state_hash_2 opad bl;

  (* Conversion of the flat hmac state back in the global state *)
  (**) be_uint32s_of_bytes state_hmac state_hmac_flat size_state_hmac


val init : (state  :uint32s{length state = U32.v size_state}) ->
           (key    :bytes  {length key % (U32.v bl) = 0 /\ disjoint key state}) -> 
           (keylen :s32    {S32.v keylen <= length key}) ->
           (rounds_mask:u32{U32.v rounds_mask * U32.v blocksize = length key})
  -> STL unit
        (requires (fun h -> live h state))
        (ensures  (fun h0 r h1 -> live h1 state /\ modifies_1 state h0 h1))

let init state key keylen rounds_mask =

  (* Push frame *)
  (**) push_frame();

  let memblen = size_state_hmac_flat in
  let memb = create (uint8_to_sint8 0uy) memblen in

  init' memb state key keylen rounds_mask;

  (* Pop frame *)
  (**) pop_frame()
  

(* Update running hmac function *)
val update : (state :uint32s{length state = U32.v size_state}) ->
             (data    :bytes{ length data >= U32.v blocksize /\ (length data) % (U32.v blocksize) = 0 /\ disjoint data state}) ->
             (len     :s32{S32.v len + 8 < pow2 32 /\ S32.v len <= length data}) ->
             (rounds_mask:u32{U32.v rounds_mask * U32.v blocksize = length data})
             -> STL unit
                  (requires (fun h -> live h state /\ live h data))
                  (ensures  (fun h0 r h1 -> live h1 state /\ live h1 data /\ modifies_1 state h0 h1))

let update state data len rounds_mask =
  (* Select the part of the state used by the inner hash function *)
  let state_hash_1 = sub state pos_state_hash_1 size_state_hash_1 in
  
  (* Step 3'' and Step 4: Feed the message to the inner hash function *)
  hash_update_masked state_hash_1 data len rounds_mask



(* Compute the final value of the hash from the last hash value *)
val finish': (memb  :bytes) ->
             (mac   :bytes   { length mac = U32.v hashsize }) ->
             (state :uint32s { disjoint state mac })
             -> STL unit
                   (requires (fun h -> live h mac /\ live h state))
                   (ensures  (fun h0 r h1 -> live h1 mac /\ live h1 state /\ modifies_2 mac state h0 h1))

let finish' memb mac state =
  (* Select the part of the state used by the inner hash function *)
  let state_hash_1 = sub state pos_state_hash_1 size_state_hash_1 in
  let state_hash_2 = sub state pos_state_hash_2 size_state_hash_2 in

  (* Select the part of the state used for HMAC *)
  let state_hmac = sub state pos_state_hmac size_state_hmac in
  let state_hmac_flat = sub memb 0ul size_state_hmac_flat in
  
  (* Select the part of the state used for the inner final hash *)
  let final_hash_1 = sub state_hmac_flat pos_final_hash_1 size_final_hash_1 in

  (* Conversion of the hmac state back to be flatten as bytes *)
  (**) be_bytes_of_uint32s state_hmac_flat state_hmac size_state_hmac_flat;

  (* Step 6: finalize inner hash *)
  hash_finish final_hash_1 state_hash_1;

  (* Step 6': feed (opad ^ okey) and the final inner hash to the outer hash *)
  hash_update state_hash_2 final_hash_1 hashsize;

  (* Step 7: finalize outer hash to compute the final mac *)
  hash_finish mac state_hash_2


(* Compute the final value of the hash from the last hash value *)
val finish: (mac   :bytes   { length mac = U32.v hashsize }) ->
            (state :uint32s { disjoint state mac })
            -> STL unit
                 (requires (fun h -> live h mac /\ live h state))
                 (ensures  (fun h0 r h1 -> live h1 mac /\ live h1 state /\ modifies_2 mac state h0 h1))

let finish mac state =

  (* Push frame *)
  (**) push_frame();

  let memblen = size_state_hmac_flat in
  let memb = create (uint8_to_sint8 0uy) memblen in

  finish' memb mac state;

  (* Pop frame *)
  (**) pop_frame()
  


val hmac_core': (memb   :uint32s) ->
                (mac    :bytes { length mac >= U32.v hashsize /\ disjoint mac memb}) ->
                (key    :bytes { disjoint key memb /\ disjoint key mac }) ->
                (keylen :s32   { length key = S32.v keylen }) ->
                (data    :bytes{ length data >= U32.v blocksize /\ (length data) % (U32.v blocksize) = 0
                                   /\ disjoint data memb}) ->
                (len     :s32{S32.v len + 8 < pow2 32 /\ S32.v len <= length data}) ->
                (rounds_mask:u32{U32.v rounds_mask * U32.v blocksize = length data})
                -> STL unit
                      (requires (fun h -> live h mac /\ live h key /\ live h data))
                      (ensures  (fun h0 r h1 -> live h1 memb /\ live h1 mac /\ modifies_2 memb mac h0 h1))

let hmac_core' memb mac key keylen data len rounds_mask =
  let state = memb in
  init state key keylen rounds_mask;
  update state data len rounds_mask;
  finish mac state


(* Compute the mac of some bytes *)
val hmac_core: (mac    :bytes {length mac >= U32.v hashsize }) ->
               (key    :bytes {length key % (U32.v bl) = 0 /\ disjoint key mac }) ->
               (keylen :s32   {S32.v keylen <= length key}) ->
               (data   :bytes{ length data >= U32.v blocksize /\ (length data) % (U32.v blocksize) = 0}) ->
               (len    :s32{S32.v len + 8 < pow2 32 /\ S32.v len <= length data}) ->
               (rounds_mask:u32{U32.v rounds_mask * U32.v blocksize = length data})
               -> STL unit
                     (requires (fun h -> live h mac /\ live h key /\ live h data))
                     (ensures  (fun h0 r h1 -> live h1 mac /\ modifies_1 mac h0 h1))

let hmac_core mac key keylen data len rounds_mask =

  (* Push frame *)
  (**) push_frame();

  (* Allocate the memory block for the underlying function *)
  let memblen = size_state in
  let memb = create (uint32_to_sint32 0ul) memblen in

  (* Call the hmac function *)
  hmac_core' memb mac key keylen data len rounds_mask;

  (* Pop frame *)
  (**) pop_frame()



(* Exposing SHA2-256 for test vectors *)
val hmac_sha256 : (mac     :bytes { length mac = U32.v hl }) ->
                  (key     :bytes { disjoint key mac }) ->
                  (keylen  :s32   { length key = S32.v keylen }) ->
                  (data    :bytes{ length data >= U32.v blocksize /\ (length data) % (U32.v blocksize) = 0}) ->
                  (len     :s32{S32.v len + 8 < pow2 32 /\ S32.v len <= length data}) ->
                  (rounds_mask:u32{U32.v rounds_mask * U32.v blocksize = length data})
                  -> STL unit
                        (requires (fun h -> live h mac /\ live h data /\ live h key))
                        (ensures  (fun h0 r h1 -> live h1 mac /\ modifies_1 mac h0 h1))

let hmac_sha256 mac key keylen data len rounds_mask = hmac_core mac key keylen data len rounds_mask

