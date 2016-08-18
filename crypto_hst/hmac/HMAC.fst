module HMAC
  
open FStar.Mul
open FStar.Ghost
open FStar.HyperStack
open FStar.HST
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


(* Define base types *)
let s8 = Hacl.UInt8.t
let u32 = FStar.UInt32.t
let s32 = Hacl.UInt32.t
let u64 = FStar.UInt64.t
let s64 = Hacl.UInt64.t
let uint32s = Hacl.SBuffer.u32s
let bytes = Hacl.SBuffer.u8s


(* Define operators *)
let op_At_Plus_Percent = U32.add_mod
let op_At_Slash = U32.div

(* Define parameters *)
module HF = Hash.Sha256
let hash = HF.sha256

(* Get parameters *)
let hash_init = HF.init
let hash_update = HF.update
let hash_finish = HF.finish

let hashsize = HF.hashsize
let blocksize = HF.blocksize
let hl = hashsize
let bl = blocksize


(* Define size of objects in the state *)
let size_state_hash_1 = HF.size_state // UInt32s
let size_state_hash_2 = HF.size_state // UInt32s

let size_key = bl // Bytes
let size_ipad = bl // Bytes
let size_opad = bl // Bytes
let size_final_hash_1 = hl // Bytes
let size_state_hmac_flat = size_key @+% size_ipad @+% size_opad @+% size_final_hash_1 // Bytes
let size_state_hmac = size_state_hmac_flat @/ 4ul // Bytes -> UInt32s

let size_state = size_state_hash_1 @+% size_state_hash_2 @+% size_state_hmac // UInt32s

(* Define position of objects in the state *)
let pos_state_hash_1 = 0ul
let pos_state_hash_2 = pos_state_hash_1 @+% size_state_hash_1

let pos_state_hmac  = pos_state_hash_2 @+% size_state_hash_2
let pos_key         = pos_state_hmac
let pos_ipad        = pos_key @+% size_key
let pos_opad        = pos_ipad @+% size_ipad
let pos_final_hash_1 = pos_opad @+% size_opad

#set-options "--lax"

(* Define a function to wrap the key length after bl bits *)
val wrap_key : (okey   :bytes{length okey = U32.v bl}) -> 
               (key    :bytes{length key % (U32.v bl) = 0 /\ disjoint okey key}) -> 
               (keylen :u32  {U32.v keylen <= length key})
  -> STL unit
        (requires (fun h -> live h okey /\ live h key))
        (ensures  (fun h0 _ h1 -> live h1 okey /\ live h1 key /\ modifies_1 okey h0 h1))

let wrap_key okey key keylen =
  if gt keylen bl then
    hash okey key keylen
  else
    blit key 0ul okey 0ul keylen


(* Define the initial hmac state *)
val init' :(memb   :bytes) -> 
           (state  :uint32s{length state = U32.v size_state}) ->
           (key    :bytes  {length key % (U32.v bl) = 0 /\ disjoint key state}) -> 
           (keylen :u32    {U32.v keylen <= length key})
  -> STL unit
        (requires (fun h -> live h state))
        (ensures  (fun h0 r h1 -> live h1 state /\ modifies_1 state h0 h1))

let init' memb state key keylen =
  (* Select the part of the state used by the inner hash function *)
  let state_hash_1 = sub state pos_state_hash_1 size_state_hash_1 in

  (* Initialize the underlying inner hash function *)
  hash_init state_hash_1;
  
  (* Select the part of the state used for HMAC *)
  let state_hmac = sub state pos_state_hmac size_state_hmac in
  let state_hmac_flat = sub memb 0ul size_state_hmac_flat in
  (**) be_bytes_of_uint32s state_hmac_flat state_hmac size_state_hmac_flat;
  
  let okey = sub state_hmac_flat pos_key size_key in

  (* Set initial values for ipad *)
  let ipad = sub state_hmac_flat pos_ipad size_ipad in
  setall ipad size_ipad (uint8_to_sint8 0x36uy);

  (* Step 1: make sure the key has the proper length *)
  wrap_key okey key keylen;

  (* Step 2: xor "result of step 1" with ipad *)
  xor_bytes ipad okey bl;

  (* Step 3': feed ipad ^ okey to the inner hash function *)
  hash_update state_hash_1 ipad size_ipad


val init : (state  :uint32s{length state = U32.v size_state}) ->
           (key    :bytes  {length key % (U32.v bl) = 0 /\ disjoint key state}) -> 
           (keylen :u32    {U32.v keylen <= length key})
  -> STL unit
        (requires (fun h -> live h state))
        (ensures  (fun h0 r h1 -> live h1 state /\ modifies_1 state h0 h1))

let init state key keylen =

  (** Push frame *)
  (**) push_frame();

  let memblen = size_state_hmac_flat in
  let memb = create (uint8_to_sint8 0uy) memblen in

  init' memb state key keylen;

  (** Pop frame *)
  (**) pop_frame()
  

(* Update running hmac function *)
val update : (state :uint32s) ->
             (data  :bytes {disjoint state data}) ->
             (len   :u32)
             -> STL unit
                  (requires (fun h -> live h state /\ live h data))
                  (ensures  (fun h0 r h1 -> live h1 state /\ live h1 data /\ modifies_1 state h0 h1))

let update state data len =
  (* Select the part of the state used by the inner hash function *)
  let state_hash_1 = sub state pos_state_hash_1 size_state_hash_1 in
  
  (* Step 3'' and Step 4: Feed the message to the inner hash function *)
  hash_update state_hash_1 data len



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

  (* Select the part of the state used by the outter hash function *)
  let state_hash_2 = sub state pos_state_hash_2 size_state_hash_2 in

  (* Initialize the underlying outer hash function *)
  hash_init state_hash_2;
  
  (* Select the part of the state used for HMAC *)
  let state_hmac = sub state pos_state_hmac size_state_hmac in
  let state_hmac_flat = sub memb 0ul size_state_hmac_flat in

  let final_hash_1 = sub state_hmac_flat pos_final_hash_1 size_final_hash_1 in
  let okey = sub state_hmac_flat pos_key size_key in

  (* Set initial values for opad *)
  let opad = sub state_hmac_flat pos_opad size_opad in
  setall opad size_opad (uint8_to_sint8 0x5cuy);

  (* Step 5: xor "result of step 1" with opad *)
  xor_bytes opad okey size_opad;

  (* Step 6: finalize inner hash *)
  hash_finish final_hash_1 state_hash_1;

  (* Step 6': feed (opad ^ okey) and the final inner hash to the outer hash *)
  hash_update state_hash_2 opad size_opad;
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

  (** Push frame *)
  (**) push_frame();

  let memblen = size_state_hmac_flat in
  let memb = create (uint8_to_sint8 0uy) memblen in

  finish' memb mac state;

  (** Pop frame *)
  (**) pop_frame()
  


val hmac_core': (memb   :uint32s) ->
                (mac    :bytes { length mac >= U32.v hashsize /\ disjoint mac memb}) ->
                (key    :bytes { disjoint key memb /\ disjoint key mac }) ->
                (keylen :u32   { length key = U32.v keylen }) ->
                (data   :bytes { disjoint data memb /\ disjoint data mac /\ disjoint data key }) ->
                (len    :u32   { length data = U32.v len })
                -> STL unit
                      (requires (fun h -> live h mac /\ live h key /\ live h data))
                      (ensures  (fun h0 r h1 -> live h1 memb /\ live h1 mac /\ modifies_2 memb mac h0 h1))

let hmac_core' memb mac key keylen data len =
  let state = memb in
  init state key keylen;
  update state data len;
  finish mac state


(* Compute the mac of some bytes *)
val hmac_core: (mac    :bytes {length mac >= U32.v hashsize }) ->
               (key    :bytes {length key % (U32.v bl) = 0 /\ disjoint key mac }) ->
               (keylen :u32   {U32.v keylen <= length key}) ->
               (data   :bytes {length key % (U32.v bl) = 0 /\ disjoint data mac /\ disjoint data key }) ->
               (len    :u32   {U32.v len <= length data})
               -> STL unit
                     (requires (fun h -> live h mac /\ live h key /\ live h data))
                     (ensures  (fun h0 r h1 -> live h1 mac /\ modifies_1 mac h0 h1))

let hmac_core mac key keylen data len =

  (** Push frame *)
  (**) push_frame();

  (* Compute size of objects *)
  let _statelen = size_state in

  (* Allocate the memory block for the underlying function *)
  let memblen = _statelen in
  let memb = create (uint32_to_sint32 0ul) memblen in

  (* Call the hmac function *)
  hmac_core' memb mac key keylen data len ;

  (** Pop frame *)
  (**) pop_frame()



(* Exposing SHA2-256 for test vectors *)
val hmac_sha256 : (mac     :bytes { length mac = U32.v hl }) ->
                  (key     :bytes { disjoint key mac }) ->
                  (keylen  :u32   { length key = U32.v keylen }) ->
                  (data    :bytes { disjoint mac data }) ->
                  (datalen :u32   {5 * U32.v bl + U32.v hl + U32.v datalen < pow2 32 /\ length data = U32.v datalen /\ U32.v datalen + U32.v bl <= pow2 32})
                  -> STL unit
                        (requires (fun h -> live h mac /\ live h data /\ live h key))
                        (ensures  (fun h0 r h1 -> live h1 mac /\ modifies_1 mac h0 h1))

let hmac_sha256 mac key keylen data datalen = hmac_core mac key keylen data datalen

