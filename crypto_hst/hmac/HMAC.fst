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


(* Define base types *)
let u32 = FStar.UInt32.t
let u64 = FStar.UInt64.t
let s64 = Hacl.UInt64.t
let s32 = Hacl.UInt32.t
let s8 = Hacl.UInt8.t
let uint32s = Hacl.SBuffer.u32s
let bytes = Hacl.SBuffer.u8s


(* Define operators *)
let op_At_Plus = UInt32.add


(* Define algorithm parameters *)
let hash_init = Hash.Sha256.init
let hash_uptdate = Hash.Sha256.update
let hash_finish = Hash.Sha256.finish
let hl = 32ul
let bl = 64ul
let hashsize = hl in
let blocksize = bl in


(* Define size of objects in the state *)
let size_hash_state = blocksize
let size_key = blocksize
let size_ipad = blocksize
let size_opad = blocksize

(* Define position of objects in the state *)
let pos_hash1_state = 0ul
let pos_hash2_state = size_hash_state
let pos_key         = size_hash_state @+ size_hash_state
let pos_ipad        = size_hash_state @+ size_hash_state @+ size_key
let pos_opad        = size_hash_state @+ size_hash_state @+ size_key @+ size_key



(* Define a function to wrap the key length after bl bits *)
val wrap_key : (okey:bytes{ length okey = v bl}) -> (key:bytes {disjoint okey key}) -> (keylen :u32 { length key = v keylen })
               -> STL unit
                     (requires (fun h -> live h okey /\ live h key))
                     (ensures  (fun h0 _ h1 -> live h1 okey /\ live h1 key /\ modifies_1 okey h0 h1))

let wrap_key okey key keylen =
  if gt keylen bl then
    hash okey key keylen
  else
    copymask key 0ul okey 0ul keylen blocksize


(* Define the initial hmac state *)
val init : state:uint32s
  -> STL unit
        (requires (fun h -> live h state))
        (ensures  (fun h0 r h1 -> live h1 state /\ modifies_1 state h0 h1))

let init state key keylen =
  (* Select the part of the state used by the inner hash function *)
  let hash_state_1 = sub state pos_hash1_state size_hash1_state in

  (* Initialize the underlying inner hash function *)
  hash_init hash_state_1;
  
  (* Select the part of the state used for HMAC *)
  let hmac_state = sub state pos_hmac_state size_hmac_state in
  let okey = sub hmac_state pos_key size_key in

  (* Set initial values for ipad *)
  let ipad = sub hmac_state pos_ipad size_ipad in
  setall ipad size_ipad 0x36uy;

  (* Step 1: make sure the key has the proper length *)
  wrap_key okey key keylen;

  (* Step 2: xor "result of step 1" with ipad *)
  xor_bytes ipad okey blocksize;

  (* Step 3': feed ipad ^ okey to the inner hash function *)
  hash_update hash_state_1 ipad size_ipad


(* Update running hmac function *)
val update : (state :uint32s) ->
             (data  :bytes {disjoint state data}) ->
             (len   :u32)
             -> STL unit
                  (requires (fun h -> live h state /\ live h data))
                  (ensures  (fun h0 r h1 -> live h1 state /\ live h1 data /\ modifies_1 state h0 h1))

let update state data len =
  (* Select the part of the state used by the inner hash function *)
  let hash_state_1 = sub state pos_hash1_state size_hash1_state in
  
  (* Step 3'' and Step 4: Feed the message to the inner hash function *)
  hash_update hash_state_1 data datalen


(* Compute the final value of the hash from the last hash value *)
val finish: (mac   :bytes   { length hash = v hashsize }) ->
            (state :uint32s { disjoint state mac })
            -> STL unit
                 (requires (fun h -> live h mac /\ live h state))
                 (ensures  (fun h0 r h1 -> live h1 mac /\ live h1 state /\ modifies_2 mac state h0 h1))

let finish mac state =
  (* Select the part of the state used by the inner hash function *)
  let hash_state_1 = sub state pos_hash1_state size_hash1_state in

  (* Select the part of the state used by the outter hash function *)
  let hash_state_2 = sub state pos_hash2_state size_hash2_state in

  (* Initialize the underlying outer hash function *)
  hash_init hash_state_2;
  
  (* Select the part of the state used for HMAC *)
  let hmac_state = sub state pos_hmac_state size_hmac_state in
  let okey = sub hmac_state pos_key size_key in

  (* Set initial values for opad *)
  let opad = sub hmac_state pos_opad size_opad in
  setall opad size_opad 0x5cuy;

  (* Step 5: xor "result of step 1" with opad *)
  xor_bytes opad okey size_opad;

  (* Step 6: finalize inner hash *)
  hash_finish final_hash1 hash_state_1;

  (* Step 6': feed (opad ^ okey) and the final inner hash to the outer hash *)
  hash_update hash_state_2 opad size_opad;
  hash_update hash_state_2 final_hash1 hashsize;

  (* Step 7: finalize outer hash to compute the final mac *)
  hash_finish mac hash_state_2


val hmac_core': (memb   :uint32s) ->
                (mac    :bytes { length mac >= v hashsize /\ disjoint mac memb}) ->
                (key    :bytes { disjoint key memb /\ disjoint key mac }) ->
                (keylen :u32   { length key = v keylen }) ->
                (data   :bytes { disjoint data memb /\ disjoint data mac /\ disjoint data key }) ->
                (len    :u32   { length data = v len })
                -> STL unit
                      (requires (fun h -> live h mac /\ live h key /\ live h data))
                      (ensures  (fun h0 r h1 -> live h1 memb /\ live h1 mac /\ modifies_2 memb mac h0 h1))

let hmac_core' memb mac key keylen data len =
  let state = memb in
  init state key keylen;
  update state data len;
  finish mac state


(* Compute the mac of some bytes *)
val hmac_core: (mac    :bytes { length mac >= v hashsize }) ->
               (key    :bytes { disjoint key mac }) ->
               (keylen :u32   { length key = v keylen }) ->
               (data   :bytes { disjoint data mac /\ disjoint data key }) ->
               (len    :u32   { length data = v len })
               -> STL unit
                     (requires (fun h -> live h mac /\ live h key /\ live h data))
                     (ensures  (fun h0 r h1 -> live h1 mac /\ modifies_1 mac h0 h1))

let hmac_core mac key keylen data len =

  (** Push frame *)
  (**) push_frame();

  (* Compute size of objects *)
  let _statelen = size_hash_state @+ size_hash_state @+ size_key @+ size_key @+ size_key in

  (* Allocate the memory block for the underlying function *)
  let memblen = _statelen in
  let memb = create 0ul memblen in

  (* Call the hmac function *)
  hmac_core' memb mac key keylen data len ;

  (** Pop frame *)
  (**) pop_frame()



(* Exposing SHA2-256 for test vectors *)
val hmac_sha256 : (mac     :bytes { length mac = v hl }) ->
                  (key     :bytes { disjoint key mac }) ->
                  (keylen  :u32   { length key = v keylen }) ->
                  (data    :bytes { disjoint mac data }) ->
                  (datalen :u32   {5 * v bl + v hl + v datalen < pow2 32 /\ length data = v datalen /\ v datalen + v bl <= pow2 32})
                  -> STL unit
                        (requires (fun h -> live h mac /\ live h data /\ live h key))
                        (ensures  (fun h0 r h1 -> live h1 mac /\ modifies_1 mac h0 h1))

let hmac_sha256 mac key keylen data datalen = hmac_core mac key keylen data datalen

