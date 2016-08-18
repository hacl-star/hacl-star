module HMAC.B

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
let op_At_Plus = U32.add_mod


(* Define parameters *)
let hash = Hash.Sha256.sha256
let hashsize = Hash.Sha256.hashsize
let blocksize = Hash.Sha256.blocksize
let hl = hashsize
let bl = blocksize



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



(* Size and positions of objects in memb *)
let size_ipad = bl
let size_opad = bl
let size_okey = bl
let size_s3 = bl @+ bl
let size_s6 = bl @+ bl
let size_memb = size_ipad @+ size_opad @+ size_okey @+ size_s3 @+ size_s6

let pos_ipad = 0ul
let pos_opad = bl
let pos_okey = bl @+ bl
let pos_s3 = bl @+ bl @+ bl
let pos_s6 = bl @+ bl @+ bl @+ bl @+ bl


(* Define the internal function *)
val hmac_core' :  (memb    :bytes {length memb = U32.v size_memb}) ->
                  (mac     :bytes {length mac = U32.v hl /\ disjoint mac memb }) ->
                  (key     :bytes {length key % (U32.v bl) = 0 /\ disjoint key memb }) ->
                  (keylen  :u32   {U32.v keylen <= length key}) ->
                  (data    :bytes {length data % (U32.v bl) = 0 /\ disjoint data memb /\ disjoint mac data }) ->
                  (datalen :u32   {U32.v datalen <= length data /\ U32.v datalen + U32.v bl <= pow2 32})
                  -> STL unit
                        (requires (fun h -> live h memb /\ live h mac /\ live h data /\ live h key))
                        (ensures  (fun h0 r h1 -> live h1 memb /\ live h1 mac /\ modifies_2 memb mac h0 h1))

let hmac_core' memb mac key keylen data datalen =

  (* Define ipad and opad *)
  (**) let h0 = HST.get() in

  (* Set initial values for ipad and opad *)
  let ipad = sub memb pos_ipad size_ipad in
  setall ipad size_ipad (uint8_to_sint8 0x36uy);
  let opad = sub memb pos_opad size_opad in
  setall opad size_opad (uint8_to_sint8 0x5cuy);

  (* Create the wrapped key location *)
  let okey = sub memb pos_okey size_okey in

  (* Create the working emplacements *)
  let s3 = sub memb pos_s3 size_s3 in
  let s6 = sub memb pos_s6 size_s6 in

  (* Step 1: make sure the key has the proper length *)
  wrap_key okey key keylen;

  (* Step 2: xor "result of step 1" with ipad *)
  xor_bytes ipad okey bl;
  let s2 = ipad in

  (* Step 3: append data to "result of step 2" *)
  blit s2 0ul s3 0ul bl;
  blit data 0ul s3 bl bl;

  (* Step 4: apply H to "result of step 3" *)
  let s4 = s2 in
  hash s4 s3 (bl @+ datalen);

  (* Step 5: xor "result of step 1" with opad *)
  xor_bytes okey opad bl;
  let s5 = okey in

  (* Step 6: append "result of step 4" to "result of step 5" *)
  blit s5 0ul s6 0ul bl;
  blit s4 0ul s6 bl bl;

  (**) let h1 = HST.get() in
  (**) assert(modifies_1 memb h0 h1);

  (* Step 7: apply H to "result of step 6" *)
  hash mac s6 (bl @+ hl);

  (**) let h2 = HST.get() in
  (**) assert(modifies_2 memb mac h0 h2);
  (**) assert(live h2 memb);
  (**) assert(live h2 mac)


#reset-options "--z3timeout 20"


(* Define the main function *)
val hmac_core : (mac     :bytes {length mac = U32.v hl}) ->
                (key     :bytes {length key % (U32.v bl) = 0}) ->
                (keylen  :u32   {U32.v keylen <= length key}) ->
                (data    :bytes {length data % (U32.v bl) = 0 /\ disjoint mac data}) ->
                (datalen :u32   {U32.v datalen <= length data /\ U32.v datalen + U32.v bl <= pow2 32})
  -> STL unit
        (requires (fun h -> live h mac /\ live h data /\ live h key))
        (ensures  (fun h0 r h1 -> live h1 mac /\ modifies_1 mac h0 h1))

let hmac_core mac key keylen data datalen =

  (** Push a new frame *)
  (**) push_frame();

  let memblen = size_memb in
  let memb = create (uint8_to_sint8 0uy) memblen in

  hmac_core' memb mac key keylen data datalen;

  (** Pop the current frame *)
  (**) pop_frame()


(* Exposing SHA2-256 for test vectors *)
val hmac_sha256 : (mac     :bytes {length mac = U32.v hl}) ->
                  (key     :bytes {length key % (U32.v bl) = 0}) ->
                  (keylen  :u32   {U32.v keylen <= length key}) ->
                  (data    :bytes {length data % (U32.v bl) = 0 /\ disjoint mac data}) ->
                  (datalen :u32   {U32.v datalen <= length data /\ U32.v datalen + U32.v bl <= pow2 32})
  -> STL unit
        (requires (fun h -> live h mac /\ live h data /\ live h key))
        (ensures  (fun h0 r h1 -> live h1 mac /\ modifies_1 mac h0 h1))

let hmac_sha256 mac key keylen data datalen = hmac_core mac key keylen data datalen
