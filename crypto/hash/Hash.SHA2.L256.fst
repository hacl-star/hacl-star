module Hash.SHA2.L256

open FStar.Mul
open FStar.Ghost
open FStar.HyperStack
open FStar.HST
open FStar.Buffer

open Hacl.Cast
open Hacl.UInt8
open Hacl.UInt32
open Hacl.SBuffer
open Hacl.Conversions
open Hacl.Operations
open FStar.UInt32

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

let u8_to_s8 = Hacl.Cast.uint8_to_sint8
let u32_to_s32 = Hacl.Cast.uint32_to_sint32
let u32_to_s64 = Hacl.Cast.uint32_to_sint64
let s32_to_s64 = Hacl.Cast.sint32_to_sint64
let u64_to_s64 = Hacl.Cast.uint64_to_sint64


#set-options "--lax"

//
// SHA-256
//

(* Define algorithm parameters *)
let hashsize    = 32ul  // 256 bits = 32 bytes (Final hash output size)
let blocksize   = 64ul  // 512 bits = 64 bytes (Working data block size)
let size_md_len = 8ul   // 64 bits = 8 bytes (MD pad length encoding)

(* Sizes of objects in the state *)
let size_k      = 64ul  // 2048 bits = 64 words of 32 bits (blocksize)
let size_ws     = 64ul  // 2048 bits = 64 words of 32 bits (blocksize)
let size_whash  = 8ul   // 256 bits = 8 words of 32 bits (hashsize/4)
let size_wblock = 16ul  // 512 bits = 64 words of 32 bits (blocksize/4)
let size_wblocklen = 1ul // 32 bits (UInt32)
let size_count  = 1ul   // 32 bits (UInt32)
let size_state  = size_k +^ size_ws +^ size_whash +^ size_wblock +^ size_wblocklen +^ size_count

(* Positions of objects in the state *)
let pos_k         = 0ul
let pos_ws        = size_k
let pos_whash     = size_k +^ size_ws
let pos_wblock    = size_k +^ size_ws +^ size_whash
let pos_wblocklen = size_k +^ size_ws +^ size_whash +^ size_wblock
let pos_count     = size_k +^ size_ws +^ size_whash +^ size_wblock  +^ 1ul



(* [FIPS 180-4] section 4.1.2 *)
val _Ch: x:s32 -> y:s32 -> z:s32 -> Tot s32
let _Ch x y z = S32.logxor (S32.logand x y) (S32.logand (S32.lognot x) z)

val _Maj: x:s32 -> y:s32 -> z:s32 -> Tot s32
let _Maj x y z = S32.logxor (S32.logand x y) (S32.logxor (S32.logand x z) (S32.logand y z))

val _Sigma0: x:s32 -> Tot s32
let _Sigma0 x = S32.logxor (rotate_right x 2ul) (S32.logxor (rotate_right x 13ul) (rotate_right x 22ul))

val _Sigma1: x:s32 -> Tot s32
let _Sigma1 x = S32.logxor (rotate_right x 6ul) (S32.logxor (rotate_right x 11ul) (rotate_right x 25ul))

val _sigma0: x:s32 -> Tot s32
let _sigma0 x = S32.logxor (rotate_right x 7ul) (S32.logxor (rotate_right x 18ul) (S32.shift_right x 3ul))

val _sigma1: x:s32 -> Tot s32
let _sigma1 x = S32.logxor (rotate_right x 17ul) (S32.logxor (rotate_right x 19ul) (S32.shift_right x 10ul))



(* [FIPS 180-4] section 4.2.2 *)
val set_k: state:uint32s{length state = U32.v size_state}
  -> STL unit (requires (fun h -> live h state))
             (ensures (fun h0 _ h1 -> live h1 state /\ modifies_1 state h0 h1))

let set_k state =
  admit(); // This is just for verification timeout
  let k = SB.sub state pos_k size_k in
  k.(0ul)  <- (u32_to_s32 0x428a2f98ul);
  k.(1ul)  <- (u32_to_s32 0x71374491ul);
  k.(2ul)  <- (u32_to_s32 0xb5c0fbcful);
  k.(3ul)  <- (u32_to_s32 0xe9b5dba5ul);
  k.(4ul)  <- (u32_to_s32 0x3956c25bul);
  k.(5ul)  <- (u32_to_s32 0x59f111f1ul);
  k.(6ul)  <- (u32_to_s32 0x923f82a4ul);
  k.(7ul)  <- (u32_to_s32 0xab1c5ed5ul);
  k.(8ul)  <- (u32_to_s32 0xd807aa98ul);
  k.(9ul)  <- (u32_to_s32 0x12835b01ul);
  k.(10ul) <- (u32_to_s32 0x243185beul);
  k.(11ul) <- (u32_to_s32 0x550c7dc3ul);
  k.(12ul) <- (u32_to_s32 0x72be5d74ul);
  k.(13ul) <- (u32_to_s32 0x80deb1feul);
  k.(14ul) <- (u32_to_s32 0x9bdc06a7ul);
  k.(15ul) <- (u32_to_s32 0xc19bf174ul);
  k.(16ul) <- (u32_to_s32 0xe49b69c1ul);
  k.(17ul) <- (u32_to_s32 0xefbe4786ul);
  k.(18ul) <- (u32_to_s32 0x0fc19dc6ul);
  k.(19ul) <- (u32_to_s32 0x240ca1ccul);
  k.(20ul) <- (u32_to_s32 0x2de92c6ful);
  k.(21ul) <- (u32_to_s32 0x4a7484aaul);
  k.(22ul) <- (u32_to_s32 0x5cb0a9dcul);
  k.(23ul) <- (u32_to_s32 0x76f988daul);
  k.(24ul) <- (u32_to_s32 0x983e5152ul);
  k.(25ul) <- (u32_to_s32 0xa831c66dul);
  k.(26ul) <- (u32_to_s32 0xb00327c8ul);
  k.(27ul) <- (u32_to_s32 0xbf597fc7ul);
  k.(28ul) <- (u32_to_s32 0xc6e00bf3ul);
  k.(29ul) <- (u32_to_s32 0xd5a79147ul);
  k.(30ul) <- (u32_to_s32 0x06ca6351ul);
  k.(31ul) <- (u32_to_s32 0x14292967ul);
  k.(32ul) <- (u32_to_s32 0x27b70a85ul);
  k.(33ul) <- (u32_to_s32 0x2e1b2138ul);
  k.(34ul) <- (u32_to_s32 0x4d2c6dfcul);
  k.(35ul) <- (u32_to_s32 0x53380d13ul);
  k.(36ul) <- (u32_to_s32 0x650a7354ul);
  k.(37ul) <- (u32_to_s32 0x766a0abbul);
  k.(38ul) <- (u32_to_s32 0x81c2c92eul);
  k.(39ul) <- (u32_to_s32 0x92722c85ul);
  k.(40ul) <- (u32_to_s32 0xa2bfe8a1ul);
  k.(41ul) <- (u32_to_s32 0xa81a664bul);
  k.(42ul) <- (u32_to_s32 0xc24b8b70ul);
  k.(43ul) <- (u32_to_s32 0xc76c51a3ul);
  k.(44ul) <- (u32_to_s32 0xd192e819ul);
  k.(45ul) <- (u32_to_s32 0xd6990624ul);
  k.(46ul) <- (u32_to_s32 0xf40e3585ul);
  k.(47ul) <- (u32_to_s32 0x106aa070ul);
  k.(48ul) <- (u32_to_s32 0x19a4c116ul);
  k.(49ul) <- (u32_to_s32 0x1e376c08ul);
  k.(50ul) <- (u32_to_s32 0x2748774cul);
  k.(51ul) <- (u32_to_s32 0x34b0bcb5ul);
  k.(52ul) <- (u32_to_s32 0x391c0cb3ul);
  k.(53ul) <- (u32_to_s32 0x4ed8aa4aul);
  k.(54ul) <- (u32_to_s32 0x5b9cca4ful);
  k.(55ul) <- (u32_to_s32 0x682e6ff3ul);
  k.(56ul) <- (u32_to_s32 0x748f82eeul);
  k.(57ul) <- (u32_to_s32 0x78a5636ful);
  k.(58ul) <- (u32_to_s32 0x84c87814ul);
  k.(59ul) <- (u32_to_s32 0x8cc70208ul);
  k.(60ul) <- (u32_to_s32 0x90befffaul);
  k.(61ul) <- (u32_to_s32 0xa4506cebul);
  k.(62ul) <- (u32_to_s32 0xbef9a3f7ul);
  k.(63ul) <- (u32_to_s32 0xc67178f2ul)


val set_whash: state:uint32s{length state = U32.v size_state}
  -> STL unit (requires (fun h -> live h state))
             (ensures (fun h0 _ h1 -> live h1 state /\ modifies_1 state h0 h1))

let set_whash state =
  admit(); // This is just for verification timeout
  let whash = SB.sub state pos_whash size_whash in
  whash.(0ul) <- (u32_to_s32 0x6a09e667ul);
  whash.(1ul) <- (u32_to_s32 0xbb67ae85ul);
  whash.(2ul) <- (u32_to_s32 0x3c6ef372ul);
  whash.(3ul) <- (u32_to_s32 0xa54ff53aul);
  whash.(4ul) <- (u32_to_s32 0x510e527ful);
  whash.(5ul) <- (u32_to_s32 0x9b05688cul);
  whash.(6ul) <- (u32_to_s32 0x1f83d9abul);
  whash.(7ul) <- (u32_to_s32 0x5be0cd19ul)


(* [FIPS 180-4] section 5.1.1 *)
(* l + 1 + k ≡ 448 mod 512 *)
(* Compute the number of blocks to store data and padding
 * We have le number of blocks for the data and we add
 * potentially one block for the partial block and another
 * for the padding. *)
val nblocks: x:u32{v x + 8 < pow2 32} -> Tot (n:u32{v n >= 1})
let nblocks x = (div ((x +^ 8ul) -^ (rem (x +^ 8ul) 64ul)) 64ul) +^ 1ul


(* Compute the pad length *)
(* Leakage resistance: the length of the partial block/padding is secret *)
(* val pad_length: rlen:s32{S32.v rlen - 64 < pow2 32} -> Tot (n:s32{S32.v n <= 64 /\ S32.v n >= 1}) *)
(* let pad_length rlen = *)
(*   let sec64 = u32_to_s32 64ul in *)
(*   let sec56 = u32_to_s32 56ul in *)
(*   admit(); // BB.TODO: More SMT automation needed. *)
(*   S32.logor (S32.logand (S32.lt_mask (S32.rem rlen sec64) sec56) *)
(*                         (S32.sub sec56 (S32.rem rlen sec64))) *)
(*             (S32.logand (S32.lognot (S32.lt_mask (S32.rem rlen sec64) sec56)) *)
(*                         (S32.sub (S32.add sec64 sec56) (S32.rem rlen sec64))) *)


(* Pad *)
val pad': (memb   :bytes{length memb >= 8}) ->
          (output :bytes{length output = v blocksize /\ disjoint output memb}) ->
          (data   :bytes{length data = v blocksize /\ disjoint data memb /\ disjoint data output}) ->
          (len    :s32  {S32.v len + 1 <= length data}) ->
          (encodedlen :s64{S64.v encodedlen + S32.v len < pow2 64})
          -> STL unit
                (requires (fun h -> live h memb /\ live h output /\ live h data))
                (ensures  (fun h0 r h1 -> live h1 memb /\ live h1 output /\ modifies_2 memb output h0 h1))

let pad' memb output data len encodedlen =

  (* Retrieve memory *)
  let len_64 = memb in
  
  (* Set the output to be all zeros except for the first
   * byte of the padding. BB.TODO: Maybe we can improve perfs. *)
  let pos1 = len in
  let pos2 = S32.add len (u32_to_s32 1ul) in
  setbuf3 output blocksize (u8_to_s8 0x00uy) (u8_to_s8 0x80uy) (u8_to_s8 0x00uy) pos1 pos2;

  (* Masked copy of the partial block of data in the output *)
  (* Leakage resistance: the copy is done in constant time and
  does not leak the length of the partial block but only the
  the size of the block *)
  copymask data (u32_to_s32 0ul) len output blocksize;

  (* Encode the length into big-endian bytes *)
  (* Leakage resistance: position and length of the MD encoded
  length are public, note that the input has size 2^64 maximum *)
  be_bytes_of_sint64 len_64 encodedlen;
  SB.blit len_64 0ul output (blocksize -^ 8ul) 8ul


val pad: (output :bytes{length output = v blocksize}) ->
         (data   :bytes{length data = v blocksize /\ disjoint data output}) ->
         (len    :s32  {S32.v len + 1 <= length data /\ S32.v len + 8 <= length output}) ->
         (encodedlen :s64{S64.v encodedlen + S32.v len < pow2 64})
         -> STL unit
              (requires (fun h -> live h output /\ live h data))
              (ensures  (fun h0 r h1 -> live h1 output /\ modifies_1 output h0 h1))

let pad output data len encodedlen =
  (* Push frame *)
  (**) push_frame ();

  (* BB.FUTURE: Because of the inherent limitations of the buffer
   * representation we currently need 8 bytes more for casts here
   * This whole wrapping function should disappear after fix *)
  let memblen = 8ul in
  let memb = create (u8_to_s8 0uy) memblen in

  (* Call the padding function *)
  pad' memb output data len encodedlen;

  (* Pop frame *)
  (**) admit(); // BB.TODO: Improve perf. (trivial)
  (**) pop_frame()


(* [FIPS 180-4] section 6.2.2 *)
(* Step 1 : Scheduling function for sixty-four 32bit words *)
val ws_upd: (state  :uint32s {length state = v size_state}) ->
            (t      :u32)
                   -> STL unit
                        (requires (fun h -> live h state))
                        (ensures  (fun h0 r h1 -> live h1 state /\ modifies_1 state h0 h1))

let rec ws_upd state t =
  (* Get necessary information from the state *)
  let ws = SB.sub state pos_ws size_ws in
  let wblock = SB.sub state pos_wblock size_wblock in

  (* Perform computations *)
  if t <^ 16ul then begin
    ws.(t) <- wblock.(t);
    ws_upd state (t +^ 1ul) end
  else if t <^ 64ul then begin
    let _t16 = ws.(t -^ 16ul) in
    let _t15 = ws.(t -^ 15ul) in
    let _t7  = ws.(t -^ 7ul) in
    let _t2  = ws.(t -^ 2ul) in

    let v0 = _sigma1 _t2 in
    let v1 = _sigma0 _t15 in

    let v = (S32.add_mod v0
                     (S32.add_mod _t7
                              (S32.add_mod v1 _t16)))
    in ws.(t) <- v;
    ws_upd state (t +^ 1ul) end
  else ()


(* [FIPS 180-4] section 5.3.3 *)
(* Define the initial hash value *)
val init : state:uint32s{length state = v size_state}
  -> STL unit
        (requires (fun h -> live h state))
        (ensures  (fun h0 r h1 -> live h1 state /\ modifies_1 state h0 h1))

let init state =
  (* Initialize constant k *)
  set_k state;
  (* The schedule state is left to zeros *)
  (* Initialize working hash *)
  set_whash state
  (* The data block is left to zeros *)
  (* The length of the (partial) block is left to 0ul *)
  (* The total number of blocks is left to 0ul *)


(* Step 3 : Perform logical operations on the working variables *)
val update_inner : (state :uint32s{length state = v size_state}) ->
                   (t     :u32) ->
                   (t1    :s32) ->
                   (t2    :s32)
                   -> STL unit
                         (requires (fun h -> live h state ))
                         (ensures  (fun h0 r h1 -> live h1 state /\ modifies_1 state h0 h1))

let rec update_inner state t t1 t2 =
  if t <^ 64ul then begin
  
    (* Get necessary information from the state *)
    let whash = SB.sub state pos_whash size_whash in
    let k = SB.sub state pos_k size_k in
    let ws = SB.sub state pos_ws size_ws in

    (* Perform computations *)
    let _h  = whash.(7ul) in
    let _kt = k.(t) in
    let _wt = ws.(t) in
    let v0 = _Sigma1 whash.(4ul) in
    let v1 = _Ch whash.(4ul) whash.(5ul) whash.(6ul) in
    let t1 = S32.add_mod _h (S32.add_mod v0 (S32.add_mod v1 (S32.add_mod _kt _wt))) in
    let z0 = _Sigma0 whash.(0ul) in
    let z1 = _Maj whash.(0ul) whash.(1ul) whash.(2ul) in
    let t2 = S32.add_mod z0 z1 in
    let _d = whash.(3ul) in

    (* Store the new working hash in the state *)
    whash.(7ul) <- whash.(6ul);
    whash.(6ul) <- whash.(5ul);
    whash.(5ul) <- whash.(4ul);
    whash.(4ul) <- (S32.add_mod _d t1);
    whash.(3ul) <- whash.(2ul);
    whash.(2ul) <- whash.(1ul);
    whash.(1ul) <- whash.(0ul);
    whash.(0ul) <- (S32.add_mod t1 t2);
    update_inner state (t +^ 1ul) t1 t2 end
  else ()


val update_step : (state :uint32s{length state = v size_state})
                  -> STL unit
                        (requires (fun h -> live h state))
                        (ensures  (fun h0 r h1 -> live h1 state /\ modifies_1 state h0 h1))

let update_step state =
  admit(); // This is just for verification timeout
  
  (* Get necessary information from the state *)
  let whash = SB.sub state pos_whash size_whash in
  
  (* Step 1 : Scheduling function for sixty-four 32 bit words *)
  ws_upd state 0ul;

  (* Step 2 : Initialize the eight working variables *)
  let input_state0 = index whash 0ul in
  let input_state1 = index whash 1ul in
  let input_state2 = index whash 2ul in
  let input_state3 = index whash 3ul in
  let input_state4 = index whash 4ul in
  let input_state5 = index whash 5ul in
  let input_state6 = index whash 6ul in
  let input_state7 = index whash 7ul in

  (* Step 3 : Perform logical operations on the working variables *)
  update_inner state 0ul (u32_to_s32 0ul) (u32_to_s32 0ul);

  (* Step 4 : Compute the ith intermediate hash value *)
  whash.(0ul) <- (S32.add_mod whash.(0ul) input_state0);
  whash.(1ul) <- (S32.add_mod whash.(1ul) input_state1);
  whash.(2ul) <- (S32.add_mod whash.(2ul) input_state2);
  whash.(3ul) <- (S32.add_mod whash.(3ul) input_state3);
  whash.(4ul) <- (S32.add_mod whash.(4ul) input_state4);
  whash.(5ul) <- (S32.add_mod whash.(5ul) input_state5);
  whash.(6ul) <- (S32.add_mod whash.(6ul) input_state6);
  whash.(7ul) <- (S32.add_mod whash.(7ul) input_state7);

  (* Increment the total number of blocks processed *)
  state.(pos_count) <- S32.add state.(pos_count) (u32_to_s32 1ul)


val update' : (memb  :bytes{length memb >= v blocksize}) ->
              (state :uint32s{length state = v size_state /\ disjoint state memb}) ->
              (data  :bytes{length data >= v blocksize /\ (length data) % (v blocksize) = 0
                           /\ disjoint state memb /\ disjoint state data }) ->
              (len   :s32{S32.v len <= length data}) ->
              (rounds:u32{v rounds * v blocksize < pow2 32}) ->
              (i     :u32{v i >= 0})
              -> STL unit
                    (requires (fun h -> live h memb /\ live h state /\ live h data))
                    (ensures  (fun h0 r h1 -> live h1 memb /\ live h1 state /\ modifies_2 memb state h0 h1))

let rec update' memb state data len rounds i =

  (* Get necessary information from the state *)
  let wblock = SB.sub state pos_wblock size_wblock in

  (* Flatten the working block *)
  (* BB.FUTURE: Inherent conversion copies from wblock
   * to block due to the representation of the buffers. *)
  let cblock = SB.sub memb 0ul blocksize in
  be_bytes_of_uint32s cblock wblock size_wblock;

  (* Get the data required to fill the partial block *)
  let cpos = i *^ blocksize in
  let cdata = SB.sub data cpos blocksize in
  
  (* Complete the partial block with data *)
  (* Leakage resistance: filling the partial block must not leak
   * it's current length, so the data block must have the length
   * blocksize to make sure the copy is done in constant time *)
  copymask cdata (u32_to_s32 0ul) (u32_to_s32 blocksize) cblock blocksize;

  (* Store the new working (potentially partial) block in the state *)
  be_uint32s_of_bytes wblock cblock blocksize;

  if i <^ rounds then begin

    (* Update the current length of the partial block after processing *)
    state.(pos_wblocklen) <- u32_to_s32 blocksize;
    
    (* Process the block *)
    update_step state;
    update' memb state data len rounds (i +^ 1ul) end

  else
  
  (* Update the current length of the partial block after processing *)
  state.(pos_wblocklen) <- S32.sub len (u32_to_s32 cpos)
  

(* [FIPS 180-4] section 6.2.2 *)
(* Update running hash function *)
val update : (state :uint32s{length state = v size_state}) ->
             (data  :bytes {length data >= v blocksize /\ (length data) % (v blocksize) = 0 /\ disjoint state data}) ->
             (len   :u32{v len + 8 < pow2 32 /\ v len <= length data})
              -> STL unit
                    (requires (fun h -> live h state /\ live h data))
                    (ensures  (fun h0 r h1 -> live h1 state /\ modifies_1 state h0 h1))

let update state data len =

  (* Push frame *)
  (**) push_frame();

  let memblen = blocksize in
  let memb = create (u8_to_s8 0uy) memblen in
  
  (* Compute the number of rounds to process the data *)
  let rounds = nblocks len -^ 1ul in
  
  (* Perform updates for all blocks except the last *)
  update' memb state data (u32_to_s32 len) rounds 0ul;

  (* Pop frame *)
  (**) pop_frame()
  

(* Compute the final value of the hash from the last hash value *)
val finish_1': (memb  :bytes{length memb >= 2 * v blocksize}) ->
               (state :uint32s{length state = v size_state /\ disjoint memb state})
             -> STL unit
                   (requires (fun h -> live h memb /\ live h state))
                   (ensures  (fun h0 r h1 -> live h1 memb /\ live h1 state /\ modifies_2 memb state h0 h1))

let finish_1' memb state =

  (* Use the provided memory for conversions *)
  let fblock = SB.sub memb 0ul blocksize in
  let cblock = SB.sub memb blocksize blocksize in

  (* Retreive the partial block from the state *)
  let wblock = SB.sub state pos_wblock size_wblock in
  be_bytes_of_uint32s cblock wblock blocksize;

  (* Retrive the number of blocks and the partial block length *)
  let count = state.(pos_count) in
  let partiallen = state.(pos_wblocklen) in

  (* Compute the final length to be encoded in the padding in bits
   * represented as UInt64 to make sure that the multiplication
   * will not overflow inside a UInt32. 
   * The cast to UInt64 is specific to the SHA2-224 and SHA2-256 *)   
  let currentlen = S64.mul (s32_to_s64 count) (u32_to_s64 blocksize) in
  let totlenbytes = S64.add currentlen (s32_to_s64 partiallen) in
  let totlen = S64.mul totlenbytes (u64_to_s64 8uL) in

  (* Pad the data in constant time *)
  pad fblock cblock partiallen totlen;

  (* Store the new working block in the state *)
  be_uint32s_of_bytes wblock fblock blocksize;

  (* Feed the last block to the update function for one round *)
  update_step state


val finish_1: (state :uint32s{length state = v size_state})
             -> STL unit
                   (requires (fun h -> live h state))
                   (ensures  (fun h0 r h1 -> live h1 state /\ modifies_1 state h0 h1))

let finish_1 state =

  (* Push frame *)
  (**) push_frame();

  (* Allocate the memory required to flatten wblock *)
  let memblen = 2ul *^ blocksize in
  let memb = create (u8_to_s8 0uy) memblen in

  finish_1' memb state;

  (* Pop frame *)
  (**) admit(); // BB.TODO: Improve perf. (trivial)
  (**) pop_frame()


val finish_2: (hash  :bytes{length hash >= v hashsize}) ->
             (state :uint32s{length state = v size_state /\ disjoint state hash })
             -> STL unit
                   (requires (fun h -> live h hash /\ live h state))
                   (ensures  (fun h0 r h1 -> live h1 hash /\ modifies_1 hash h0 h1))

let finish_2 hash state =
  (* Store the final hash to the output location *)
  let whash = SB.sub state pos_whash size_whash in
  be_bytes_of_uint32s hash whash hashsize


(* Compute the final value of the hash from the last hash value *)
val finish: (hash  :bytes{length hash >= v hashsize}) ->
            (state :uint32s{length state = v size_state /\ disjoint state hash})
            -> STL unit
                 (requires (fun h -> live h hash /\ live h state))
                 (ensures  (fun h0 r h1 -> live h1 hash /\ live h1 state /\ modifies_2 hash state h0 h1))

let finish hash state =
  (* Compute the final state *)
  finish_1 state;
  (* Flatten and store the final hash *)
  finish_2 hash state


(* Compute the sha256 hash of the data *)
val sha256': (memb :uint32s{ length memb >= v size_state}) ->
             (hash :bytes{ length hash >= v hashsize /\ disjoint hash memb}) ->
             (data :bytes{ length data >= v blocksize /\ (length data) % (v blocksize) = 0
                         /\ disjoint data memb /\ disjoint data hash}) ->
             (len  :u32{v len + 8 < pow2 32 /\ v len <= length data})
             -> STL unit
                   (requires (fun h -> live h memb /\ live h hash /\ live h data))
                   (ensures  (fun h0 r h1 -> live h1 memb /\ live h1 hash /\ modifies_2 memb hash h0 h1))

let sha256' memb hash data len =
  let state = SB.sub memb 0ul size_state in
  init state;
  update state data len;
  finish hash state


(* Compute the sha256 hash of some bytes *)
val sha256: (hash :bytes{ length hash >= v hashsize}) ->
            (data :bytes{ length data >= v blocksize /\ (length data) % (v blocksize) = 0 /\ disjoint data hash}) ->
            (len  :u32{v len + 8 < pow2 32 /\ v len <= length data})
            -> STL unit
                 (requires (fun h -> live h hash /\ live h data))
                 (ensures  (fun h0 r h1 -> live h1 hash /\ modifies_1 hash h0 h1))

let sha256 hash data len =

  (* Push frame *)
  (**) push_frame();

  (* Allocate the memory block for the underlying function *)
  let memblen = size_state in
  let memb = create (u32_to_s32 0ul) memblen in

  (* Call the sha256 function *)
  sha256' memb hash data len ;

  (* Pop frame *)
  (**) admit(); // BB.TODO: Improve perf. (trivial)
  (**) pop_frame()
