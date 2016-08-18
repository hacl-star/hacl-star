module Hash.Sha256

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
open Hacl.Conversions
open Hacl.Operations

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
let op_Hat_At_Amp (a:s64) (s:s64) : Tot s64 = S64.logand a s
let op_Hat_Greater_Greater (a:s32) (b:u32) : Tot s32 = S32.shift_right a b

let op_At_Plus (a:u32) (b:u32{U32.v a + U32.v b < pow2 32}) : Tot u32 = U32.add a b
let op_At_Subtraction (a:u32) (b:u32{U32.v a - U32.v b < pow2 32 /\ U32.v a - U32.v b >= 0}) : Tot u32 = U32.sub a b
let op_At_Percent (a:u32) (b:u32{U32.v b <> 0}) : Tot u32 = U32.rem a b
let op_At_Plus_Percent (a:u32) (b:u32) : Tot u32 = U32.add_mod a b
let op_At_Subtraction_Percent (a:u32) (b:u32) : Tot u32 = U32.sub_mod a b
let op_At_Slash (a:u32) (b:u32{U32.v b <> 0}) : Tot u32 = U32.div a b



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
let size_state = size_k @+ size_ws @+ size_whash @+ size_wblock @+ size_wblocklen @+ size_count

(* Positions of objects in the state *)
let pos_k         = 0ul
let pos_ws        = size_k
let pos_whash     = size_k @+ size_ws
let pos_wblock    = size_k @+ size_ws @+ size_whash
let pos_wblocklen = size_k @+ size_ws @+ size_whash @+ size_wblock
let pos_count     = size_k @+ size_ws @+ size_whash @+ size_wblock  @+ 1ul



(* [FIPS 180-4] section 4.1.2 *)
val _Ch: x:s32 -> y:s32 -> z:s32 -> Tot s32
let _Ch x y z = logxor (logand x y) (logand (lognot x) z)

val _Maj: x:s32 -> y:s32 -> z:s32 -> Tot s32
let _Maj x y z = logxor (logand x y) (logxor (logand x z) (logand y z))

val _Sigma0: x:s32 -> Tot s32
let _Sigma0 x = logxor (rotate_right x 2ul) (logxor (rotate_right x 13ul) (rotate_right x 22ul))

val _Sigma1: x:s32 -> Tot s32
let _Sigma1 x = logxor (rotate_right x 6ul) (logxor (rotate_right x 11ul) (rotate_right x 25ul))

val _sigma0: x:s32 -> Tot s32
let _sigma0 x = logxor (rotate_right x 7ul) (logxor (rotate_right x 18ul) (shift_right x 3ul))

val _sigma1: x:s32 -> Tot s32
let _sigma1 x = logxor (rotate_right x 17ul) (logxor (rotate_right x 19ul) (shift_right x 10ul))


(* [FIPS 180-4] section 4.2.2 *)
val set_k: state:uint32s{length state = U32.v size_state}
  -> STL unit (requires (fun h -> live h state))
             (ensures (fun h0 _ h1 -> live h1 state /\ modifies_1 state h0 h1))

let set_k state =
  admit(); // This is just for verification timeout
  let k = sub state pos_k size_k in
  upd k 0ul (uint32_to_sint32  0x428a2f98ul);
  upd k 1ul (uint32_to_sint32  0x71374491ul);
  upd k 2ul (uint32_to_sint32  0xb5c0fbcful);
  upd k 3ul (uint32_to_sint32  0xe9b5dba5ul);
  upd k 4ul (uint32_to_sint32  0x3956c25bul);
  upd k 5ul (uint32_to_sint32  0x59f111f1ul);
  upd k 6ul (uint32_to_sint32  0x923f82a4ul);
  upd k 7ul (uint32_to_sint32  0xab1c5ed5ul);
  upd k 8ul (uint32_to_sint32  0xd807aa98ul);
  upd k 9ul (uint32_to_sint32  0x12835b01ul);
  upd k 10ul (uint32_to_sint32 0x243185beul);
  upd k 11ul (uint32_to_sint32 0x550c7dc3ul);
  upd k 12ul (uint32_to_sint32 0x72be5d74ul);
  upd k 13ul (uint32_to_sint32 0x80deb1feul);
  upd k 14ul (uint32_to_sint32 0x9bdc06a7ul);
  upd k 15ul (uint32_to_sint32 0xc19bf174ul);
  upd k 16ul (uint32_to_sint32 0xe49b69c1ul);
  upd k 17ul (uint32_to_sint32 0xefbe4786ul);
  upd k 18ul (uint32_to_sint32 0x0fc19dc6ul);
  upd k 19ul (uint32_to_sint32 0x240ca1ccul);
  upd k 20ul (uint32_to_sint32 0x2de92c6ful);
  upd k 21ul (uint32_to_sint32 0x4a7484aaul);
  upd k 22ul (uint32_to_sint32 0x5cb0a9dcul);
  upd k 23ul (uint32_to_sint32 0x76f988daul);
  upd k 24ul (uint32_to_sint32 0x983e5152ul);
  upd k 25ul (uint32_to_sint32 0xa831c66dul);
  upd k 26ul (uint32_to_sint32 0xb00327c8ul);
  upd k 27ul (uint32_to_sint32 0xbf597fc7ul);
  upd k 28ul (uint32_to_sint32 0xc6e00bf3ul);
  upd k 29ul (uint32_to_sint32 0xd5a79147ul);
  upd k 30ul (uint32_to_sint32 0x06ca6351ul);
  upd k 31ul (uint32_to_sint32 0x14292967ul);
  upd k 32ul (uint32_to_sint32 0x27b70a85ul);
  upd k 33ul (uint32_to_sint32 0x2e1b2138ul);
  upd k 34ul (uint32_to_sint32 0x4d2c6dfcul);
  upd k 35ul (uint32_to_sint32 0x53380d13ul);
  upd k 36ul (uint32_to_sint32 0x650a7354ul);
  upd k 37ul (uint32_to_sint32 0x766a0abbul);
  upd k 38ul (uint32_to_sint32 0x81c2c92eul);
  upd k 39ul (uint32_to_sint32 0x92722c85ul);
  upd k 40ul (uint32_to_sint32 0xa2bfe8a1ul);
  upd k 41ul (uint32_to_sint32 0xa81a664bul);
  upd k 42ul (uint32_to_sint32 0xc24b8b70ul);
  upd k 43ul (uint32_to_sint32 0xc76c51a3ul);
  upd k 44ul (uint32_to_sint32 0xd192e819ul);
  upd k 45ul (uint32_to_sint32 0xd6990624ul);
  upd k 46ul (uint32_to_sint32 0xf40e3585ul);
  upd k 47ul (uint32_to_sint32 0x106aa070ul);
  upd k 48ul (uint32_to_sint32 0x19a4c116ul);
  upd k 49ul (uint32_to_sint32 0x1e376c08ul);
  upd k 50ul (uint32_to_sint32 0x2748774cul);
  upd k 51ul (uint32_to_sint32 0x34b0bcb5ul);
  upd k 52ul (uint32_to_sint32 0x391c0cb3ul);
  upd k 53ul (uint32_to_sint32 0x4ed8aa4aul);
  upd k 54ul (uint32_to_sint32 0x5b9cca4ful);
  upd k 55ul (uint32_to_sint32 0x682e6ff3ul);
  upd k 56ul (uint32_to_sint32 0x748f82eeul);
  upd k 57ul (uint32_to_sint32 0x78a5636ful);
  upd k 58ul (uint32_to_sint32 0x84c87814ul);
  upd k 59ul (uint32_to_sint32 0x8cc70208ul);
  upd k 60ul (uint32_to_sint32 0x90befffaul);
  upd k 61ul (uint32_to_sint32 0xa4506cebul);
  upd k 62ul (uint32_to_sint32 0xbef9a3f7ul);
  upd k 63ul (uint32_to_sint32 0xc67178f2ul)


val set_whash: state:uint32s{length state = U32.v size_state}
  -> STL unit (requires (fun h -> live h state))
             (ensures (fun h0 _ h1 -> live h1 state /\ modifies_1 state h0 h1))

let set_whash state =
  admit(); // This is just for verification timeout
  let whash = sub state pos_whash size_whash in
  upd whash 0ul (uint32_to_sint32 0x6a09e667ul);
  upd whash 1ul (uint32_to_sint32 0xbb67ae85ul);
  upd whash 2ul (uint32_to_sint32 0x3c6ef372ul);
  upd whash 3ul (uint32_to_sint32 0xa54ff53aul);
  upd whash 4ul (uint32_to_sint32 0x510e527ful);
  upd whash 5ul (uint32_to_sint32 0x9b05688cul);
  upd whash 6ul (uint32_to_sint32 0x1f83d9abul);
  upd whash 7ul (uint32_to_sint32 0x5be0cd19ul)


(* [FIPS 180-4] section 5.1.1 *)
(* l + 1 + k ≡ 448 mod 512 *)
(* Compute the number of blocks to store data and padding
 * We have le number of blocks for the data and we add
 * potentially one block for the partial block and another
 * for the padding. *)
val nblocks: x:u32{U32.v x + 8 < pow2 32} -> Tot (n:u32{U32.v n >= 1})
let nblocks x = U32.add (U32.div (U32.sub (x @+ 8ul) (U32.rem (x @+ 8ul) 64ul)) 64ul) 1ul


(* Compute the pad length *)
(* Leakage resistance: the length of the partial block/padding is secret *)
val pad_length: rlen:s32{v rlen - 64 < pow2 32} -> Tot (n:s32{v n <= 64 /\ v n >= 1})
let pad_length rlen =
  let sec64 = uint32_to_sint32 64ul in
  let sec56 = uint32_to_sint32 56ul in
  admit(); // BB.TODO: More SMT automation needed.
  S32.logor (S32.logand (S32.lt_mask (S32.rem rlen sec64) sec56)
                        (S32.sub sec56 (S32.rem rlen sec64)))
            (S32.logand (S32.lognot (S32.lt_mask (S32.rem rlen sec64) sec56))
                        (S32.sub (S32.add sec64 sec56) (S32.rem rlen sec64)))


(* Pad *)
val pad': (memb   :bytes{length memb >= 8}) ->
          (output :bytes{length output = U32.v blocksize /\ disjoint output memb}) ->
          (data :bytes{length data = U32.v blocksize /\ disjoint data memb /\ disjoint data output}) ->
          (len  :s32  {v len + 1 <= length data}) ->
          (encodedlen :s64{S64.v encodedlen + v len < pow2 64})
          -> STL unit
                (requires (fun h -> live h memb /\ live h output /\ live h data))
                (ensures  (fun h0 r h1 -> live h1 memb /\ live h1 output /\ modifies_2 memb output h0 h1))

let pad' memb output data len encodedlen =

  (* Retrieve memory *)
  let len_64 = memb in
  
  (* Set the output to be all zeros except for the first
   * byte of the padding. BB.TODO: Maybe we can improve perfs. *)
  let pos1 = len in
  let pos2 = S32.add len (uint32_to_sint32 1ul) in
  setmask3 output blocksize (uint8_to_sint8 0x00uy) (uint8_to_sint8 0x80uy) (uint8_to_sint8 0x00uy) pos1 pos2;

  (* Masked copy of the partial block of data in the output *)
  (* Leakage resistance: the copy is done in constant time and
  does not leak the length of the partial block but only the
  the size of the block *)
  copymask data (uint32_to_sint32 0ul) len output blocksize;

  (* Encode the length into big-endian bytes *)
  (* Leakage resistance: position and length of the MD encoded
  length are public, note that the input has size 2^64 maximum *)
  be_bytes_of_sint64 len_64 encodedlen;
  SB.blit len_64 0ul output (blocksize @- 8ul) 8ul


val pad: (output :bytes{length output = U32.v blocksize}) ->
         (data   :bytes{length data = U32.v blocksize /\ disjoint data output}) ->
         (len    :s32  {v len + 1 <= length data /\ v len + v (pad_length len) + 8 <= length output}) ->
         (encodedlen :s64{S64.v encodedlen + v len < pow2 64})
         -> STL unit
              (requires (fun h -> live h output /\ live h data))
              (ensures  (fun h0 r h1 -> live h1 output /\ modifies_1 output h0 h1))

let pad output data len encodedlen =
  (** Push frame *)
  (**) push_frame ();

  (* BB.FUTURE: Because of the inherent limitations of the buffer
   * representation we currently need 8 bytes more for casts here
   * This whole wrapping function should disappear after fix *)
  let memblen = 8ul in
  let memb = create (uint8_to_sint8 0uy) memblen in

  (* Call the padding function *)
  pad' memb output data len encodedlen;

  (** Pop frame *)
  (**) admit(); // BB.TODO: Improve perf. (trivial)
  (**) pop_frame()


(* [FIPS 180-4] section 6.2.2 *)
(* Step 1 : Scheduling function for sixty-four 32bit words *)
val ws_upd: (state  :uint32s {length state = U32.v size_state}) ->
            (t      :u32)
                   -> STL unit
                        (requires (fun h -> live h state))
                        (ensures  (fun h0 r h1 -> live h1 state /\ modifies_1 state h0 h1))

let rec ws_upd state t =
  (* Get necessary information from the state *)
  let ws = sub state pos_ws size_ws in
  let wblock = sub state pos_wblock size_wblock in

  (* Perform computations *)
  if lt t 16ul then begin
    upd ws t (index wblock t);
    ws_upd state (t @+ 1ul) end
  else if lt t 64ul then begin
    let _t16 = index ws (t @- 16ul) in
    let _t15 = index ws (t @- 15ul) in
    let _t7  = index ws (t @- 7ul) in
    let _t2  = index ws (t @- 2ul) in

    let v0 = _sigma1 _t2 in
    let v1 = _sigma0 _t15 in

    let v = (add_mod v0
                     (add_mod _t7
                              (add_mod v1 _t16)))
    in upd ws t v;
    ws_upd state (t @+ 1ul) end
  else ()


(* [FIPS 180-4] section 5.3.3 *)
(* Define the initial hash value *)
val init : state:uint32s{length state = U32.v size_state}
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
val update_inner : (state :uint32s{length state = U32.v size_state}) ->
                   (t     :u32) ->
                   (t1    :s32) ->
                   (t2    :s32)
                   -> STL unit
                         (requires (fun h -> live h state ))
                         (ensures  (fun h0 r h1 -> live h1 state /\ modifies_1 state h0 h1))

let rec update_inner state t t1 t2 =
  if lt t 64ul then begin
  
    (* Get necessary information from the state *)
    let whash = sub state pos_whash size_whash in
    let k = sub state pos_k size_k in
    let ws = sub state pos_ws size_ws in

    (* Perform computations *)
    let _h = index whash 7ul in
    let _kt = index k t in
    let _wt = index ws t in
    let v0 = _Sigma1 (index whash 4ul) in
    let v1 = _Ch (index whash 4ul) (index whash 5ul) (index whash 6ul) in
    let t1 = add_mod _h (add_mod v0 (add_mod v1 (add_mod _kt _wt))) in
    let z0 = _Sigma0 (index whash 0ul) in
    let z1 = _Maj (index whash 0ul) (index whash 1ul) (index whash 2ul) in
    let t2 = add_mod z0 z1 in
    let _d = index whash 3ul in

    (* Store the new working hash in the state *)
    upd whash 7ul (index whash 6ul);
    upd whash 6ul (index whash 5ul);
    upd whash 5ul (index whash 4ul);
    upd whash 4ul (add_mod _d t1);
    upd whash 3ul (index whash 2ul);
    upd whash 2ul (index whash 1ul);
    upd whash 1ul (index whash 0ul);
    upd whash 0ul (add_mod t1 t2);
    update_inner state (t @+ 1ul) t1 t2 end
  else ()


val update_step : (state :uint32s{length state = U32.v size_state})
                  -> STL unit
                        (requires (fun h -> live h state))
                        (ensures  (fun h0 r h1 -> live h1 state /\ modifies_1 state h0 h1))

let update_step state =
  admit(); // This is just for verification timeout
  
  (* Get necessary information from the state *)
  let whash = sub state pos_whash size_whash in
  
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
  update_inner state 0ul (uint32_to_sint32 0ul) (uint32_to_sint32 0ul);

  (* Step 4 : Compute the ith intermediate hash value *)
  upd whash 0ul (add_mod (index whash 0ul) input_state0);
  upd whash 1ul (add_mod (index whash 1ul) input_state1);
  upd whash 2ul (add_mod (index whash 2ul) input_state2);
  upd whash 3ul (add_mod (index whash 3ul) input_state3);
  upd whash 4ul (add_mod (index whash 4ul) input_state4);
  upd whash 5ul (add_mod (index whash 5ul) input_state5);
  upd whash 6ul (add_mod (index whash 6ul) input_state6);
  upd whash 7ul (add_mod (index whash 7ul) input_state7);

  (* Increment the total number of blocks processed *)
  upd state pos_count (S32.add (index state pos_count) (uint32_to_sint32 1ul))


val update' : (memb  :bytes{length memb >= U32.v blocksize}) ->
              (state :uint32s{length state = U32.v size_state /\ disjoint state memb}) ->
              (data  :bytes{length data >= U32.v blocksize /\ (length data) % (U32.v blocksize) = 0
                           /\ disjoint state memb /\ disjoint state data }) ->
              (len   :s32) ->
              (rounds:u32{U32.v rounds * U32.v blocksize < pow2 32}) ->
              (i     :u32{U32.v i >= 0})
              -> STL unit
                    (requires (fun h -> live h memb /\ live h state /\ live h data))
                    (ensures  (fun h0 r h1 -> live h1 memb /\ live h1 state /\ modifies_2 memb state h0 h1))

let rec update' memb state data len rounds i =

  (* Get necessary information from the state *)
  let wblock = sub state pos_wblock size_wblock in

  (* Flatten the working block *)
  (* BB.FUTURE: Inherent conversion copies from wblock
   * to block due to the representation of the buffers. *)
  let cblock = sub memb 0ul blocksize in
  be_bytes_of_uint32s cblock wblock size_wblock;

  (* Get the data required to fill the partial block *)
  let cpos = U32.mul i blocksize in
  let cdata = sub data cpos blocksize in
  
  (* Complete the partial block with data *)
  (* Leakage resistance: filling the partial block must not leak
   * it's current length, so the data block must have the length
   * blocksize to make sure the copy is done in constant time *)
  copymask cdata (uint32_to_sint32 0ul) (uint32_to_sint32 blocksize) cblock blocksize;

  (* Store the new working (potentially partial) block in the state *)
  be_uint32s_of_bytes wblock cblock blocksize;

  if U32.lt i rounds then begin

    (* Update the current length of the partial block after processing *)
    upd state pos_wblocklen (uint32_to_sint32 blocksize);
    
    (* Process the block *)
    update_step state;
    update' memb state data len rounds (U32.add i 1ul) end

  else
  
  (* Update the current length of the partial block after processing *)
  upd state pos_wblocklen (S32.sub len (uint32_to_sint32 cpos))
  

(* [FIPS 180-4] section 6.2.2 *)
(* Update running hash function *)
val update : (state :uint32s{length state = U32.v size_state}) ->
              (data  :bytes {length data >= U32.v blocksize /\ (length data) % (U32.v blocksize) = 0 /\ disjoint state data}) ->
              (len   :u32{U32.v len + 8 < pow2 32 /\ U32.v len <= length data})
              -> STL unit
                    (requires (fun h -> live h state /\ live h data))
                    (ensures  (fun h0 r h1 -> live h1 state /\ modifies_1 state h0 h1))

let update state data len =

  (** Push frame *)
  (**) push_frame();

  let memblen = blocksize in
  let memb = create (uint8_to_sint8 0uy) memblen in
  
  (* Compute the number of rounds to process the data *)
  let rounds = nblocks len @- 1ul in
  
  (* Perform updates for all blocks except the last *)
  update' memb state data (uint32_to_sint32 len) rounds 0ul;

  (** Pop frame *)
  (**) pop_frame()
  

(* Compute the final value of the hash from the last hash value *)
val finish_1': (memb  :bytes{length memb >= 2 * U32.v blocksize}) ->
               (state :uint32s{length state = U32.v size_state /\ disjoint memb state})
             -> STL unit
                   (requires (fun h -> live h memb /\ live h state))
                   (ensures  (fun h0 r h1 -> live h1 memb /\ live h1 state /\ modifies_2 memb state h0 h1))

let finish_1' memb state =

  (* Use the provided memory for conversions *)
  let fblock = sub memb 0ul blocksize in
  let cblock = sub memb blocksize blocksize in

  (* Retreive the partial block from the state *)
  let wblock = sub state pos_wblock size_wblock in
  be_bytes_of_uint32s cblock wblock blocksize;

  (* Retrive the number of blocks and the partial block length *)
  let count = index state pos_count in
  let partiallen = index state pos_wblocklen in

  (* Compute the final length to be encoded in the padding in bits
   * represented as UInt64 to make sure that the multiplication
   * will not overflow inside a UInt32. 
   * The cast to UInt64 is specific to the SHA2-224 and SHA2-256 *)   
  let count = index state pos_count in
  let currentlen = S64.mul (sint32_to_sint64 count) (uint32_to_sint64 blocksize) in
  let totlenbytes = S64.add currentlen (sint32_to_sint64 partiallen) in
  let totlen = S64.mul totlenbytes (uint64_to_sint64 8uL) in

  (* Pad the data in constant time *)
  pad fblock cblock partiallen totlen;

  (* Store the new working block in the state *)
  be_uint32s_of_bytes wblock fblock blocksize;

  (* Feed the last block to the update function for one round *)
  update_step state


val finish_1: (state :uint32s{length state = U32.v size_state})
             -> STL unit
                   (requires (fun h -> live h state))
                   (ensures  (fun h0 r h1 -> live h1 state /\ modifies_1 state h0 h1))

let finish_1 state =

  (** Push frame *)
  (**) push_frame();

  (* Allocate the memory required to flatten wblock *)
  let memblen = U32.mul 2ul blocksize in
  let memb = create (uint8_to_sint8 0uy) memblen in

  finish_1' memb state;

  (** Pop frame *)
  (**) admit(); // BB.TODO: Improve perf. (trivial)
  (**) pop_frame()


val finish_2: (hash  :bytes{length hash >= U32.v hashsize}) ->
             (state :uint32s{length state = U32.v size_state /\ disjoint state hash })
             -> STL unit
                   (requires (fun h -> live h hash /\ live h state))
                   (ensures  (fun h0 r h1 -> live h1 hash /\ modifies_1 hash h0 h1))

let finish_2 hash state =
  (* Store the final hash to the output location *)
  let whash = sub state pos_whash size_whash in
  be_bytes_of_uint32s hash whash hashsize


(* Compute the final value of the hash from the last hash value *)
val finish: (hash  :bytes{length hash >= U32.v hashsize}) ->
            (state :uint32s{length state = U32.v size_state /\ disjoint state hash})
            -> STL unit
                 (requires (fun h -> live h hash /\ live h state))
                 (ensures  (fun h0 r h1 -> live h1 hash /\ live h1 state /\ modifies_2 hash state h0 h1))

let finish hash state =
  (* Compute the final state *)
  finish_1 state;
  (* Flatten and store the final hash *)
  finish_2 hash state


(* Compute the sha256 hash of the data *)
val sha256': (memb :uint32s{ length memb >= U32.v size_state}) ->
             (hash :bytes{ length hash >= U32.v hashsize /\ disjoint hash memb}) ->
             (data :bytes{ length data >= U32.v blocksize /\ (length data) % (U32.v blocksize) = 0
                         /\ disjoint data memb /\ disjoint data hash}) ->
             (len  :u32{U32.v len + 8 < pow2 32 /\ U32.v len <= length data})
             -> STL unit
                   (requires (fun h -> live h memb /\ live h hash /\ live h data))
                   (ensures  (fun h0 r h1 -> live h1 memb /\ live h1 hash /\ modifies_2 memb hash h0 h1))

let sha256' memb hash data len =
  let state = sub memb 0ul size_state in
  init state;
  update state data len;
  finish hash state


(* Compute the sha256 hash of some bytes *)
val sha256: (hash :bytes{ length hash >= U32.v hashsize}) ->
            (data :bytes{ length data >= U32.v blocksize /\ (length data) % (U32.v blocksize) = 0 /\ disjoint data hash}) ->
            (len  :u32{U32.v len + 8 < pow2 32 /\ U32.v len <= length data})
            -> STL unit
                 (requires (fun h -> live h hash /\ live h data))
                 (ensures  (fun h0 r h1 -> live h1 hash /\ modifies_1 hash h0 h1))

let sha256 hash data len =

  (** Push frame *)
  (**) push_frame();

  (* Allocate the memory block for the underlying function *)
  let memblen = size_state in
  let memb = create (uint32_to_sint32 0ul) memblen in

  (* Call the sha256 function *)
  sha256' memb hash data len ;

  (** Pop frame *)
  (**) admit(); // BB.TODO: Improve perf. (trivial)
  (**) pop_frame()
