module Hacl.Hash.SHA2.L256

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
[@"substitute"]
let u8_to_s8 = Cast.uint8_to_sint8
[@"substitute"]
let u32_to_s32 = Cast.uint32_to_sint32
[@"substitute"]
let u32_to_s64 = Cast.uint32_to_sint64
[@"substitute"]
let s32_to_s8  = Cast.sint32_to_sint8
[@"substitute"]
let s32_to_s64 = Cast.sint32_to_sint64
[@"substitute"]
let u64_to_s64 = Cast.uint64_to_sint64




//
// SHA-256
//

(* Define algorithm parameters *)
inline_for_extraction let hashsize    = 32ul  // 256 bits = 32 bytes (Final hash output size)
inline_for_extraction let hashsize_32   = 8ul  // 256 bits = 8 blocks of 32 bits (Final hash output size)
inline_for_extraction let blocksize   = 64ul  // 512 bits = 64 bytes (Working data block size)
inline_for_extraction let blocksize_32  = 16ul  // 512 bits = 16 blocks of 32 bits (Working data block size)
inline_for_extraction let size_md_len = 8ul   // 64 bits = 8 bytes (MD pad length encoding)

(* Sizes of objects in the state *)
inline_for_extraction let size_k_32      = 64ul  // 2048 bits = 64 words of 32 bits (blocksize)
inline_for_extraction let size_ws_32     = 64ul  // 2048 bits = 64 words of 32 bits (blocksize)
inline_for_extraction let size_whash_32  = 8ul   // 256 bits = 8 words of 32 bits (hashsize/4)
inline_for_extraction let size_count_32  = 1ul   // 32 bits (UInt32)
inline_for_extraction let size_state  = size_k_32 +^ size_ws_32 +^ size_whash_32 +^ size_count_32

(* Positions of objects in the state *)
inline_for_extraction let pos_k_32       = 0ul
inline_for_extraction let pos_ws_32      = size_k_32
inline_for_extraction let pos_whash_32   = size_k_32 +^ size_ws_32
inline_for_extraction let pos_count_32   = size_k_32 +^ size_ws_32 +^ size_whash_32



(* [FIPS 180-4] section 4.1.2 *)
[@"substitute"]
private val _Ch: x:suint32_t -> y:suint32_t -> z:suint32_t -> Tot suint32_t
[@"substitute"]
let _Ch x y z = S32.logxor (S32.logand x y) (S32.logand (S32.lognot x) z)

[@"substitute"]
private val _Maj: x:suint32_t -> y:suint32_t -> z:suint32_t -> Tot suint32_t
[@"substitute"]
let _Maj x y z = S32.logxor (S32.logand x y) (S32.logxor (S32.logand x z) (S32.logand y z))

[@"substitute"]
private val _Sigma0: x:suint32_t -> Tot suint32_t
[@"substitute"]
let _Sigma0 x = S32.logxor (rotate_right x 2ul) (S32.logxor (rotate_right x 13ul) (rotate_right x 22ul))

[@"substitute"]
private val _Sigma1: x:suint32_t -> Tot suint32_t
[@"substitute"]
let _Sigma1 x = S32.logxor (rotate_right x 6ul) (S32.logxor (rotate_right x 11ul) (rotate_right x 25ul))

[@"substitute"]
private val _sigma0: x:suint32_t -> Tot suint32_t
[@"substitute"]
let _sigma0 x = S32.logxor (rotate_right x 7ul) (S32.logxor (rotate_right x 18ul) (S32.shift_right x 3ul))

[@"substitute"]
private val _sigma1: x:suint32_t -> Tot suint32_t
[@"substitute"]
let _sigma1 x = S32.logxor (rotate_right x 17ul) (S32.logxor (rotate_right x 19ul) (S32.shift_right x 10ul))



(* [FIPS 180-4] section 4.2.2 *)
[@"substitute"]
private val constants_set_k:
  state:suint32_p{length state = U32.v size_state} ->
  Stack unit
        (requires (fun h -> live h state))
        (ensures (fun h0 _ h1 -> live h1 state /\ modifies_1 state h0 h1))

[@"substitute"]
let constants_set_k state =
  let k = Buffer.sub state pos_k_32 size_k_32 in
  upd4 k 0ul  0x428a2f98ul 0x71374491ul 0xb5c0fbcful 0xe9b5dba5ul;
  upd4 k 4ul  0x3956c25bul 0x59f111f1ul 0x923f82a4ul 0xab1c5ed5ul;
  upd4 k 8ul  0xd807aa98ul 0x12835b01ul 0x243185beul 0x550c7dc3ul;
  upd4 k 12ul 0x72be5d74ul 0x80deb1feul 0x9bdc06a7ul 0xc19bf174ul;
  upd4 k 16ul 0xe49b69c1ul 0xefbe4786ul 0x0fc19dc6ul 0x240ca1ccul;
  upd4 k 20ul 0x2de92c6ful 0x4a7484aaul 0x5cb0a9dcul 0x76f988daul;
  upd4 k 24ul 0x983e5152ul 0xa831c66dul 0xb00327c8ul 0xbf597fc7ul;
  upd4 k 28ul 0xc6e00bf3ul 0xd5a79147ul 0x06ca6351ul 0x14292967ul;
  upd4 k 32ul 0x27b70a85ul 0x2e1b2138ul 0x4d2c6dfcul 0x53380d13ul;
  upd4 k 36ul 0x650a7354ul 0x766a0abbul 0x81c2c92eul 0x92722c85ul;
  upd4 k 40ul 0xa2bfe8a1ul 0xa81a664bul 0xc24b8b70ul 0xc76c51a3ul;
  upd4 k 44ul 0xd192e819ul 0xd6990624ul 0xf40e3585ul 0x106aa070ul;
  upd4 k 48ul 0x19a4c116ul 0x1e376c08ul 0x2748774cul 0x34b0bcb5ul;
  upd4 k 52ul 0x391c0cb3ul 0x4ed8aa4aul 0x5b9cca4ful 0x682e6ff3ul;
  upd4 k 56ul 0x748f82eeul 0x78a5636ful 0x84c87814ul 0x8cc70208ul;
  upd4 k 60ul 0x90befffaul 0xa4506cebul 0xbef9a3f7ul 0xc67178f2ul


[@"substitute"]
private val constants_set_h_0:
  state:suint32_p{length state = U32.v size_state} ->
  Stack unit (requires (fun h -> live h state))
               (ensures (fun h0 _ h1 -> live h1 state /\ modifies_1 state h0 h1))

[@"substitute"]
private let constants_set_h_0 state =
  let whash = Buffer.sub state pos_whash_32 size_whash_32 in
  upd4 whash 0ul 0x6a09e667ul 0xbb67ae85ul 0x3c6ef372ul 0xa54ff53aul;
  upd4 whash 4ul 0x510e527ful 0x9b05688cul 0x1f83d9abul 0x5be0cd19ul



(* [FIPS 180-4] section 6.2.2 *)
(* Step 1 : Scheduling function for sixty-four 32bit words *)
inline_for_extraction private val ws_compute:
  state  :suint32_p {length state = v size_state} ->
  wblock :suint32_p {length wblock = v blocksize_32} ->
  t      :uint32_t  {v t + 64 < pow2 32} ->
  Stack unit
        (requires (fun h -> live h state /\ live h wblock))
        (ensures  (fun h0 r h1 -> live h1 state /\ modifies_1 state h0 h1))

let rec ws_compute state wblock t =
  (* Get necessary information from the state *)
  let ws = Buffer.sub state pos_ws_32 size_ws_32 in

  (* Perform computations *)
  if t <^ 16ul then begin
    ws.(t) <- wblock.(t);
    ws_compute state wblock (t +^ 1ul) end
  else if t <^ 64ul then begin
    let t16 = ws.(t -^ 16ul) in
    let t15 = ws.(t -^ 15ul) in
    let t7  = ws.(t -^ 7ul) in
    let t2  = ws.(t -^ 2ul) in
    ws.(t) <- ((_sigma1 t2) +%^ (t7 +%^ ((_sigma0 t15) +%^ t16)));
    ws_compute state wblock (t +^ 1ul) end
  else ()


[@"c_inline"]
private val shuffle_core:
  state :suint32_p{length state = v size_state} ->
  t     :uint32_t {v t < v size_k_32} ->
  Stack unit
        (requires (fun h -> live h state ))
        (ensures  (fun h0 r h1 -> live h1 state /\ modifies_1 state h0 h1))

[@"c_inline"]
let shuffle_core state t =

  (* Get necessary information from the state *)
  let hash = Buffer.sub state pos_whash_32 size_whash_32 in
  let k = Buffer.sub state pos_k_32 size_k_32 in
  let ws = Buffer.sub state pos_ws_32 size_ws_32 in

  let a = Buffer.index hash 0ul in
  let b = Buffer.index hash 1ul in
  let c = Buffer.index hash 2ul in
  let d = Buffer.index hash 3ul in
  let e = Buffer.index hash 4ul in
  let f = Buffer.index hash 5ul in
  let g = Buffer.index hash 6ul in
  let h = Buffer.index hash 7ul in

  (* Perform computations *)
  let t1 = h +%^ (_Sigma1 e) +%^ (_Ch e f g) +%^ (Buffer.index k t) +%^ (Buffer.index ws t) in
  let t2 = (_Sigma0 a) +%^ (_Maj a b c) in

  (* Store the new working hash in the state *)
  Buffer.upd hash 7ul g;
  Buffer.upd hash 6ul f;
  Buffer.upd hash 5ul e;
  Buffer.upd hash 4ul (d +%^ t1);
  Buffer.upd hash 3ul c;
  Buffer.upd hash 2ul b;
  Buffer.upd hash 1ul a;
  Buffer.upd hash 0ul (t1 +%^ t2)


(* Step 3 : Perform logical operations on the working variables *)
[@"c_inline"]
private val shuffle:
  state :suint32_p{length state = v size_state} ->
  i     :uint32_t {v i + 64 < pow2 32} ->
  Stack unit
        (requires (fun h -> live h state ))
        (ensures  (fun h0 r h1 -> live h1 state /\ modifies_1 state h0 h1))

[@"c_inline"]
let rec shuffle state t =
  if t <^ 64ul then begin
    shuffle_core state t;
    shuffle state (t +^ 1ul) end
  else ()


#set-options "--z3rlimit 50"


val alloc:
  unit ->
  StackInline (state:suint32_p{length state = v size_state})
        (requires (fun h0 -> True))
        (ensures  (fun h0 state h1 -> modifies_0 h0 h1 /\ live h1 state))

let alloc () = Buffer.create (u32_to_s32 0ul) size_state


(* [FIPS 180-4] section 5.3.3 *)
val init:
  state:suint32_p{length state = v size_state} ->
  Stack unit
        (requires (fun h0 -> live h0 state))
        (ensures  (fun h0 r h1 -> modifies_1 state h0 h1))

let init state =
  constants_set_k state;
  constants_set_h_0 state


(* [FIPS 180-4] section 6.2.2 *)
(* Update running hash function *)
val update:
  state:suint32_p{length state = v size_state} ->
  data_8 :suint8_p {length data_8 = v blocksize} ->
  Stack unit
        (requires (fun h0 -> live h0 state /\ live h0 data_8))
        (ensures  (fun h0 r h1 -> live h1 state /\ modifies_1 state h0 h1))
let update state data_8 =

  (* Push a new frame *)
  (**) push_frame();

  (* Allocate space for converting the data block *)
  let data_32 = create (u32_to_s32 0ul) blocksize_32 in

  (* Cast the data bytes into a uint32_t buffer *)
  (**) cut(v blocksize % 4 = 0);
  (**) cut(v blocksize <= length data_8);
  (**) cut(v blocksize <= 4 * length data_32);
  Hacl.Utils.Experimental.load32s_be data_32 data_8 blocksize;

  (* Get necessary information from the state *)
  let h = Buffer.sub state pos_whash_32 size_whash_32 in

  (* Step 1 : Scheduling function for sixty-four 32 bit words *)
  ws_compute state data_32 0ul;

  (* Step 2 : Initialize the eight working variables *)
  let a_0 = h.(0ul) in
  let b_0 = h.(1ul) in
  let c_0 = h.(2ul) in
  let d_0 = h.(3ul) in
  let e_0 = h.(4ul) in
  let f_0 = h.(5ul) in
  let g_0 = h.(6ul) in
  let h_0 = h.(7ul) in

  (* Step 3 : Perform logical operations on the working variables *)
  shuffle state 0ul;

  (* Step 4 : Compute the ith intermediate hash value *)
  let a_1 = h.(0ul) in
  let b_1 = h.(1ul) in
  let c_1 = h.(2ul) in
  let d_1 = h.(3ul) in
  let e_1 = h.(4ul) in
  let f_1 = h.(5ul) in
  let g_1 = h.(6ul) in
  let h_1 = h.(7ul) in

  h.(0ul) <- (a_0 +%^ a_1);
  h.(1ul) <- (b_0 +%^ b_1);
  h.(2ul) <- (c_0 +%^ c_1);
  h.(3ul) <- (d_0 +%^ d_1);
  h.(4ul) <- (e_0 +%^ e_1);
  h.(5ul) <- (f_0 +%^ f_1);
  h.(6ul) <- (g_0 +%^ g_1);
  h.(7ul) <- (h_0 +%^ h_1);

  (* Increment the total number of blocks processed *)
  state.(pos_count_32) <- (state.(pos_count_32) +%^ (u32_to_s32 1ul));

  (* Pop the frame *)
  (**) pop_frame()



val update_multi:
  state :suint32_p{length state = v size_state} ->
  data  :suint8_p ->
  n     :uint32_t{v n * v blocksize <= length data} ->
  idx   :uint32_t{v idx <= v n} ->
  Stack unit
        (requires (fun h0 -> live h0 state /\ live h0 data))
        (ensures  (fun h0 _ h1 -> live h1 state /\ modifies_1 state h0 h1))

let rec update_multi state data n idx =

  if (idx =^ n) then ()
  else

    (* Get the current block for the data *)
    let b = Buffer.sub data (idx *%^ blocksize) blocksize in

    (* Call the update function on the current block *)
    update state b;

    (* Recursive call *)
    update_multi state data n (idx +^ 1ul)



val update_last:
  state :suint32_p{length state = v size_state} ->
  data  :suint8_p {length data <= v blocksize} ->
  len   :uint32_t {U32.v len = length data} ->
  Stack unit
        (requires (fun h0 -> live h0 state /\ live h0 data))
        (ensures  (fun h0 r h1 -> live h1 state /\ modifies_1 state h0 h1))

let update_last state data len =

  (* Push a new memory frame *)
  (**) push_frame();

  (* Allocate memory for integer conversions *)
  let len_64 = Buffer.create (uint8_to_sint8 0uy) 8ul in

  (* Alocate memory set to zeros for the last two blocks of data *)
  let blocks = Buffer.create (uint8_to_sint8 0uy) (2ul *^ blocksize) in

  (* Copy the data to the final construct *)
  Buffer.blit data 0ul blocks 0ul len;

  (* Set the first byte of the padding *)
  blocks.(len) <- (u8_to_s8 0x80uy);

  (* Compute the final length of the data *)
  let count = state.(pos_count_32) in
  let l_0 = S64.((s32_to_s64 count) *%^ (u32_to_s64 blocksize)) in
  let l_1 = u32_to_s64 len in
  let t_0 = S64.((l_0 +^ l_1) *%^ (u32_to_s64 8ul)) in
  Hacl.Endianness.hstore64_be len_64 t_0;

  (* Verification of how many blocks are necessary *)
  (* Threat model. The length are considered public here ! *)
  if U32.(len <^ 55ul) then (

    (* Encode the total length at the end of the padding *)
    Buffer.blit len_64 0ul blocks (blocksize -^ 8ul) 8ul;

    (* Get the first block *)
    let block_0 = Buffer.sub blocks 0ul blocksize in

    (* Process a single block *)
    update state block_0)
  else (

    (* Encode the total length at the end of the padding *)
    Buffer.blit len_64 0ul blocks (blocksize +^ blocksize -^ 8ul) 8ul;

    (* Split the final data into two blocks *)
    let block_0 = Buffer.sub blocks 0ul blocksize in
    let block_1 = Buffer.sub blocks blocksize blocksize in

    (* Process two blocks *)
    update state block_0;
    update state block_1);

  (* Pop the memory frame *)
  (**) pop_frame()



val finish:
  state :suint32_p{length state = v size_state} ->
  hash  :suint8_p{length hash = v hashsize} ->
  Stack unit
        (requires (fun h0 -> live h0 state /\ live h0 hash))
        (ensures  (fun h0 _ h1 -> live h1 hash /\ modifies_1 hash h0 h1))

let finish state hash =

  (* Store the final hash to the output location *)
  let whash = Buffer.sub state pos_whash_32 size_whash_32 in
  store32s_be hash whash hashsize_32



val hash:
  hash :suint8_p{length hash = v hashsize} ->
  input:suint8_p ->
  len  :uint32_t{v len = length input} ->
  Stack unit
        (requires (fun h0 -> live h0 hash /\ live h0 input))
        (ensures  (fun h0 _ h1 -> live h1 hash /\ modifies_1 hash h0 h1))

let hash hash input len =

  (* Push a new memory frame *)
  (**) push_frame ();

  (* Allocate memory for the hash state *)
  let ctx = Buffer.create (u32_to_s32 0ul) size_state in

  (* Compute the number of blocks to process *)
  let n = U32.div len blocksize in
  let r = U32.rem len blocksize in

  (* Initialize the hash function *)
  init ctx;

  (* Update the state with data blocks *)
  update_multi ctx input n 0ul;

  (* Get the last block *)
  let input_last = Buffer.sub input (n *%^ blocksize) r in

  (* Process the last block of data *)
  update_last ctx input_last r;

  (* Finalize the hash output *)
  finish ctx hash;

  (* Pop the memory frame *)
  (**) pop_frame ()
