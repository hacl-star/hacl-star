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

module Spec = Spec.SHA2


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

inline_for_extraction let wlen = 4ul // Size of the word in bytes

(* Define algorithm parameters *)
inline_for_extraction let size_hash_w = 8ul // 8 words (Final hash output size)
inline_for_extraction let size_hash   = wlen *^ size_hash_w
inline_for_extraction let size_block_w = 16ul  // 16 words (Working data block size)
inline_for_extraction let size_block   = wlen *^ size_block_w

(* Sizes of objects in the state *)
inline_for_extraction let size_k_w      = 64ul  // 2048 bits = 64 words of 32 bits (size_block)
inline_for_extraction let size_ws_w     = size_k_w
inline_for_extraction let size_whash_w  = size_hash_w
inline_for_extraction let size_count_w  = 1ul  // 1 word
inline_for_extraction let size_state  = size_k_w +^ size_ws_w +^ size_whash_w +^ size_count_w

(* Positions of objects in the state *)
inline_for_extraction let pos_k_w       = 0ul
inline_for_extraction let pos_ws_w      = size_k_w
inline_for_extraction let pos_whash_w   = size_k_w +^ size_ws_w
inline_for_extraction let pos_count_w   = size_k_w +^ size_ws_w +^ size_whash_w



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
  let k = Buffer.sub state pos_k_w size_k_w in
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
private val _constants_set_h_0:
  hash:suint32_p{length hash = U32.v size_hash_w} ->
  Stack unit
    (requires (fun h -> live h hash))
    (ensures (fun h0 _ h1 -> live h1 hash /\ modifies_1 hash h0 h1
             /\ (let s = as_seq h1 hash in
             U32.v (Seq.index s 0) = 0x6a09e667 /\
             U32.v (Seq.index s 1) = 0xbb67ae85 /\
             U32.v (Seq.index s 2) = 0x3c6ef372 /\
             U32.v (Seq.index s 3) = 0xa54ff53a /\
             U32.v (Seq.index s 4) = 0x510e527f /\
             U32.v (Seq.index s 5) = 0x9b05688c /\
             U32.v (Seq.index s 6) = 0x1f83d9ab /\
             U32.v (Seq.index s 7) = 0x5be0cd19)))
//             forall i. Seq.index s i = Seq.index Spec.list_h_0 i

[@"substitute"]
private let _constants_set_h_0 hash =
  upd4 hash 0ul 0x6a09e667ul 0xbb67ae85ul 0x3c6ef372ul 0xa54ff53aul;
  upd4 hash 4ul 0x510e527ful 0x9b05688cul 0x1f83d9abul 0x5be0cd19ul


[@"substitute"]
private val constants_set_h_0:
  state:suint32_p{length state = U32.v size_state} ->
  Stack unit
    (requires (fun h -> live h state))
    (ensures  (fun h0 _ h1 -> live h1 state /\ modifies_1 state h0 h1
              /\ (let hash = Seq.slice (as_seq h1 state) (U32.v pos_whash_w) (U32.(v pos_whash_w + v size_whash_w)) in
              Hacl.Spec.Endianness.reveal_h32s hash == Seq.createL Spec.list_h_0)))

[@"substitute"]
private let constants_set_h_0 state =
  let hash = Buffer.sub state pos_whash_w size_whash_w in
  _constants_set_h_0 hash;
  let h = ST.get() in
  assert_norm (Seq.length (Seq.createL Spec.list_h_0) = 8);
  assert_norm(let s = (Seq.createL Spec.list_h_0) in Seq.index s 0 = 0x6a09e667ul);
  assert_norm(let s = (Seq.createL Spec.list_h_0) in Seq.index s 1 = 0xbb67ae85ul);
  assert_norm(let s = (Seq.createL Spec.list_h_0) in Seq.index s 2 = 0x3c6ef372ul);
  assert_norm(let s = (Seq.createL Spec.list_h_0) in Seq.index s 3 = 0xa54ff53aul);
  assert_norm(let s = (Seq.createL Spec.list_h_0) in Seq.index s 4 = 0x510e527ful);
  assert_norm(let s = (Seq.createL Spec.list_h_0) in Seq.index s 5 = 0x9b05688cul);
  assert_norm(let s = (Seq.createL Spec.list_h_0) in Seq.index s 6 = 0x1f83d9abul);
  assert_norm(let s = (Seq.createL Spec.list_h_0) in Seq.index s 7 = 0x5be0cd19ul);
  Seq.lemma_eq_intro (Hacl.Spec.Endianness.reveal_h32s (as_seq h hash)) (Seq.createL Spec.list_h_0)


(* [FIPS 180-4] section 6.2.2 *)
(* Step 1 : Scheduling function for sixty-four 32bit words *)
inline_for_extraction
val ws_compute:
  state  :suint32_p {length state = v size_state} ->
  wblock :suint32_p {length wblock = v size_block_w} ->
  t      :uint32_t  {v t + 64 < pow2 32} ->
  Stack unit
        (requires (fun h -> live h state /\ live h wblock))
        (ensures  (fun h0 r h1 -> live h1 state /\ modifies_1 state h0 h1
                  /\ (let seq_ws_0 = Seq.slice (as_seq h0 state) (U32.v pos_ws_w) (U32.(v pos_ws_w + v size_ws_w)) in
                  let seq_ws_1 = Seq.slice (as_seq h1 state) (U32.v pos_ws_w) (U32.(v pos_ws_w + v size_ws_w)) in
                  let seq_wblock = as_seq h1 wblock in
                  seq_ws_1 == Spec.ws_compute seq_ws_0 seq_wblock (U32.v t))))

let rec ws_compute state wblock t =
  (* Get necessary information from the state *)
  let ws = Buffer.sub state pos_ws_w size_ws_w in

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
  t     :uint32_t {v t < v size_k_w} ->
  Stack unit
        (requires (fun h -> live h state))
        (ensures  (fun h0 r h1 -> live h1 state /\ modifies_1 state h0 h1
                  /\ (let seq_hash_0 = Seq.slice (as_seq h0 state) (U32.v pos_whash_w) (U32.(v pos_whash_w + v size_whash_w)) in
                  let seq_hash_1 = Seq.slice (as_seq h1 state) (U32.v pos_whash_w) (U32.(v pos_whash_w + v size_whash_w)) in
                  let seq_ws = Seq.slice (as_seq h1 state) (U32.v pos_ws_w) (U32.(v pos_ws_w + v size_ws_w)) in
                  seq_hash_1 == Spec.shuffle_core seq_hash_0 seq_ws (U32.v t))))

[@"c_inline"]
let shuffle_core state t =

  (* Get necessary information from the state *)
  let hash = Buffer.sub state pos_whash_w size_whash_w in
  let k = Buffer.sub state pos_k_w size_k_w in
  let ws = Buffer.sub state pos_ws_w size_ws_w in

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
        (ensures  (fun h0 r h1 -> live h1 state /\ modifies_1 state h0 h1
        /\ (let seq_hash_0 = Seq.slice (as_seq h0 state) (U32.v pos_whash_w) (U32.(v pos_whash_w + v size_whash_w)) in
        let seq_hash_1 = Seq.slice (as_seq h1 state) (U32.v pos_whash_w) (U32.(v pos_whash_w + v size_whash_w)) in
        let seq_ws = Seq.slice (as_seq h1 state) (U32.v pos_ws_w) (U32.(v pos_ws_w + v size_ws_w)) in
        seq_hash_1 == Spec.shuffle seq_hash_0 seq_ws (U32.v i))))

[@"c_inline"]
let rec shuffle state t =
  if t <^ 64ul then begin
    shuffle_core state t;
    shuffle state (t +^ 1ul) end
  else ()


[@ "c_inline"]
val sum_hash:
  hash_0:suint32_p{length hash_0 = v size_hash_w} ->
  hash_1:suint32_p{length hash_0 = v size_hash_w /\ disjoint hash_0 hash_1} ->
  Stack unit
    (requires (fun h -> live h hash_0 /\ live h hash_1))
    (ensures  (fun h0 _ h1 -> live h0 hash_0 /\ live h1 hash_0 /\ live h0 hash_1 /\ modifies_1 hash_0 h0 h1
              /\ (let new_seq_hash_0 = as_seq h1 hash_0 in
              let seq_hash_0 = as_seq h0 hash_0 in
              let seq_hash_1 = as_seq h0 hash_1 in
              new_seq_hash_0 == C.Loops.seq_map2 (fun x y -> S32.(x +%^ y)) seq_hash_0 seq_hash_1 )))

[@"c_inline"]
let sum_hash hash_0 hash_1 =
  C.Loops.in_place_map2 hash_0 hash_1 size_hash_w (fun x y -> S32.(x +%^ y))


#set-options "--z3rlimit 50"

[@"c_inline"]
val alloc:
  unit ->
  StackInline (state:suint32_p{length state = v size_state})
        (requires (fun h0 -> True))
        (ensures (fun h0 st h1 -> ~(contains h0 st) /\ live h1 st /\ modifies_0 h0 h1 /\ frameOf st == h1.tip
      /\ Map.domain h1.h == Map.domain h0.h))

[@"c_inline"]
let alloc () = Buffer.create (u32_to_s32 0ul) size_state


(* [FIPS 180-4] section 5.3.3 *)
val init:
  state:suint32_p{length state = v size_state} ->
  Stack unit
        (requires (fun h0 -> live h0 state))
        (ensures  (fun h0 r h1 -> modifies_1 state h0 h1
                  /\ (let seq_k = Seq.slice (as_seq h1 state) (U32.v pos_k_w) (U32.(v pos_k_w + v size_k_w)) in
                  Hacl.Spec.Endianness.reveal_h32s seq_k == Seq.createL Spec.list_k)
                  /\ (let seq_h_0 = Seq.slice (as_seq h1 state) (U32.v pos_whash_w) (U32.(v pos_whash_w + v size_whash_w)) in
                  Hacl.Spec.Endianness.reveal_h32s seq_h_0 == Seq.createL Spec.list_h_0)))

let init state =
  constants_set_k state;
  constants_set_h_0 state


(* [FIPS 180-4] section 6.2.2 *)
(* Update running hash function *)
val update:
  state:suint32_p{length state = v size_state} ->
  data_8:suint8_p {length data_8 = v size_block} ->
  Stack unit
        (requires (fun h0 -> live h0 state /\ live h0 data_8))
        (ensures  (fun h0 r h1 -> live h1 state /\ modifies_1 state h0 h1))

let update state data_8 =

  (* Push a new frame *)
  (**) push_frame();

  (* Allocate space for converting the data block *)
  let data_w = create (u32_to_s32 0ul) size_block_w in
  let hash_0 = create (u32_to_s32 0ul) size_hash_w in

  (* Cast the data bytes into a uint32_t buffer *)
  (**) cut(v size_block % 4 = 0);
  (**) cut(v size_block <= length data_8);
  (**) cut(v size_block <= 4 * length data_w);
  Hacl.Utils.Experimental.load32s_be data_w data_8 size_block;

  (* Keep track of the the current working hash from the state *)
  Buffer.blit state pos_whash_w hash_0 0ul size_whash_w;

  (* Step 1 : Scheduling function for sixty-four 32 bit words *)
  ws_compute state data_w 0ul;

  (* Step 2 : Initialize the eight working variables *)
  (* Step 3 : Perform logical operations on the working variables *)
  (* Step 4 : Compute the ith intermediate hash value *)
  shuffle state 0ul;

  (* Retrieve the current working hash *)
  let hash_1 = Buffer.sub state pos_whash_w size_whash_w in

  (* Use the previous one to update it inplace *)
  sum_hash hash_1 hash_0;

  (* Increment the total number of blocks processed *)
  state.(pos_count_w) <- (state.(pos_count_w) +%^ (u32_to_s32 1ul));

  (* Pop the frame *)
  (**) pop_frame()



val update_multi:
  state :suint32_p{length state = v size_state} ->
  data  :suint8_p ->
  n     :uint32_t{v n * v size_block <= length data} ->
  idx   :uint32_t{v idx <= v n} ->
  Stack unit
        (requires (fun h0 -> live h0 state /\ live h0 data))
        (ensures  (fun h0 _ h1 -> live h1 state /\ modifies_1 state h0 h1))

let rec update_multi state data n idx =

  if (idx =^ n) then ()
  else

    (* Get the current block for the data *)
    let b = Buffer.sub data (idx *%^ size_block) size_block in

    (* Call the update function on the current block *)
    update state b;

    (* Recursive call *)
    update_multi state data n (idx +^ 1ul)



val update_last:
  state :suint32_p{length state = v size_state} ->
  data  :suint8_p {length data <= v size_block} ->
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
  let blocks = Buffer.create (uint8_to_sint8 0uy) (2ul *^ size_block) in

  (* Copy the data to the final construct *)
  (* Leakage model : allowed because the length is public *)
  Buffer.blit data 0ul blocks 0ul len;

  (* Set the first byte of the padding *)
  blocks.(len) <- (u8_to_s8 0x80uy);

  (* Compute the final length of the data *)
  let count = state.(pos_count_w) in
  let l_0 = S64.((s32_to_s64 count) *%^ (u32_to_s64 size_block)) in
  let l_1 = u32_to_s64 len in
  let t_0 = S64.((l_0 +^ l_1) *%^ (u32_to_s64 8ul)) in
  Hacl.Endianness.hstore64_be len_64 t_0;

  (* Verification of how many blocks are necessary *)
  (* Threat model. The length are considered public here ! *)
  if U32.(len <^ 55ul) then (

    (* Encode the total length at the end of the padding *)
    Buffer.blit len_64 0ul blocks (size_block -^ 8ul) 8ul;

    (* Get the first block *)
    let block_0 = Buffer.sub blocks 0ul size_block in

    (* Process a single block *)
    update state block_0)
  else (

    (* Encode the total length at the end of the padding *)
    Buffer.blit len_64 0ul blocks (size_block +^ size_block -^ 8ul) 8ul;

    (* Split the final data into two blocks *)
    let block_0 = Buffer.sub blocks 0ul size_block in
    let block_1 = Buffer.sub blocks size_block size_block in

    (* Process two blocks *)
    update state block_0;
    update state block_1);

  (* Pop the memory frame *)
  (**) pop_frame()



val finish:
  state :suint32_p{length state = v size_state} ->
  hash  :suint8_p{length hash = v size_hash} ->
  Stack unit
        (requires (fun h0 -> live h0 state /\ live h0 hash))
        (ensures  (fun h0 _ h1 -> live h1 hash /\ modifies_1 hash h0 h1))

let finish state hash =

  (* Store the final hash to the output location *)
  let whash = Buffer.sub state pos_whash_w size_whash_w in
  store32s_be hash whash size_hash_w



val hash:
  hash :suint8_p{length hash = v size_hash} ->
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
  let n = U32.div len size_block in
  let r = U32.rem len size_block in

  (* Initialize the hash function *)
  init ctx;

  (* Update the state with data blocks *)
  update_multi ctx input n 0ul;

  (* Get the last block *)
  let input_last = Buffer.sub input (n *%^ size_block) r in

  (* Process the last block of data *)
  update_last ctx input_last r;

  (* Finalize the hash output *)
  finish ctx hash;

  (* Pop the memory frame *)
  (**) pop_frame ()
