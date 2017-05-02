module Hacl.Hash.SHA2.L512

open FStar.Mul
open FStar.Ghost
open FStar.HyperStack
open FStar.ST
open FStar.Buffer

open C.Loops

open Hacl.Cast
open Hacl.UInt8
open Hacl.UInt32
open FStar.UInt32

open Hacl.Utils.Experimental


(* Definition of aliases for modules *)
module U8 = FStar.UInt8
module U32 = FStar.UInt32
module U64 = FStar.UInt64
module U128 = FStar.UInt128

module H32 = Hacl.UInt32
module H64 = Hacl.UInt64
module H128 = Hacl.UInt128

module HS = FStar.HyperStack
module Buffer = FStar.Buffer
module Cast = Hacl.Cast

module Spec = Spec.SHA2
module Lemmas = Hacl.Hash.SHA2.Lemmas
module Utils = Hacl.Utils.Experimental


(* Definition of base types *)
private let uint8_t   = FStar.UInt8.t
private let uint32_t  = FStar.UInt32.t
private let uint64_t  = FStar.UInt64.t

private let uint8_ht  = Hacl.UInt8.t
private let uint64_ht = Hacl.UInt64.t

private let uint64_p = Buffer.buffer uint64_ht
private let uint8_p  = Buffer.buffer uint8_ht


(* Definitions of aliases for functions *)
[@"substitute"]
private let u8_to_h8 = Cast.uint8_to_sint8
[@"substitute"]
private let u32_to_h32 = Cast.uint32_to_sint32
[@"substitute"]
private let u32_to_h64 = Cast.uint32_to_sint64
[@"substitute"]
private let h32_to_h8  = Cast.sint32_to_sint8
[@"substitute"]
private let h32_to_h64 = Cast.sint32_to_sint64
[@"substitute"]
private let u32_to_h128 = Cast.uint32_to_sint128
[@"substitute"]
private let u64_to_h64 = Cast.uint64_to_sint64
[@"substitute"]
private let h64_to_h128 = Cast.sint64_to_sint128


//
// SHA-512
//

(* Define word size *)
inline_for_extraction let size_word = 8ul

(* Define algorithm parameters *)
inline_for_extraction let size_hash_w  = 8ul
inline_for_extraction let size_block_w = 16ul
inline_for_extraction let size_hash    = size_word *^ size_hash_w
inline_for_extraction let size_block   = size_word *^ size_block_w

(* Sizes of objects in the state *)
inline_for_extraction private let size_k_w     = 80ul
inline_for_extraction private let size_ws_w    = size_k_w
inline_for_extraction private let size_whash_w = size_hash_w
inline_for_extraction private let size_count_w = 1ul

inline_for_extraction let size_state   = size_k_w +^ size_ws_w +^ size_whash_w +^ size_count_w

(* Positions of objects in the state *)
inline_for_extraction private let pos_k_w      = 0ul
inline_for_extraction private let pos_ws_w     = size_k_w
inline_for_extraction private let pos_whash_w  = size_k_w +^ size_ws_w
inline_for_extraction private let pos_count_w  = size_k_w +^ size_ws_w +^ size_whash_w


[@"substitute"]
private val _Ch: x:uint64_ht -> y:uint64_ht -> z:uint64_ht -> Tot uint64_ht
[@"substitute"]
let _Ch x y z = H64.logxor (H64.logand x y) (H64.logand (H64.lognot x) z)

[@"substitute"]
private val _Maj: x:uint64_ht -> y:uint64_ht -> z:uint64_ht -> Tot uint64_ht
[@"substitute"]
let _Maj x y z = H64.logxor (H64.logand x y) (H64.logxor (H64.logand x z) (H64.logand y z))

[@"substitute"]
private val _Sigma0: x:uint64_ht -> Tot uint64_ht
[@"substitute"]
let _Sigma0 x = H64.logxor (rotate_right64 x 28ul) (H64.logxor (rotate_right64 x 34ul) (rotate_right64 x 39ul))

[@"substitute"]
private val _Sigma1: x:uint64_ht -> Tot uint64_ht
[@"substitute"]
let _Sigma1 x = H64.logxor (rotate_right64 x 14ul) (H64.logxor (rotate_right64 x 18ul) (rotate_right64 x 41ul))

[@"substitute"]
private val _sigma0: x:uint64_ht -> Tot uint64_ht
[@"substitute"]
let _sigma0 x = H64.logxor (rotate_right64 x 1ul) (H64.logxor (rotate_right64 x 8ul) (H64.shift_right x 7ul))

[@"substitute"]
private val _sigma1: x:uint64_ht -> Tot uint64_ht
[@"substitute"]
let _sigma1 x = H64.logxor (rotate_right64 x 19ul) (H64.logxor (rotate_right64 x 61ul) (H64.shift_right x 6ul))


[@"substitute"]
private val constants_set_k:
  k:uint64_p{length k = v size_k_w} ->
  Stack unit
        (requires (fun h -> live h k))
        (ensures (fun h0 _ h1 -> live h1 k /\ modifies_1 k h0 h1))

[@"substitute"]
let constants_set_k k =
  Hacl.Utils.Experimental.hupd64_80 k
  0x428a2f98d728ae22uL 0x7137449123ef65cduL 0xb5c0fbcfec4d3b2fuL 0xe9b5dba58189dbbcuL
  0x3956c25bf348b538uL 0x59f111f1b605d019uL 0x923f82a4af194f9buL 0xab1c5ed5da6d8118uL
  0xd807aa98a3030242uL 0x12835b0145706fbeuL 0x243185be4ee4b28cuL 0x550c7dc3d5ffb4e2uL
  0x72be5d74f27b896fuL 0x80deb1fe3b1696b1uL 0x9bdc06a725c71235uL 0xc19bf174cf692694uL
  0xe49b69c19ef14ad2uL 0xefbe4786384f25e3uL 0x0fc19dc68b8cd5b5uL 0x240ca1cc77ac9c65uL
  0x2de92c6f592b0275uL 0x4a7484aa6ea6e483uL 0x5cb0a9dcbd41fbd4uL 0x76f988da831153b5uL
  0x983e5152ee66dfabuL 0xa831c66d2db43210uL 0xb00327c898fb213fuL 0xbf597fc7beef0ee4uL
  0xc6e00bf33da88fc2uL 0xd5a79147930aa725uL 0x06ca6351e003826fuL 0x142929670a0e6e70uL
  0x27b70a8546d22ffcuL 0x2e1b21385c26c926uL 0x4d2c6dfc5ac42aeduL 0x53380d139d95b3dfuL
  0x650a73548baf63deuL 0x766a0abb3c77b2a8uL 0x81c2c92e47edaee6uL 0x92722c851482353buL
  0xa2bfe8a14cf10364uL 0xa81a664bbc423001uL 0xc24b8b70d0f89791uL 0xc76c51a30654be30uL
  0xd192e819d6ef5218uL 0xd69906245565a910uL 0xf40e35855771202auL 0x106aa07032bbd1b8uL
  0x19a4c116b8d2d0c8uL 0x1e376c085141ab53uL 0x2748774cdf8eeb99uL 0x34b0bcb5e19b48a8uL
  0x391c0cb3c5c95a63uL 0x4ed8aa4ae3418acbuL 0x5b9cca4f7763e373uL 0x682e6ff3d6b2b8a3uL
  0x748f82ee5defb2fcuL 0x78a5636f43172f60uL 0x84c87814a1f0ab72uL 0x8cc702081a6439ecuL
  0x90befffa23631e28uL 0xa4506cebde82bde9uL 0xbef9a3f7b2c67915uL 0xc67178f2e372532buL
  0xca273eceea26619cuL 0xd186b8c721c0c207uL 0xeada7dd6cde0eb1euL 0xf57d4f7fee6ed178uL
  0x06f067aa72176fbauL 0x0a637dc5a2c898a6uL 0x113f9804bef90daeuL 0x1b710b35131c471buL
  0x28db77f523047d84uL 0x32caab7b40c72493uL 0x3c9ebe0a15c9bebcuL 0x431d67c49c100d4cuL
  0x4cc5d4becb3e42b6uL 0x597f299cfc657e2auL 0x5fcb6fab3ad6faecuL 0x6c44198c4a475817uL
  

[@"substitute"]
val constants_set_h_0:
  hash:uint64_p{length hash = v size_hash_w} ->
  Stack unit
    (requires (fun h -> live h hash))
    (ensures (fun h0 _ h1 -> live h1 hash /\ modifies_1 hash h0 h1))

[@"substitute"]
let constants_set_h_0 hash =
  Hacl.Utils.Experimental.hupd64_8 hash
  0x6a09e667f3bcc908uL 0xbb67ae8584caa73buL 0x3c6ef372fe94f82buL 0xa54ff53a5f1d36f1uL
  0x510e527fade682d1uL 0x9b05688c2b3e6c1fuL 0x1f83d9abfb41bd6buL 0x5be0cd19137e2179uL


private val ws:
  ws_w    :uint64_p {length ws_w = 80} -> // TODO replace 80 by a constant
  block_w :uint64_p {length block_w = v size_block_w /\ disjoint ws_w block_w} ->
  t       :uint32_t {v t <= Spec.size_k_w} ->
  Stack unit
        (requires (fun h -> live h block_w /\ live h ws_w))
        (ensures  (fun h0 r h1 -> modifies_1 ws_w h0 h1 /\ live h0 block_w /\ live h0 ws_w /\ live h1 ws_w))

let rec ws ws_w block_w t =
  if t =^ 80ul then ()
  else (
    if t <^ 16ul then
      ws_w.(t) <- block_w.(t)
    else (
      let tm16 = t -^ 16ul in
      let tm15 = t -^ 15ul in
      let tm7 = t -^ 7ul in
      let tm2 = t -^ 2ul in
      let t16 = ws_w.(tm16) in
      let t15 = ws_w.(tm15) in
      let t7  = ws_w.(tm7) in
      let t2  = ws_w.(tm2) in
      ws_w.(t) <- H64.((_sigma1 t2) +%^ (t7 +%^ ((_sigma0 t15) +%^ t16)))
    );
    ws ws_w block_w (t +^ 1ul)
  )


[@"substitute"]
private val shuffle_core:
  hash_w :uint64_p {length hash_w = v size_hash_w} ->
  block_w:uint64_p {length block_w = v size_block_w} ->
  ws_w   :uint64_p {length ws_w = v size_ws_w} ->
  k_w    :uint64_p {length k_w = v size_k_w} ->
  t      :uint32_t {v t < v size_k_w} ->
  Stack unit
        (requires (fun h -> live h hash_w /\ live h ws_w /\ live h k_w /\ live h block_w))
        (ensures  (fun h0 r h1 -> live h0 hash_w /\ live h0 ws_w /\ live h0 k_w /\ live h0 block_w
                  /\ live h1 hash_w /\ modifies_1 hash_w h0 h1))

[@"substitute"]
let shuffle_core hash block ws k t =
  let a = hash.(0ul) in
  let b = hash.(1ul) in
  let c = hash.(2ul) in
  let d = hash.(3ul) in
  let e = hash.(4ul) in
  let f = hash.(5ul) in
  let g = hash.(6ul) in
  let h = hash.(7ul) in

  (* Perform computations *)
  let k_t = k.(t) in // Introduce these variables
  let ws_t = ws.(t) in
  let t1 = H64.(h +%^ (_Sigma1 e) +%^ (_Ch e f g) +%^ k_t +%^ ws_t) in
  let t2 = H64.((_Sigma0 a) +%^ (_Maj a b c)) in

  (* Store the new working hash in the state *)
  Utils.hupd64_8 hash H64.(t1 +%^ t2) a b c H64.(d +%^ t1) e f g


[@"substitute"]
private val shuffle:
  hash_w :uint64_p {length hash_w = v size_hash_w} ->
  block_w:uint64_p {length block_w = v size_block_w /\ disjoint block_w hash_w} ->
  ws_w   :uint64_p {length ws_w = v size_ws_w /\ disjoint ws_w hash_w} ->
  k_w    :uint64_p {length k_w = v size_k_w /\ disjoint k_w hash_w} ->
  Stack unit
        (requires (fun h -> live h hash_w /\ live h ws_w /\ live h k_w /\ live h block_w ))
        (ensures  (fun h0 r h1 -> live h1 hash_w /\ modifies_1 hash_w h0 h1 /\ live h0 block_w /\ live h0 hash_w))

#reset-options "--max_fuel 0 --max_ifuel 0 --z3rlimit 100"

[@"substitute"]
let shuffle hash block ws k =
  let h0 = ST.get() in
  let inv (h1: HS.mem) (i: nat) : Type0 =
    live h1 hash /\ modifies_1 hash h0 h1
  in
  let f' (t:uint32_t {v t < v size_ws_w}) :
    Stack unit
      (requires (fun h -> inv h (UInt32.v t)))
      (ensures (fun h_1 _ h_2 -> inv h_2 (UInt32.v t + 1)))
    =
    shuffle_core hash block ws k t
  in
  for 0ul size_ws_w inv f'


[@"substitute"]
private val sum_hash:
  hash_0:uint64_p{length hash_0 = v size_hash_w} ->
  hash_1:uint64_p{length hash_1 = v size_hash_w /\ disjoint hash_0 hash_1} ->
  Stack unit
    (requires (fun h -> live h hash_0 /\ live h hash_1))
    (ensures  (fun h0 _ h1 -> live h0 hash_0 /\ live h1 hash_0 /\ live h0 hash_1 /\ modifies_1 hash_0 h0 h1))

[@"substitute"]
let sum_hash hash_0 hash_1 =
  C.Loops.in_place_map2 hash_0 hash_1 size_hash_w (fun x y -> H64.(x +%^ y))


[@"c_inline"]
val alloc:
  unit ->
  StackInline (state:uint64_p{length state = v size_state})
    (requires (fun h0 -> True))
    (ensures (fun h0 st h1 -> ~(contains h0 st) /\ live h1 st /\ modifies_0 h0 h1 /\ frameOf st == h1.tip
             /\ Map.domain h1.h == Map.domain h0.h))

[@"c_inline"]
let alloc () = Buffer.create (u32_to_h64 0ul) size_state


val init:
  state:uint64_p{length state = v size_state} ->
  Stack unit
    (requires (fun h0 -> live h0 state))
    (ensures  (fun h0 r h1 -> live h1 state /\ modifies_1 state h0 h1))

let init state =
  let k = Buffer.sub state pos_k_w size_k_w in
  let h_0 = Buffer.sub state pos_whash_w size_whash_w in
  constants_set_k k;
  constants_set_h_0 h_0


[@"substitute"]
private val copy_hash:
  hash_w_1 :uint64_p {length hash_w_1 = v size_hash_w} ->
  hash_w_2 :uint64_p {length hash_w_2 = v size_hash_w /\ disjoint hash_w_1 hash_w_2} ->
  Stack unit
        (requires (fun h0 -> live h0 hash_w_1 /\ live h0 hash_w_2))
        (ensures  (fun h0 _ h1 -> live h0 hash_w_1 /\ live h0 hash_w_2 /\ live h1 hash_w_1 /\ modifies_1 hash_w_1 h0 h1))

[@"substitute"]
let copy_hash hash_w_1 hash_w_2 =
  Buffer.blit hash_w_2 0ul hash_w_1 0ul size_hash_w


[@"substitute"]
private val update_core:
  hash_w :uint64_p {length hash_w = v size_hash_w} ->
  data   :uint8_p  {length data = v size_block} ->
  data_w :uint64_p {length data_w = v size_block_w} ->
  ws_w   :uint64_p {length ws_w = v size_ws_w} ->
  k_w    :uint64_p {length k_w = v size_k_w} ->
  Stack unit
        (requires (fun h0 -> live h0 hash_w /\ live h0 data /\ live h0 data_w /\ live h0 ws_w /\ live h0 k_w))
        (ensures  (fun h0 r h1 -> live h0 hash_w /\ live h0 data /\ live h0 data_w /\ live h1 hash_w /\ modifies_1 hash_w h0 h1))

[@"substitute"]
let update_core hash_w data data_w ws_w k_w =

  (* Push a new frame *)
  (**) push_frame();

  (* Allocate space for converting the data block *)
  let hash_0 = Buffer.create (u64_to_h64 0uL) size_hash_w in

  (* Keep track of the the current working hash from the state *)
  copy_hash hash_0 hash_w;

  (* Step 2 : Initialize the eight working variables *)
  (* Step 3 : Perform logical operations on the working variables *)
  (* Step 4 : Compute the ith intermediate hash value *)
  shuffle hash_0 data_w ws_w k_w;

  (* Use the previous one to update it inplace *)
  sum_hash hash_w hash_0;

  (* Pop the frame *)
  (**) pop_frame()


val update:
  state :uint64_p {length state = v size_state} ->
  data  :uint8_p  {length data = v size_block /\ disjoint state data} ->
  Stack unit
        (requires (fun h0 -> live h0 state /\ live h0 data))
        (ensures  (fun h0 r h1 -> live h0 state /\ live h0 data /\ live h1 state /\ modifies_1 state h0 h1))

let update state data =

  (* Push a new frame *)
  (**) push_frame();

  (* Allocate space for converting the data block *)
  let data_w = Buffer.create (u32_to_h64 0ul) size_block_w in

  (* Cast the data bytes into a uint32_t buffer *)
  Hacl.Utils.Experimental.load64s_be data_w data size_block;

  (* Retreive values from the state *)
  let hash_w = Buffer.sub state pos_whash_w size_whash_w in
  let ws_w = Buffer.sub state pos_ws_w size_ws_w in
  let k_w = Buffer.sub state pos_k_w size_k_w in

  (* Step 1 : Scheduling function for sixty-four 32 bit words *)
  ws ws_w data_w 0ul;

  (* Step 2 : Initialize the eight working variables *)
  (* Step 3 : Perform logical operations on the working variables *)
  (* Step 4 : Compute the ith intermediate hash value *)
  update_core hash_w data data_w ws_w k_w;

  (* Increment the total number of blocks processed *)
  let state_len = Buffer.sub state (pos_count_w) 1ul in
  let c0 = state_len.(0ul) in
  let one = u32_to_h64 1ul in
  state_len.(0ul) <- H64.(c0 +%^ one);

  (* Pop the memory frame *)
  (**) pop_frame()


val update_multi:
  state :uint64_p{length state = v size_state} ->
  data  :uint8_p {length data % v size_block = 0 /\ disjoint state data} ->
  n     :uint32_t{v n * v size_block = length data} ->
  Stack unit
        (requires (fun h0 -> live h0 state /\ live h0 data))
        (ensures  (fun h0 _ h1 -> live h0 state /\ live h0 data /\ live h1 state /\ modifies_1 state h0 h1))

let rec update_multi state data n =
  if n =^ 0ul then ()
  else
    begin

    (* Get the current block for the data *)
    let b = Buffer.sub data 0ul size_block in

    (* Remove the current block from the data left to process *)
    let data = Buffer.offset data size_block in

    (* Call the update function on the current block *)
    update state b;

    (* Recursive call *)
    update_multi state data (n -^ 1ul) end


val update_last:
  state :uint64_p{length state = v size_state} ->
  data  :uint8_p {length data <= v size_block} ->
  len   :uint32_t {v len = length data} ->
  Stack unit
        (requires (fun h0 -> live h0 state /\ live h0 data))
        (ensures  (fun h0 r h1 -> live h1 state /\ modifies_1 state h0 h1))

let update_last state data len =

  (* Push a new memory frame *)
  (**) push_frame();

  (* Alocate memory set to zeros for the last two blocks of data *)
  let blocks = Buffer.create (uint8_to_sint8 0uy) (2ul *^ size_block) in

  (* Compute the final length of the data *)
  let count_h64 = state.(pos_count_w) in
  let size_block_h64 = u32_to_h64 size_block in
  let l_0 = H64.(count_h64 *%^ size_block_h64) in
  let l_1 = u32_to_h64 len in
  let l = H64.add_mod l_0 l_1 in
  let lb = u32_to_h64 8ul in
  let t_0 = h64_to_h128 (H64.mul_mod l lb) in

  (* Encode the total length at the end of the padding *)
  let len_128 = Buffer.sub blocks (size_block +^ size_block -^ 16ul) 16ul in
  Hacl.Endianness.hstore128_be len_128 t_0;

  (* Verification of how many blocks are necessary *)
  (* Threat model. The length are considered public here ! *)
  let (n,final_blocks) =
    if U32.(len <^ 111ul) then (1ul, Buffer.sub blocks size_block size_block)
    else (2ul, Buffer.sub blocks 0ul (2ul *^ size_block))
  in

  (* Copy the data to the final construct *)
  (* Leakage model : allowed because the length is public *)
  Buffer.blit data 0ul final_blocks 0ul len;

  (* Set the first byte of the padding *)
  final_blocks.(len) <- (u8_to_h8 0x80uy);

  (* Call the update function on one or two blocks *)
  update_multi state final_blocks n;

  (* Pop the memory frame *)
  (**) pop_frame()


[@"substitute"]
val finish_core:
  hash_w :uint64_p {length hash_w = v size_hash_w} ->
  hash   :uint8_p  {length hash = v size_hash} ->
  Stack unit
        (requires (fun h0 -> live h0 hash_w /\ live h0 hash))
        (ensures  (fun h0 _ h1 -> live h0 hash_w /\ live h0 hash /\ live h1 hash /\ modifies_1 hash h0 h1))

[@"substitute"]
let finish_core hash_w hash = store64s_be hash hash_w size_hash_w


val finish:
  state :uint64_p{length state = v size_state} ->
  hash  :uint8_p{length hash = v size_hash} ->
  Stack unit
        (requires (fun h0 -> live h0 state /\ live h0 hash))
        (ensures  (fun h0 _ h1 -> live h0 state /\ live h1 hash /\ modifies_1 hash h0 h1))

let finish state hash =
  let hash_w = Buffer.sub state pos_whash_w size_whash_w in
  finish_core hash_w hash


val hash:
  hash :uint8_p {length hash = v size_hash} ->
  input:uint8_p {length input < Spec.max_input_len_8} ->
  len  :uint32_t{v len = length input} ->
  Stack unit
        (requires (fun h0 -> live h0 hash /\ live h0 input))
        (ensures  (fun h0 _ h1 -> live h0 input /\ live h0 hash /\ live h1 hash /\ modifies_1 hash h0 h1
                  /\ (let seq_input = as_seq h0 input in
                  let seq_hash = as_seq h1 hash in
                  seq_hash == Spec.hash seq_input)))

let hash hash input len =

  (* Push a new memory frame *)
  (**) push_frame ();

  (* Allocate memory for the hash state *)
  let state = Buffer.create (u32_to_h64 0ul) size_state in

  (* Compute the number of blocks to process *)
  let n = U32.div len size_block in
  let r = U32.rem len size_block in

  (* Get the last block *)
  let input_last = Buffer.sub input (n *%^ size_block) r in

  (* Initialize the hash function *)
  init state;

  (* Update the state with data blocks *)
  update_multi state input n;

  (* Process the last block of data *)
  update_last state input_last r;

  (* Finalize the hash output *)
  finish state hash;

  (* Pop the memory frame *)
  (**) pop_frame ()
