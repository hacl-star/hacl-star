module Hacl.Impl.Blake2b.Partial

open FStar.Mul
open FStar.HyperStack
open FStar.HyperStack.ST

open Lib.IntTypes
open Lib.Buffer
open Lib.ByteBuffer
open Lib.LoopCombinators

open Hacl.Impl.Blake2b

module ST = FStar.HyperStack.ST
module Seq = Lib.Sequence
module Loops = Lib.LoopCombinators
module Spec = Spec.Blake2

#set-options "--z3rlimit 50 --max_ifuel 0 --max_fuel 0"

val declassify: word_t -> Tot (Spec.pub_word_t Spec.Blake2.Blake2B)
let declassify x =
  admit();
  let l :uint_t (Spec.wt Spec.Blake2.Blake2B) PUB = x in
  l



(** Define the size of the state *)
inline_for_extraction
let size_state_w = 1ul +. (size Spec.size_hash_w) +. 1ul +. 1ul +. (size Spec.size_block_w)

inline_for_extraction
let pos_state_kk = 0ul

inline_for_extraction
let pos_state_hash = pos_state_kk +. 1ul

inline_for_extraction
let pos_state_nblocks = pos_state_hash +. (size Spec.size_hash_w)

inline_for_extraction
let pos_state_plength = pos_state_nblocks +. 1ul

inline_for_extraction
let pos_state_block = pos_state_plength +. 1ul

(** Define the state *)
type state_wp = lbuffer word_t size_state_w


private
val get_state_kk:
  state:state_wp ->
  Stack (lbuffer word_t 1ul)
  (requires fun h -> live h state)
  (ensures  fun h0 r h1 ->
    h0 == h1 /\
    r == gsub state pos_state_kk 1ul)

let get_state_kk state = sub state pos_state_kk 1ul


private
val get_state_kk_value:
  state:state_wp ->
  Stack word_t
  (requires fun h -> live h state)
  (ensures  fun h0 r h1 ->
    h0 == h1 /\
    (let kkb = gsub state pos_state_kk 1ul in
     let kk = Seq.index (as_seq h1 kkb) 0 in
    r == kk))

let get_state_kk_value state =
  let kkb = sub state pos_state_kk 1ul in
  index kkb 0ul


private
val get_state_hash:
  state:state_wp ->
  Stack hash_wp
  (requires fun h -> live h state)
  (ensures  fun h0 r h1 ->
    h0 == h1 /\
    r == gsub state pos_state_hash (size Spec.size_hash_w))

let get_state_hash state = sub state pos_state_hash (size Spec.size_hash_w)


private
val get_state_nblocks:
  state:state_wp ->
  Stack (lbuffer word_t 1ul)
  (requires fun h -> live h state)
  (ensures  fun h0 r h1 ->
    h0 == h1 /\
    r == gsub state pos_state_nblocks 1ul)

let get_state_nblocks state = sub state pos_state_nblocks 1ul


private
val get_state_plength:
  state:state_wp ->
  Stack (lbuffer word_t 1ul)
  (requires fun h -> live h state)
  (ensures  fun h0 r h1 ->
    h0 == h1 /\
    r == gsub state pos_state_plength 1ul)

let get_state_plength state = sub state pos_state_plength 1ul

private
val get_state_plength_value:
  state:state_wp ->
  Stack word_t
  (requires fun h -> live h state)
  (ensures  fun h0 r h1 ->
    h0 == h1 /\
    (let plb = gsub state pos_state_plength 1ul in
     let pl = Seq.index (as_seq h1 plb) 0 in
    r == pl))

let get_state_plength_value state =
  let plb = sub state pos_state_plength 1ul in
  index plb 0ul


private
val get_state_block:
  state:state_wp ->
  Stack block_wp
  (requires fun h -> live h state)
  (ensures  fun h0 r h1 ->
    h0 == h1 /\
    r == gsub state pos_state_block (size Spec.size_block_w))

let get_state_block state = sub state pos_state_block (size Spec.size_block_w)



val blake2b_partial_init:
    state: state_wp
  -> kk: size_t{v kk <= 64}
  -> k: lbuffer uint8 kk
  -> nn: size_t{1 <= v nn /\ v nn <= 64} ->
  Stack unit
  (requires fun h ->
    live h state /\ live h k /\
    disjoint state k)
  (ensures  fun h0 _ h1 ->
    modifies1 state h0 h1)

let blake2b_partial_init state kk k nn =
  let hash: hash_wp = get_state_hash state in
  blake2b_init hash kk k nn



inline_for_extraction
val blake2b_partial_update:
    state:state_wp
  -> ll:size_t
  -> input:lbuffer uint8 ll ->
  Stack unit
  (requires fun h ->
    live h state /\ live h input /\ disjoint state input /\
    (let kkb = gsub state pos_state_kk 1ul in
     let kk = Seq.index (as_seq h kkb) 0 in
    v kk <= 64 /\ (if v kk = 0 then v ll < pow2 128 else v ll + 128 < pow2 128))
  )
  (ensures  fun h0 _ h1 ->
    modifies1 state h0 h1)

let blake2b_partial_update state ll input =
  let hash = get_state_hash state in
  let kkb = get_state_kk state in
  let kk = get_state_kk_value state in
  let nblocks = get_state_nblocks state in
  let plength = get_state_plength_value state in
  let block = get_state_block state in
  (* The length is public and we need to declassify it *)
  let pplen = declassify plength in
  (* Compute the remaining space in the partial block *)
  (* let rem = size_block -. pplen in *)
  (* Copy all input or the size available in the partial block *)
  (* let clen = if ll <=. rem then ll else rem in *)
  (* let rinput = sub input 0ul clen in *)
  (* update_sub #MUT #word_t #(size ) block pplen rem; *)
  (* Process the block *)
  ()
