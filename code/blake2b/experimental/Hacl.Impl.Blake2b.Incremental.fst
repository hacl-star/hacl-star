module Hacl.Impl.Blake2b.Incremental

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


assume val to_size128: nat -> Tot size128_t


val declassify_word: word_t -> Tot (Spec.pub_word_t Spec.Blake2.Blake2B)
let declassify_word x =
  let px = Lib.RawIntTypes.u64_to_UInt64 x in
  let l :uint_t (Spec.wt Spec.Blake2.Blake2B) PUB = px in
  l


val declassify_word_to_size: word_t -> Tot size_t
let declassify_word_to_size x =
  let x32 = to_u32 x in
  let y32 = Lib.RawIntTypes.u32_to_UInt32 x32 in
  let l :size_t = Lib.RawIntTypes.size_from_UInt32 y32 in
  l



(** Define the state *)
noeq type state_r = {
  hash: hash_wp;
  n: size_t;
  pl: l:size_t{v l <= v size_block};
  block: block_p;
}


type state_inv (h:mem) (s:state_r) =
  live h s.hash /\ live h s.block /\ disjoint s.hash s.block



val blake2b_init_partial:
    state: state_r
  -> kk: size_t{v kk <= 64}
  -> k: lbuffer uint8 kk
  -> nn: size_t{1 <= v nn /\ v nn <= 64} ->
  Stack state_r
  (requires fun h ->
    live h state.hash /\ live h k /\
    disjoint state.hash k)
  (ensures  fun h0 _ h1 ->
    modifies1 state.hash h0 h1)

let blake2b_init_partial state kk k nn =
  blake2b_init state.hash kk k nn;
  [@inline_let]
  let n = if kk =. 0ul then 0ul else 1ul in
  { state with
    n = n; }



inline_for_extraction
val blake2b_update_partial:
    state:state_r
  -> ll:size_t
  -> input:lbuffer uint8 ll ->
  Stack state_r
  (requires fun h ->
    state_inv h state /\ live h input /\
    disjoint state.hash input /\ disjoint state.block input /\
    v (state.n *. size_block) + v ll < pow2 128)
  (ensures  fun h0 _ h1 ->
    modifies2 state.hash state.block h0 h1)

let blake2b_update_partial state ll input =
  let nll = ll /. size_block in
  if length input = 0 then state else (
  if not (state.n +. nll +. 2ul <= max_size_t) then state else (
  let rb = size_block -. state.pl in
  let ll0 = if ll <. rb then ll else rb in
  let partial = sub input 0ul ll0 in
  update_sub #MUT #uint8 #size_block state.block state.pl ll0 partial;
  if ll <=. rb then ({state with pl = state.pl +. ll0})
  else (
    let prev = to_u128 (secret ((state.n +. 1ul) *. size_block)) in
    blake2b_update_block state.hash prev state.block;
    (* Handle all full blocks available *)
    let n1 = (ll -. ll0) /. size_block in
    let input1 = sub input ll0 (ll -. ll0) in
    let h0 = ST.get () in

    loop_nospec #h0 n1 state.hash
    (fun i ->
      let block = sub input1 (i *. size_block) size_block in
      let h1 = ST.get () in
      let prev = to_u128 (secret ((state.n +. i +. 1ul) *. size_block)) in
      blake2b_update_block state.hash prev block);
    let state = {state with n = state.n +. n1;} in
    (* Store the remainder *)
    let ll2 = (ll -. ll0) %. size_block in
    let input2 = sub input (ll -. ll2) ll2 in
    let block = update_sub state.block 0ul ll2 input2 in
    ({state with pl = ll2;})
  )))



val blake2b_finish_partial:
    nn:size_t{1 <= v nn /\ v nn <= 64}
  -> output:lbuffer uint8 nn
  -> state:state_r ->
  Stack unit
    (requires fun h ->
      state_inv h state /\ live h output
      /\ disjoint output state.hash)
    (ensures  fun h0 _ h1 ->
      modifies1 output h0 h1 /\
      h1.[|output|] == Spec.Blake2.blake2_finish Spec.Blake2B h0.[|state.hash|] (v nn))

let blake2b_finish_partial nn output state =
  let empty = create 0ul (u8 0) in
  let last = sub state.block 0 state.pl in
  let prev = to_u128 (state.n *. size_block +. state.pl) in
  blake2b_update_last state.hash prev state.pl last;
  blake2b_finish nn output state.hash
