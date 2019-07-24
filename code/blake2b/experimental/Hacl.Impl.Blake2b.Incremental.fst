module Hacl.Impl.Blake2b.Incremental

open FStar.Mul
open FStar.HyperStack
open FStar.HyperStack.ST

open Lib.IntTypes
open Lib.Buffer
open Lib.ByteBuffer
open Lib.LoopCombinators

open Hacl.Impl.Blake2b
open Spec.Blake2.Incremental

module ST = FStar.HyperStack.ST
module Seq = Lib.Sequence
module Loops = Lib.LoopCombinators

module Spec = Spec.Blake2.Incremental

#set-options "--z3rlimit 150 --max_fuel 0"


(** Define the state *)
noeq type state_r = {
  hash: hash_wp;
  n: size_t;
  pl: l:size_t{v l <= v size_block};
  block: block_p;
}


let state_inv (h:mem) (state:state_r) =
  live h state.hash /\ live h state.block /\ disjoint state.hash state.block

let state_empty (h:mem) (state:state_r) =
  h.[|state.hash|] == Lib.Sequence.create Spec.Blake2.size_hash_w (u64 0) /\
  v state.n == 0 /\
  v state.pl == 0 /\
  h.[|state.block|] == Lib.Sequence.create (Spec.Blake2.size_block Spec.Blake2.Blake2B) (u8 0)

val state_eq: h:mem -> state_r -> (Spec.state_r Spec.Blake2.Blake2B) -> prop
let state_eq h istate sstate =
  sstate.Spec.hash == h.[|istate.hash|] /\
  sstate.Spec.n == v istate.n /\
  sstate.Spec.pl == v istate.pl /\
  sstate.Spec.block == h.[|istate.block|]

val spec_of: h:mem -> state_r -> GTot (Spec.state_r Spec.Blake2.Blake2B)
let spec_of h state =
  let hash: Spec.Blake2.hash_ws Spec.Blake2.Blake2B = h.[|state.hash|] in
  let n: size_nat = v state.n in
  let pl: l:size_nat{l <= Spec.Blake2.size_block Spec.Blake2.Blake2B} = v state.pl in
  let block: Spec.Blake2.block_s Spec.Blake2.Blake2B = h.[|state.block|] in
  Spec.Blake2.Incremental.Mkstate_r hash n pl block


val blake2b_incremental_init:
    state: state_r
  -> kk: size_t{v kk <= 64}
  -> k: lbuffer uint8 kk
  -> nn: size_t{1 <= v nn /\ v nn <= 64} ->
  Stack state_r
  (requires fun h ->
    live h state.hash /\ live h k /\
    disjoint state.hash k /\
    state_empty h state)
  (ensures  fun h0 rstate h1 ->
    modifies1 state.hash h0 h1 /\
    spec_of h1 rstate == Spec.Blake2.Incremental.blake2_incremental_init Spec.Blake2.Blake2B h0.[|k|] (v nn))

let blake2b_incremental_init state kk k nn =
  (**) let h0 = ST.get () in
  assert(state_empty h0 state);
  assert(h0.[|state.block|] == Lib.Sequence.create (Spec.Blake2.size_block Spec.Blake2.Blake2B) (u8 0));
  admit();
  blake2b_init state.hash kk k nn;
  (**) let h1 = ST.get () in
  [@inline_let]
  let n = if kk =. 0ul then 0ul else 1ul in
  let rstate = { state with n = n; } in
  (**) let hf = ST.get () in
  (**) assert(hf.[|rstate.hash|] == Spec.Blake2.blake2_init Spec.Blake2.Blake2B (v kk) h0.[|k|] (v nn));
  (**) assert(hf.[|rstate.block|] == Seq.create (Spec.Blake2.size_block Spec.Blake2.Blake2B) (u8 0));
  rstate



inline_for_extraction
val blake2b_incremental_update:
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

let blake2b_incremental_update state ll input =
  let nll = ll /. size_block in
  if ll =. 0ul then state else (
  if not (state.n +. nll +. 2ul <=. size 0xFFFFFFFF) then state else (
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
    let input2 = sub #MUT #uint8 #ll input (ll -. ll2) ll2 in
    let block = update_sub state.block 0ul ll2 input2 in
    ({state with pl = ll2;})
  )))



val blake2b_incremental_finish:
    nn:size_t{1 <= v nn /\ v nn <= 64}
  -> output:lbuffer uint8 nn
  -> state:state_r ->
  Stack unit
    (requires fun h ->
      state_inv h state /\ live h output
      /\ disjoint output state.hash)
    (ensures  fun h0 _ h1 ->
      modifies2 output state.hash h0 h1)// /\
//      h1.[|output|] == Spec.Blake2.Incremental.blake2_incremental_finish Spec.Blake2B (spec_of h0 state) (v nn))

let blake2b_incremental_finish nn output state =
  let last = sub state.block 0ul state.pl in
  let prev = to_u128 (state.n *. size_block +. state.pl) in
  blake2b_update_last state.hash prev state.pl last;
  blake2b_finish nn output state.hash
