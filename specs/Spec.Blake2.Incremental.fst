module Spec.Blake2.Incremental

open FStar.Mul
open Lib.IntTypes
open Lib.Sequence
open Lib.ByteSequence
open Lib.LoopCombinators

open Spec.Blake2


#set-options "--z3rlimit 100"

noeq type state_r (a:alg) = {
  hash: hash_ws a; // Current hash state
  n: size_nat; // Number of blocks already processed
  pl: pl:size_nat{pl <= size_block a}; // Partial length of the block
  block: block_s a; // Storage block
}


val blake2_incremental_init:
    a:alg
  -> k:bytes{length k <= max_key a}
  -> nn:size_nat{1 <= nn /\ nn <= max_output a} ->
  Tot (state_r a)

let blake2_incremental_init a k nn =
  let kk = length k in
  let hash = blake2_init a kk k nn in
  let block = create (size_block a) (u8 0) in
  let n = if kk = 0 then 0 else 1 in
  {
    hash = hash;
    n = n;
    pl = 0;
    block = block;
  }


val blake2_incremental_update:
    a:alg
  -> input:bytes{length input <= max_size_t}
  -> state:state_r a ->
  Tot (option (state_r a))

let blake2_incremental_update a input state =
  let ll = length input in
  let nll = ll / size_block a in
  if length input = 0 then Some state else (
  if not (state.n + nll + 2 <= max_size_t) then None else (
  (* Compute the remainder space in the block *)
  let rb = size_block a - state.pl in
  (* Fill the partial block in the state *)
  let ll0 = if ll < rb then ll else rb in
  let partial = sub #uint8 #ll input 0 ll0 in
  let block: block_s a = update_sub state.block state.pl ll0 partial in
  if ll < rb then (
    Some ({state with pl = state.pl + ll; block = block}))
  else (
    let hash = blake2_update_block a ((state.n + 1) * size_block a) block state.hash in
    let state = {state with hash = hash; n = state.n + 1; pl = 0;} in
    (* Handle all full blocks available *)
    let n1 = (ll - ll0) / size_block a in
    let input1 = sub #uint8 #ll input ll0 (ll - ll0) in
    let hash = repeati n1 (fun i ->
        let block = sub #uint8 #(length input1) input1 (i * size_block a) (size_block a) in
        blake2_update_block a ((state.n + i + 1) * size_block a) block
      ) state.hash
    in
    let state = {state with hash = hash; n = state.n + n1;} in
    (* Store the remainder *)
    let ll2 = (ll - ll0) % size_block a in
    let input2 = sub #uint8 #ll input (ll - ll2) ll2 in
    let block = update_sub block 0 ll2 input2 in
    Some ({state with pl = ll2; block = block})
  )))



val blake2_incremental_finish:
    a:alg
  -> s:state_r a
  -> nn:size_nat{1 <= nn /\ nn <= max_output a} ->
  Tot (lbytes nn)

let blake2_incremental_finish a state nn =
  let last = sub state.block 0 state.pl in
  // Not very efficient because a full block will be recreated from the partial input
  let hash = blake2_update_last a (state.n * size_block a + state.pl) state.pl last state.hash in
  blake2_finish a hash nn


//
// This function has an artificial bound on the size of the input
// for technical reasons and should not be used !
//
// Please use Spec.Blake2.blake2 instead !
//

val blake2_incremental:
    a:alg
  -> d:bytes{length d <= max_size_t}
  -> k:bytes{length k <= max_key a /\ (if length k = 0 then length d <= max_limb a else length d + size_block a <= max_limb a)}
  -> nn:size_nat{1 <= nn /\ nn <= max_output a} ->
  Tot (option (lbytes nn))

let blake2_incremental a d k nn =
  let size_pblock = size_block a - 7 in
  let kk = length k in
  let nd = length d / size_pblock in
  let rd = length d % size_pblock in
  let plast = sub #uint8 #(length d) d (nd * size_pblock) rd in
  let st = blake2_incremental_init a k nn in
  match repeati nd (fun i ost ->
    let pinput = sub #uint8 #(length d) d (i * size_pblock) size_pblock in
    match ost with
    | None -> None
    | Some st -> blake2_incremental_update a pinput st
  ) (Some st)
  with
  | None -> None
  | Some st ->
  match blake2_incremental_update a plast st with
  | None -> None
  | Some st -> Some (blake2_incremental_finish a st nn)
