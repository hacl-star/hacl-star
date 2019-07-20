module Spec.Blake2.Incremental

open FStar.Mul
open Lib.IntTypes
open Lib.Sequence
open Lib.ByteSequence
open Lib.LoopCombinators

open Spec.Blake2


type size64_nat = n:nat{n <= pow2 64 - 1}


noeq type state_r (a:alg) = {
  hash: hash_ws a; // Current hash state
  n: n:size64_nat{n * size_block a <= max_limb a}; // Number of blocks
  pl: pl:size_nat{pl <= size_block a}; // Partial length of the block
  block: block_s a; // Storage block
}


val blake2_incremental_init:
    a:alg
  -> kk:size_nat{kk <= max_key a}
  -> k:lbytes kk
  -> nn:size_nat{1 <= nn /\ nn <= max_output a} ->
  Tot (state_r a)

let blake2_incremental_init a kk k nn =
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
  -> input:bytes{length input <= max_size_t} // This limitation is stupid (comes from sub) !
  -> state:state_r a{
            let n = length input / size_block a in
            (state.n + n + 2) * size_block a <= max_limb a} -> // The counter handling is annoying !
  Tot (state_r a)

let blake2_incremental_update a input state =
  let ll = length input in
  let br = size_block a - state.pl in
  let ll0 = if ll <= br then ll else br in
  let input0 = sub #uint8 #ll input 0 ll0 in
  let block: block_s a = update_sub state.block state.pl ll0 input0 in
  if ll <= br then {state with pl = state.pl + ll0; block = block}
  else (
    (* Handle the first partial block *)
    let hash = blake2_update_block a (state.n * (size_block a)) block state.hash in
    let n = state.n + 1 in
    let pl = 0 in
    (* Handle all full blocks available *)
    let rn = (ll - ll0) / size_block a in
    assert(let n = length input / size_block a in
            (state.n + n + 2) * size_block a <= max_limb a);
    admit();
    let hash = repeati rn (fun i ->
      blake2_update_block a ((n + i) * size_block a) block)
      hash
    in
    let n = n + rn in
    (* Store the remainder *)
    let ll1 = (ll - ll0) % size_block a in
    let input1 = sub #uint8 #ll input (ll - ll1) ll1 in
    let block = update_sub block 0 ll1 input1 in
    {state with n = n; pl = ll1; block = block}
  )


val blake2_incremental_finish:
    a:alg
  -> s:state_r a
  -> nn:size_nat{1 <= nn /\ nn <= max_output a} ->
  Tot (lbytes nn)

let blake2_incremental_finish a state nn =
  let empty = create 0 (u8 0) in
  let last = sub state.block 0 state.pl in
  // Not very efficient because a full block will be recreated from the partial input
  let hash = blake2_update_last a (state.n * (size_block a)) state.pl last state.hash in
  blake2_finish a hash nn
