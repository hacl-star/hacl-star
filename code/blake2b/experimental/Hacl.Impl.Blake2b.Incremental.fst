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
module LBS = Lib.ByteSequence

module Spec = Spec.Blake2
module SpecI = Spec.Blake2.Incremental


#set-options "--z3rlimit 200 --max_fuel 0"


let n_t = size_t
let n_tp = lbuffer n_t 1ul

let pl_t = l:size_t{v l <= v size_block}
let pl_tp = lbuffer pl_t 1ul


(** Define the state *)
noeq type state_r = {
  hash: hash_wp;
  n: n_tp;
  pl: pl_tp;
  block: block_p;
}


unfold let state_inv (h:mem) (state:state_r) =
  live h state.hash /\ live h state.block
  /\ live h state.n /\ live h state.pl
  /\ disjoint state.hash state.block
  /\ disjoint state.hash state.n
  /\ disjoint state.hash state.pl
  /\ disjoint state.block state.pl
  /\ disjoint state.block state.n
  /\ disjoint state.n state.pl


(* unfold let state_inv_trans (state0:state_r) (state1:state_r) = *)
(*   state0.hash == state1.hash *)
(*   /\ state0.block == state1.block *)
(*   /\ state0.n == state1.n *)
(*   /\ state0.pl == state1.pl *)

unfold let state_empty (h:mem) (state:state_r) =
  h.[|state.hash|] == Seq.create Spec.size_hash_w (u64 0) /\
  h.[|state.n|] == Seq.create 1 (size 0) /\
  h.[|state.pl|] == Seq.create 1 (size 0) /\
  h.[|state.block|] == Seq.create (Spec.size_block Spec.Blake2B) (u8 0)


(* unfold let state_modifies4 (state:state_r) (h0:mem) (h1:mem) = *)
(*   modifies4 state.hash state.block state.n state.pl h0 h1 *)

val state_hash_eq: h:mem -> state_r -> (SpecI.state_r Spec.Blake2B) -> prop
let state_hash_eq h istate sstate =
  sstate.SpecI.hash == h.[|istate.hash|]

val state_block_eq: h:mem -> state_r -> (SpecI.state_r Spec.Blake2B) -> prop
let state_block_eq h istate sstate =
  sstate.SpecI.block == h.[|istate.block|]

val state_eq: h:mem -> state_r -> (SpecI.state_r Spec.Blake2B) -> prop
let state_eq h istate sstate =
  sstate.SpecI.hash == h.[|istate.hash|] /\
  sstate.SpecI.n == v (Lib.Sequence.index h.[|istate.n|] 0) /\
  sstate.SpecI.pl == v (Lib.Sequence.index h.[|istate.pl|] 0) /\
  sstate.SpecI.block == h.[|istate.block|]


val spec_of: h:mem -> state_r -> GTot (SpecI.state_r Spec.Blake2B)
let spec_of h state =
  let hash: Spec.hash_ws Spec.Blake2B = h.[|state.hash|] in
  let n: size_nat = v (Lib.Sequence.index h.[|state.n|] 0) in
  let pl: l:size_nat{l <= Spec.size_block Spec.Blake2B} =  v (Lib.Sequence.index h.[|state.pl|] 0) in
  let block: Spec.block_s Spec.Blake2B = h.[|state.block|] in
  Spec.Blake2.Incremental.Mkstate_r hash n pl block

val gstate_get_n: h:mem -> state:state_r -> GTot (n:n_t{v n == (spec_of h state).SpecI.n})
let gstate_get_n h state = Lib.Sequence.index (as_seq h state.n) 0

val state_get_n: state:state_r -> Stack n_t
  (requires fun h -> state_inv h state)
  (ensures fun h0 n h1 -> h0 == h1 /\ v n == v (gstate_get_n h0 state))
  (* (ensures fun h0 n h1 -> v n == (spec_of h0 state).SpecI.n) *)
let state_get_n state = index state.n 0ul


val gstate_get_pl: h:mem -> state:state_r -> GTot (n:n_t{v n == (spec_of h state).SpecI.pl})
let gstate_get_pl h state = Lib.Sequence.index (as_seq h state.pl) 0

val state_get_pl: state:state_r -> Stack pl_t
  (requires fun h -> state_inv h state)
  (ensures fun h0 pl h1 -> h0 == h1 /\ v pl == v (gstate_get_pl h0 state))
let state_get_pl state = index state.pl 0ul


val blake2b_incremental_init:
    state: state_r
  -> kk: size_t{v kk <= 64}
  -> k: lbuffer uint8 kk
  -> nn: size_t{1 <= v nn /\ v nn <= 64} ->
  Stack unit
  (requires fun h ->
    live h state.hash /\ live h k /\
    disjoint state.hash k /\
    state_inv h state /\
    state_empty h state)
  (ensures  fun h0 _ h1 ->
    modifies2 state.hash state.n h0 h1 /\
    spec_of h1 state == SpecI.blake2_incremental_init Spec.Blake2B h0.[|k|] (v nn))

let blake2b_incremental_init state kk k nn =
  blake2b_init state.hash kk k nn;
  let n: n_t = if kk =. 0ul then 0ul else 1ul in
  upd state.n 0ul n


noextract
val spec_blake2_incremental_update_first:
    block:Spec.block_s Spec.Blake2B
  -> pl: size_nat{pl <= Spec.size_block Spec.Blake2B}
  -> ll: size_nat
  -> input: Seq.lseq uint8 ll ->
  Tot (Spec.block_s Spec.Blake2B)

noextract
let spec_blake2_incremental_update_first block pl ll input =
  let rb = Spec.size_block Spec.Blake2B - pl in
  let ll0 = if ll < rb then ll else rb in
  let partial = Seq.sub #uint8 #ll input 0 ll0 in
  Seq.update_sub block pl ll0 partial


val blake2b_incremental_update_first:
    block:block_p
  -> pl:size_t{v pl <= v size_block}
  -> ll:size_t
  -> input:lbuffer uint8 ll ->
  Stack unit
  (requires fun h ->
    live h block /\ live h input /\
    disjoint block input)
  (ensures  fun h0 _ h1 ->
    modifies1 block h0 h1 /\
    h1.[|block|] == spec_blake2_incremental_update_first h0.[|block|] (v pl) (v ll) h0.[|input|])

let blake2b_incremental_update_first block pl ll input =
  let rb = size_block -! pl in
  let ll0 = if ll <. rb then ll else rb in
  let partial = sub input 0ul ll0 in
  update_sub #MUT #uint8 #size_block block pl ll0 partial


 (* /\ i * Spec.size_block Spec.Blake2B <= Seq.length input /\ init + (i * Spec.size_block Spec.Blake2B) <= Spec.max_limb Spec.Blake2B}) *)
noextract
let spec_incremental_update_block
  (init:size_nat)
  (n:size_nat)
  (ll:size_nat)
  (input:LBS.lbytes ll{n * Spec.size_block Spec.Blake2B <= Seq.length input})
  (i:size_nat{i < n})
  (hash:Spec.hash_ws Spec.Blake2B)
  =
  let block: Spec.block_s Spec.Blake2B =
    Seq.sub #uint8 #(Seq.length input) input (i * (Spec.size_block Spec.Blake2B)) (Spec.size_block Spec.Blake2B)
  in
  Spec.blake2_update_block Spec.Blake2B (init + (i * Spec.size_block Spec.Blake2B)) block hash


noextract
val spec_blake2_incremental_update_loop:
  init:size_nat
  -> blocks:LBS.bytes{Seq.length blocks <= max_size_t /\ (init + (Seq.length blocks / (Spec.size_block Spec.Blake2B))) * (Spec.size_block Spec.Blake2B) <= pow2 128 - 1}
  -> hash:Spec.hash_ws Spec.Blake2B ->
  Tot (Spec.hash_ws Spec.Blake2B)

noextract
let spec_blake2_incremental_update_loop init blocks hash =
  let n = Seq.length blocks / Spec.size_block Spec.Blake2B in
  repeati n (fun i hash ->
    let block = Seq.sub #uint8 #(Seq.length blocks) blocks (i * Spec.size_block Spec.Blake2B) (Spec.size_block Spec.Blake2B) in
      Spec.blake2_update_block Spec.Blake2B ((init + i + 1) * Spec.size_block Spec.Blake2B) block hash
    ) hash


val blake2b_incremental_update_loop:
    state:state_r
  -> n:size_t
  -> blocks:lbuffer uint8 (n *. size_block) ->
  Stack unit
  (requires fun h ->
    live h blocks /\
    disjoint state.hash blocks /\ disjoint state.block blocks /\
    state_inv h state /\
    v n * v size_block <= max_size_t)
//    /\ v ((state.n +. n) *. size_block) <= pow2 128 - 1)
  (ensures  fun h0 _ h1 ->
    modifies1 state.hash h0 h1
    /\ h1.[|state.hash|] == spec_blake2_incremental_update_loop (v (Lib.Sequence.index h0.[|state.n|] 0)) h0.[|blocks|] h0.[|state.hash|])

let blake2b_incremental_update_loop state n blocks =
  admit();
  let h0 = ST.get () in
  [@inline_let]
  let spec h = spec_incremental_update_block (v (Lib.Sequence.index h0.[|state.n|] 0)) (v n) (v n * Spec.size_block Spec.Blake2B) h.[|blocks|] in
  loop1 h0 n state.hash spec
  (fun i ->
    Loops.unfold_repeati (v n) (spec h0) h0.[|state.hash|] (v i);
    let block = sub blocks (i *. size_block) size_block in
    let n64 = to_u64 (state_get_n state) in
    let i64 = to_u64 i in
    let size_block64 = to_u64 size_block in
    let prev = to_u128 ((n64 +! i64 +! (u64 1)) *! size_block64) in
    blake2b_update_block state.hash prev block)


noextract
val spec_blake2_incremental_update_end:
    block:Spec.block_s Spec.Blake2B
  -> ll: size_nat
  -> ll0: size_nat{ll0 <= ll}
  -> ll2: size_nat{ll2 = (ll - ll0) % (Spec.size_block Spec.Blake2B)}
  -> input: Seq.lseq uint8 ll ->
  Tot (Spec.block_s Spec.Blake2B)

noextract
let spec_blake2_incremental_update_end block ll ll0 ll2 input =
  (* let ll2 = (ll - ll0) % (Spec.size_block Spec.Blake2B) in *)
  let input2 = Seq.sub #uint8 #ll input (ll - ll2) ll2 in
  Seq.update_sub block 0 ll2 input2


val blake2b_incremental_update_end:
    block:block_p
  -> ll:size_t
  -> ll0:size_t{v ll0 <= v ll}
  -> ll2:size_t{v ll2 = (v ll - v ll0) % (Spec.size_block Spec.Blake2B)}
  -> input:lbuffer uint8 ll ->
  Stack unit
  (requires fun h ->
    live h block /\ live h input /\
    disjoint block input)
  (ensures  fun h0 _ h1 ->
    modifies1 block h0 h1 /\
    h1.[|block|] == spec_blake2_incremental_update_end h0.[|block|] (v ll) (v ll0) (v ll2) h0.[|input|])

let blake2b_incremental_update_end block ll ll0 ll2 input =
  (* let ll2 = (ll -. ll0) %. size_block in *)
  let input2 = sub #MUT #uint8 #ll input (ll -. ll2) ll2 in
  update_sub block 0ul ll2 input2


noextract
val spec_compute_prev:
  n:size_nat ->
  Tot (r:uint128)

noextract
let spec_compute_prev n =
  let prev = (n + 1) * Spec.size_block Spec.Blake2B in
  u128 prev



val compute_prev:
  n:n_t ->
  Tot (r:uint128{v r == v (spec_compute_prev (v n))})

let compute_prev n  =
  let n64 = to_u64 n in
  let size_block64 = to_u64 size_block in
  let prev64 = (n64 +! (u64 1)) *! size_block64 in
  to_u128 prev64



noextract
val spec_blake2b_incremental_update_inner_longer1:
  ll:size_nat
  -> input:LBS.lbytes ll{Seq.length input <= max_size_t}
  -> state:SpecI.state_r Spec.Blake2B{state.SpecI.n + 1 <= max_size_t}
  -> rb:size_nat{rb <= Spec.size_block Spec.Blake2B}
  -> ll0:size_nat{ll0 = (if ll < rb then ll else rb)} ->
  Tot (SpecI.state_r Spec.Blake2B)

noextract
let spec_blake2b_incremental_update_inner_longer1 ll input state rb ll0 =
  let open Spec.Blake2.Incremental in
  let n = state.SpecI.n in
  let tlen = v (spec_compute_prev n) in
  let hash = Spec.blake2_update_block Spec.Blake2B tlen state.SpecI.block state.SpecI.hash in
  let state = {state with hash = hash; n = n + 1; pl = 0;} in
  state


inline_for_extraction
val blake2b_incremental_update_inner_longer1:
    #h:mem
  -> state:state_r
  -> ll:size_t{v (gstate_get_n h state) + 1 + (v ll / v size_block) <= max_size_t}
  -> input:lbuffer uint8 ll
  -> rb:size_t{v rb <= v size_block}
  -> ll0:size_t{v ll0 = (if ll <. rb then v ll else v rb)} ->
  Stack unit
  (requires fun h ->
    state_inv h state /\ live h input /\
    disjoint state.hash input /\ disjoint state.block input /\
    state_inv h state /\
    (spec_of h state).SpecI.n + 1 <= max_size_t /\
    (v (gstate_get_n h state) * v size_block) + v ll < pow2 128)
  (ensures  fun h0 _ h1 ->
    modifies3 state.hash state.n state.pl h0 h1 /\
    state_eq h1 state (spec_blake2b_incremental_update_inner_longer1 (v ll) h0.[|input|] (spec_of h0 state) (v rb) (v ll0)))

let blake2b_incremental_update_inner_longer1 #h state ll input rb ll0 =
  let n: n_t = state_get_n state in
  let tlen = compute_prev n in
  blake2b_update_block state.hash tlen state.block;
  upd state.n 0ul (n +! 1ul);
  upd state.pl 0ul 0ul
//  {state with n = state.n +! 1ul; pl = 0ul}


noextract
val spec_blake2b_incremental_update_inner_longer2:
  ll:size_nat
  -> input:LBS.lbytes ll{Seq.length input <= max_size_t}
  -> state:SpecI.state_r Spec.Blake2B
  -> rb:size_nat{rb <= Spec.size_block Spec.Blake2B}
  -> ll0:size_nat{ll0 = (if ll < rb then ll else rb) /\ state.SpecI.n + (ll - ll0) / Spec.size_block Spec.Blake2B <= max_size_t} ->
  Tot (SpecI.state_r Spec.Blake2B)

noextract
let spec_blake2b_incremental_update_inner_longer2 ll input state rb ll0 =
  let open Spec.Blake2.Incremental in
  let n1 = (ll - ll0) / Spec.size_block Spec.Blake2B in
  let input1 = Seq.sub #uint8 #ll input ll0 (n1 * Spec.size_block Spec.Blake2B) in
  let hash = spec_blake2_incremental_update_loop state.n input1 state.hash in
  let state = {state with hash = hash; n = state.SpecI.n + n1;} in
  state


inline_for_extraction
val blake2b_incremental_update_inner_longer2:
    #h:mem
  -> state:state_r
  -> ll:size_t
  -> input:lbuffer uint8 ll
  -> rb:size_t{v rb <= v size_block}
  -> ll0:size_t{v ll0 = (if ll <. rb then v ll else v rb)} ->
  Stack unit
  (requires fun h ->
    state_inv h state /\ live h input /\
    disjoint state.hash input /\ disjoint state.block input /\
    v (gstate_get_n h state) + (v ll - v ll0) / v size_block <= max_size_t /\
    v (gstate_get_n h state) * (v size_block) + v ll < pow2 128)
  (ensures  fun h0 _ h1 ->
    modifies3 state.hash state.block state.n h0 h1 /\
    state_inv h1 state /\
    state_eq h1 state (spec_blake2b_incremental_update_inner_longer2 (v ll) h0.[|input|] (spec_of h0 state) (v rb) (v ll0)))

let blake2b_incremental_update_inner_longer2 #h state ll input rb ll0 =
  (* Handle all full blocks available *)
  let n = state_get_n state in
  let n1 = (ll -. ll0) /. size_block in
  let input1 = sub input ll0 (n1 *! size_block) in
  blake2b_incremental_update_loop state n1 input1;
  upd state.n 0ul (n +! n1)


noextract
val spec_blake2b_incremental_update_inner_longer3:
  ll:size_nat
  -> input:LBS.lbytes ll{Seq.length input <= max_size_t}
  -> state:SpecI.state_r Spec.Blake2B
  -> rb:size_nat{rb <= Spec.size_block Spec.Blake2B}
  -> ll0:size_nat{ll0 = (if ll < rb then ll else rb)} ->
  Tot (SpecI.state_r Spec.Blake2B)

noextract
let spec_blake2b_incremental_update_inner_longer3 ll input state rb ll0 =
  let open Spec.Blake2.Incremental in
  (* Store the remainder *)
  let ll2 = (ll - ll0) % Spec.size_block Spec.Blake2B in
  let block = spec_blake2_incremental_update_end state.block ll ll0 ll2 input in
  {state with pl = ll2; block = block}


inline_for_extraction
val blake2b_incremental_update_inner_longer3:
    state:state_r
  -> ll:size_t//{v state.n + 1 + (v ll / v size_block) <= max_size_t}
  -> input:lbuffer uint8 ll
  -> rb:size_t{v rb <= v size_block}
  -> ll0:size_t{v ll0 = (if ll <. rb then v ll else v rb)} ->
  Stack unit
  (requires fun h ->
    live h input /\
    disjoint state.hash input /\ disjoint state.block input /\
    state_inv h state /\
    v (gstate_get_n h state) * (v size_block) + v ll < pow2 128)
  (ensures  fun h0 _ h1 ->
    modifies3 state.hash state.block state.pl h0 h1 /\
    state_inv h1 state /\
    state_eq h1 state (spec_blake2b_incremental_update_inner_longer3 (v ll) h0.[|input|] (spec_of h0 state) (v rb) (v ll0)))

let blake2b_incremental_update_inner_longer3 state ll input rb ll0 =
  (* Store the remainder *)
  let ll2 = (ll -. ll0) %. size_block in
  blake2b_incremental_update_end state.block ll ll0 ll2 input;
  upd state.pl 0ul ll2


noextract
val spec_blake2b_incremental_update_inner_longer_split:
  ll:size_nat
  -> input:LBS.lbytes ll{Seq.length input <= max_size_t}
  -> state:SpecI.state_r Spec.Blake2B{state.SpecI.n + 1 + (ll / Spec.size_block Spec.Blake2B) <= max_size_t}
  -> rb:size_nat{rb <= Spec.size_block Spec.Blake2B}
  -> ll0:size_nat{ll0 = (if ll < rb then ll else rb)} ->
  Tot (SpecI.state_r Spec.Blake2B)

noextract
let spec_blake2b_incremental_update_inner_longer_split ll input state rb ll0 =
  let open Spec.Blake2.Incremental in
  let state = spec_blake2b_incremental_update_inner_longer1 ll input state rb ll0 in
  (* Handle all full blocks available *)
  let state = spec_blake2b_incremental_update_inner_longer2 ll input state rb ll0 in
  (* Store the remainder *)
  spec_blake2b_incremental_update_inner_longer3 ll input state rb ll0


noextract
val spec_blake2b_incremental_update_inner_longer:
  ll:size_nat
  -> input:LBS.lbytes ll{Seq.length input <= max_size_t}
  -> state:SpecI.state_r Spec.Blake2B{state.SpecI.n + 1 + (ll / Spec.size_block Spec.Blake2B) <= max_size_t}
  -> rb:size_nat{rb <= Spec.size_block Spec.Blake2B}
  -> ll0:size_nat{ll0 = (if ll < rb then ll else rb)} ->
  Tot (SpecI.state_r Spec.Blake2B)

noextract
let spec_blake2b_incremental_update_inner_longer ll input state rb ll0 =
  let open Spec.Blake2.Incremental in
  let tlen = v (spec_compute_prev state.SpecI.n) in
  let hash = Spec.blake2_update_block Spec.Blake2B tlen state.SpecI.block state.SpecI.hash in
  let state = {state with hash = hash; n = state.SpecI.n + 1; pl = 0;} in
  (* Handle all full blocks available *)
  let n1 = (ll - ll0) / Spec.size_block Spec.Blake2B in
  let input1 = Seq.sub #uint8 #ll input ll0 (n1 * Spec.size_block Spec.Blake2B) in
  let hash = spec_blake2_incremental_update_loop state.n input1 state.hash in
  let state = {state with hash = hash; n = state.SpecI.n + n1;} in
  (* Store the remainder *)
  let ll2 = (ll - ll0) % Spec.size_block Spec.Blake2B in
  let block = spec_blake2_incremental_update_end state.block ll ll0 ll2 input in
  {state with pl = ll2; block = block}


val lemma_equal_spec_blake2b_incremental_update_inner_longer:
  ll:size_nat
  -> input:LBS.lbytes ll{Seq.length input <= max_size_t}
  -> state:SpecI.state_r Spec.Blake2B{state.SpecI.n + 1 + (ll / Spec.size_block Spec.Blake2B) <= max_size_t}
  -> rb:size_nat{rb <= Spec.size_block Spec.Blake2B}
  -> ll0:size_nat{ll0 = (if ll < rb then ll else rb)} ->
  Lemma (ensures (
     spec_blake2b_incremental_update_inner_longer_split ll input state rb ll0
  == spec_blake2b_incremental_update_inner_longer ll input state rb ll0))

let lemma_equal_spec_blake2b_incremental_update_inner_longer ll input state rb ll0 = ()


inline_for_extraction
val blake2b_incremental_update_inner_longer:
    #h: mem
  -> state:state_r
  -> ll:size_t
  -> input:lbuffer uint8 ll
  -> rb:size_t{v rb <= v size_block}
  -> ll0:size_t{v ll0 = (if ll <. rb then v ll else v rb)} ->
  Stack unit
  (requires fun h ->
    live h input /\
    disjoint state.hash input /\ disjoint state.block input /\
    disjoint state.n input /\ disjoint state.pl input /\
    state_inv h state /\
    v (gstate_get_n h state) + 1 + (v ll / v size_block) <= max_size_t /\
    v (gstate_get_n h state) * (v size_block) + v ll < pow2 128)
  (ensures  fun h0 _ h1 ->
    modifies4 state.hash state.block state.n state.pl h0 h1 /\
    state_inv h1 state /\
    state_eq h1 state (spec_blake2b_incremental_update_inner_longer_split (v ll) h0.[|input|] (spec_of h0 state) (v rb) (v ll0)))

let blake2b_incremental_update_inner_longer #h state ll input rb ll0 =
  let h0 = ST.get () in
  blake2b_incremental_update_inner_longer1 #h0 state ll input rb ll0;
  let h1 = ST.get () in
  blake2b_incremental_update_inner_longer2 #h1 state ll input rb ll0;
  blake2b_incremental_update_inner_longer3 state ll input rb ll0


noextract
val spec_blake2b_incremental_update_inner:
    state:(SpecI.state_r Spec.Blake2B)
  -> ll:size_nat{state.SpecI.n + 1 + ll / v size_block <= max_size_t}
  -> rb:size_nat{rb = (Spec.size_block Spec.Blake2B) - state.SpecI.pl /\ rb <= Spec.size_block Spec.Blake2B}
  -> ll0:size_nat{ll0 = (if ll < rb then ll else rb) /\ state.SpecI.pl + ll0 <= v size_block}
  -> input:LBS.lbytes ll ->
  Tot (SpecI.state_r Spec.Blake2B)

let spec_blake2b_incremental_update_inner state ll rb ll0 input =
  let open Spec.Blake2.Incremental in
  if ll <= rb then ({state with pl = state.SpecI.pl + ll0})
  else
    spec_blake2b_incremental_update_inner_longer ll input state rb ll0


inline_for_extraction
val blake2b_incremental_update_inner:
    state:state_r
  -> ll:size_t
  -> rb:size_t
  -> ll0:size_t{v ll0 = (if ll <. rb then v ll else v rb)}
  -> input:lbuffer uint8 ll ->
  Stack unit
  (requires fun h ->
    live h input /\
    disjoint state.hash input /\ disjoint state.block input /\
    disjoint state.n input /\ disjoint state.pl input /\
    state_inv h state /\
    v (gstate_get_pl h state) + v ll0 <= v size_block /\
    v rb = v size_block - v (gstate_get_pl h state) /\ v rb <= v size_block /\
    v (gstate_get_n h state) + 1 + v ll / v size_block <= max_size_t /\
    v (gstate_get_n h state) * (v size_block) + v ll < pow2 128)
  (ensures  fun h0 _ h1 ->
    modifies4 state.hash state.block state.n state.pl h0 h1 /\
    state_inv h1 state /\
    state_eq h1 state (spec_blake2b_incremental_update_inner (spec_of h0 state) (v ll) (v rb) (v ll0) h0.[|input|]))

let blake2b_incremental_update_inner state ll rb ll0 input =
  let h0 = ST.get () in
  let pl = state_get_pl state in
  if ll <=. rb then (
    let ha0 = ST.get () in
    upd state.pl 0ul (pl +! ll0);
    let ha1 = ST.get () in
    modifies1_is_modifies4 state.pl state.hash state.block state.n ha0 ha1)
  else
    blake2b_incremental_update_inner_longer #h0 state ll input rb ll0


noextract
val spec_compute_branching_condition:
    state:(SpecI.state_r Spec.Blake2B)
  -> ll:size_nat{state.SpecI.n + 2 + ll / v size_block <= max_size_t} ->
  Tot bool

let spec_compute_branching_condition state ll =
  let nll = ll / v size_block in
  ll = 0 || not (state.SpecI.n + nll + 2 <= max_size_t)


val compute_branching_condition:
    #h:mem
  -> state:state_r
  -> ll:size_t{v (gstate_get_n h state) + 2 + v ll / v size_block <= max_size_t} ->
  Stack bool
  (requires fun h ->
    state_inv h state /\
    v (gstate_get_n h state) + 2 + v ll / v size_block <= max_size_t)
  (ensures (fun h0 b h1 -> (h0 == h1 /\ b == spec_compute_branching_condition (spec_of h state) (v ll))))

let compute_branching_condition #h state ll =
  [@inline_let]
  let max = normalize_term (size max_size_t) in
  let nll = ll /. size_block in
  let n: size_t = state_get_n state in
  ll =. 0ul || not (n +! nll +! 2ul <=. max)


noextract
val spec_blake2b_incremental_update:
    state:(SpecI.state_r Spec.Blake2B)
  -> ll:size_nat{state.SpecI.n + 2 + ll / v size_block <= max_size_t} // Why N+2? (Might be too strong!)
  -> input:LBS.lbytes ll ->
  Tot (option (SpecI.state_r Spec.Blake2B))

let spec_blake2b_incremental_update state ll input =
  let open Spec.Blake2.Incremental in
  if spec_compute_branching_condition state ll then None else (
  let rb = v size_block - state.SpecI.pl in
  let ll0 = if ll < rb then ll else rb in
  let partial = Lib.Sequence.sub input 0 ll0 in
  let block = Lib.Sequence.update_sub state.SpecI.block state.SpecI.pl ll0 partial in
  let state = {state with block = block} in
  let state = spec_blake2b_incremental_update_inner state ll rb ll0 input in
  Some state)


inline_for_extraction
val blake2b_incremental_update:
    state:state_r
  -> ll:size_t
  -> input:lbuffer uint8 ll ->
  Stack bool
  (requires fun h ->
    live h input /\
    disjoint state.hash input /\ disjoint state.block input /\
    disjoint state.n input /\ disjoint state.pl input /\
    state_inv h state /\
    v (gstate_get_n h state) + 2 + v ll / v size_block <= max_size_t /\
    v (gstate_get_n h state) * (v size_block) + v ll < pow2 128)
  (ensures  fun h0 b h1 ->
    state_inv h1 state /\
    modifies4 state.hash state.block state.n state.pl h0 h1 /\
    (let osstate = (SpecI.blake2_incremental_update Spec.Blake2B h0.[|input|] (spec_of h0 state)) in
    match osstate with | None -> b == false | Some sstate -> b == true))// /\ (spec_of h1 state) == sstate))

let blake2b_incremental_update state ll input =
  let h0 = ST.get() in
  if compute_branching_condition #h0 state ll then false
  else (
    let pl = state_get_pl state in
    let rb = size_block -! pl in
    let ll0 = if ll <. rb then ll else rb in
    let partial = sub input 0ul ll0 in
    update_sub state.block pl ll0 partial;
    blake2b_incremental_update_inner state ll rb ll0 input;
    true)


val blake2b_incremental_finish:
    nn:size_t{1 <= v nn /\ v nn <= 64}
  -> output:lbuffer uint8 nn
  -> state:state_r ->
  Stack unit
    (requires fun h ->
      state_inv h state /\ live h output /\
      disjoint output state.hash /\
      state_inv h state)
    (ensures  fun h0 _ h1 ->
      modifies2 output state.hash h0 h1 /\
      h1.[|output|] == Spec.Blake2.Incremental.blake2_incremental_finish Spec.Blake2.Blake2B (spec_of h0 state) (v nn))


let blake2b_incremental_finish nn output state =
  let h0 = ST.get () in
  let pl = state_get_pl state  in
  let last = sub state.block 0ul pl in
  let n = state_get_n state in
  let n64 = to_u64 n in
  let size_block64 = to_u64 size_block in
  let pl64 = to_u64 pl in
  let prev = to_u128 (n64 *! size_block64 +! pl64) in
  assert(v prev = (spec_of h0 state).SpecI.n * (Spec.Blake2.size_block Spec.Blake2.Blake2B) + (spec_of h0 state).SpecI.pl);
  blake2b_update_last state.hash prev pl last;
  blake2b_finish nn output state.hash


(* inline_for_extraction *)
(* val blake2b_incremental_update: *)
(*     state:state_r *)
(*   -> ll:size_t *)
(*   -> input:lbuffer uint8 ll -> *)
(*   Stack state_r *)
(*   (requires fun h -> *)
(*     state_inv h state /\ live h input /\ *)
(*     disjoint state.hash input /\ disjoint state.block input /\ *)
(*     state_inv h state /\ *)
(*     v (state.n *. size_block) + v ll < pow2 128) *)
(*   (ensures  fun h0 _ h1 -> *)
(*     modifies2 state.hash state.block h0 h1) *)

(* let blake2b_incremental_update state ll input = *)
(*   let nll = ll /. size_block in *)
(*   if ll =. 0ul || not (state.n +. nll +. 2ul <=. size 0xFFFFFFFF) then state else ( *)
(*   let rb = size_block -. state.pl in *)
(*   let ll0 = if ll <. rb then ll else rb in *)
(*   let partial = sub input 0ul ll0 in *)
(*   update_sub #MUT #uint8 #size_block state.block state.pl ll0 partial; *)
(*   if ll <=. rb then ({state with pl = state.pl +. ll0}) *)
(*   else ( *)
(*     let prev = to_u128 ((state.n +. 1ul) *. size_block) in *)
(*     blake2b_update_block state.hash prev state.block; *)
(*     (\* Handle all full blocks available *\) *)
(*     let n1 = (ll -. ll0) /. size_block in *)
(*     let input1 = sub input ll0 (ll -. ll0) in *)
(*     let h0 = ST.get () in *)
(*     loop_nospec #h0 n1 state.hash *)
(*     (fun i -> *)
(*       let block = sub input1 (i *. size_block) size_block in *)
(*       let h1 = ST.get () in *)
(*       let prev = to_u128 (secret ((state.n +. i +. 1ul) *. size_block)) in *)
(*       blake2b_update_block state.hash prev block); *)
(*     let state = {state with n = state.n +. n1;} in *)
(*     (\* Store the remainder *\) *)
(*     let ll2 = (ll -. ll0) %. size_block in *)
(*     let input2 = sub #MUT #uint8 #ll input (ll -. ll2) ll2 in *)
(*     let block = update_sub state.block 0ul ll2 input2 in *)
(*     ({state with pl = ll2;}) *)
(*   )) *)
