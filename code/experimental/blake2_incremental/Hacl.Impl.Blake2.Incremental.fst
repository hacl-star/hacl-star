module Hacl.Impl.Blake2.Incremental

open FStar.Mul
open FStar.HyperStack
open FStar.HyperStack.ST

open Lib.IntTypes
open Lib.Buffer
open Lib.ByteBuffer
open Lib.LoopCombinators

open Hacl.Impl.Blake2
open Spec.Blake2.Incremental

module ST = FStar.HyperStack.ST
module Seq = Lib.Sequence
module Loops = Lib.LoopCombinators
module LBS = Lib.ByteSequence

module Spec = Spec.Blake2
module SpecI = Spec.Blake2.Incremental



#set-options "--z3rlimit 200 --max_fuel 0"


(** Define the types of counters *)
inline_for_extraction
let n_t = size_t

inline_for_extraction
let pl_t (al:Spec.alg) = l:size_t{v l <= v (size_block al)}


(** Define the state *)
inline_for_extraction
noeq type state_r (al:Spec.alg) = {
  hash: hash_wp al;
  n: lbuffer n_t 1ul;
  pl: lbuffer (pl_t al) 1ul;
  block: block_p al;
}


unfold let state_inv (h:mem) (al:Spec.alg) (state:state_r al) =
  live h state.hash /\ live h state.block
  /\ live h state.n /\ live h state.pl
  /\ disjoint state.hash state.block
  /\ disjoint state.hash state.n
  /\ disjoint state.hash state.pl
  /\ disjoint state.block state.pl
  /\ disjoint state.block state.n
  /\ disjoint state.n state.pl

unfold let state_empty (h:mem) (al:Spec.alg) (state:state_r al) =
  h.[|state.hash|] == Seq.create Spec.size_hash_w (Spec.nat_to_word al 0) /\
  h.[|state.n|] == Seq.create 1 (size 0) /\
  h.[|state.pl|] == Seq.create 1 (size 0) /\
  h.[|state.block|] == Seq.create (Spec.size_block Spec.Blake2B) (u8 0)

val state_hash_eq: h:mem -> al:Spec.alg -> state_r al -> SpecI.state_r al -> prop
let state_hash_eq h al istate sstate =
  sstate.SpecI.hash == h.[|istate.hash|]

val state_block_eq: h:mem -> al:Spec.alg -> state_r al -> SpecI.state_r al -> prop
let state_block_eq h al istate sstate =
  sstate.SpecI.block == h.[|istate.block|]

val state_eq: h:mem -> al:Spec.alg -> state_r al -> SpecI.state_r al -> prop
let state_eq h al istate sstate =
  sstate.SpecI.hash == h.[|istate.hash|] /\
  sstate.SpecI.n == v (Lib.Sequence.index h.[|istate.n|] 0) /\
  sstate.SpecI.pl == v (Lib.Sequence.index h.[|istate.pl|] 0) /\
  sstate.SpecI.block == h.[|istate.block|]


val spec_of: h:mem -> al:Spec.alg -> state_r al -> GTot (SpecI.state_r al)
let spec_of h al state =
  let hash: Spec.hash_ws al = h.[|state.hash|] in
  let n: size_nat = v (Lib.Sequence.index h.[|state.n|] 0) in
  let pl: l:size_nat{l <= Spec.size_block al} =  v (Lib.Sequence.index h.[|state.pl|] 0) in
  let block: Spec.block_s al = h.[|state.block|] in
  Spec.Blake2.Incremental.Mkstate_r hash n pl block


inline_for_extraction noextract
val gstate_get_n: h:mem -> al:Spec.alg -> state:state_r al -> GTot (n:n_t{v n == (spec_of h al state).SpecI.n})
let gstate_get_n h al state = Lib.Sequence.index (as_seq h state.n) 0


inline_for_extraction noextract
val state_get_n: al:Spec.alg -> state:state_r al -> Stack n_t
  (requires fun h -> state_inv h al state)
  (ensures fun h0 n h1 -> h0 == h1 /\ v n == v (gstate_get_n h0 al state))

let state_get_n al state = index state.n 0ul


inline_for_extraction noextract
val gstate_get_pl: h:mem -> al:Spec.alg -> state:state_r al -> GTot (n:n_t{v n == (spec_of h al state).SpecI.pl})
let gstate_get_pl h al state = Lib.Sequence.index (as_seq h state.pl) 0

inline_for_extraction noextract
val state_get_pl: al:Spec.alg -> state:state_r al -> Stack (pl_t al)
  (requires fun h -> state_inv h al state)
  (ensures fun h0 pl h1 -> h0 == h1 /\ v pl == v (gstate_get_pl h0 al state))
let state_get_pl al state = index state.pl 0ul


inline_for_extraction noextract
let blake2_incremental_init_t (al:Spec.alg) =
    state: state_r al
  -> kk: size_t{v kk <= 64}
  -> k: lbuffer uint8 kk
  -> nn: size_t{1 <= v nn /\ v nn <= 64} ->
  Stack unit
  (requires fun h ->
    live h state.hash /\ live h k /\
    disjoint state.hash k /\
    state_inv h al state /\
    state_empty h al state)
  (ensures  fun h0 _ h1 ->
    modifies2 state.hash state.n h0 h1 /\
    spec_of h1 al state == SpecI.blake2_incremental_init al h0.[|k|] (v nn))

inline_for_extraction noextract
val blake2_incremental_init: al:Spec.alg -> blake2_update_block_t al -> blake2_incremental_init_t al

let blake2_incremental_init al blake2_update_block state kk k nn =
  blake2_init al blake2_update_block state.hash kk k nn;
  let n: n_t = if kk =. 0ul then 0ul else 1ul in
  upd state.n 0ul n


noextract
val spec_blake2_incremental_update_first:
    al:Spec.alg
  -> block:Spec.block_s al
  -> pl: size_nat{pl <= Spec.size_block al}
  -> ll: size_nat
  -> input: Seq.lseq uint8 ll ->
  Tot (Spec.block_s al)

noextract
let spec_blake2_incremental_update_first al block pl ll input =
  let rb = Spec.size_block al - pl in
  let ll0 = if ll < rb then ll else rb in
  let partial = Seq.sub #uint8 #ll input 0 ll0 in
  Seq.update_sub block pl ll0 partial

inline_for_extraction noextract
val blake2_incremental_update_first:
    al:Spec.alg
  -> block:block_p al
  -> pl:size_t{v pl <= v (size_block al)}
  -> ll:size_t
  -> input:lbuffer uint8 ll ->
  Stack unit
  (requires fun h ->
    live h block /\ live h input /\
    disjoint block input)
  (ensures  fun h0 _ h1 ->
    modifies1 block h0 h1 /\
    h1.[|block|] == spec_blake2_incremental_update_first al h0.[|block|] (v pl) (v ll) h0.[|input|])

let blake2_incremental_update_first al block pl ll input =
  let rb = (size_block al) -! pl in
  let ll0 = if ll <. rb then ll else rb in
  let partial = sub input 0ul ll0 in
  update_sub #MUT #uint8 #(size_block al) block pl ll0 partial


noextract
let spec_incremental_update_loop_step
  (al:Spec.alg)
  (state:SpecI.state_r al)
  (ni:size_nat)
  (ll:size_nat)
  (input:LBS.lbytes ll{ni * Spec.size_block al <= Seq.length input})
  (i:size_nat{i < ni})
  (hash:Spec.hash_ws al)
  =
  let block: Spec.block_s al =
    Seq.sub #uint8 #(Seq.length input) input (i * (Spec.size_block al)) (Spec.size_block al)
  in
  Spec.blake2_update_block al false ((state.SpecI.n * Spec.size_block al) + (i * Spec.size_block al)) block hash


inline_for_extraction noextract
let blake2_incremental_update_loop_step_t
    (al:Spec.alg) =
    state:state_r al
  -> ni:size_t
  -> i:size_t{v i < v ni}
  -> blocks:lbuffer uint8 (ni *. (size_block al)) ->
  Stack unit
  (requires fun h ->
    live h blocks /\
    disjoint state.hash blocks /\ disjoint state.block blocks /\
    disjoint state.n blocks /\ disjoint state.pl blocks /\
    state_inv h al state /\
    v (gstate_get_n h al state) * v (size_block al) <= max_size_t /\
    v ni * v (size_block al) <= max_size_t)
  (ensures  fun h0 _ h1 ->
    modifies1 state.hash h0 h1 /\
    state_inv h1 al state /\
    h1.[|state.hash|] == spec_incremental_update_loop_step al (spec_of h0 al state) (v ni) (v ni * Spec.size_block al) h0.[|blocks|] (v i) h0.[|state.hash|])



inline_for_extraction noextract
val blake2_incremental_update_loop_step: al:Spec.alg -> blake2_update_block_t al -> blake2_incremental_update_loop_step_t al

let blake2_incremental_update_loop_step al blake2_update_block state ni i blocks =
  let h0 = ST.get () in
  let block = sub blocks (i *! (size_block al)) (size_block al) in
  assert(h0.[|block|] == Seq.sub #uint8 #(Seq.length h0.[|blocks|]) h0.[|blocks|] (v i * (Spec.size_block al)) (Spec.size_block al));
  let n64 = to_u64 (state_get_n al state) in
  let i64 = to_u64 i in
  let size_block64 = to_u64 (size_block al) in
  let prev = to_u128 ((n64 *! size_block64) +! (i64 *! size_block64)) in
  admit();
  blake2_update_block state.hash false prev block


noextract
val spec_blake2_incremental_update_loop:
  (al:Spec.alg) ->
  (state:SpecI.state_r al)
  -> blocks:LBS.bytes{Seq.length blocks <= max_size_t /\ Seq.length blocks % (Spec.size_block al) = 0 /\ ((state.SpecI.n * Spec.size_block al) + (Seq.length blocks / (Spec.size_block al))) * (Spec.size_block al) < pow2 128}
  -> hash:Spec.hash_ws al ->
  Tot (Spec.hash_ws al)

noextract
let spec_blake2_incremental_update_loop al state blocks hash =
  let ni = Seq.length blocks / Spec.size_block al in
  [@inline_let]
  let spec = spec_incremental_update_loop_step al state ni (ni * Spec.size_block al) blocks in
  repeati ni spec hash


inline_for_extraction noextract
let blake2_incremental_update_loop_t (al:Spec.alg) =
    state:state_r al
  -> ni:size_t
  -> blocks:lbuffer uint8 (ni *. (size_block al)) ->
  Stack unit
  (requires fun h ->
    live h blocks /\
    disjoint state.hash blocks /\ disjoint state.block blocks /\
    disjoint state.n blocks /\ disjoint state.pl blocks /\
    state_inv h al state /\
    v ni * v (size_block al) <= max_size_t /\
    v (gstate_get_n h al state) * v (size_block al) <= max_size_t /\
    v (gstate_get_n h al state) * v (size_block al) < pow2 128)
  (ensures  fun h0 _ h1 ->
    modifies1 state.hash h0 h1 /\
    state_inv h1 al state /\
    h1.[|state.hash|] == spec_blake2_incremental_update_loop al (spec_of h0 al state) h0.[|blocks|] h0.[|state.hash|])

inline_for_extraction noextract
val blake2_incremental_update_loop: al:Spec.alg -> blake2_incremental_update_loop_step_t al -> blake2_incremental_update_loop_t al

let blake2_incremental_update_loop al blake2_incremental_update_loop_step state ni blocks =
  let h0 = ST.get () in
  [@inline_let]
  let spec h = spec_incremental_update_loop_step al (spec_of h0 al state) (v ni) (v ni * (Spec.size_block al)) h.[|blocks|] in
  loop1 h0 ni state.hash spec
  (fun i ->
    Loops.unfold_repeati (v ni) (spec h0) h0.[|state.hash|] (v i);
    blake2_incremental_update_loop_step state ni i blocks)


noextract
val spec_blake2_incremental_update_end:
    al:Spec.alg
  -> block:Spec.block_s al
  -> ll: size_nat
  -> ll0: size_nat{ll0 <= ll}
  -> ll2: size_nat{ll2 = (ll - ll0) % (Spec.size_block al)}
  -> input: Seq.lseq uint8 ll ->
  Tot (Spec.block_s al)

noextract
let spec_blake2_incremental_update_end al block ll ll0 ll2 input =
  let input2 = Seq.sub #uint8 #ll input (ll - ll2) ll2 in
  Seq.update_sub block 0 ll2 input2


inline_for_extraction noextract
val blake2_incremental_update_end:
    al:Spec.alg
  -> block:block_p al
  -> ll:size_t
  -> ll0:size_t{v ll0 <= v ll}
  -> ll2:size_t{v ll2 = (v ll - v ll0) % (Spec.size_block al)}
  -> input:lbuffer uint8 ll ->
  Stack unit
  (requires fun h ->
    live h block /\ live h input /\
    disjoint block input)
  (ensures  fun h0 _ h1 ->
    modifies1 block h0 h1 /\
    h1.[|block|] == spec_blake2_incremental_update_end al h0.[|block|] (v ll) (v ll0) (v ll2) h0.[|input|])

inline_for_extraction noextract
let blake2_incremental_update_end al block ll ll0 ll2 input =
  let input2 = sub #MUT #uint8 #ll input (ll -. ll2) ll2 in
  update_sub block 0ul ll2 input2


noextract
val spec_compute_prev:
  al:Spec.alg
  -> n:size_nat ->
  Tot (r:Spec.limb_t al)

noextract
let spec_compute_prev al n =
  let prev = (n + 1) * Spec.size_block al in
  Spec.nat_to_limb al prev


inline_for_extraction noextract
val compute_prev:
  al: Spec.alg
  -> n:n_t{v n + 1 <= max_size_t} ->
  Tot (r:Spec.limb_t al{v r == v (spec_compute_prev al (v n))})

let compute_prev al n  =
  let nw: word_t al = size_to_word al n in
  let size_blockw: word_t al = size_to_word al (size_block al) in
  admit();
  let prevw: word_t al = (nw +! (Spec.nat_to_word al 1)) *! size_blockw in
  size_to_limb al prevw


noextract
val spec_blake2_incremental_update_inner_longer1:
    al:Spec.alg
  -> ll:size_nat
  -> input:LBS.lbytes ll{Seq.length input <= max_size_t}
  -> state:SpecI.state_r al{state.SpecI.n + 1 <= max_size_t}
  -> rb:size_nat{rb <= Spec.size_block al}
  -> ll0:size_nat{ll0 = (if ll < rb then ll else rb)} ->
  Tot (SpecI.state_r al)

noextract
let spec_blake2_incremental_update_inner_longer1 al ll input state rb ll0 =
  let open Spec.Blake2.Incremental in
  let n = state.SpecI.n in
  let tlen = v (spec_compute_prev al n) in
  let hash = Spec.blake2_update_block al false tlen state.SpecI.block state.SpecI.hash in
  let state = {state with hash = hash; n = n + 1; pl = 0;} in
  state


inline_for_extraction noextract
let blake2_incremental_update_inner_longer1_t (al:Spec.alg) =
    h:mem
  -> state:state_r al
  -> ll:size_t{v (gstate_get_n h al state) + 1 + (v ll / v (size_block al)) <= max_size_t}
  -> input:lbuffer uint8 ll
  -> rb:size_t{v rb <= v (size_block al)}
  -> ll0:size_t{v ll0 = (if ll <. rb then v ll else v rb)} ->
  Stack unit
  (requires fun h ->
    state_inv h al state /\ live h input /\
    disjoint state.hash input /\ disjoint state.block input /\
    state_inv h al state /\
    (spec_of h al state).SpecI.n + 1 <= max_size_t /\
    (v (gstate_get_n h al state) * v (size_block al)) + v ll < pow2 128)
  (ensures  fun h0 _ h1 ->
    modifies3 state.hash state.n state.pl h0 h1 /\
    state_eq h1 al state (spec_blake2_incremental_update_inner_longer1 al (v ll) h0.[|input|] (spec_of h0 al state) (v rb) (v ll0)))

inline_for_extraction noextract
val blake2_incremental_update_inner_longer1: al:Spec.alg -> blake2_update_block_t al -> blake2_incremental_update_inner_longer1_t al

let blake2_incremental_update_inner_longer1 al blake2_update_block h state ll input rb ll0 =
  let n: n_t = state_get_n al state in
  let tlen = compute_prev al n in
  blake2_update_block state.hash false tlen state.block;
  upd state.n 0ul (n +! 1ul);
  upd state.pl 0ul 0ul


noextract
val spec_blake2_incremental_update_inner_longer2:
  al:Spec.alg
  -> ll:size_nat
  -> input:LBS.lbytes ll{Seq.length input <= max_size_t}
  -> state:SpecI.state_r al
  -> rb:size_nat{rb <= Spec.size_block al}
  -> ll0:size_nat{ll0 = (if ll < rb then ll else rb) /\ state.SpecI.n + (ll - ll0) / Spec.size_block al <= max_size_t} ->
  Tot (SpecI.state_r al)

noextract
let spec_blake2_incremental_update_inner_longer2 al ll input state rb ll0 =
  let open Spec.Blake2.Incremental in
  let n1 = (ll - ll0) / Spec.size_block al in
  let input1 = Seq.sub #uint8 #ll input ll0 (n1 * Spec.size_block al) in
  let hash = spec_blake2_incremental_update_loop al state input1 state.hash in
  let state = {state with hash = hash; n = state.SpecI.n + n1;} in
  state


inline_for_extraction noextract
let blake2_incremental_update_inner_longer2_t (al:Spec.alg) =
    h:mem
  -> state:state_r al
  -> ll:size_t
  -> input:lbuffer uint8 ll
  -> rb:size_t{v rb <= v (size_block al)}
  -> ll0:size_t{v ll0 = (if ll <. rb then v ll else v rb)} ->
  Stack unit
  (requires fun h ->
    state_inv h al state /\ live h input /\
    disjoint state.hash input /\ disjoint state.block input /\
    disjoint state.n input /\ disjoint state.pl input /\
    v (gstate_get_n h al state) + (v ll - v ll0) / v (size_block al) <= max_size_t /\
    v (gstate_get_n h al state) * v (size_block al) <= max_size_t /\
    v (gstate_get_n h al state) * v (size_block al) + v ll < pow2 128)
  (ensures  fun h0 _ h1 ->
    modifies3 state.hash state.block state.n h0 h1 /\
    state_inv h1 al state /\
    state_eq h1 al state (spec_blake2_incremental_update_inner_longer2 al (v ll) h0.[|input|] (spec_of h0 al state) (v rb) (v ll0)))

inline_for_extraction noextract
val blake2_incremental_update_inner_longer2: al:Spec.alg -> blake2_incremental_update_loop_t al -> blake2_incremental_update_inner_longer2_t al

let blake2_incremental_update_inner_longer2 al blake2_incremental_update_loop h state ll input rb ll0 =
  (* Handle all full blocks available *)
  let n = state_get_n al state in
  let n1 = (ll -. ll0) /. (size_block al) in
  let input1 = sub input ll0 (n1 *! (size_block al)) in
  blake2_incremental_update_loop state n1 input1;
  upd state.n 0ul (n +! n1)


noextract
val spec_blake2_incremental_update_inner_longer3:
  al: Spec.alg
  -> ll:size_nat
  -> input:LBS.lbytes ll{Seq.length input <= max_size_t}
  -> state:SpecI.state_r al
  -> rb:size_nat{rb <= Spec.size_block al}
  -> ll0:size_nat{ll0 = (if ll < rb then ll else rb)} ->
  Tot (SpecI.state_r al)

let spec_blake2_incremental_update_inner_longer3 al ll input state rb ll0 =
  let open Spec.Blake2.Incremental in
  (* Store the remainder *)
  let ll2 = (ll - ll0) % Spec.size_block al in
  let block = spec_blake2_incremental_update_end al state.block ll ll0 ll2 input in
  {state with pl = ll2; block = block}


inline_for_extraction noextract
val blake2_incremental_update_inner_longer3:
    al:Spec.alg
  -> state:state_r al
  -> ll:size_t
  -> input:lbuffer uint8 ll
  -> rb:size_t{v rb <= v (size_block al)}
  -> ll0:size_t{v ll0 = (if ll <. rb then v ll else v rb)} ->
  Stack unit
  (requires fun h -> live h input /\
    disjoint state.hash input /\ disjoint state.block input /\
    state_inv h al state /\
    v (gstate_get_n h al state) * v (size_block al) + v ll < Spec.Blake2.max_limb al)
  (ensures  fun h0 _ h1 ->
    modifies3 state.hash state.block state.pl h0 h1 /\
    state_inv h1 al state /\
    state_eq h1 al state (spec_blake2_incremental_update_inner_longer3 al (v ll) h0.[|input|] (spec_of h0 al state) (v rb) (v ll0)))

inline_for_extraction noextract
let blake2_incremental_update_inner_longer3 al state ll input rb ll0 =
  (* Store the remainder *)
  let ll2 = (ll -. ll0) %. (size_block al) in
  let h0 = ST.get () in
  blake2_incremental_update_end al state.block ll ll0 ll2 input;
  upd state.pl 0ul ll2


noextract
val spec_blake2_incremental_update_inner_longer_split:
  al:Spec.alg
  -> ll:size_nat
  -> input:LBS.lbytes ll{Seq.length input <= max_size_t}
  -> state:SpecI.state_r al{state.SpecI.n + 1 + (ll / Spec.size_block al) <= max_size_t}
  -> rb:size_nat{rb <= Spec.size_block al}
  -> ll0:size_nat{ll0 = (if ll < rb then ll else rb)} ->
  Tot (SpecI.state_r al)

noextract
let spec_blake2_incremental_update_inner_longer_split al ll input state rb ll0 =
  let open Spec.Blake2.Incremental in
  let state = spec_blake2_incremental_update_inner_longer1 al ll input state rb ll0 in
  (* Handle all full blocks available *)
  let state = spec_blake2_incremental_update_inner_longer2 al ll input state rb ll0 in
  (* Store the remainder *)
  spec_blake2_incremental_update_inner_longer3 al ll input state rb ll0


noextract
val spec_blake2_incremental_update_inner_longer:
  al:Spec.alg
  -> ll:size_nat
  -> input:LBS.lbytes ll{Seq.length input <= max_size_t}
  -> state:SpecI.state_r al{state.SpecI.n + 1 + (ll / Spec.size_block al) <= max_size_t}
  -> rb:size_nat{rb <= Spec.size_block al}
  -> ll0:size_nat{ll0 = (if ll < rb then ll else rb)} ->
  Tot (SpecI.state_r al)

noextract
let spec_blake2_incremental_update_inner_longer al ll input state rb ll0 =
  let open Spec.Blake2.Incremental in
  let tlen = v (spec_compute_prev al state.SpecI.n) in
  let hash = Spec.blake2_update_block al false tlen state.SpecI.block state.SpecI.hash in
  let state = {state with hash = hash; n = state.SpecI.n + 1; pl = 0;} in
  (* Handle all full blocks available *)
  let n1 = (ll - ll0) / Spec.size_block al in
  let input1 = Seq.sub #uint8 #ll input ll0 (n1 * Spec.size_block al) in
  let hash = spec_blake2_incremental_update_loop al state input1 state.hash in
  let state = {state with hash = hash; n = state.SpecI.n + n1;} in
  (* Store the remainder *)
  let ll2 = (ll - ll0) % Spec.size_block al in
  let block = spec_blake2_incremental_update_end al state.block ll ll0 ll2 input in
  {state with pl = ll2; block = block}


val lemma_equal_spec_blake2b_incremental_update_inner_longer:
  al:Spec.alg
  -> ll:size_nat
  -> input:LBS.lbytes ll{Seq.length input <= max_size_t}
  -> state:SpecI.state_r al{state.SpecI.n + 1 + (ll / Spec.size_block al) <= max_size_t}
  -> rb:size_nat{rb <= Spec.size_block al}
  -> ll0:size_nat{ll0 = (if ll < rb then ll else rb)} ->
  Lemma (ensures (
     spec_blake2_incremental_update_inner_longer_split al ll input state rb ll0
  == spec_blake2_incremental_update_inner_longer al ll input state rb ll0))

let lemma_equal_spec_blake2_incremental_update_inner_longer ll input state rb ll0 = ()


inline_for_extraction noextract
let blake2_incremental_update_inner_longer_t (al:Spec.alg) =
    h: mem
  -> state:state_r al
  -> ll:size_t
  -> input:lbuffer uint8 ll
  -> rb:size_t{v rb <= v (size_block al)}
  -> ll0:size_t{v ll0 = (if ll <. rb then v ll else v rb)} ->
  Stack unit
  (requires fun h ->
    live h input /\
    disjoint state.hash input /\ disjoint state.block input /\
    disjoint state.n input /\ disjoint state.pl input /\
    state_inv h al state /\
    v (gstate_get_n h al state) + 1 + (v ll / v (size_block al)) <= max_size_t /\
    (v (gstate_get_n h al state) + 1) * v (size_block al) <= max_size_t /\
    v (gstate_get_n h al state) * v (size_block al) + v ll < Spec.max_limb al)
  (ensures  fun h0 _ h1 ->
    modifies4 state.hash state.block state.n state.pl h0 h1 /\
    state_inv h1 al state /\
    state_eq h1 al state (spec_blake2_incremental_update_inner_longer_split al (v ll) h0.[|input|] (spec_of h0 al state) (v rb) (v ll0)))

inline_for_extraction noextract
val blake2_incremental_update_inner_longer: al:Spec.alg -> blake2_update_block_t al -> blake2_incremental_update_loop_t al -> blake2_incremental_update_inner_longer_t al

let blake2_incremental_update_inner_longer al blake2_update_block blake2_incremental_update_loop h state ll input rb ll0 =
  let h0 = ST.get () in
  blake2_incremental_update_inner_longer1 al blake2_update_block h0 state ll input rb ll0;
  let h1 = ST.get () in
  blake2_incremental_update_inner_longer2 al blake2_incremental_update_loop h1 state ll input rb ll0;
  blake2_incremental_update_inner_longer3 al state ll input rb ll0


noextract
val spec_blake2_incremental_update_inner:
    al:Spec.alg
  -> state:SpecI.state_r al
  -> ll:size_nat{state.SpecI.n + 1 + ll / v (size_block al) <= max_size_t}
  -> rb:size_nat{rb = (Spec.size_block al) - state.SpecI.pl /\ rb <= Spec.size_block al}
  -> ll0:size_nat{ll0 = (if ll < rb then ll else rb) /\ state.SpecI.pl + ll0 <= v (size_block al)}
  -> input:LBS.lbytes ll ->
  Tot (SpecI.state_r al)

let spec_blake2_incremental_update_inner al state ll rb ll0 input =
  let open Spec.Blake2.Incremental in
  if ll <= rb then ({state with pl = state.SpecI.pl + ll0})
  else
    spec_blake2_incremental_update_inner_longer al ll input state rb ll0


inline_for_extraction noextract
let blake2_incremental_update_inner_t (al:Spec.alg) =
    state:state_r al
  -> ll:size_t
  -> rb:size_t
  -> ll0:size_t{v ll0 = (if ll <. rb then v ll else v rb)}
  -> input:lbuffer uint8 ll ->
  Stack unit
  (requires fun h ->
    live h input /\
    disjoint state.hash input /\ disjoint state.block input /\
    disjoint state.n input /\ disjoint state.pl input /\
    state_inv h al state /\
    v (gstate_get_pl h al state) + v ll0 <= v (size_block al) /\
    v rb = v (size_block al) - v (gstate_get_pl h al state) /\ v rb <= v (size_block al) /\
    v (gstate_get_n h al state) + 1 + v ll / v (size_block al) <= max_size_t /\
    (v (gstate_get_n h al state) + 1) * v (size_block al) <= max_size_t /\
    v (gstate_get_n h al state) * v (size_block al) + v ll < Spec.max_limb al)
  (ensures  fun h0 _ h1 ->
    modifies4 state.hash state.block state.n state.pl h0 h1 /\
    state_inv h1 al state /\
    state_eq h1 al state (spec_blake2_incremental_update_inner al (spec_of h0 al state) (v ll) (v rb) (v ll0) h0.[|input|]))

inline_for_extraction noextract
val blake2_incremental_update_inner: al:Spec.alg -> blake2_incremental_update_inner_longer_t al -> blake2_incremental_update_inner_t al

let blake2_incremental_update_inner al blake2_incremental_update_inner_longer state ll rb ll0 input =
  let h0 = ST.get () in
  let pl = state_get_pl al state in
  if ll <=. rb then (
    let ha0 = ST.get () in
    upd state.pl 0ul (pl +! ll0);
    let ha1 = ST.get () in
    modifies1_is_modifies4 state.pl state.hash state.block state.n ha0 ha1)
  else
    blake2_incremental_update_inner_longer h0 state ll input rb ll0


noextract
val spec_compute_branching_condition:
    al:Spec.alg
  -> state:(SpecI.state_r al)
  -> ll:size_nat{state.SpecI.n + 2 + ll / v (size_block al) <= max_size_t} ->
  Tot bool

let spec_compute_branching_condition al state ll =
  let nll = ll / v (size_block al) in
  ll = 0 || not (state.SpecI.n + nll + 2 <= max_size_t)


inline_for_extraction noextract
val compute_branching_condition:
    al:Spec.alg
  -> h:mem
  -> state:state_r al
  -> ll:size_t{v (gstate_get_n h al state) + 2 + v ll / v (size_block al) <= max_size_t} ->
  Stack bool
  (requires fun h ->
    state_inv h al state /\
    v (gstate_get_n h al state) + 2 + v ll / v (size_block al) <= max_size_t)
  (ensures (fun h0 b h1 -> (h0 == h1 /\ b == spec_compute_branching_condition al (spec_of h al state) (v ll))))

inline_for_extraction noextract
let compute_branching_condition al h state ll =
  [@inline_let]
  let max = normalize_term (size max_size_t) in
  let nll = ll /. (size_block al) in
  let n: size_t = state_get_n al state in
  ll =. 0ul || not (n +! nll +! 2ul <=. max)


noextract
val spec_blake2_incremental_update:
    al:Spec.Blake2.alg
  -> state:(SpecI.state_r al)
  -> ll:size_nat{state.SpecI.n + 2 + ll / v (size_block al) <= max_size_t} // Why N+2? (Might be too strong!)
  -> input:LBS.lbytes ll ->
  Tot (option (SpecI.state_r al))

let spec_blake2_incremental_update al state ll input =
  let open Spec.Blake2.Incremental in
  if spec_compute_branching_condition al state ll then None else (
  let rb = v (size_block al) - state.SpecI.pl in
  let ll0 = if ll < rb then ll else rb in
  let partial = Lib.Sequence.sub input 0 ll0 in
  let block = Lib.Sequence.update_sub state.SpecI.block state.SpecI.pl ll0 partial in
  let state = {state with block = block} in
  let state = spec_blake2_incremental_update_inner al state ll rb ll0 input in
  Some state)


///
/// BB. TODO: Show 'spec_blake2b_incremental_update state ll input
///                 == SpecI.blake2_incremental_update Spec.Blake2B h0.[|input|] (spec_of h0 state)'
///

inline_for_extraction noextract
let blake2_incremental_update_t (al:Spec.alg) =
    state:state_r al
  -> ll:size_t
  -> input:lbuffer uint8 ll ->
  Stack bool
  (requires fun h ->
    live h input /\
    disjoint state.hash input /\ disjoint state.block input /\
    disjoint state.n input /\ disjoint state.pl input /\
    state_inv h al state /\
    v (gstate_get_n h al state) + 2 + v ll / v (size_block al) <= max_size_t /\
    (v (gstate_get_n h al state) + 1) * v (size_block al) <= max_size_t /\
    v (gstate_get_n h al state) * v (size_block al) + v ll < Spec.max_limb al)
  (ensures  fun h0 b h1 ->
    state_inv h1 al state /\
    modifies4 state.hash state.block state.n state.pl h0 h1 /\
    (let osstate = spec_blake2_incremental_update al (spec_of h0 al state) (v ll) h0.[|input|] in
    match osstate with | None -> b == false | Some sstate -> b == true /\ (spec_of h1 al state) == sstate))

inline_for_extraction noextract
val blake2_incremental_update: al:Spec.alg -> blake2_incremental_update_inner_t al -> blake2_incremental_update_t al
let blake2_incremental_update al blake2_incremental_update_inner state ll input =
  let h0 = ST.get() in
  if compute_branching_condition al h0 state ll then false // BB. I am surprised that this works regarding 'modifies'
  else (
    let pl = state_get_pl al state in
    let rb = size_block al -! pl in
    let ll0 = if ll <. rb then ll else rb in
    let partial = sub input 0ul ll0 in
    update_sub state.block pl ll0 partial;
    blake2_incremental_update_inner state ll rb ll0 input;
    true)

inline_for_extraction noextract
let blake2_incremental_finish_t (al:Spec.alg) =
    nn:size_t{1 <= v nn /\ v nn <= Spec.max_key al}
  -> output:lbuffer uint8 nn
  -> state:state_r al ->
  Stack unit
    (requires fun h ->
      state_inv h al state /\ live h output /\
      disjoint output state.hash /\
      state_inv h al state)
    (ensures  fun h0 _ h1 ->
      modifies2 output state.hash h0 h1 /\
      h1.[|output|] == Spec.Blake2.Incremental.blake2_incremental_finish al (spec_of h0 al state) (v nn))

inline_for_extraction noextract
val blake2_incremental_finish: al:Spec.alg -> blake2_update_last_t al -> blake2_finish_t al -> blake2_incremental_finish_t al

let blake2_incremental_finish al blake2_update_last blake2_finish nn output state =
  let h0 = ST.get () in
  let pl = state_get_pl al state  in
  let last = sub state.block 0ul pl in
  let n = state_get_n al state in
  let wn = size_to_word al n in
  let wsize_block = size_to_word al (size_block al) in
  let wpl = size_to_word al pl in
  admit();
  let prev = Spec.word_to_limb al (wn *! wsize_block +! wpl) in
  assert(v prev = (spec_of h0 al state).SpecI.n * (Spec.Blake2.size_block al) + (spec_of h0 al state).SpecI.pl);
  blake2_update_last state.hash prev pl last;
  blake2_finish nn output state.hash
