module Hacl.Impl.Frodo.Gen

open FStar.HyperStack.All
open FStar.HyperStack
open FStar.HyperStack.ST
open FStar.Mul

open LowStar.Buffer
open LowStar.BufferOps

open Lib.IntTypes
open Lib.PQ.Buffer

open Hacl.Impl.PQ.Lib
open Hacl.Keccak
open Hacl.Impl.Frodo.Params

module ST = FStar.HyperStack.ST
module Lemmas = Spec.Frodo.Lemmas

#reset-options "--z3rlimit 50 --max_fuel 0 --max_ifuel 0 --using_facts_from '* -FStar.Seq'"

val frodo_gen_matrix_cshake:
    n:size_t{0 < 2 * v n /\ 2 * v n < max_size_t /\ v n * v n < max_size_t}
  -> seed_len:size_t{v seed_len > 0}
  -> seed:lbytes seed_len
  -> res:matrix_t n n
  -> Stack unit
    (requires fun h -> live h seed /\ live h res /\ disjoint seed res)
    (ensures  fun h0 r h1 -> live h1 res /\ modifies (loc_buffer res) h0 h1)
[@"c_inline"]
let frodo_gen_matrix_cshake n seed_len seed res =
  push_frame();
  let r = create (size 2 *! n) (u8 0) in
  let h0 = ST.get () in
  let inv h1 j =
    live h1 res /\ live h1 r /\ modifies (loc_union (loc_buffer res) (loc_buffer r)) h0 h1
  in
  let f' (i:size_t{0 <= v i /\ v i < v n}): Stack unit
    (requires fun h -> inv h (v i))
    (ensures  fun _ _ h2 -> inv h2 (v i + 1)) =
    let ctr = size_to_uint32 (size 256 +. i) in
    cshake128_frodo seed_len seed (to_u16 ctr) (size 2 *! n) r;
    let h0 = ST.get () in
    loop_nospec #h0 n res
    (fun j ->
      let resij = sub r (size 2 *! j) (size 2) in
      mset res i j (uint_from_bytes_le resij)
    )
  in
  Lib.Loops.for (size 0) n inv f';
  pop_frame()
