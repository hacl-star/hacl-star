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
module HS = FStar.HyperStack
module B = LowStar.Buffer
module Lemmas = Spec.Frodo.Lemmas
module S = Spec.Frodo.Gen

#reset-options "--z3rlimit 50 --max_fuel 0 --max_ifuel 0 --using_facts_from '* -FStar.Seq'"

private
val gen_inv:
    h0:HS.mem
  -> h1:HS.mem
  -> h2:HS.mem
  -> n:size_t{2 * v n < max_size_t /\ 256 + v n < maxint U16 /\ v n * v n < max_size_t}
  -> seed_len:size_t{v seed_len > 0}
  -> seed:lbytes seed_len
  -> r:lbytes (size 2 *! n)
  -> res:matrix_t n n
  -> i:size_t{v i < v n}
  -> j:size_nat
  -> Type0
let gen_inv h0 h1 h2 n seed_len seed r res i j =
  B.live h2 res /\ B.live h2 seed /\ B.live h2 r /\
  disjoint seed res /\ disjoint r res /\
  modifies (loc_buffer res) h1 h2 /\ j <= v n /\
  (forall (i0:size_nat{i0 < v i}) (j:size_nat{j < v n}). get h2 res i0 j == get h1 res i0 j) /\
  (forall (j0:size_nat{j0 < j}). get h2 res (v i) j0 == S.frodo_gen_matrix_cshake_fc (v n) (v seed_len) (as_seq h0 seed) (v i) j0) /\
  (forall (j0:size_nat{j <= j0 /\ j0 < v n}). get h2 res (v i) j0 == get h0 res (v i) j0) /\
  (forall (i0:size_nat{v i < i0 /\ i0 < v n}) (j:size_nat{j < v n}). get h2 res i0 j == get h0 res i0 j) /\
  as_seq h1 r == Spec.Frodo.Keccak.cshake128_frodo (v seed_len) (as_seq h0 seed) (u16 (256 + v i)) (2 * v n) /\
  as_seq h1 r == as_seq h2 r

inline_for_extraction noextract private
val frodo_gen_matrix_cshake_fc:
    h0:HS.mem
  -> h1:HS.mem
  -> n:size_t{2 * v n < max_size_t /\ 256 + v n < maxint U16 /\ v n * v n < max_size_t}
  -> seed_len:size_t{v seed_len > 0}
  -> seed:lbytes seed_len
  -> r:lbytes (size 2 *! n)
  -> res0:matrix_t n n
  -> i:size_t{v i < v n}
  -> j:size_t{v j < v n}
  -> Stack unit
    (requires fun h2 -> gen_inv h0 h1 h2 n seed_len seed r res0 i (v j))
    (ensures  fun _ _ h2 -> gen_inv h0 h1 h2 n seed_len seed r res0 i (v j + 1))
let frodo_gen_matrix_cshake_fc h0 h1 n seed_len seed r res0 i j =
  let resij = sub r (size 2 *! j) (size 2) in
  mset res0 i j (uint_from_bytes_le resij)

private
val gen_inner_inv:
    h0:HS.mem
  -> h1:HS.mem
  -> n:size_t{2 * v n < max_size_t /\ 256 + v n < maxint U16 /\ v n * v n < max_size_t}
  -> seed_len:size_t{v seed_len > 0}
  -> seed:lbytes seed_len
  -> res:matrix_t n n
  -> r:lbytes (size 2 *! n)
  -> i:size_nat{i <= v n}
  -> Type0
let gen_inner_inv h0 h1 n seed_len seed res r i =
  B.live h1 r /\ B.live h1 res /\ B.live h1 seed /\
  disjoint seed res /\ disjoint seed r /\ disjoint r res /\
  modifies (loc_union (loc_buffer res) (loc_buffer r)) h0 h1 /\ as_seq h0 seed == as_seq h1 seed /\
  (forall (i0:size_nat{i0 < i}) (j:size_nat{j < v n}). get h1 res i0 j == S.frodo_gen_matrix_cshake_fc (v n) (v seed_len) (as_seq h0 seed) i0 j) /\
  (forall (i0:size_nat{i <= i0 /\ i0 < v n}) (j:size_nat{j < v n}). get h1 res i0 j == get h0 res i0 j)

inline_for_extraction noextract private
val frodo_gen_matrix_cshake_inner:
    h0:HS.mem
  -> n:size_t{0 < 2 * v n /\ 2 * v n < max_size_t /\ 256 + v n < maxint U16 /\ v n * v n < max_size_t}
  -> seed_len:size_t{v seed_len > 0}
  -> seed:lbytes seed_len
  -> res:matrix_t n n
  -> r:lbytes (size 2 *! n)
  -> i:size_t{v i < v n}
  -> Stack unit
    (requires fun h1 -> gen_inner_inv h0 h1 n seed_len seed res r (v i))
    (ensures  fun _ _ h1 -> gen_inner_inv h0 h1 n seed_len seed res r (v i + 1))
let frodo_gen_matrix_cshake_inner h0 n seed_len seed res r i =
  let h0 = ST.get () in
  let ctr = size_to_uint32 (size 256 +. i) in
  uintv_extensionality (to_u16 (size_to_uint32 (size 256 +. i))) (u16 (256 + v i));
  cshake128_frodo seed_len seed (to_u16 ctr) (size 2 *! n) r;
  let h1 = ST.get () in
  Lib.Loops.for (size 0) n
    (fun h2 j -> gen_inv h0 h1 h2 n seed_len seed r res i j)
    (fun j -> frodo_gen_matrix_cshake_fc h0 h1 n seed_len seed r res i j);
  let h2 = ST.get () in
  assert (gen_inner_inv h0 h2 n seed_len seed res r (v i + 1))

val frodo_gen_matrix_cshake:
    n:size_t{0 < v n /\ 2 * v n < max_size_t /\ 256 + v n < maxint U16 /\ v n * v n < max_size_t}
  -> seed_len:size_t{v seed_len > 0}
  -> seed:lbytes seed_len
  -> res:matrix_t n n
  -> Stack unit
    (requires fun h -> live h seed /\ live h res /\ disjoint seed res)
    (ensures  fun h0 _ h1 ->
      live h1 res /\ modifies (loc_buffer res) h0 h1 /\
      as_matrix h1 res == S.frodo_gen_matrix_cshake (v n) (v seed_len) (as_seq h0 seed))
[@"c_inline"]
let frodo_gen_matrix_cshake n seed_len seed res =
  push_frame ();
  let r = create (size 2 *! n) (u8 0) in
  let h0 = ST.get () in
  Lib.Loops.for (size 0) n
    (fun h1 i -> gen_inner_inv h0 h1 n seed_len seed res r i)
    (fun i -> frodo_gen_matrix_cshake_inner h0 n seed_len seed res r i);
  pop_frame ();
  let h1 = ST.get () in
  Spec.Matrix.extensionality (as_matrix h1 res) (S.frodo_gen_matrix_cshake (v n) (v seed_len) (as_seq h0 seed))
