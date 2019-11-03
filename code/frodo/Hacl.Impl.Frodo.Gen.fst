module Hacl.Impl.Frodo.Gen

open FStar.HyperStack
open FStar.HyperStack.ST
open FStar.Mul

open LowStar.Buffer

open Lib.IntTypes
open Lib.Buffer
open Lib.ByteBuffer

open Hacl.Impl.Matrix

module ST = FStar.HyperStack.ST
module HS = FStar.HyperStack
module B = LowStar.Buffer
module Lemmas = Spec.Frodo.Lemmas
module S = Spec.Frodo.Gen
module SHA3 = Hacl.SHA3

#reset-options "--z3rlimit 50 --max_fuel 0 --max_ifuel 0 --using_facts_from '* -FStar.Seq'"

inline_for_extraction noextract private
val frodo_gen_matrix_cshake0:
    n:size_t{2 * v n <= max_size_t /\ 256 + v n < maxint U16 /\ v n * v n <= max_size_t}
  -> i:size_t{v i < v n}
  -> r:lbytes (size 2 *! n)
  -> j:size_t{v j < v n}
  -> res:matrix_t n n
  -> Stack unit
    (requires fun h -> live h r /\ live h res)
    (ensures  fun h0 _ h1 ->
      modifies1 res h0 h1 /\
      as_matrix h1 res ==
      S.frodo_gen_matrix_cshake0 (v n) (v i) (as_seq h0 r) (v j) (as_matrix h0 res))
let frodo_gen_matrix_cshake0 n i r j res =
  let resij = sub r (size 2 *! j) (size 2) in
  mset res i j (uint_from_bytes_le resij)

inline_for_extraction noextract private
val frodo_gen_matrix_cshake1:
    n:size_t{2 * v n <= max_size_t /\ 256 + v n < maxint U16 /\ v n * v n <= max_size_t}
  -> seed_len:size_t{v seed_len > 0}
  -> seed:lbytes seed_len
  -> r:lbytes (size 2 *! n)
  -> i:size_t{v i < v n}
  -> res:matrix_t n n
  -> Stack unit
    (requires fun h ->
      live h seed /\ live h res /\ live h r /\
      disjoint res seed /\ disjoint res r /\ disjoint r seed)
    (ensures  fun h0 _ h1 ->
      modifies2 res r h0 h1 /\
      as_matrix h1 res == S.frodo_gen_matrix_cshake1 (v n) (v seed_len) (as_seq h0 seed) (v i) (as_matrix h0 res))
let frodo_gen_matrix_cshake1 n seed_len seed r i res =
  let ctr = size_to_uint32 (size 256 +. i) in
  //uintv_extensionality (to_u16 ctr) (u16 (256 + v i));
  SHA3.cshake128_frodo seed_len seed (to_u16 ctr) (size 2 *! n) r;
  [@ inline_let]
  let spec h0 = S.frodo_gen_matrix_cshake0 (v n) (v i) (as_seq h0 r) in
  let h0 = ST.get () in
  loop1 h0 n res spec
  (fun j ->
    Lib.LoopCombinators.unfold_repeati (v n) (spec h0) (as_matrix h0 res) (v j);
    frodo_gen_matrix_cshake0 n i r j res
  )

val frodo_gen_matrix_cshake:
    n:size_t{0 < v n /\ 2 * v n <= max_size_t /\ 256 + v n < maxint U16 /\ v n * v n <= max_size_t}
  -> seed_len:size_t{v seed_len > 0}
  -> seed:lbytes seed_len
  -> res:matrix_t n n
  -> Stack unit
    (requires fun h -> live h seed /\ live h res /\ disjoint seed res)
    (ensures  fun h0 _ h1 ->
      modifies1 res h0 h1 /\
      as_matrix h1 res == S.frodo_gen_matrix_cshake (v n) (v seed_len) (as_seq h0 seed))
[@"c_inline"]
let frodo_gen_matrix_cshake n seed_len seed res =
  push_frame ();
  let r = create (size 2 *! n) (u8 0) in
  memset res (u16 0) (n *! n);
  let h0 = ST.get () in
  Lib.Sequence.eq_intro (Lib.Sequence.sub (as_seq h0 res) 0 (v n * v n)) (as_seq h0 res);
  [@ inline_let]
  let refl h i = as_matrix h res in
  [@ inline_let]
  let footprint i = loc res |+| loc r in
  [@ inline_let]
  let spec h0 = S.frodo_gen_matrix_cshake1 (v n) (v seed_len) (as_seq h0 seed) in
  let h0 = ST.get () in
  loop h0 n (S.frodo_gen_matrix_cshake_s (v n)) refl footprint spec
  (fun i ->
    Lib.LoopCombinators.unfold_repeat_gen (v n) (S.frodo_gen_matrix_cshake_s (v n)) (spec h0) (refl h0 0) (v i);
    frodo_gen_matrix_cshake1 n seed_len seed r i res
  );
  pop_frame ()

inline_for_extraction noextract private
val frodo_gen_matrix_cshake_4x0:
    n:size_t{2 * v n <= max_size_t /\ 256 + v n < maxint U16 /\ v n * v n <= max_size_t}
  -> i:size_t{v i < v n / 4}
  -> r0:lbytes (size 2 *! n)
  -> r1:lbytes (size 2 *! n)
  -> r2:lbytes (size 2 *! n)
  -> r3:lbytes (size 2 *! n)
  -> j:size_t{v j < v n}
  -> res:matrix_t n n
  -> Stack unit
    (requires fun h ->
      live h r0 /\ live h r1 /\ live h r2 /\
      live h r3 /\ live h res /\
      B.loc_pairwise_disjoint
        [loc res; loc r0; loc r1; loc r2; loc r3])
    (ensures  fun h0 _ h1 ->
      modifies1 res h0 h1 /\
      as_matrix h1 res ==
      S.frodo_gen_matrix_cshake_4x0 (v n) (v i) (as_seq h0 r0) (as_seq h0 r1)
        (as_seq h0 r2) (as_seq h0 r3) (v j) (as_matrix h0 res))
let frodo_gen_matrix_cshake_4x0 n i r0 r1 r2 r3 j res =
  let resij0 = sub r0 (j *! size 2) (size 2) in
  let resij1 = sub r1 (j *! size 2) (size 2) in
  let resij2 = sub r2 (j *! size 2) (size 2) in
  let resij3 = sub r3 (j *! size 2) (size 2) in
  mset res (size 4 *! i +! size 0) j (uint_from_bytes_le resij0);
  mset res (size 4 *! i +! size 1) j (uint_from_bytes_le resij1);
  mset res (size 4 *! i +! size 2) j (uint_from_bytes_le resij2);
  mset res (size 4 *! i +! size 3) j (uint_from_bytes_le resij3)

// 2019.03.04: SZ this works with ifuel=0 in interactive mode but fails in batch
#set-options "--z3rlimit 150 --initial_ifuel 1 --max_ifuel 1"

inline_for_extraction noextract private
val frodo_gen_matrix_cshake_4x1:
    n:size_t{2 * v n <= max_size_t /\ 256 + v n < maxint U16 /\ v n * v n <= max_size_t}
  -> seed_len:size_t{v seed_len > 0}
  -> seed:lbytes seed_len
  -> r:lbytes (size 8 *! n)
  -> i:size_t{v i < v n / 4}
  -> res:matrix_t n n
  -> Stack unit
    (requires fun h ->
      live h seed /\ live h res /\ live h r /\
      disjoint res seed /\ disjoint res r /\ disjoint r seed)
    (ensures  fun h0 _ h1 ->
      modifies2 res r h0 h1 /\
      as_matrix h1 res ==
      S.frodo_gen_matrix_cshake_4x1 (v n) (v seed_len) (as_seq h0 seed) (v i) (as_matrix h0 res))
let frodo_gen_matrix_cshake_4x1 n seed_len seed r i res =
  let r0 = sub r (size 0 *! n) (size 2 *! n) in
  let r1 = sub r (size 2 *! n) (size 2 *! n) in
  let r2 = sub r (size 4 *! n) (size 2 *! n) in
  let r3 = sub r (size 6 *! n) (size 2 *! n) in
  let ctr0 = size_to_uint32 (size 256 +. size 4 *! i +. size 0) in
  assert (to_u16 ctr0 == u16 (256 + 4 * v i + 0));
  let ctr1 = size_to_uint32 (size 256 +. size 4 *! i +. size 1) in
  assert (to_u16 ctr1 == u16 (256 + 4 * v i + 1));
  let ctr2 = size_to_uint32 (size 256 +. size 4 *! i +. size 2) in
  assert (to_u16 ctr2 == u16 (256 + 4 * v i + 2));
  let ctr3 = size_to_uint32 (size 256 +. size 4 *! i +. size 3) in
  assert (to_u16 ctr3 == u16 (256 + 4 * v i + 3));
  Hacl.Keccak.cshake128_frodo_4x seed_len seed
    (to_u16 ctr0) (to_u16 ctr1) (to_u16 ctr2) (to_u16 ctr3)
    (size 2 *! n) r0 r1 r2 r3;
  [@ inline_let]
  let spec h0 = S.frodo_gen_matrix_cshake_4x0 (v n) (v i)
    (as_seq h0 r0) (as_seq h0 r1) (as_seq h0 r2) (as_seq h0 r3) in
  let h0 = ST.get () in
  loop1 h0 n res spec
  (fun j ->
    Lib.LoopCombinators.unfold_repeati (v n) (spec h0) (as_matrix h0 res) (v j);
    frodo_gen_matrix_cshake_4x0 n i r0 r1 r2 r3 j res
  )

#reset-options "--z3rlimit 150 --max_fuel 1 --max_ifuel 0 --using_facts_from '* -FStar.Seq'"

inline_for_extraction noextract
val frodo_gen_matrix_cshake_4x:
    n:size_t{0 < v n /\ 2 * v n <= max_size_t /\ 256 + v n < maxint U16 /\ v n * v n <= max_size_t /\ v n % 4 = 0}
  -> seed_len:size_t{v seed_len > 0}
  -> seed:lbytes seed_len
  -> res:matrix_t n n
  -> Stack unit
    (requires fun h ->
      8 * v n <= max_size_t /\
      live h seed /\ live h res /\ disjoint seed res)
    (ensures  fun h0 _ h1 ->
      modifies1 res h0 h1 /\
      as_matrix h1 res == S.frodo_gen_matrix_cshake (v n) (v seed_len) (as_seq h0 seed))
let frodo_gen_matrix_cshake_4x n seed_len seed res =
  push_frame ();
  let r = create (size 8 *! n) (u8 0) in
  memset res (u16 0) (n *! n);
  let h0 = ST.get () in
  Lib.Sequence.eq_intro (Lib.Sequence.sub (as_seq h0 res) 0 (v n * v n)) (as_seq h0 res);
  [@ inline_let]
  let refl h i = as_matrix h res in
  [@ inline_let]
  let footprint i = loc res |+| loc r in
  [@ inline_let]
  let spec h0 = S.frodo_gen_matrix_cshake_4x1 (v n) (v seed_len) (as_seq h0 seed) in
  let n4 = n /. size 4 in
  let h0 = ST.get () in
  loop h0 n4 (S.frodo_gen_matrix_cshake_4x_s (v n)) refl footprint spec
  (fun i ->
    Lib.LoopCombinators.unfold_repeat_gen (v n4) (S.frodo_gen_matrix_cshake_4x_s (v n)) (spec h0) (refl h0 0) (v i);
    frodo_gen_matrix_cshake_4x1 n seed_len seed r i res
  );
  let h1 = ST.get () in
  assert (as_matrix h1 res ==
    Lib.LoopCombinators.repeat_gen (v n4) (S.frodo_gen_matrix_cshake_4x_s (v n)) (spec h0) (refl h0 0));
  S.frodo_gen_matrix_cshake_4x_lemma (v n) (v seed_len) (as_seq h0 seed);
  assert (
    S.frodo_gen_matrix_cshake_4x (v n) (v seed_len) (as_seq h0 seed) ==
    Lib.LoopCombinators.repeat_gen (v n4) (S.frodo_gen_matrix_cshake_4x_s (v n)) (spec h0) (refl h0 0));
  pop_frame ();
  assert (
    S.frodo_gen_matrix_cshake_4x (v n) (v seed_len) (as_seq h0 seed) ==
    S.frodo_gen_matrix_cshake (v n) (v seed_len) (as_seq h0 seed))


/// AES128

#reset-options "--z3rlimit 200 --max_fuel 0 --max_ifuel 0 --using_facts_from '* -FStar.Seq'"

val frodo_gen_matrix_aes:
    n:size_t{v n * v n <= max_size_t /\ v n < maxint U16}
  -> seed_len:size_t{v seed_len == 16}
  -> seed:lbytes seed_len
  -> a:matrix_t n n
  -> Stack unit
    (requires fun h -> live h seed /\ live h a /\ disjoint seed a)
    (ensures  fun h0 _ h1 ->
      modifies1 a h0 h1 /\
      as_matrix h1 a == S.frodo_gen_matrix_aes (v n) (v seed_len) (as_seq h0 seed))
[@"c_inline"]
let frodo_gen_matrix_aes n seed_len seed a =
  push_frame();
  let key = create (size 176) (u8 0) in
  Hacl.AES128.aes128_key_expansion seed key;

  let h0 = ST.get() in
  Lib.Loops.for (size 0) n
    (fun h1 i -> modifies1 a h0 h1)
    (fun i ->
      let h1 = ST.get() in
      Lib.Loops.for (size 0) (n /. size 8)
        (fun h2 j -> modifies1 a h1 h2)
        (fun j ->
          let j = j *! size 8 in
          a.[i, j] <- to_u16 (size_to_uint32 i);
          a.[i, j +! size 1] <- to_u16 (size_to_uint32 j)
        )
    );

  let h0 = ST.get() in
  Lib.Loops.for (size 0) n
    (fun h1 i -> modifies1 a h0 h1)
    (fun i ->
      let h1 = ST.get() in
      Lib.Loops.for (size 0) (n /. size 8)
        (fun h2 j -> modifies1 a h1 h2)
        (fun j ->
          let j = j *! size 8 in
          assert (v j + 8 <= v n);
          assert (v i <= v n - 1);
          FStar.Math.Lemmas.lemma_mult_le_right (v n) (v i) (v n - 1);
          assert (v i * v n + v j + 8 <= (v n - 1) * v n + v n);
          let b = sub a (i *! n +! j) (size 8) in
          Hacl.AES128.aes128_encrypt_block b b key
        )
    );
  pop_frame();
  let h1 = ST.get() in
  assume (as_matrix h1 a == S.frodo_gen_matrix_aes (v n) (v seed_len) (as_seq h0 seed))
