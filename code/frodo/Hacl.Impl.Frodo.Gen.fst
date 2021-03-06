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
module B = LowStar.Buffer
module LSeq = Lib.Sequence
module BSeq = Lib.ByteSequence
module Loops = Lib.LoopCombinators

module S = Spec.Frodo.Gen
module Lemmas = Spec.Frodo.Lemmas
module SHA3 = Hacl.SHA3

#set-options "--z3rlimit 50 --fuel 0 --ifuel 0"

inline_for_extraction noextract private
val frodo_gen_matrix_shake0:
    n:size_t{v n * v n <= max_size_t /\ 2 * v n <= max_size_t}
  -> i:size_t{v i < v n}
  -> r:lbytes (size 2 *! n)
  -> j:size_t{v j < v n}
  -> res:matrix_t n n
  -> Stack unit
    (requires fun h -> live h r /\ live h res)
    (ensures  fun h0 _ h1 -> modifies1 res h0 h1 /\
      as_matrix h1 res == S.frodo_gen_matrix_shake0 (v n) (v i) (as_seq h0 r) (v j) (as_matrix h0 res))

let frodo_gen_matrix_shake0 n i r j res =
  let resij = sub r (size 2 *! j) (size 2) in
  mset res i j (uint_from_bytes_le resij)


inline_for_extraction noextract private
val concat_ind_seed:
    tmp_seed:lbytes 18ul
  -> i:size_t{v i < maxint U16}
  -> Stack unit
    (requires fun h -> live h tmp_seed)
    (ensures  fun h0 _ h1 -> modifies (loc tmp_seed) h0 h1 /\
      as_seq h1 tmp_seed == LSeq.concat (BSeq.uint_to_bytes_le (u16 (v i))) (LSeq.sub (as_seq h0 tmp_seed) 2 16) /\
      LSeq.sub (as_seq h0 tmp_seed) 2 16 == LSeq.sub (as_seq h1 tmp_seed) 2 16)

let concat_ind_seed tmp_seed i =
  let h0 = ST.get () in
  update_sub_f h0 tmp_seed 0ul 2ul
    (fun h -> BSeq.uint_to_bytes_le (to_u16 i))
    (fun _ -> uint_to_bytes_le (sub tmp_seed 0ul 2ul) (to_u16 i));
  let h1 = ST.get () in
  LSeq.eq_intro
    (as_seq h1 tmp_seed)
    (LSeq.concat (BSeq.uint_to_bytes_le (to_u16 i)) (LSeq.sub (as_seq h0 tmp_seed) 2 16));
  LSeq.eq_intro (LSeq.sub (as_seq h0 tmp_seed) 2 16) (LSeq.sub (as_seq h1 tmp_seed) 2 16)


inline_for_extraction noextract private
val frodo_gen_matrix_shake1:
    n:size_t{v n * v n <= max_size_t /\ v n <= maxint U16}
  -> tmp_seed:lbytes 18ul
  -> r:lbytes (size 2 *! n)
  -> i:size_t{v i < v n}
  -> res:matrix_t n n
  -> Stack unit
    (requires fun h ->
      live h tmp_seed /\ live h res /\ live h r /\
      disjoint res tmp_seed /\ disjoint res r /\ disjoint r tmp_seed)
    (ensures  fun h0 _ h1 -> modifies (loc res |+| loc r |+| loc tmp_seed) h0 h1 /\
      as_matrix h1 res == S.frodo_gen_matrix_shake1 (v n) (LSeq.sub (as_seq h0 tmp_seed) 2 16) (v i) (as_matrix h0 res) /\
      LSeq.sub (as_seq h0 tmp_seed) 2 16 == LSeq.sub (as_seq h1 tmp_seed) 2 16)

let frodo_gen_matrix_shake1 n tmp_seed r i res =
  concat_ind_seed tmp_seed i;
  SHA3.shake128_hacl 18ul tmp_seed (2ul *! n) r;

  [@ inline_let]
  let spec h0 = S.frodo_gen_matrix_shake0 (v n) (v i) (as_seq h0 r) in
  let h0 = ST.get () in
  loop1 h0 n res spec
  (fun j ->
    Loops.unfold_repeati (v n) (spec h0) (as_matrix h0 res) (v j);
    frodo_gen_matrix_shake0 n i r j res
  )


val frodo_gen_matrix_shake:
    n:size_t{0 < v n /\ v n * v n <= max_size_t /\ v n <= maxint U16}
  -> seed:lbytes 16ul
  -> res:matrix_t n n
  -> Stack unit
    (requires fun h ->
      live h seed /\ live h res /\ disjoint seed res)
    (ensures  fun h0 _ h1 -> modifies1 res h0 h1 /\
      as_matrix h1 res == S.frodo_gen_matrix_shake (v n) (as_seq h0 seed))

[@"c_inline"]
let frodo_gen_matrix_shake n seed res =
  push_frame ();
  let r = create (size 2 *! n) (u8 0) in
  let tmp_seed = create 18ul (u8 0) in
  copy (sub tmp_seed 2ul 16ul) seed;

  memset res (u16 0) (n *! n);
  let h0 = ST.get () in
  LSeq.eq_intro (LSeq.sub (as_seq h0 res) 0 (v n * v n)) (as_seq h0 res);

  [@ inline_let]
  let spec h0 = S.frodo_gen_matrix_shake1 (v n) (as_seq h0 seed) in

  [@ inline_let]
  let inv h (i:nat{i <= v n}) =
    modifies (loc res |+| loc r |+| loc tmp_seed) h0 h /\
    LSeq.sub (as_seq h0 tmp_seed) 2 16 == LSeq.sub (as_seq h tmp_seed) 2 16 /\
    as_seq h res == Loops.repeati i (spec h0) (as_seq h0 res) in

  Loops.eq_repeati0 (v n) (spec h0) (as_seq h0 res);
  Lib.Loops.for 0ul n inv
    (fun i ->
      Loops.unfold_repeati (v n) (spec h0) (as_seq h0 res) (v i);
      frodo_gen_matrix_shake1 n tmp_seed r i res);
  pop_frame ()


inline_for_extraction noextract private
val frodo_gen_matrix_shake_4x0:
    n:size_t{v n * v n <= max_size_t /\ v n <= maxint U16}
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
      B.loc_pairwise_disjoint [loc res; loc r0; loc r1; loc r2; loc r3])
    (ensures  fun h0 _ h1 -> modifies1 res h0 h1 /\
      as_matrix h1 res ==
      S.frodo_gen_matrix_shake_4x0 (v n) (v i) (as_seq h0 r0) (as_seq h0 r1)
        (as_seq h0 r2) (as_seq h0 r3) (v j) (as_matrix h0 res))

let frodo_gen_matrix_shake_4x0 n i r0 r1 r2 r3 j res =
  let resij0 = sub r0 (j *! size 2) (size 2) in
  let resij1 = sub r1 (j *! size 2) (size 2) in
  let resij2 = sub r2 (j *! size 2) (size 2) in
  let resij3 = sub r3 (j *! size 2) (size 2) in
  mset res (size 4 *! i +! size 0) j (uint_from_bytes_le resij0);
  mset res (size 4 *! i +! size 1) j (uint_from_bytes_le resij1);
  mset res (size 4 *! i +! size 2) j (uint_from_bytes_le resij2);
  mset res (size 4 *! i +! size 3) j (uint_from_bytes_le resij3)


val tmp_seed4_pre: h:mem -> tmp_seed:lbytes (18ul *! 4ul) -> Type0
let tmp_seed4_pre h tmp_seed =
  let seed0 = LSeq.sub (as_seq h tmp_seed) 2 16 in
  let seed1 = LSeq.sub (as_seq h tmp_seed) 20 16 in
  let seed2 = LSeq.sub (as_seq h tmp_seed) 38 16 in
  let seed3 = LSeq.sub (as_seq h tmp_seed) 56 16 in
  seed0 == seed1 /\ seed0 == seed2 /\ seed0 == seed3


inline_for_extraction noextract private
val frodo_gen_matrix_shake_4x1_get_r:
    n:size_t{v n * v n <= max_size_t /\ v n <= maxint U16}
  -> tmp_seed:lbytes (18ul *! 4ul)
  -> r0:lbytes (2ul *! n)
  -> r1:lbytes (2ul *! n)
  -> r2:lbytes (2ul *! n)
  -> r3:lbytes (2ul *! n)
  -> i:size_t{v i < v n / 4}
  -> Stack unit
    (requires fun h -> tmp_seed4_pre h tmp_seed /\
      live h tmp_seed /\ live h r0 /\ live h r1 /\ live h r2 /\ live h r3 /\
      loc_pairwise_disjoint [loc tmp_seed; loc r0; loc r1; loc r2; loc r3])
    (ensures  fun h0 _ h1 -> modifies (loc r0 |+| loc r1 |+| loc r2 |+| loc r3 |+| loc tmp_seed) h0 h1 /\
      (as_seq h1 r0, as_seq h1 r1, as_seq h1 r2, as_seq h1 r3) ==
      S.frodo_gen_matrix_shake_4x1_get_r (v n) (LSeq.sub (as_seq h0 tmp_seed) 2 16) (v i) /\
      LSeq.sub (as_seq h0 tmp_seed) 2 16 == LSeq.sub (as_seq h1 tmp_seed) 2 16 /\ tmp_seed4_pre h1 tmp_seed)

let frodo_gen_matrix_shake_4x1_get_r n tmp_seed r0 r1 r2 r3 i =
  let tmp_seed0 = sub tmp_seed 0ul 18ul in
  let tmp_seed1 = sub tmp_seed 18ul 18ul in
  let tmp_seed2 = sub tmp_seed 36ul 18ul in
  let tmp_seed3 = sub tmp_seed 54ul 18ul in
  concat_ind_seed tmp_seed0 (4ul *! i +! 0ul);
  concat_ind_seed tmp_seed1 (4ul *! i +! 1ul);
  concat_ind_seed tmp_seed2 (4ul *! i +! 2ul);
  concat_ind_seed tmp_seed3 (4ul *! i +! 3ul);

  Hacl.Keccak.shake128_4x 18ul tmp_seed0 tmp_seed1 tmp_seed2 tmp_seed3 (size 2 *! n) r0 r1 r2 r3


inline_for_extraction noextract private
val frodo_gen_matrix_shake_4x1:
    n:size_t{v n * v n <= max_size_t /\ v n <= maxint U16}
  -> tmp_seed:lbytes (18ul *! 4ul)
  -> r:lbytes (size 8 *! n)
  -> i:size_t{v i < v n / 4}
  -> res:matrix_t n n
  -> Stack unit
    (requires fun h -> tmp_seed4_pre h tmp_seed /\
      live h tmp_seed /\ live h res /\ live h r /\
      disjoint res tmp_seed /\ disjoint res r /\ disjoint r tmp_seed)
    (ensures  fun h0 _ h1 -> modifies (loc res |+| loc r |+| loc tmp_seed) h0 h1 /\
      as_matrix h1 res ==
      S.frodo_gen_matrix_shake_4x1 (v n) (LSeq.sub (as_seq h0 tmp_seed) 2 16) (v i) (as_matrix h0 res) /\
      LSeq.sub (as_seq h0 tmp_seed) 2 16 == LSeq.sub (as_seq h1 tmp_seed) 2 16 /\ tmp_seed4_pre h1 tmp_seed)

let frodo_gen_matrix_shake_4x1 n tmp_seed r i res =
  let r0 = sub r (size 0 *! n) (size 2 *! n) in
  let r1 = sub r (size 2 *! n) (size 2 *! n) in
  let r2 = sub r (size 4 *! n) (size 2 *! n) in
  let r3 = sub r (size 6 *! n) (size 2 *! n) in
  frodo_gen_matrix_shake_4x1_get_r n tmp_seed r0 r1 r2 r3 i;

  [@inline_let]
  let spec h0 = S.frodo_gen_matrix_shake_4x0 (v n) (v i)
    (as_seq h0 r0) (as_seq h0 r1) (as_seq h0 r2) (as_seq h0 r3) in
  let h0 = ST.get () in
  loop1 h0 n res spec
  (fun j ->
    Loops.unfold_repeati (v n) (spec h0) (as_matrix h0 res) (v j);
    frodo_gen_matrix_shake_4x0 n i r0 r1 r2 r3 j res
  )


val frodo_gen_matrix_shake_4x:
    n:size_t{0 < v n /\ v n * v n <= max_size_t /\ v n <= maxint U16 /\ v n % 4 = 0}
  -> seed:lbytes 16ul
  -> res:matrix_t n n
  -> Stack unit
    (requires fun h ->
      live h seed /\ live h res /\ disjoint seed res)
    (ensures  fun h0 _ h1 -> modifies (loc res) h0 h1 /\
      as_matrix h1 res == S.frodo_gen_matrix_shake (v n) (as_seq h0 seed))

[@"c_inline"]
let frodo_gen_matrix_shake_4x n seed res =
  push_frame ();
  let r = create (size 8 *! n) (u8 0) in
  let tmp_seed = create 72ul (u8 0) in
  copy (sub tmp_seed 2ul 16ul) seed;
  copy (sub tmp_seed 20ul 16ul) seed;
  copy (sub tmp_seed 38ul 16ul) seed;
  copy (sub tmp_seed 56ul 16ul) seed;

  memset res (u16 0) (n *! n);
  let h0 = ST.get () in
  assert (tmp_seed4_pre h0 tmp_seed);
  LSeq.eq_intro (LSeq.sub (as_seq h0 res) 0 (v n * v n)) (as_seq h0 res);

  [@ inline_let]
  let spec h0 = S.frodo_gen_matrix_shake_4x1 (v n) (as_seq h0 seed) in

  [@ inline_let]
  let inv h (i:nat{i <= v n / 4}) =
    modifies (loc res |+| loc r |+| loc tmp_seed) h0 h /\
    LSeq.sub (as_seq h0 tmp_seed) 2 16 == LSeq.sub (as_seq h tmp_seed) 2 16 /\
    tmp_seed4_pre h tmp_seed /\
    as_seq h res == Loops.repeati i (spec h0) (as_seq h0 res) in

  Loops.eq_repeati0 (v n / 4) (spec h0) (as_seq h0 res);
  Lib.Loops.for 0ul (n /. 4ul) inv
    (fun i ->
      Loops.unfold_repeati (v n / 4) (spec h0) (as_seq h0 res) (v i);
      frodo_gen_matrix_shake_4x1 n tmp_seed r i res);
  let h1 = ST.get () in
  assert (as_matrix h1 res == S.frodo_gen_matrix_shake_4x (v n) (as_seq h0 seed));
  S.frodo_gen_matrix_shake_4x_lemma (v n) (as_seq h0 seed);
  pop_frame ()


/// AES128

val frodo_gen_matrix_aes:
    n:size_t{v n * v n <= max_size_t /\ v n <= maxint U16}
  -> seed:lbytes 16ul
  -> a:matrix_t n n
  -> Stack unit
    (requires fun h ->
      live h seed /\ live h a /\ disjoint seed a)
    (ensures  fun h0 _ h1 -> modifies1 a h0 h1 /\
      as_matrix h1 a == S.frodo_gen_matrix_aes (v n) (as_seq h0 seed))

[@"c_inline"]
let frodo_gen_matrix_aes n seed a =
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
  assume (as_matrix h1 a == S.frodo_gen_matrix_aes (v n) (as_seq h0 seed))
