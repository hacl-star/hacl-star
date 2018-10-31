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
      modifies (loc_buffer res) h0 h1 /\
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
  -> i:size_t{v i < v n}
  -> res:matrix_t n n
  -> Stack unit
    (requires fun h ->
      live h seed /\ live h res /\ disjoint res seed)
    (ensures  fun h0 _ h1 ->
      modifies (loc_buffer res) h0 h1 /\
      as_matrix h1 res == S.frodo_gen_matrix_cshake1 (v n) (v seed_len) (as_seq h0 seed) (v i) (as_matrix h0 res))
let frodo_gen_matrix_cshake1 n seed_len seed i res =
  push_frame ();
  //TODO (?): create this buffer in `frodo_gen_matrix_cshake`
  let r = create #_ #(2 * v n) (size 2 *! n) (u8 0) in
  let ctr = size_to_uint32 (size 256 +. i) in
  uintv_extensionality (to_u16 (size_to_uint32 (size 256 +. i))) (u16 (256 + v i));
  SHA3.cshake128_frodo seed_len seed (to_u16 ctr) (size 2 *! n) r;
  [@ inline_let]
  let spec h0 = S.frodo_gen_matrix_cshake0 (v n) (v i) (as_seq h0 r) in
  let h0 = ST.get () in
  loop1 h0 n res spec
  (fun j ->
    Lib.LoopCombinators.unfold_repeati (v n) (spec h0) (as_matrix h0 res) (v j);
    frodo_gen_matrix_cshake0 n i r j res
  );
  pop_frame ()

val frodo_gen_matrix_cshake:
    n:size_t{0 < v n /\ 2 * v n <= max_size_t /\ 256 + v n < maxint U16 /\ v n * v n <= max_size_t}
  -> seed_len:size_t{v seed_len > 0}
  -> seed:lbytes seed_len
  -> res:matrix_t n n
  -> Stack unit
    (requires fun h -> live h seed /\ live h res /\ disjoint seed res)
    (ensures  fun h0 _ h1 ->
      modifies (loc_buffer res) h0 h1 /\
      as_matrix h1 res == S.frodo_gen_matrix_cshake (v n) (v seed_len) (as_seq h0 seed))
[@"c_inline"]
let frodo_gen_matrix_cshake n seed_len seed res =
  memset res (u16 0) (n *! n);
  let h0 = ST.get () in
  Lib.Sequence.eq_intro (Lib.Sequence.sub (as_seq h0 res) 0 (v n * v n)) (as_seq h0 res);
  [@ inline_let]
  let spec h0 = S.frodo_gen_matrix_cshake1 (v n) (v seed_len) (as_seq h0 seed) in
  loop1 h0 n res spec
  (fun i ->
    Lib.LoopCombinators.unfold_repeati (v n) (spec h0) (as_matrix h0 res) (v i);
    frodo_gen_matrix_cshake1 n seed_len seed i res
  )

val frodo_gen_matrix_cshake_4x:
    n:size_t{0 < v n /\ 2 * v n <= max_size_t /\ 256 + v n < maxint U16 /\ v n * v n <= max_size_t}
  -> seed_len:size_t{v seed_len > 0}
  -> seed:lbytes seed_len
  -> res:matrix_t n n
  -> Stack unit
    (requires fun h -> live h seed /\ live h res /\ disjoint seed res)
    (ensures  fun h0 _ h1 ->
      modifies (loc_buffer res) h0 h1 /\
      as_matrix h1 res == S.frodo_gen_matrix_cshake (v n) (v seed_len) (as_seq h0 seed))
[@"c_inline"]
let frodo_gen_matrix_cshake_4x n seed_len seed res =
  let h = ST.get() in
  push_frame ();
  let r: lbuffer uint8 (8 * v n) = create (size 8 *! n) (u8 0) in
  let r0 = sub r (size 0 *! n) (size 2 *! n) in
  let r1 = sub r (size 2 *! n) (size 2 *! n) in
  let r2 = sub r (size 4 *! n) (size 2 *! n) in
  let r3 = sub r (size 6 *! n) (size 2 *! n) in
  let n4 = n /. size 4 in
  assert(B.loc_pairwise_disjoint
        [loc_buffer seed; loc_buffer r0; loc_buffer r1;
         loc_buffer r2; loc_buffer r3]);
  let h0 = ST.get() in
  Lib.Loops.for (size 0) n4
    (fun h1 i ->
      B.modifies (loc_union (loc_buffer res) (loc_buffer r)) h0 h1 /\
      B.live h1 seed /\ B.live h1 res /\
      B.live h1 r0 /\ B.live h1 r1 /\ B.live h1 r2 /\ B.live h1 r3)
    (fun i ->
     let ctr0 = size_to_uint32 (size 256 +. size 4 *! i +. size 0) in
     let ctr1 = size_to_uint32 (size 256 +. size 4 *! i +. size 1) in
     let ctr2 = size_to_uint32 (size 256 +. size 4 *! i +. size 2) in
     let ctr3 = size_to_uint32 (size 256 +. size 4 *! i +. size 3) in
     Hacl.Keccak.cshake128_frodo_4x seed_len seed
       (to_u16 ctr0) (to_u16 ctr1) (to_u16 ctr2) (to_u16 ctr3)
       (size 2 *! n) r0 r1 r2 r3;
     let h1' = ST.get() in
     Lib.Loops.for (size 0) n
       (fun h2 j ->
          B.modifies (loc_union (loc_buffer res) (loc_buffer r)) h1' h2 /\
          B.live h2 seed /\ B.live h2 res /\
          B.live h2 r0 /\ B.live h2 r1 /\ B.live h2 r2 /\ B.live h2 r3)
       (fun j ->
         let resij0 = sub r0 (size 2 *! j) (size 2) in
         let resij1 = sub r1 (size 2 *! j) (size 2) in
         let resij2 = sub r2 (size 2 *! j) (size 2) in
         let resij3 = sub r3 (size 2 *! j) (size 2) in
         mset res (size 4 *! i +! size 0) j (uint_from_bytes_le resij0);
         mset res (size 4 *! i +! size 1) j (uint_from_bytes_le resij1);
         mset res (size 4 *! i +! size 2) j (uint_from_bytes_le resij2);
         mset res (size 4 *! i +! size 3) j (uint_from_bytes_le resij3)
       )
    );
  pop_frame ();
  // TODO: Verify this
  let h' = ST.get() in
  assume (as_matrix h' res == S.frodo_gen_matrix_cshake (v n) (v seed_len) (as_seq h seed))

/// AES128

val frodo_gen_matrix_aes:
    n:size_t{v n * v n <= max_size_t}
  -> seed_len:size_t{v seed_len == 16}
  -> seed:lbytes seed_len
  -> a:matrix_t n n
  -> Stack unit
    (requires fun h -> live h seed /\ live h a /\ disjoint seed a)
    (ensures  fun h0 _ h1 -> modifies (loc_buffer a) h0 h1)
[@"c_inline"]
let frodo_gen_matrix_aes n seed_len seed a =
  push_frame();
  let key = B.alloca (u8 0) 176ul in
  Hacl.AES128.aes128_key_expansion seed key;

  let h0 = ST.get() in
  Lib.Loops.for (size 0) n
    (fun h1 i -> modifies (loc_buffer a) h0 h1)
    (fun i ->
      let h1 = ST.get() in
      Lib.Loops.for (size 0) (n /. size 8)
        (fun h2 j -> modifies (loc_buffer a) h1 h2)
        (fun j ->
          let j = j *! size 8 in
          a.[i, j] <- to_u16 (size_to_uint32 i);
          a.[i, j +! size 1] <- to_u16 (size_to_uint32 j)
        )
    );

  let h0 = ST.get() in
  Lib.Loops.for (size 0) n
    (fun h1 i -> modifies (loc_buffer a) h0 h1)
    (fun i ->
      let h1 = ST.get() in
      Lib.Loops.for (size 0) (n /. size 8)
        (fun h2 j -> modifies (loc_buffer a) h1 h2)
        (fun j ->
          let j = j *! size 8 in
          assert (v j + 8 <= v n);
          assert (v i <= v n - 1);
          assert_spinoff (v i * v n + v j + 8 <= (v n - 1) * v n + v n);
          let b = sub a (i *! n +! j) (size 8) in
          Hacl.AES128.aes128_encrypt_block b b key
        )
    );
  pop_frame()
