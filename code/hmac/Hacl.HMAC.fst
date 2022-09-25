module Hacl.HMAC

module S = FStar.Seq
module D = Hacl.Hash.Definitions
module ST = FStar.HyperStack.ST
module B = LowStar.Buffer
module MB = LowStar.Monotonic.Buffer
module C = Hacl.Impl.Blake2.Core

open FStar.HyperStack.ST
open FStar.Integers
open LowStar.BufferOps

open Spec.Hash.Definitions
open Spec.Agile.HMAC
open Spec.Agile.Hash
open Spec.Hash.Incremental
open Spec.Hash.Incremental.Lemmas
open Spec.Hash.PadFinish
open Spec.Hash.Lemmas
friend Spec.Agile.HMAC
friend Spec.Agile.Hash

let _: squash (inversion hash_alg) = allow_inversion hash_alg

#set-options "--max_fuel 0 --max_ifuel 0 --z3rlimit 50"

/// Helpers

inline_for_extraction
val xor_bytes_inplace:
  a: B.buffer uint8 ->
  b: B.buffer uint8 ->
  len: UInt32.t {v len = B.length a /\ v len = B.length b} ->
  Stack unit
  (requires fun h0 -> B.disjoint a b /\ B.live h0 a /\ B.live h0 b)
  (ensures fun h0 _ h1 ->
    B.(modifies (loc_buffer a) h0 h1) /\
    B.as_seq h1 a == Spec.Loops.seq_map2 ( ^. ) (B.as_seq h0 a) (B.as_seq h0 b))
inline_for_extraction
let xor_bytes_inplace a b len =
  C.Loops.in_place_map2 a b len ( ^. )

/// Agile implementation

// we rely on the output being zero-initialized for the correctness of padding
inline_for_extraction noextract
let wrap_key_st (a: hash_alg) =
  output: B.buffer uint8 { B.length output == block_length a } ->
  key: B.buffer uint8 {B.length key `less_than_max_input_length` a /\ B.disjoint output key} ->
  len: UInt32.t {v len = B.length key} ->
  Stack unit
    (requires fun h0 ->
      B.live h0 output /\ B.live h0 key /\
      B.as_seq h0 output == Seq.create (block_length a) (u8 0))
    (ensures fun h0 _ h1 ->
      B.(modifies (loc_buffer output) h0 h1) /\
      B.as_seq h1 output == wrap a (B.as_seq h0 key))

/// This one is only to avoid a warning about a pattern that is not encoding properly.
inline_for_extraction
let helper_smtpat (a: hash_alg) (len: uint32_t{ v len `less_than_max_input_length` a }):
  x:uint32_t { x <= D.block_len a } =
  if len <= D.block_len a then len else D.hash_len a

#set-options "--z3rlimit 40"

inline_for_extraction noextract
let mk_wrap_key (a: hash_alg) (hash: Hacl.Hash.Definitions.hash_st a): wrap_key_st a =
fun output key len ->
  //[@inline_let] //18-08-02 does *not* prevents unused-but-set-variable warning in C
  let i = helper_smtpat a len in
  let nkey = B.sub output 0ul i in
  let zeroes = B.sub output i (D.block_len a - i) in
  (**) assert B.(loc_disjoint (loc_buffer nkey) (loc_buffer zeroes));
  (**) let h0 = ST.get () in
  (**) assert (Seq.equal (B.as_seq h0 zeroes) (Seq.create (v (D.block_len a - i)) (u8 0)));
  if len <= D.block_len a then begin
    B.blit key 0ul nkey 0ul len;
    let h1 = ST.get () in
    (**) assert (Seq.equal (B.as_seq h1 zeroes) (B.as_seq h0 zeroes));
    (**) assert (Seq.equal (B.as_seq h1 nkey) (B.as_seq h0 key));
    (**) assert (Seq.equal (B.as_seq h1 output) (S.append (B.as_seq h1 nkey) (B.as_seq h1 zeroes)));
    (**) Seq.lemma_eq_elim (B.as_seq h1 output) (S.append (B.as_seq h1 nkey) (B.as_seq h1 zeroes));
    (**) assert (B.as_seq h1 output == wrap a (B.as_seq h0 key))
  end else begin
    hash key len nkey;
    (**) let h1 = ST.get () in
    (**) assert (Seq.equal (B.as_seq h1 zeroes) (B.as_seq h0 zeroes));
    (**) assert (Seq.equal (B.as_seq h1 nkey) (Spec.Agile.Hash.hash a (B.as_seq h0 key)));
    (**) assert (Seq.equal (B.as_seq h1 output) (S.append (B.as_seq h1 nkey) (B.as_seq h1 zeroes)));
    (**) Seq.lemma_eq_elim (B.as_seq h1 output) (S.append (B.as_seq h1 nkey) (B.as_seq h1 zeroes));
    (**) assert (B.as_seq h1 output == wrap a (B.as_seq h0 key))
  end

inline_for_extraction noextract
let block_len_as_len (a: hash_alg { not (is_sha3 a) }):
  Tot (l:len_t a { len_v a l = block_length a })
=
  let open FStar.Int.Cast.Full in
  assert_norm (128 < pow2 32);
  match a with
  | MD5 | SHA1 | SHA2_224 | SHA2_256 | Blake2S -> uint32_to_uint64 (D.block_len a)
  | SHA2_384 | SHA2_512 | Blake2B -> uint64_to_uint128 (uint32_to_uint64 (D.block_len a))


/// This implementation is optimized by reusing an existing hash state ``s``
/// rather than allocating a new one. Note that the disjointness hypotheses are
/// voluntarily very loose (in particular, the hash state and the key are not
/// necessarily disjoint).
inline_for_extraction noextract
val part2:
  a: hash_alg ->
  m : D.m_spec a ->
  init: D.init_st (|a, m|) ->
  update_multi: D.update_multi_st (|a, m|) ->
  update_last: D.update_last_st (|a, m|) ->
  finish: D.finish_st (|a, m|) ->
  s: D.state (|a, m|) ->
  dst: B.buffer uint8 { B.length dst = hash_length a } ->
  key: B.buffer uint8 { B.length key = block_length a } ->
  data: B.buffer uint8 ->
  len: UInt32.t { B.length data = v len } ->
  Stack unit
    (requires fun h0 ->
      B.disjoint s key /\
      B.disjoint s data /\
      B.disjoint s dst /\
      MB.(all_live h0 [ buf s; buf dst; buf key; buf data ]))
    (ensures fun h0 _ h1 ->
      key_and_data_fits a;
      B.(modifies (loc_union (loc_buffer s) (loc_buffer dst)) h0 h1) /\
      B.as_seq h1 dst `Seq.equal`
        Spec.Agile.Hash.hash a (S.append (B.as_seq h0 key) (B.as_seq h0 data)))

let update_multi_extra_state_eq'
  (a: hash_alg) (h: words_state a)
  (input: bytes_blocks a) :
  Lemma
  (requires (is_blake a ==> Seq.length input <= max_extra_state a))
  (ensures (is_blake a ==>
    (snd (Spec.Agile.Hash.update_multi a h input) ==
         extra_state_add_nat (snd h) (Seq.length input)))) =
  if is_blake a then update_multi_extra_state_eq a h input else ()

#push-options "--z3rlimit 100 --split_queries"

// TODO: move
(* We can't directly introduce uint128 literals *)
inline_for_extraction
let zero_to_len (a:hash_alg { not (is_sha3 a) }) : uint_t (len_int_type a) PUB =
  match a with
  | MD5 | SHA1
  | SHA2_224 | SHA2_256
  | Blake2S -> UInt64.uint_to_t 0
  | SHA2_384 | SHA2_512
  | Blake2B -> FStar.Int.Cast.Full.uint64_to_uint128 (UInt64.uint_to_t 0)

#restart-solver
inline_for_extraction noextract
let part2 a m init update_multi update_last finish s dst key data len =
  (**) key_and_data_fits a;
  (**) let h0 = ST.get () in
  (**) let key_v0 : Ghost.erased _ = B.as_seq h0 key in
  (**) let data_v0 : Ghost.erased _ = B.as_seq h0 data in
  (**) let key_data_v0 : Ghost.erased _ = Seq.append key_v0 data_v0 in
  let ev = init s in
  (**) let h1 = ST.get () in
  (**) assert(B.(modifies (loc_buffer s) h0 h1));
  (**) let init_v : Ghost.erased (init_t a) = Spec.Agile.Hash.init a in
  (**) assert ((D.as_seq h1 s, ev) == Ghost.reveal init_v);
  let ev =
    if len = 0ul then
      let ev = update_last s ev (if is_sha3 a then () else zero_to_len a) key (D.block_len a) in
      (**) let h2 = ST.get () in
      (**) Spec.Hash.Lemmas.block_length_smaller_than_max_input a;
      (**) assert(key_data_v0 `S.equal` key_v0);
      (**) Spec.Hash.Incremental.Lemmas.hash_incremental_block_is_update_last a init_v key_v0;
      (**) assert((D.as_seq h2 s, ev) ==
      (**)  Spec.Hash.Incremental.hash_incremental_body a key_data_v0 init_v);
      ev
    else
      let ev1 = update_multi s ev key 1ul in
      (**) let h2 = ST.get () in
      (**) assert ((D.as_seq h2 s, ev1) ==
      (**)           Spec.Agile.Hash.(update_multi a (init a) key_v0));
      (**) update_multi_extra_state_eq' a (D.as_seq h1 s, ev) key_v0;
      (**) assert(is_blake a ==> (ev1 == extra_state_add_nat ev (Seq.length key_v0)));
      (**) assert(is_blake a ==> (extra_state_v ev1 == block_length a));
      let block_len = D.block_len a in
      let n_blocks, rem_len = Lib.UpdateMulti.split_at_last_st block_len len in
      let full_blocks_len = n_blocks `FStar.UInt32.mul` block_len in
      let full_blocks = B.sub data 0ul full_blocks_len in
      let rem = B.sub data full_blocks_len rem_len in
      let ev2 = update_multi s ev1 full_blocks n_blocks in
      (**) update_multi_extra_state_eq' a (D.as_seq h2 s, ev1) (B.as_seq h0 full_blocks);
      let ev3 = update_last s ev2 (if is_sha3 a then () else Hacl.Hash.MD.len_add32 a (block_len_as_len a) full_blocks_len) rem rem_len in
      (**) let h3 = ST.get () in
      (**) assert ((D.as_seq h3 s, ev3) ==
      (**) Spec.Hash.Incremental.update_last a
              (Spec.Agile.Hash.update_multi a
                (Spec.Agile.Hash.(update_multi a (init a) key_v0))
                (B.as_seq h0 full_blocks))
              (block_length a + UInt32.v full_blocks_len)
              (B.as_seq h0 rem));
      (**) Lib.UpdateMulti.update_multi_associative (block_length a) (update a) (Spec.Agile.Hash.init a) key_v0 (B.as_seq h0 full_blocks);
      (**) assert ((D.as_seq h3 s, ev3) ==
      (**) Spec.Hash.Incremental.update_last a
              (Spec.Agile.Hash.update_multi a (Spec.Agile.Hash.init a) (key_v0 `Seq.append` B.as_seq h0 full_blocks))
              (block_length a + UInt32.v full_blocks_len)
              (B.as_seq h0 rem));
      (**)  Spec.Hash.Incremental.Lemmas.lemma_split_blocks_assoc a key_v0 (B.as_seq h0 data);
      (**)  assert (Spec.Hash.Incremental.split_blocks a (key_v0 `S.append` B.as_seq h0 data) ==
              (key_v0 `S.append` B.as_seq h0 full_blocks, B.as_seq h0 rem));
      // JP: this is the difficult proof. Works fine in interactive mode,
      // doesn't work in batch mode unless with split queries. Probably need to
      // do a case analysis manually (need to prove prev_len irrelevant in sha3
      // case).
      (**) assert ((D.as_seq h3 s, ev3) ==
      (**)   Spec.Hash.Incremental.hash_incremental_body a (key_v0 `S.append` B.as_seq h0 data) (Spec.Agile.Hash.init a));
      ev3
  in
  (**) let h3 = ST.get () in
  (**) assert(B.(modifies (loc_buffer s) h0 h3));
  finish s ev dst;
  (**) let h4 = ST.get () in
  (**) assert(B.(modifies (loc_union (loc_buffer s) (loc_buffer dst)) h3 h4));
  (**) assert(B.(modifies (loc_union (loc_buffer s) (loc_buffer dst)) h0 h4));
  (**) let open Spec.Hash.PadFinish in
  (**) let open Spec.Hash.Incremental in
  (**) let open Spec.Agile.Hash in
  (**) let open Spec.Hash.Lemmas in
  (**) if len =. 0ul then begin
  (**)   (* TODO: doesn't work if we put a calc here *)
  (**)   assert(B.as_seq h4 dst `S.equal` finish a (hash_incremental_body a key_data_v0 init_v));
  (**)   assert(B.as_seq h4 dst `S.equal` hash_incremental a key_data_v0)
  (**) end else begin
  (**)   assert(B.as_seq h4 dst `S.equal` hash_incremental a key_data_v0)
  (**) end;
  (**) Spec.Hash.Incremental.hash_is_hash_incremental a key_data_v0;
  (**) assert(B.as_seq h4 dst `S.equal` hash a key_data_v0)

#pop-options

/// This implementation is optimized. First, it reuses an existing hash state
/// ``s`` rather than allocating a new one. Second, it writes out the result of
/// the hash directly in its parameter ``key`` rather than taking a destination
/// output buffer.
inline_for_extraction noextract
val part1:
  a: hash_alg ->
  m : D.m_spec a ->
  init: D.init_st (|a, m|) ->
  update_multi: D.update_multi_st (|a, m|) ->
  update_last: D.update_last_st (|a, m|) ->
  finish: D.finish_st (|a, m|) ->
  s: D.state (|a, m|) ->
  key: B.buffer uint8 { B.length key = block_length a } ->
  data: B.buffer uint8 ->
  len: UInt32.t { B.length data = v len } ->
  Stack unit
    (requires fun h0 ->
      B.disjoint s key /\
      B.disjoint s data /\
      MB.(all_live h0 [ buf s; buf key; buf data ]))
    (ensures fun h0 _ h1 ->
      key_and_data_fits a;
      B.(modifies (loc_union (loc_buffer s) (loc_buffer key)) h0 h1) /\
      S.slice (B.as_seq h1 key) 0 (hash_length a) `Seq.equal`
        Spec.Agile.Hash.hash a (S.append (B.as_seq h0 key) (B.as_seq h0 data)))

let part1 a m init update_multi update_last finish s key data len =
  let dst = B.sub key 0ul (D.hash_len a) in
  part2 a m init update_multi update_last finish s dst key data len

let block_len_positive (a: hash_alg): Lemma (D.block_len a > 0ul) = ()
let hash_lt_block (a: hash_alg): Lemma (hash_length a < block_length a) = ()

#set-options "--z3rlimit 100"
let mk_compute i hash alloca init update_multi update_last finish dst key key_len data data_len =
  [@inline_let] let a = D.get_alg i in
  [@inline_let] let m = D.get_spec i in
  block_len_positive a;
  hash_lt_block a;
  (**) let h0 = ST.get() in
  push_frame ();
  (**) let h1 = ST.get () in
  let l = D.block_len a in
  let key_block = B.alloca (u8 0x00) l in
  mk_wrap_key a hash key_block key key_len;
  (**) let h2 = ST.get () in
  (**) assert (B.as_seq h2 key_block `Seq.equal` wrap a (B.as_seq h0 key));
  let ipad = B.alloca (u8 0x36) l in
  xor_bytes_inplace ipad key_block l;
  (**) let h3 = ST.get () in
  (**) assert (B.as_seq h3 ipad `Seq.equal` S.(xor (u8 0x36) (wrap a (B.as_seq h0 key))));
  let opad = B.alloca (u8 0x5c) l in
  xor_bytes_inplace opad key_block l;
  (**) let h4 = ST.get () in
  (**) assert B.(modifies (loc_buffer key_block `loc_union` loc_buffer ipad
  (**)   `loc_union` loc_buffer opad) h1 h4);
  (**) S.lemma_eq_intro (B.as_seq h4 ipad) (S.(xor (u8 0x36) (wrap a (B.as_seq h0 key))));
  (**) S.lemma_eq_intro (B.as_seq h4 opad) (S.(xor (u8 0x5c) (wrap a (B.as_seq h0 key))));
  (**) S.lemma_eq_intro (B.as_seq h4 data) (B.as_seq h0 data);
  let s, _ = alloca () in
  part1 a m init update_multi update_last finish s ipad data data_len;
  (**) key_and_data_fits a;
  (**) let h5 = ST.get () in
  (**) S.lemma_eq_intro (S.slice (B.as_seq h5 ipad) 0 (hash_length a))
  (**)    (Spec.Agile.Hash.hash a S.(append (xor (u8 0x36) (wrap a (B.as_seq h0 key)))
  (**)                          (B.as_seq h0 data)));
  let hash1 = B.sub ipad 0ul (D.hash_len a) in
  part2 a m init update_multi update_last finish s dst opad hash1 (D.hash_len a);
  (**) let h6 = ST.get () in
  (**) assert (B.as_seq h6 dst `S.equal` hmac a (B.as_seq h0 key) (B.as_seq h0 data));
  pop_frame ();
  (**) let h7 = ST.get () in
  (**) assert B.(modifies (loc_buffer key_block `loc_union` loc_buffer ipad `loc_union`
  (**)                     loc_buffer opad `loc_union` loc_buffer s) h1 h2);
  (**) LowStar.Monotonic.Buffer.modifies_fresh_frame_popped h0 h1 (B.loc_buffer dst) h6 h7

let legacy_compute_sha1: compute_st SHA1 =
  let open Hacl.Hash.SHA1 in
  mk_compute (D.mk_impl SHA1 ()) legacy_hash legacy_alloca legacy_init
             legacy_update_multi legacy_update_last legacy_finish

let compute_sha2_256: compute_st SHA2_256 =
  let open Hacl.Hash.SHA2 in
  mk_compute (D.mk_impl SHA2_256 ()) hash_256 alloca_256 init_256
             update_multi_256 update_last_256 finish_256

let compute_sha2_384: compute_st SHA2_384 =
  let open Hacl.Hash.SHA2 in
  mk_compute (D.mk_impl SHA2_384 ()) hash_384 alloca_384 init_384
             update_multi_384 update_last_384 finish_384

let compute_sha2_512: compute_st SHA2_512 =
  let open Hacl.Hash.SHA2 in
  mk_compute (D.mk_impl SHA2_512 ()) hash_512 alloca_512 init_512
             update_multi_512 update_last_512 finish_512

let compute_blake2s_32: compute_st Blake2S =
  let open Hacl.Hash.Blake2 in
  mk_compute (D.mk_impl Blake2S C.M32) hash_blake2s_32 alloca_blake2s_32 init_blake2s_32
             update_multi_blake2s_32 update_last_blake2s_32 finish_blake2s_32

let compute_blake2b_32: compute_st Blake2B =
  let open Hacl.Hash.Blake2 in
  mk_compute (D.mk_impl Blake2B C.M32) hash_blake2b_32 alloca_blake2b_32 init_blake2b_32
             update_multi_blake2b_32 update_last_blake2b_32 finish_blake2b_32
