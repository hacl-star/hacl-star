module Hacl.HMAC

module S = Lib.Sequence
module D = Hacl.Hash.Definitions
module ST = FStar.HyperStack.ST
module B = Lib.Buffer
module MB = LowStar.Monotonic.Buffer

open FStar.HyperStack.ST
open FStar.Integers
open LowStar.BufferOps
open Lib.IntTypes

open Spec.Hash.Definitions
open Spec.HMAC
friend Spec.HMAC

let _: squash (inversion hash_alg) = allow_inversion hash_alg

#set-options "--max_fuel 0 --max_ifuel 0"

/// Helpers

inline_for_extraction
val xor_bytes_inplace:
  a: buffer uint8 ->
  b: buffer uint8 ->
  len: size_t {v len = B.length a /\ v len = B.length b} ->
  Stack unit
  (requires fun h0 -> B.disjoint a b /\ B.live h0 a /\ B.live h0 b)
  (ensures fun h0 _ h1 ->
    B.(modifies1 a h0 h1) /\
    B.as_seq #MUT #uint8 #(size (B.length a)) h1 a ==
      Spec.Loops.seq_map2 logxor (B.as_seq  #MUT #uint8 #(size (B.length a)) h0 a)
	(B.as_seq #MUT #uint8 #(size (B.length b)) h0 b))
inline_for_extraction
let xor_bytes_inplace a b len =
  C.Loops.in_place_map2 a b len logxor

/// Agile implementation

// we rely on the output being zero-initialized for the correctness of padding
inline_for_extraction noextract
let wrap_key_st (a: hash_alg) =
  output: lbuffer uint8 (size (block_length a)) ->
  key: buffer uint8 {B.length key < max_input_length a /\ B.disjoint output key} ->
  len: UInt32.t {v len = B.length key} ->
  Stack unit
    (requires fun h0 ->
      B.live h0 output /\ B.live h0 key /\
      B.as_seq h0 output == Seq.create (block_length a) (u8 0))
    (ensures fun h0 _ h1 ->
      B.(modifies1 output h0 h1) /\
      B.as_seq h1 output == wrap a (B.as_seq #MUT #uint8 #(size (B.length key)) h0 key))

/// This one is only to avoid a warning about a pattern that is not encoding properly.
inline_for_extraction
let helper_smtpat (a: hash_alg) (len: size_t{ v len < max_input_length a }):
  x:size_t { x <= D.block_len a } =
  if len <= D.block_len a then len else D.hash_len a

inline_for_extraction noextract
let mk_wrap_key (a: hash_alg) (hash: Hacl.Hash.Definitions.hash_st a): wrap_key_st a =
fun output key len ->
  //[@inline_let] //18-08-02 does *not* prevents unused-but-set-variable warning in C
  let i = helper_smtpat a len in
  let nkey = B.sub output 0ul i in
  let zeroes = B.sub output i (D.block_len a - i) in
  assert B.(disjoint nkey zeroes);
  let h0 = ST.get () in
  assert (Seq.equal (B.as_seq h0 zeroes) (Seq.create (v (D.block_len a -. i)) (u8 0)));
  if len <= D.block_len a then begin
    //B.blit key 0ul nkey 0ul len;
    copy #MUT #uint8 #len nkey key;
    let h1 = ST.get () in
    assert (Seq.equal (B.as_seq h1 zeroes) (B.as_seq h0 zeroes));
    assert (Seq.equal (B.as_seq h1 nkey) (B.as_seq #MUT #uint8 #len h0 key));
    assert (Seq.equal (B.as_seq h1 output) (S.concat (B.as_seq h1 nkey) (B.as_seq h1 zeroes)));
    Seq.lemma_eq_elim (B.as_seq h1 output) (S.concat (B.as_seq h1 nkey) (B.as_seq h1 zeroes));
    assert (B.as_seq h1 output == wrap a (B.as_seq #MUT #uint8 #i h0 key))
  end else begin
    hash key len nkey;
    let h1 = ST.get () in
    assert (Seq.equal (B.as_seq h1 zeroes) (B.as_seq h0 zeroes));
    assert (Seq.equal (B.as_seq h1 nkey) (Spec.Hash.hash a (B.as_seq #MUT #uint8 #len h0 key)));
    assert (Seq.equal (B.as_seq h1 output) (S.concat (B.as_seq h1 nkey) (B.as_seq h1 zeroes)));
    Seq.lemma_eq_elim (B.as_seq h1 output) (S.concat (B.as_seq h1 nkey) (B.as_seq h1 zeroes));
    assert (B.as_seq h1 output == wrap a (B.as_seq #MUT #uint8 #len h0 key))
  end

/// This implementation is optimized. First, it reuses an existing hash state
/// ``s`` rather than allocating a new one. Second, it writes out the result of
/// the hash directly in its parameter ``key`` rather than taking a destination
/// output buffer.
inline_for_extraction noextract
val part1:
  a: hash_alg ->
  init: D.init_st a ->
  update_multi: D.update_multi_st a ->
  update_last: D.update_last_st a ->
  finish: D.finish_st a ->
  s: D.state a ->
  key: B.lbuffer uint8 (size (block_length a)) ->
  data: B.buffer uint8 ->
  len: size_t { B.length data = v len /\ v len + (block_length a) <= max_size_t } ->
  Stack unit
    (requires fun h0 ->
      B.disjoint #MUT #MUT #(Spec.Hash.Definitions.word a) #uint8 s key /\
      B.disjoint #MUT #MUT #(Spec.Hash.Definitions.word a) #uint8 s data /\
      B.live #MUT #(Spec.Hash.Definitions.word a) h0 s /\ B.live h0 key /\ B.live h0 data
    )
    (ensures fun h0 _ h1 ->
      key_and_data_fits a;
      B.(modifies2 s key h0 h1) /\
      S.slice (B.as_seq h1 key) 0 (hash_length a) `Seq.equal`
        Spec.Hash.hash a (S.concat (B.as_seq h0 key) (B.as_seq #MUT #uint8 #len h0 data)))

inline_for_extraction noextract
let block_len_as_len (a: hash_alg):
  Tot (l:len_t a { len_v a l = block_length a })
=
  let open FStar.Int.Cast.Full in
  assert_norm (128 < pow2 32);
  match a with
  | MD5 | SHA1 | SHA2_224 | SHA2_256 -> uint32_to_uint64 (D.block_len a)
  | SHA2_384 | SHA2_512 -> uint64_to_uint128 (uint32_to_uint64 (D.block_len a))

#set-options "--z3rlimit 50"

inline_for_extraction noextract
let part1 a init update_multi update_last finish s key data len =
  (**) key_and_data_fits a;
  (**) let h0 = ST.get () in
  init s;
  (**) let h1 = ST.get () in
  (**) assert (B.as_seq #MUT #(Spec.Hash.Definitions.word a)
    #(size (Spec.Hash.Definitions.state_word_length a))
    h1 s `Seq.equal` Spec.Hash.init a);
  update_multi s key 1ul;
  (**) let h2 = ST.get () in
  (**) assert (B.as_seq #MUT #(Spec.Hash.Definitions.word a)
    #(size (Spec.Hash.Definitions.state_word_length a))
    h2 s `Seq.equal` Spec.Hash.(update_multi a (init a) (B.as_seq h0 key)));
  update_last s (block_len_as_len a) data len;
  (**) let h3 = ST.get () in
  (**) assert (B.as_seq #MUT #(Spec.Hash.Definitions.word a)
    #(size (Spec.Hash.Definitions.state_word_length a))
    h3 s `Seq.equal`
    Spec.Hash.Incremental.update_last a
      (Spec.Hash.(update_multi a (init a) (B.as_seq h0 key))) (block_length a)
        (B.as_seq #MUT #uint8 #len h0 data));
  let dst = B.sub key 0ul (D.hash_len a) in
  finish s dst;
  (**) let h4 = ST.get () in
  begin
    let open Spec.Hash.PadFinish in
    let open Spec.Hash.Incremental in
    let open Spec.Hash in
    let open Spec.Hash.Lemmas in
    calc (S.equal) {
      B.as_seq h4 dst;
    (S.equal) { }
      finish a (update_last a (update_multi a (init a) (B.as_seq h0 key))
        (block_length a) (B.as_seq  #MUT #uint8 #len h0 data));
    (S.equal) { }
      finish a (update_multi a (update_multi a (init a) (B.as_seq h0 key))
        (FStar.Seq.append
	  (B.as_seq  #MUT #uint8 #len h0 data) (pad a (block_length a + v len))));
    (S.equal) { }
      finish a (update_multi a (init a)
        (FStar.Seq.append (B.as_seq h0 key)
          (FStar.Seq.append (B.as_seq  #MUT #uint8 #len h0 data)
	  (pad a (block_length a + v len)))));
    (S.equal) { FStar.Seq.append_assoc
      (B.as_seq h0 key)
      (B.as_seq #MUT #uint8 #len h0 data)
      (pad a (block_length a + v len))
    }
      finish a (update_multi a (init a)
        (FStar.Seq.append
	  (S.concat (B.as_seq h0 key) (B.as_seq #MUT #uint8 #len h0 data))
          (pad a (block_length a + v len))));
    (S.equal) {
      Spec.Hash.Lemmas.hash_is_hash_incremental a (S.concat (B.as_seq h0 key)
	(B.as_seq #MUT #uint8 #len h0 data))
    }
      hash a (S.concat (B.as_seq h0 key) (B.as_seq #MUT #uint8 #len h0 data));
    }
  end

inline_for_extraction noextract
val part2:
  a: hash_alg ->
  init: D.init_st a ->
  update_multi: D.update_multi_st a ->
  update_last: D.update_last_st a ->
  finish: D.finish_st a ->
  s: D.state a ->
  dst: B.lbuffer uint8 (size (hash_length a)) ->
  key: B.lbuffer uint8 (size (block_length a)) ->
  data: B.buffer uint8 ->
  len: size_t { B.length data = v len /\ v len + (block_length a) <= max_size_t } ->
  Stack unit
    (requires fun h ->
      B.disjoint #MUT #MUT #(Spec.Hash.Definitions.word a) #uint8 s key /\
      B.disjoint #MUT #MUT #(Spec.Hash.Definitions.word a) #uint8 s data /\
      B.disjoint #MUT #MUT #(Spec.Hash.Definitions.word a) #uint8 s dst /\
      B.live #MUT #(Spec.Hash.Definitions.word a) h s /\ B.live h dst /\ B.live h key /\ B.live h data)
    (ensures fun h0 _ h1 ->
      key_and_data_fits a;
      B.(modifies2 s dst h0 h1) /\
      B.as_seq h1 dst `Seq.equal`
        Spec.Hash.hash a (S.concat (B.as_seq h0 key) (B.as_seq #MUT #uint8 #len h0 data)))

#set-options "--z3rlimit 40"
inline_for_extraction noextract
let part2 a init update_multi update_last finish s dst key data len =
  (**) key_and_data_fits a;
  (**) let h0 = ST.get () in
  init s;
  (**) let h1 = ST.get () in
  (**) assert (B.as_seq #MUT #(Spec.Hash.Definitions.word a)
    #(size (Spec.Hash.Definitions.state_word_length a)) h1 s `Seq.equal` Spec.Hash.init a);
  update_multi s key 1ul;
  (**) let h2 = ST.get () in
  (**) assert (B.as_seq #MUT #(Spec.Hash.Definitions.word a)
    #(size (Spec.Hash.Definitions.state_word_length a)) h2 s `Seq.equal` Spec.Hash.(update_multi a (init a) (B.as_seq h0 key)));
  update_last s (block_len_as_len a) data len;
  (**) let h3 = ST.get () in
  (**) assert (B.as_seq #MUT #(Spec.Hash.Definitions.word a)
    #(size (Spec.Hash.Definitions.state_word_length a)) h3 s `Seq.equal`
    Spec.Hash.Incremental.update_last a
      (Spec.Hash.(update_multi a (init a) (B.as_seq h0 key))) (block_length a)
        (B.as_seq #MUT #uint8 #len h0 data));
  finish s dst;
  (**) let h4 = ST.get () in
  begin
    let open Spec.Hash.PadFinish in
    let open Spec.Hash.Incremental in
    let open Spec.Hash in
    let open Spec.Hash.Lemmas in
    calc (S.equal) {
      B.as_seq h4 dst;
    (S.equal) { }
      finish a (update_last a (update_multi a (init a) (B.as_seq h0 key))
        (block_length a) (B.as_seq #MUT #uint8 #len h0 data));
    (S.equal) { }
      finish a (update_multi a (update_multi a (init a) (B.as_seq h0 key))
        (FStar.Seq.append (B.as_seq #MUT #uint8 #len h0 data) (pad a (block_length a + v len))));
    (S.equal) { }
      finish a (update_multi a (init a)
        (FStar.Seq.append (B.as_seq h0 key)
          (FStar.Seq.append (B.as_seq #MUT #uint8 #len h0 data) (pad a (block_length a + v len)))));
    (S.equal) { FStar.Seq.append_assoc
      (B.as_seq h0 key)
      (B.as_seq #MUT #uint8 #len h0 data)
      (pad a (block_length a + v len))
    }
      finish a (update_multi a (init a)
        (FStar.Seq.append (S.concat (B.as_seq h0 key) (B.as_seq #MUT #uint8 #len h0 data))
          (pad a (block_length a + v len))));
    (S.equal) {
      Spec.Hash.Lemmas.hash_is_hash_incremental a (S.concat (B.as_seq h0 key)
        (B.as_seq #MUT #uint8 #len h0 data))
    }
      hash a (S.concat (B.as_seq h0 key) (B.as_seq #MUT #uint8 #len h0 data));
    }
  end


#set-options "--z3rlimit 200"
inline_for_extraction noextract
let mk_compute a hash alloca init update_multi update_last finish dst key key_len data data_len =
  (**) let h0 = ST.get() in
  push_frame ();
  (**) let h1 = ST.get () in
  let l = D.block_len a in
  let key_block = B.create l (u8 0) in
  mk_wrap_key a hash key_block key key_len;
  (**) let h2 = ST.get () in
  (**) assert (B.as_seq h2 key_block `Seq.equal` wrap a
  (**)   (B.as_seq #MUT #uint8 #key_len h0 key));
  let ipad = B.create l (u8 0x36) in
  xor_bytes_inplace ipad key_block l;
  (**) let h3 = ST.get () in
  (**) assert (B.as_seq h3 ipad `Seq.equal` S.(xor (u8 0x36) (wrap a
  (**)  (B.as_seq #MUT #uint8 #key_len h0 key))));
  let opad = B.create l (u8 0x5c) in
  xor_bytes_inplace opad key_block l;
  (**) let h4 = ST.get () in
  (**) assert (B.as_seq h4 opad `Seq.equal` S.(xor (u8 0x5c) (wrap a
  (**)  (B.as_seq #MUT #uint8 #key_len h0 key))));

  let s = alloca () in
  part1 a init update_multi update_last finish s ipad data data_len;
  (**) key_and_data_fits a;
  (**) let h5 = ST.get () in
  (**) assert (S.slice (B.as_seq h5 ipad) 0 (hash_length a) `S.equal`
  (**)  Spec.Hash.hash a S.(FStar.Seq.append (xor (u8 0x36) (wrap a (B.as_seq #MUT #uint8 #key_len h0 key)))
    (B.as_seq #MUT #uint8 #data_len h0 data)));
  let hash1 = B.sub ipad 0ul (D.hash_len a) in
  part2 a init update_multi update_last finish s dst opad hash1 (D.hash_len a);
  (**) let h6 = ST.get () in
  (**) assert (B.as_seq h6 dst `S.equal`
    hmac a (B.as_seq #MUT #uint8 #key_len h0 key) (B.as_seq #MUT #uint8 #data_len h0 data));
  pop_frame ();
  (**) let h7 = ST.get () in
  (**) LowStar.Monotonic.Buffer.modifies_fresh_frame_popped h0 h1
  (**)  (LowStar.Buffer.loc_buffer (dst <: LowStar.Buffer.buffer uint8)) h6 h7

let compute_sha2_256: compute_st SHA2_256 =
  let open Hacl.Hash.SHA2 in
  mk_compute SHA2_256 hash_256 alloca_256 init_256 update_multi_256 update_last_256 finish_256
