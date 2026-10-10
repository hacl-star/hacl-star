module EverCrypt.Poly1305

/// A multiplexed frontend for Poly1305.

module B = LowStar.Buffer
module U32 = FStar.UInt32
module ST = FStar.HyperStack.ST
module S = FStar.Seq
module P = Vale.Poly1305.Spec_s
module PM = Vale.Poly1305.Math
module IT = Vale.Interop.Types
module MH = Vale.AsLowStar.MemoryHelpers

open FStar.HyperStack.ST
open FStar.Mul
open Lib.Buffer.Lemmas

#reset-options "--fuel 1 --ifuel 0"

friend Lib.IntTypes


#push-options "--z3rlimit 30 --ifuel 1 --split_queries always"
unfold private let accumulator (h:FStar.HyperStack.mem)
  (ctx:B.buffer UInt8.t{B.length ctx == 192 /\ B.live h ctx}) : GTot int =
  Vale.Wrapper.X64.Poly.math_aux ctx 24;
  LowStar.BufferView.Down.length_eq (IT.get_downview ctx);
  PM.lowerUpper192
    (PM.lowerUpper128
      (UInt64.v (MH.low_buffer_read IT.TUInt8 IT.TUInt64 h ctx 0))
      (UInt64.v (MH.low_buffer_read IT.TUInt8 IT.TUInt64 h ctx 1)))
    (UInt64.v (MH.low_buffer_read IT.TUInt8 IT.TUInt64 h ctx 2))

private let full_blocks_append (first last:Lib.ByteSequence.bytes) (blocks:nat) : Lemma
  (requires S.length first == 16 * blocks)
  (ensures forall (i:int). 0 <= i /\ i < blocks ==>
    Vale.Poly1305.Equiv.block_fun first i ==
    Vale.Poly1305.Equiv.block_fun (S.append first last) i) =
  let joined = S.append first last in
  assert_norm (Spec.Poly1305.size_block == 16);
  FStar.Math.Lemmas.cancel_mul_div blocks 16;
  FStar.Math.Lemmas.lemma_div_le (S.length first) (S.length joined) 16;
  S.append_slices first last;
  let same_block (i:int) : Lemma
    (0 <= i /\ i < blocks ==>
      Vale.Poly1305.Equiv.block_fun first i ==
      Vale.Poly1305.Equiv.block_fun joined i) =
    if 0 <= i && i < blocks then
      S.slice_slice joined 0 (S.length first) (i * 16) (i * 16 + 16)
  in
  FStar.Classical.forall_intro same_block

#push-options "--fuel 2 --z3rlimit 100"
private let hash_append_last (first last:Lib.ByteSequence.bytes) (blocks:nat)
  (key_r key_s:Vale.Def.Words_s.nat128) : Lemma
  (requires S.length first == 16 * blocks /\ S.length last < 16)
  (ensures (
    let open Vale.Poly1305.Spec_s in
    let open Vale.Poly1305.Equiv in
    norm [delta_only [`%poly1305_hash_all; `%poly1305_hash]] (
    poly1305_hash_all
      (poly1305_hash_blocks 0 Vale.Def.Words_s.pow2_128 (make_r key_r)
        (block_fun first) blocks)
      key_r key_s (block_fun last) (S.length last) ==
    poly1305_hash key_r key_s (block_fun (S.append first last))
      (S.length (S.append first last))))) =
  let open Vale.Poly1305.Spec_s in
  let open Vale.Poly1305.Equiv in
  let joined = S.append first last in
  full_blocks_append first last blocks;
  Vale.Poly1305.Util.lemma_equal_blocks 0 Vale.Def.Words_s.pow2_128
    (make_r key_r) (block_fun first) (block_fun joined) blocks;
  FStar.Math.Lemmas.division_addition_lemma (S.length last) 16 blocks;
  FStar.Math.Lemmas.modulo_addition_lemma (S.length last) 16 blocks;
  S.append_slices first last;
  S.slice_length last;
  assert (block_fun joined blocks == block_fun last 0);
  assert (S.length last / 16 == 0 /\ S.length last % 16 == S.length last);
  assert (S.length joined / 16 == blocks /\ S.length joined % 16 == S.length last);
  let h = poly1305_hash_blocks 0 Vale.Def.Words_s.pow2_128
    (make_r key_r) (block_fun first) blocks in
  assert (poly1305_hash_blocks h Vale.Def.Words_s.pow2_128
    (make_r key_r) (block_fun last) 0 == h)

#push-options "--fuel 3 --z3refresh"
private let tag_after_last (first last:Lib.ByteSequence.bytes) (blocks:nat)
  (k:Spec.Poly1305.key) (tag:S.lseq UInt8.t 16) : Lemma
  (requires (
    let open Vale.Poly1305.Equiv in
    let key_r = nat_from_bytes_le (S.slice k 0 16) in
    let key_s = nat_from_bytes_le (S.slice k 16 32) in
    S.length first == 16 * blocks /\ S.length last < 16 /\
    FStar.Endianness.le_to_n tag ==
      P.poly1305_hash_all
        (P.poly1305_hash_blocks 0 Vale.Def.Words_s.pow2_128 (P.make_r key_r)
          (block_fun first) blocks)
        key_r key_s (block_fun last) (S.length last)))
  (ensures tag `S.equal`
    BF.of_bytes (Spec.Poly1305.poly1305_mac (S.append first last) k)) =
  let open Vale.Poly1305.Equiv in
  let key_r = nat_from_bytes_le (S.slice k 0 16) in
  let key_s = nat_from_bytes_le (S.slice k 16 32) in
  hash_append_last first last blocks key_r key_s;
  let h = P.poly1305_hash_blocks 0 Vale.Def.Words_s.pow2_128 (P.make_r key_r)
    (block_fun first) blocks in
  assert_norm (P.poly1305_hash_all h key_r key_s (block_fun last) (S.length last) ==
    norm [delta_only [`%P.poly1305_hash_all]]
      (P.poly1305_hash_all h key_r key_s (block_fun last) (S.length last)));
  assert_norm (P.poly1305_hash key_r key_s (block_fun (S.append first last))
      (S.length (S.append first last)) ==
    norm [delta_only [`%P.poly1305_hash; `%P.poly1305_hash_all]]
      (P.poly1305_hash key_r key_s (block_fun (S.append first last))
        (S.length (S.append first last))));
  assert (FStar.Endianness.le_to_n tag ==
    P.poly1305_hash key_r key_s (block_fun (S.append first last))
      (S.length (S.append first last)));
  lemma_poly1305_equiv (S.append first last) k;
  BF.lemma_le_to_n_is_nat_from_bytes tag;
  BF.lemma_n_to_le_is_nat_to_bytes 16 (FStar.Endianness.le_to_n tag);
  FStar.Endianness.n_to_le_le_to_n 16 tag
#pop-options
#pop-options
#pop-options

open FStar.Integers

#push-options "--z3rlimit 300 --split_queries always --z3refresh --ifuel 1"
let poly1305_vale
    (dst:B.buffer UInt8.t { B.length dst = 16 })
    (src:B.buffer UInt8.t)
    (len:U32.t { U32.v len = B.length src /\ U32.v len + 16 <= UInt.max_int 32 })
    (key:B.buffer UInt8.t { B.length key = 32 })
  : Stack unit
    (requires fun h ->
      EverCrypt.TargetConfig.hacl_can_compile_vale /\
      B.live h src /\ B.live h dst /\ B.live h key /\
      B.disjoint dst src /\ B.disjoint dst key)
    (ensures fun h0 _ h1 ->
      B.(modifies (loc_buffer dst) h0 h1 /\ (
      B.as_seq h1 dst ==
        BF.of_bytes (Spec.Poly1305.poly1305_mac
          (BF.to_bytes (B.as_seq h0 src))
          (BF.to_bytes (B.as_seq h0 key))))))
  =
  if EverCrypt.TargetConfig.hacl_can_compile_vale then
    let h0 = ST.get () in
    push_frame ();
    let h_frame = ST.get () in
    B.fresh_frame_modifies h0 h_frame;
    // Vale wants a large context
    let ctx = B.alloca 0uy 192ul in
    let h_ctx = ST.get () in
    unused_buffer_disjoint h_frame key ctx;
    unused_buffer_disjoint h_frame src ctx;
    unused_buffer_disjoint h_frame dst ctx;
    // With the key located at bytes [ 24; 56 )
    B.blit key 0ul ctx 24ul 32ul;

    let h_key = ST.get () in
    [@inline_let] let run_poly1305 () : StackInline unit
      (requires fun h -> h == h_key)
      (ensures fun _ _ h ->
        B.modifies (B.loc_buffer ctx) h_key h /\
        S.slice (B.as_seq h ctx) 0 16 `S.equal`
          Spec.Poly1305.poly1305_mac (B.as_seq h_key src) (B.as_seq h_key key)) =
      let n_blocks = len / 16ul in
      let n_extra = len % 16ul in
      if n_extra = 0ul then begin
        // Call Vale
        let h1 = ST.get () in
        // Initial hash (0) is located at bytes [ 0; 24 )
        assert_spinoff (forall (i:int).{:pattern (Seq.index (B.as_seq h1 ctx) i)} 0 <= i /\ i < 24 ==>
          Seq.index (Seq.slice (B.as_seq h1 ctx) 0 24) i == 0uy);
        Vale.Poly1305.CallingFromLowStar.lemma_hash_init h1 h1 ctx true;
        let res = Vale.Wrapper.X64.Poly.x64_poly1305 ctx src (FStar.Int.Cast.Full.uint32_to_uint64 len) 1UL in
        LowStar.Ignore.ignore res;
        let h2 = ST.get () in
        assert (B.length src == 8 * Vale.Poly1305.Util.readable_words (Seq.length (Vale.Arch.BufferFriend.to_bytes (B.as_seq h1 src))));
        Vale.Poly1305.CallingFromLowStar.lemma_call_poly1305 h1 h2 ctx src
          (Vale.Arch.BufferFriend.to_bytes (B.as_seq h1 src))
          (Vale.Arch.BufferFriend.to_bytes (B.as_seq h1 key));
        Vale.Poly1305.Equiv.lemma_poly1305_equiv (Vale.Arch.BufferFriend.to_bytes (B.as_seq h1 src))
          (Vale.Arch.BufferFriend.to_bytes (B.as_seq h1 key));
        Vale.Arch.BufferFriend.lemma_le_to_n_is_nat_from_bytes (S.slice (B.as_seq h2 ctx) 0 16);
        Vale.Arch.BufferFriend.lemma_n_to_le_is_nat_to_bytes 16 (FStar.Endianness.le_to_n (S.slice (B.as_seq h2 ctx) 0 16));
        FStar.Endianness.n_to_le_le_to_n 16 (S.slice (B.as_seq h2 ctx) 0 16);
        assert (S.slice (B.as_seq h2 ctx) 0 16 `S.equal`
          Spec.Poly1305.poly1305_mac (B.as_seq h1 src) (B.as_seq h1 key));
        ()
      end else begin
        let h_tmp = ST.get () in
        let tmp = B.alloca 0uy 16ul in // space for last 0..15 bytes
        let h_tmp_alloc = ST.get () in
        unused_buffer_disjoint h_tmp src tmp;
        unused_buffer_disjoint h_tmp key tmp;
        unused_buffer_disjoint h_tmp ctx tmp;
        unused_buffer_disjoint h_tmp dst tmp;
        let len16 = n_blocks * 16ul in
        assert (U32.v len16 == 16 * U32.v n_blocks);
        FStar.Math.Lemmas.cancel_mul_div (U32.v n_blocks) 16;
        assert (U32.v len16 + U32.v n_extra == U32.v len);
        let src16 = B.sub src 0ul len16 in
        B.blit src len16 tmp 0ul n_extra;
        // Call Vale: all but last bytes
        let h1 = ST.get () in
        B.modifies_buffer_elim src (B.loc_buffer tmp) h_tmp h1;
        B.modifies_buffer_elim key (B.loc_buffer tmp) h_tmp h1;
        assert (B.as_seq h1 src == B.as_seq h_key src /\
          B.as_seq h1 key == B.as_seq h_key key);
        assert (S.slice (B.as_seq h1 tmp) 0 (U32.v n_extra) ==
          S.slice (B.as_seq h1 src) (U32.v len16) (U32.v len));
        // Initial hash (0) is located at bytes [ 0; 24 )
        assert (forall (i:int).{:pattern (Seq.index (B.as_seq h1 ctx) i)} 0 <= i /\ i < 24 ==>
          Seq.index (Seq.slice (B.as_seq h1 ctx) 0 24) i == 0uy);
        Vale.Poly1305.CallingFromLowStar.lemma_hash_init h1 h1 ctx true;
        let res = Vale.Wrapper.X64.Poly.x64_poly1305 ctx src16 (FStar.Int.Cast.Full.uint32_to_uint64 len16) 0UL in
        LowStar.Ignore.ignore res;
        let h1' = ST.get () in
        Vale.Wrapper.X64.Poly.math_aux ctx 24;
        LowStar.BufferView.Down.length_eq (IT.get_downview ctx);
        assert (UInt64.v (MH.low_buffer_read IT.TUInt8 IT.TUInt64 h1' ctx 2) < 5);
        Vale.Poly1305.CallingFromLowStar.lemma_call_poly1305 h1 h1' ctx src16
          (Vale.Arch.BufferFriend.to_bytes (B.as_seq h1 src16))
          (Vale.Arch.BufferFriend.to_bytes (B.as_seq h1 key));
        assert (P.modp (accumulator h1' ctx) ==
          P.poly1305_hash_blocks 0 Vale.Def.Words_s.pow2_128
            (P.make_r (Vale.Poly1305.Equiv.nat_from_bytes_le
              (S.slice (BF.to_bytes (B.as_seq h1 key)) 0 16)))
            (Vale.Poly1305.Equiv.block_fun (BF.to_bytes (B.as_seq h1 src16)))
            (U32.v n_blocks));
        // Call Vale: last 0..15 bytes
        B.blit key 0ul ctx 24ul 32ul;
        let h1'' = ST.get () in
        B.modifies_buffer_elim tmp (B.loc_buffer ctx) h1 h1'';
        B.modifies_buffer_elim key (B.loc_buffer ctx) h1 h1'';
        B.modifies_buffer_elim src (B.loc_buffer ctx) h1 h1'';
        assert (forall (i:int).{:pattern (Seq.index (B.as_seq h1'' ctx) i)} 0 <= i /\ i < 24 ==>
          Seq.index (Seq.slice (B.as_seq h1'' ctx) 0 24) i ==
          Seq.index (Seq.slice (B.as_seq h1' ctx) 0 24) i);
        Vale.Poly1305.CallingFromLowStar.lemma_hash_init h1' h1'' ctx false;
        assert (UInt64.v (MH.low_buffer_read IT.TUInt8 IT.TUInt64 h1'' ctx 2) < 5);
        assert (accumulator h1'' ctx == accumulator h1' ctx);
        let res = Vale.Wrapper.X64.Poly.x64_poly1305 ctx tmp (FStar.Int.Cast.Full.uint32_to_uint64 n_extra) 1UL in
        LowStar.Ignore.ignore res;
        let h2 = ST.get () in
        B.modifies_buffer_elim tmp (B.loc_buffer ctx) h1'' h2;
        let proof : squash (S.slice (B.as_seq h2 ctx) 0 16 `S.equal` Spec.Poly1305.poly1305_mac (B.as_seq h1 src) (B.as_seq h1 key)) =
          let open FStar.Seq.Base in
          let open Vale.Poly1305.Spec_s in
          let open Vale.Def.Words_s in
          let open Vale.Poly1305.Util in
          let tmps = B.sub tmp 0ul n_extra in
          B.as_seq_gsub h1 src 0ul len16 (B.trivial_preorder UInt8.t);
          B.as_seq_gsub h1'' tmp 0ul n_extra (B.trivial_preorder UInt8.t);
          S.lemma_split (B.as_seq h1 src) (U32.v len16);
          let src' = Vale.Arch.BufferFriend.to_bytes (B.as_seq h1 src) in
          let src16' = Vale.Arch.BufferFriend.to_bytes (B.as_seq h1 src16) in
          let tmps' = Vale.Arch.BufferFriend.to_bytes (B.as_seq h1'' tmps) in
          B.length_as_seq h1 src16;
          B.length_as_seq h1'' tmps;
          assert (S.length src16' == 16 * U32.v n_blocks);
          assert (S.length tmps' == U32.v n_extra /\ S.length tmps' < 16);
          let key' = Vale.Arch.BufferFriend.to_bytes (B.as_seq h1'' key) in
          let key_r:nat128 = Vale.Poly1305.Equiv.nat_from_bytes_le (slice key' 0 16) in
          let key_s:nat128 = Vale.Poly1305.Equiv.nat_from_bytes_le (slice key' 16 32) in
          assert (P.modp (accumulator h1'' ctx) ==
            poly1305_hash_blocks 0 Vale.Def.Words_s.pow2_128
              (make_r key_r) (Vale.Poly1305.Equiv.block_fun src16') (U32.v n_blocks));
          assert (equal src' (append src16' tmps'));
          Vale.Poly1305.CallingFromLowStar.lemma_call_poly1305 h1'' h2 ctx tmp tmps' key';
          BF.lemma_le_to_n_is_nat_from_bytes (S.slice (B.as_seq h2 ctx) 0 16);
          assert (FStar.Endianness.le_to_n (S.slice (B.as_seq h2 ctx) 0 16) ==
            poly1305_hash_all (P.modp (accumulator h1'' ctx)) key_r key_s
              (Vale.Poly1305.Equiv.block_fun tmps') (length tmps'));
          tag_after_last src16' tmps' (U32.v n_blocks) key'
            (S.slice (B.as_seq h2 ctx) 0 16);
          ()
        in
        let h_tmp_end = ST.get () in
        B.modifies_remove_new_locs (B.loc_buffer tmp) B.loc_none (B.loc_buffer ctx)
          h_tmp h_tmp_alloc h_tmp_end;
        B.modifies_buffer_elim src (B.loc_buffer ctx) h_key h_tmp_end;
        B.modifies_buffer_elim key (B.loc_buffer ctx) h_key h_tmp_end;
        assert (S.slice (B.as_seq h_tmp_end ctx) 0 16 `S.equal`
          Spec.Poly1305.poly1305_mac (B.as_seq h_key src) (B.as_seq h_key key));
        assert (ST.inline_stack_inv h_key h_tmp_end)
      end
    in
    run_poly1305 ();

    B.blit ctx 0ul dst 0ul 16ul;
    let h_end = ST.get () in
    B.modifies_remove_new_locs (B.loc_buffer ctx) B.loc_none (B.loc_buffer dst)
      h_frame h_ctx h_end;
    assert (ST.inline_stack_inv h_frame h_end);
    pop_frame ();

    let h3 = ST.get () in
    B.modifies_fresh_frame_popped h0 h_frame (B.loc_buffer dst) h_end h3;
    stack_frame_equal_domains h0 h_frame h_end h_end h3;
    assert (B.as_seq h3 dst `S.equal` Spec.Poly1305.poly1305_mac (B.as_seq h0 src) (B.as_seq h0 key))
#pop-options

let mac output input input_len key =
  let h0 = ST.get () in
  let vec256 = EverCrypt.AutoConfig2.has_vec256 () in
  let vec128 = EverCrypt.AutoConfig2.has_vec128 () in

  if EverCrypt.TargetConfig.hacl_can_compile_vec256 && vec256 then begin
    LowStar.Ignore.ignore vec128;
    Hacl.Streaming.Poly1305_256.mac output input input_len key

  end else if EverCrypt.TargetConfig.hacl_can_compile_vec128 && vec128 then begin
    LowStar.Ignore.ignore vec256;
    Hacl.Streaming.Poly1305_128.mac output input input_len key

  end else begin
    LowStar.Ignore.ignore vec256;
    LowStar.Ignore.ignore vec128;
    if EverCrypt.TargetConfig.hacl_can_compile_vale then
      poly1305_vale output input input_len key
    else (
      LowStar.Ignore.ignore poly1305_vale;
      Hacl.Streaming.Poly1305_32.mac output input input_len key
    )
  end
