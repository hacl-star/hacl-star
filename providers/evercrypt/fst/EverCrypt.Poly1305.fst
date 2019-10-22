module EverCrypt.Poly1305

/// A multiplexed frontend for Poly1305.

module B = LowStar.Buffer
module U32 = FStar.UInt32
module ST = FStar.HyperStack.ST
module F = Hacl.Impl.Poly1305.Fields
module S = FStar.Seq

open FStar.HyperStack.ST
open FStar.Integers

#reset-options "--initial_fuel 1 --max_fuel 1 --max_ifuel 0"

friend Lib.IntTypes

#push-options "--z3rlimit 200"
let poly1305_vale
    (dst:B.buffer UInt8.t { B.length dst = 16 })
    (src:B.buffer UInt8.t)
    (len:U32.t { U32.v len = B.length src /\ U32.v len + 16 <= UInt.max_int 32 })
    (key:B.buffer UInt8.t { B.length key = 32 })
  : Stack unit
    (requires fun h ->
      EverCrypt.TargetConfig.x64 /\
      B.live h src /\ B.live h dst /\ B.live h key /\
      B.disjoint dst src /\ B.disjoint dst key)
    (ensures fun h0 _ h1 ->
      B.(modifies (loc_buffer dst) h0 h1 /\ (
      B.as_seq h1 dst ==
        BF.of_bytes (Spec.Poly1305.poly1305_mac
          (BF.to_bytes (B.as_seq h0 src))
          (BF.to_bytes (B.as_seq h0 key))))))
  =
  let h0 = ST.get () in
  push_frame ();
  // Vale wants a large context
  let ctx = B.alloca 0uy 192ul in
  // With the key located at bytes [ 24; 56 )
  B.blit key 0ul ctx 24ul 32ul;

  let n_blocks = len / 16ul in
  let n_extra = len % 16ul in
  if n_extra = 0ul then begin
    // Call Vale
    let h1 = ST.get () in
    // Initial hash (0) is located at bytes [ 0; 24 )
    assert (forall (i:int).{:pattern (Seq.index (B.as_seq h1 ctx) i)} 0 <= i /\ i < 24 ==>
      Seq.index (Seq.slice (B.as_seq h1 ctx) 0 24) i == 0uy);
    Vale.Poly1305.CallingFromLowStar.lemma_hash_init h1 h1 ctx true;
    Vale.Wrapper.X64.Poly.x64_poly1305 ctx src (FStar.Int.Cast.Full.uint32_to_uint64 len) 1UL;
    let h2 = ST.get () in
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
    let tmp = B.alloca 0uy 16ul in // space for last 0..15 bytes
    let len16 = n_blocks * 16ul in
    let src16 = B.sub src 0ul len16 in
    B.blit src len16 tmp 0ul n_extra;
    // Call Vale: all but last bytes
    let h1 = ST.get () in
    // Initial hash (0) is located at bytes [ 0; 24 )
    assert (forall (i:int).{:pattern (Seq.index (B.as_seq h1 ctx) i)} 0 <= i /\ i < 24 ==>
      Seq.index (Seq.slice (B.as_seq h1 ctx) 0 24) i == 0uy);
    Vale.Poly1305.CallingFromLowStar.lemma_hash_init h1 h1 ctx true;
    Vale.Wrapper.X64.Poly.x64_poly1305 ctx src16 (FStar.Int.Cast.Full.uint32_to_uint64 len16) 0UL;
    let h1' = ST.get () in
    Vale.Poly1305.CallingFromLowStar.lemma_call_poly1305 h1 h1' ctx src16
      (Vale.Arch.BufferFriend.to_bytes (B.as_seq h1 src16))
      (Vale.Arch.BufferFriend.to_bytes (B.as_seq h1 key));
    // Call Vale: last 0..15 bytes
    B.blit key 0ul ctx 24ul 32ul;
    let h1'' = ST.get () in
    assert (forall (i:int).{:pattern (Seq.index (B.as_seq h1'' ctx) i)} 0 <= i /\ i < 24 ==>
      Seq.index (Seq.slice (B.as_seq h1'' ctx) 0 24) i ==
      Seq.index (Seq.slice (B.as_seq h1' ctx) 0 24) i);
    Vale.Poly1305.CallingFromLowStar.lemma_hash_init h1' h1'' ctx false;
    Vale.Wrapper.X64.Poly.x64_poly1305 ctx tmp (FStar.Int.Cast.Full.uint32_to_uint64 n_extra) 1UL;
    let h2 = ST.get () in
    let proof : squash (S.slice (B.as_seq h2 ctx) 0 16 `S.equal` Spec.Poly1305.poly1305_mac (B.as_seq h1 src) (B.as_seq h1 key)) =
      let open FStar.Seq.Base in
      let open Vale.Poly1305.Spec_s in
      let open Vale.Def.Words_s in
      let open Vale.Poly1305.Util in
      let tmps = B.sub tmp 0ul n_extra in
      let src' = Vale.Arch.BufferFriend.to_bytes (B.as_seq h1 src) in
      let src16' = Vale.Arch.BufferFriend.to_bytes (B.as_seq h1 src16) in
      let tmps' = Vale.Arch.BufferFriend.to_bytes (B.as_seq h1'' tmps) in
      let key' = Vale.Arch.BufferFriend.to_bytes (B.as_seq h1'' key) in
      let key_r:nat128 = Vale.Poly1305.Equiv.nat_from_bytes_le (slice key' 0 16) in
      let key_s:nat128 = Vale.Poly1305.Equiv.nat_from_bytes_le (slice key' 16 32) in
      let n = 0x10000000000000000 in
      let inp1:int -> nat128 = Vale.Poly1305.Equiv.block_fun src16' in
      let inp2:int -> nat128 = Vale.Poly1305.Equiv.block_fun (append src16' tmps') in
      assert (equal src' (append src16' tmps'));
      lemma_equal_blocks 0 (n * n) (make_r key_r) inp1 inp2 (UInt32.v n_blocks);
      Vale.Poly1305.Equiv.lemma_poly1305_equiv
        (Vale.Arch.BufferFriend.to_bytes (B.as_seq h1 src))
        (Vale.Arch.BufferFriend.to_bytes (B.as_seq h1 key));
      Vale.Arch.BufferFriend.lemma_le_to_n_is_nat_from_bytes (S.slice (B.as_seq h2 ctx) 0 16);
      Vale.Arch.BufferFriend.lemma_n_to_le_is_nat_to_bytes 16 (FStar.Endianness.le_to_n (S.slice (B.as_seq h2 ctx) 0 16));
      FStar.Endianness.n_to_le_le_to_n 16 (S.slice (B.as_seq h2 ctx) 0 16);
      Vale.Poly1305.CallingFromLowStar.lemma_call_poly1305 h1'' h2 ctx tmp tmps' key';
      ()
    in
    ()
  end;

  B.blit ctx 0ul dst 0ul 16ul;
  pop_frame ();

  let h3 = ST.get () in
  assert (B.as_seq h3 dst `S.equal` Spec.Poly1305.poly1305_mac (B.as_seq h0 src) (B.as_seq h0 key))

let poly1305 dst src len key =
  let h0 = ST.get () in
  let avx2 = EverCrypt.AutoConfig2.has_avx2 () in
  let avx = EverCrypt.AutoConfig2.has_avx () in
  let vale = EverCrypt.AutoConfig2.wants_vale () in

  if EverCrypt.TargetConfig.x64 && avx2 then begin
    Hacl.Poly1305_256.poly1305_mac dst len src key

  end else if EverCrypt.TargetConfig.x64 && avx then begin
    Hacl.Poly1305_128.poly1305_mac dst len src key

  end else if EverCrypt.TargetConfig.x64 && vale then begin
    poly1305_vale dst src len key

  end else begin
    Hacl.Poly1305_32.poly1305_mac dst len src key
  end
