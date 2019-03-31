module EverCrypt.Poly1305

/// A multiplexed frontend for Poly1305.

module B = LowStar.Buffer
module U32 = FStar.UInt32
module ST = FStar.HyperStack.ST
module F = Hacl.Impl.Poly1305.Fields
module S = FStar.Seq

open FStar.HyperStack.ST

#reset-options "--max_fuel 0 --max_ifuel 0"

friend Lib.IntTypes

#push-options "--z3rlimit 200"
let poly1305 dst src len key =
  let h0 = ST.get () in
  let avx2 = EverCrypt.AutoConfig2.has_avx2 () in
  let avx = EverCrypt.AutoConfig2.has_avx () in
  if EverCrypt.TargetConfig.x64 && avx2 then begin
    Hacl.Poly1305_256.poly1305_mac dst src len key;
    Hacl.Spec.Poly1305.Vec.poly1305_vec_is_poly1305 #4 (B.as_seq h0 src) (B.as_seq h0 key)
  end else if EverCrypt.TargetConfig.x64 && avx then begin
    Hacl.Poly1305_128.poly1305_mac dst src len key;
    Hacl.Spec.Poly1305.Vec.poly1305_vec_is_poly1305 #2 (B.as_seq h0 src) (B.as_seq h0 key)
  end else if EverCrypt.TargetConfig.x64 then begin
    push_frame ();
    // Vale wants a large context
    let ctx = B.alloca 0uy 192ul in
    // With the key located at bytes [ 24; 56 )
    B.blit key 0ul ctx 24ul 32ul;
    // With an extra constraint on the size of the input buffer (to be alleviated)
    assume (U32.v len % 16 = 0);

    // Call Vale
    let h1 = ST.get () in
    Poly_stdcalls.poly1305 ctx src (FStar.Int.Cast.Full.uint32_to_uint64 len);
    let h2 = ST.get () in

    X64.Poly1305.CallingFromLowStar.lemma_call_poly1305 h1 h2 ctx (*inp*)src
      (Arch.BufferFriend.to_bytes (B.as_seq h1 src))
      (Arch.BufferFriend.to_bytes (B.as_seq h1 key));

    Poly1305.Equiv.lemma_poly1305_equiv (Arch.BufferFriend.to_bytes (B.as_seq h1 src))
      (Arch.BufferFriend.to_bytes (B.as_seq h1 key));

    assume (S.slice (B.as_seq h2 ctx) 0 16 `S.equal`
      Spec.Poly1305.poly1305 (B.as_seq h1 src) (B.as_seq h1 key));

    B.blit ctx 0ul dst 0ul 16ul;
    pop_frame ();

    let h3 = ST.get () in
    assert (B.as_seq h3 dst `S.equal` Spec.Poly1305.poly1305 (B.as_seq h0 src) (B.as_seq h0 key))

  end else begin
    Hacl.Poly1305_32.poly1305_mac dst src len key;
    Hacl.Spec.Poly1305.Vec.poly1305_vec_is_poly1305 #1 (B.as_seq h0 src) (B.as_seq h0 key)
  end
