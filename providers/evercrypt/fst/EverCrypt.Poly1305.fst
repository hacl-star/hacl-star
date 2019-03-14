module EverCrypt.Poly1305

/// A multiplexed frontend for Poly1305.

module B = LowStar.Buffer
module U32 = FStar.UInt32
module ST = FStar.HyperStack.ST
module F = Hacl.Impl.Poly1305.Fields

open FStar.HyperStack.ST

#reset-options "--max_fuel 0 --max_ifuel 0"

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
    let ctx = B.alloca 0uy 192ul in
    B.blit key 0ul ctx 16ul 64ul;
    Poly_stdcalls.poly1305 ctx src (FStar.Int.Cast.Full.uint32_to_uint64 len);
    B.blit ctx 0ul dst 0ul 16ul;
    let h1 = ST.get () in
    // Missing spec equivalence proof here.
    assume (B.as_seq h1 dst == Spec.Poly1305.poly1305 (B.as_seq h0 src) (B.as_seq h0 key));
    pop_frame ()
  end else begin
    Hacl.Poly1305_32.poly1305_mac dst src len key;
    Hacl.Spec.Poly1305.Vec.poly1305_vec_is_poly1305 #1 (B.as_seq h0 src) (B.as_seq h0 key)
  end
