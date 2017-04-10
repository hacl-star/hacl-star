module Hacl.Impl.Ed25519.Verify

open FStar.Buffer
open FStar.UInt32


let uint8_p = buffer UInt8.t
let felem   = b:buffer UInt64.t{length b = 5}

val gte_q:
  s:buffer UInt64.t{length s = 5} ->
  Stack bool
    (requires (fun h -> live h s))
    (ensures (fun h0 b h1 -> live h0 s /\ h0 == h1))
let gte_q s =
  let s0 = s.(0ul) in
  let s1 = s.(1ul) in
  let s2 = s.(2ul) in
  let s3 = s.(3ul) in
  let s4 = s.(4ul) in
  let open FStar.UInt64 in
       if s4 >^ 0x00000010000000uL then true
  else if s4 <^ 0x00000010000000uL then false
  else if s3 >^ 0x00000000000000uL then true
  else if s2 >^ 0x000000000014deuL then true
  else if s2 <^ 0x000000000014deuL then false
  else if s1 >^ 0xf9dea2f79cd658uL then true
  else if s1 <^ 0xf9dea2f79cd658uL then false
  else if s0 >=^ 0x12631a5cf5d3eduL then true
  else false


val eq:
  a:felem ->
  b:felem ->
  Stack bool
    (requires (fun h -> live h a /\ live h b))
    (ensures (fun h0 r h1 -> live h0 a /\ live h0 b /\ h0 == h1 /\ r <==> as_seq h0 b == as_seq h0 a))
let eq a b =
  let a0 = a.(0ul) in
  let a1 = a.(1ul) in
  let a2 = a.(2ul) in
  let a3 = a.(3ul) in
  let a4 = a.(4ul) in
  let b0 = b.(0ul) in
  let b1 = b.(1ul) in
  let b2 = b.(2ul) in
  let b3 = b.(3ul) in
  let b4 = b.(4ul) in
  FStar.UInt64.(a0 =^ b0 && a1 =^ b1 && a2 =^ b2 && a3 =^ b3 && a4 =^ b4)


val point_equal:
  p:Hacl.Impl.Ed25519.ExtPoint.point ->
  q:Hacl.Impl.Ed25519.ExtPoint.point ->
  Stack bool
    (requires (fun h -> live h p /\ live h q))
    (ensures (fun h0 _ h1 -> live h0 p /\ live h0 q /\ modifies_0 h0 h1))
let point_equal p q =
  push_frame();
  let tmp = create 0uL 80ul in
  let pxqz = Buffer.sub tmp 0ul 20ul in
  let qxpz = Buffer.sub tmp 20ul 20ul in
  let pyqz = Buffer.sub tmp 40ul 20ul in
  let qypz = Buffer.sub tmp 60ul 20ul in
  Hacl.Bignum25519.fmul pxqz (Hacl.Impl.Ed25519.ExtPoint.getx p) (Hacl.Impl.Ed25519.ExtPoint.getz q);
  Hacl.Bignum25519.fmul qxpz (Hacl.Impl.Ed25519.ExtPoint.getx q) (Hacl.Impl.Ed25519.ExtPoint.getz p);
  Hacl.Bignum25519.reduce pxqz;
  Hacl.Bignum25519.reduce qxpz;
  let b = eq pxqz qxpz in
  let res =
    if b then (
      Hacl.Bignum25519.fmul pyqz (Hacl.Impl.Ed25519.ExtPoint.gety p) (Hacl.Impl.Ed25519.ExtPoint.getz q);
      Hacl.Bignum25519.fmul qypz (Hacl.Impl.Ed25519.ExtPoint.gety q) (Hacl.Impl.Ed25519.ExtPoint.getz p);
      Hacl.Bignum25519.reduce pyqz;
      Hacl.Bignum25519.reduce qypz;
      let b' = eq pyqz qypz in
      if b' then true
      else false
   ) else false in
   pop_frame();
   res
    

val verify:
  public:uint8_p{length public = 32} ->
  msg:uint8_p ->
  len:UInt32.t{length msg = UInt32.v len} ->
  signature:uint8_p{length signature = 64} ->
  Stack bool
    (requires (fun h -> live h public /\ live h msg /\ live h signature))
    (ensures (fun h0 _ h1 -> modifies_0 h0 h1 /\ live h0 msg /\ live h0 public /\ live h0 signature))
let verify public msg len signature =
  push_frame();
  let a' = create 0uL 20ul in
  let b = Hacl.Impl.Ed25519.PointDecompress.point_decompress a' public in
  let res =
  if b then (
    let rs = Buffer.sub signature 0ul 32ul in
    let r' = create 0uL 20ul in
    let b' = Hacl.Impl.Ed25519.PointDecompress.point_decompress r' rs in
    if b' then (
      let s = create 0uL 5ul in
      Hacl.Impl.Load56.load_32_bytes s (Buffer.sub signature 32ul 32ul);
      let b'' = gte_q s in
      if b'' then false
      else (
        let rs_public_msg = create 0uy (len +^ 64ul) in
        blit rs 0ul rs_public_msg 0ul 32ul;
        blit public 0ul rs_public_msg 32ul 32ul;
        blit msg 0ul rs_public_msg 64ul len;
        let h = create 0uL 5ul in
        Hacl.Impl.SHA512.ModQ.sha512_modq h rs_public_msg (len +^ 64ul);
        let g = create 0uL 20ul in
        Hacl.Impl.Ed25519.G.make_g g;
        let sB = create 0uL 20ul in
        Hacl.Impl.Ed25519.Ladder.point_mul sB (Buffer.sub signature 32ul 32ul) g;
        let hA = create 0uL 20ul in
        let h' = create 0uy 32ul in
        Hacl.Impl.Store56.store_56 h' h;
        Hacl.Impl.Ed25519.Ladder.point_mul hA h' a';
        let rhA = create 0uL 20ul in
        Hacl.Impl.Ed25519.PointAdd.point_add rhA r' hA;
        point_equal sB rhA
      )
    ) else false
  ) else false in
  pop_frame();
  res
