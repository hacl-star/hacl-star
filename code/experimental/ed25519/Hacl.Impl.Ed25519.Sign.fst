module Hacl.Impl.Ed25519.Sign

open FStar.Buffer
open FStar.UInt32

let hint8_p = buffer Hacl.UInt8.t
let op_String_Access h b = Hacl.Spec.Endianness.reveal_sbytes (as_seq h b)


#reset-options "--max_fuel 0 --z3rlimit 20"

val sign:
  signature:hint8_p{length signature = 64} ->
  secret:hint8_p{length secret = 32} ->
  msg:hint8_p ->
  len:UInt32.t{UInt32.v len = length msg} ->
  Stack unit
    (requires (fun h -> live h signature /\ live h msg /\ live h secret))
    (ensures (fun h0 _ h1 -> live h0 signature /\ live h0 msg /\ live h0 secret /\
      live h1 signature /\ modifies_1 signature h0 h1 /\
      h1.[signature] == Spec.Ed25519.sign h0.[secret] h0.[msg]))
let sign signature secret msg len =
  push_frame();
  let tmp = create 0uL 40ul in
  let g = Buffer.sub tmp 0ul 20ul in
  let tmpa = Buffer.sub tmp 20ul 20ul in
  Hacl.Impl.Ed25519.G.make_g g;
  push_frame();
  let buf = create 0uy 96ul in
  let s' = Buffer.sub buf 0ul 64ul in
  let a' = Buffer.create 0uL 5ul in
  Hacl.Impl.Ed25519.SecretExpand.secret_expand s' secret;
  let a = Buffer.sub s' 0ul 32ul in
  let prefix = Buffer.sub s' 32ul 64ul in
  Hacl.Impl.Ed25519.Ladder.point_mul tmpa a g;
  Hacl.Impl.Ed25519.PointCompress.point_compress a' tmpa;
  let a'' = create 0uy 32ul in
  Hacl.Impl.Store51.store_51 a'' a';
  let prefix_at_message = create 0uy (len +^ 64ul) in (* TODO: remove one copy of msg *)
  blit prefix 0ul prefix_at_message 0ul 32ul;
  blit msg 0ul prefix_at_message 32ul len;
  let r = create 0uL 5ul in
  Hacl.Impl.SHA512.ModQ.sha512_modq r prefix_at_message (len+^32ul);
  let rb = create 0uy 32ul in
  Hacl.Impl.Store56.store_56 rb r;
  let r' = create 0uL 20ul in
  Hacl.Impl.Ed25519.Ladder.point_mul r' rb g;
  let rs = create 0uL 20ul in
  Hacl.Impl.Ed25519.PointCompress.point_compress rs r';
  let rs' = create 0uy 32ul in
  Hacl.Impl.Store51.store_51 rs' rs;
  let h = create 0uL 5ul in
  blit rs'  0ul prefix_at_message 0ul 32ul;
  blit a''  0ul prefix_at_message 32ul 32ul;
  blit msg 0ul prefix_at_message 64ul len;
  Hacl.Impl.SHA512.ModQ.sha512_modq h prefix_at_message (len+^64ul);
  let aq = create 0uL 5ul in
  Hacl.Impl.Load56.load_32_bytes aq a;
  let ha = create 0uL 5ul in
  Hacl.Impl.BignumQ.Mul.mul_modq ha h aq;
  let s = create 0uL 5ul in
  Hacl.Impl.BignumQ.Mul.add_modq s r ha;
  let s' = create 0uy 32ul in
  Hacl.Impl.Store56.store_56 s' s;
  blit rs' 0ul signature 0ul 32ul;
  blit s' 0ul signature 32ul 32ul;
  pop_frame();
  pop_frame()
