module Hacl.Impl.Ed25519.Verify.Steps

open FStar.Mul
open FStar.Buffer
open FStar.UInt32

open Hacl.Bignum25519
open Hacl.Impl.Ed25519.ExtPoint

#reset-options "--max_fuel 0 --z3rlimit 20"


let uint8_p = buffer UInt8.t
let felem   = b:buffer UInt64.t{length b = 5}


let point_inv h (p:point) : GTot Type0 =
  live h p /\ (let x = getx p in let y = gety p in let z = getz p in let t = gett p in
  red_513 (as_seq h x) /\ red_513 (as_seq h y) /\ red_513 (as_seq h z) /\ red_513 (as_seq h t))


val verify_step_1:
  r':buffer Hacl.UInt64.t{length r' = 20} ->
  signature:uint8_p{length signature = 64 /\ disjoint r' signature} ->
  Stack bool
    (requires (fun h -> live h r' /\ live h signature))
    (ensures (fun h0 z h1 -> live h1 r' /\ live h0 signature /\ live h1 signature /\
      modifies_1 r' h0 h1 /\
      (let decpoint = Spec.Ed25519.point_decompress (Seq.slice (as_seq h0 signature) 0 32) in
       if z = true then (Some? decpoint /\ Some?.v decpoint == as_point h1 r' /\ point_inv h1 r')
       else (None? decpoint))))


#reset-options "--max_fuel 0 --z3rlimit 200"

let verify_step_1 r' signature =
  let h = ST.get() in
  let rs = Buffer.sub signature 0ul 32ul in
  Seq.lemma_eq_intro (as_seq h rs) (Seq.slice (as_seq h signature)0 32);
  let b' = Hacl.Impl.Ed25519.PointDecompress.point_decompress r' rs in
  b'


val verify_step_2:
  r:buffer UInt8.t{length r = 32} ->
  msg:buffer UInt8.t{disjoint msg r} ->
  len:UInt32.t{UInt32.v len = length msg /\ length msg < pow2 32 - 64} ->
  rs:buffer UInt8.t{length rs = 32 /\ disjoint rs r} ->
  public:buffer UInt8.t{length public = 32 /\ disjoint public r} ->
  Stack unit
    (requires (fun h -> live h r /\ live h msg /\ live h rs /\ live h public))
    (ensures (fun h0 _ h1 -> live h0 r /\ live h0 msg /\ live h0 rs /\ live h0 public /\
      live h1 r /\ live h1 msg /\ live h1 rs /\ live h1 public /\ modifies_1 r h0 h1 /\
      as_seq h1 r ==
        FStar.Endianness.(little_bytes 32ul (Spec.Ed25519.sha512_modq FStar.Seq.(as_seq h0 rs @| as_seq h0 public @| as_seq h0 msg))) ))

let verify_step_2 r msg len rs public =
  admit();
  push_frame();
  let rs_public_msg = create 0uy (len +^ 64ul) in
  push_frame();
  let r' = create 0uL 5ul in
  blit rs 0ul rs_public_msg 0ul 32ul;
  blit public 0ul rs_public_msg 32ul 32ul;
  blit msg 0ul rs_public_msg 64ul len;
  Hacl.Impl.SHA512.ModQ.sha512_modq r' rs_public_msg (len +^ 64ul);
  Hacl.Impl.Store56.store_56 r r';
  pop_frame();
  pop_frame()



val verify_step_4:
  s:buffer UInt8.t{length s = 32} ->
  h':buffer UInt8.t{length h' = 32} ->
  a':point ->
  r':point ->
  Stack bool
    (requires (fun h -> live h s  /\ live h h' /\ live h a' /\ live h r'))
    (ensures (fun h0 z h1 -> live h0 s /\ live h0 h' /\ live h0 a' /\ live h0 r' /\
      live h1 s /\ live h1 h' /\ live h1 a' /\ modifies_0 h0 h1 /\ live h1 r' /\
      z == Spec.Ed25519.(
        let sB = point_mul (as_seq h0 s) g in
        let hA = point_mul (as_seq h0 h') (as_point h0 a') in
        point_equal sB (point_add (as_point h0 r') hA))))

let verify_step_4 s h' a' r' =
  admit();
  push_frame();
  let g = create 0uL 20ul in
  Hacl.Impl.Ed25519.G.make_g g;
  push_frame();
  let tmp = Buffer.create 0uL 60ul in
  let hA   = Buffer.sub tmp  0ul  20ul in
  let rhA  = Buffer.sub tmp 20ul  20ul in
  let sB   = Buffer.sub tmp 40ul  20ul in
  Hacl.Impl.Ed25519.Ladder.point_mul sB s g;
  Hacl.Impl.Ed25519.Ladder.point_mul hA h' a';
  Hacl.Impl.Ed25519.PointAdd.point_add rhA r' hA;
  let b = Hacl.Impl.Ed25519.PointEqual.point_equal sB rhA in
  pop_frame();
  pop_frame();
  b
