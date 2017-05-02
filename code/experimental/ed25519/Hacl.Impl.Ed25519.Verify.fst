module Hacl.Impl.Ed25519.Verify

open FStar.Mul
open FStar.Buffer
open FStar.UInt32

open Hacl.Impl.Ed25519.ExtPoint

open Hacl.Impl.Ed25519.Verify.Steps

#reset-options "--max_fuel 0 --z3rlimit 20"


let uint8_p = buffer UInt8.t
let felem   = b:buffer UInt64.t{length b = 5}


val verify__:
  public:uint8_p{length public = 32} ->
  msg:uint8_p ->
  len:UInt32.t{length msg = UInt32.v len /\ length msg < pow2 32 - 64} ->
  signature:uint8_p{length signature = 64} ->
  tmp:buffer UInt64.t{length tmp = 45} ->
  tmp':buffer UInt8.t{length tmp' = 32} ->
  Stack bool
    (requires (fun h -> live h public /\ live h msg /\ live h signature))
    (ensures (fun h0 z h1 -> modifies_0 h0 h1 /\ live h0 msg /\ live h0 public /\ live h0 signature /\
      z == Spec.Ed25519.(verify (as_seq h0 public) (as_seq h0 msg) (as_seq h0 signature))
    ))
let verify__ public msg len signature tmp tmp' =
  let a' = Buffer.sub tmp 0ul  20ul in
  let r' = Buffer.sub tmp 20ul 20ul in
  let s  = Buffer.sub tmp 40ul 5ul  in
  let h'  = tmp' in
  let b = Hacl.Impl.Ed25519.PointDecompress.point_decompress a' public in
  let res =
  if b then (
    let rs = Buffer.sub signature 0ul 32ul in
    let b' = Hacl.Impl.Ed25519.PointDecompress.point_decompress r' rs in
    if b' then (
      (* let s = create 0uL 5ul in *)
      Hacl.Impl.Load56.load_32_bytes s (Buffer.sub signature 32ul 32ul);
      let b'' = Hacl.Impl.Ed25519.PointEqual.gte_q s in
      if b'' then false
      else (
        verify_step_2 h' msg len rs public;
        verify_step_4 (Buffer.sub signature 32ul 32ul) h' a' r'
        (* let rs_public_msg = create 0uy (len +^ 64ul) in *)
        (* blit rs 0ul rs_public_msg 0ul 32ul; *)
        (* blit public 0ul rs_public_msg 32ul 32ul; *)
        (* blit msg 0ul rs_public_msg 64ul len; *)
        (* let h = create 0uL 5ul in *)
        (* Hacl.Impl.SHA512.ModQ.sha512_modq h rs_public_msg (len +^ 64ul); *)
        (* let g = create 0uL 20ul in *)
        (* Hacl.Impl.Ed25519.G.make_g g; *)
        (* Hacl.Impl.Ed25519.Ladder.point_mul sB (Buffer.sub signature 32ul 32ul) g; *)
        (* let h' = create 0uy 32ul in *)
        (* Hacl.Impl.Store56.store_56 h' h; *)
        (* Hacl.Impl.Ed25519.Ladder.point_mul hA h' a'; *)
        (* Hacl.Impl.Ed25519.PointAdd.point_add rhA r' hA; *)
        (* Hacl.Impl.Ed25519.PointEqual.point_equal sB rhA *)
      )
    ) else false
  ) else false in
  res


val verify_:
  public:uint8_p{length public = 32} ->
  msg:uint8_p ->
  len:UInt32.t{length msg = UInt32.v len /\ length msg < pow2 32 - 64} ->
  signature:uint8_p{length signature = 64} ->
  Stack bool
    (requires (fun h -> live h public /\ live h msg /\ live h signature))
    (ensures (fun h0 z h1 -> modifies_0 h0 h1 /\ live h0 msg /\ live h0 public /\ live h0 signature /\
      z == Spec.Ed25519.(verify (as_seq h0 public) (as_seq h0 msg) (as_seq h0 signature))
    ))
let verify_ public msg len signature =
  push_frame();
  let tmp = create 0uL 45ul in
  push_frame();
  let tmp' = create 0uy 32ul in
  let res = verify__ public msg len signature tmp tmp' in
  pop_frame();
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
  verify_ public msg len signature
