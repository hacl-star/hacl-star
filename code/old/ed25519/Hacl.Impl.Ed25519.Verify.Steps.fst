module Hacl.Impl.Ed25519.Verify.Steps

module ST = FStar.HyperStack.ST

open FStar.HyperStack.All

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
        FStar.Old.Endianness.(little_bytes 32ul (Spec.Ed25519.sha512_modq FStar.Seq.(as_seq h0 rs @| as_seq h0 public @| as_seq h0 msg))) ))

let verify_step_2 r msg len rs public =
  assert_norm(pow2 56 = 0x100000000000000);
  push_frame();
  let h0 = ST.get() in
  let r' = create 0uL 5ul in
  let h1 = ST.get() in
  Hacl.Impl.SHA512.ModQ.sha512_modq_pre_pre2 r' rs public msg len;
  let h2 = ST.get() in
  Hacl.Impl.Store56.store_56 r r';
  let h3 = ST.get() in
  lemma_modifies_0_2 r r' h0 h1 h3;
  FStar.Old.Endianness.lemma_little_endian_inj (as_seq h3 r)
                                     (FStar.Old.Endianness.little_bytes 32ul (Spec.Ed25519.sha512_modq FStar.Seq.(as_seq h0 rs @| as_seq h0 public @| as_seq h0 msg)));
  pop_frame()


val point_mul_g:
  result:point ->
  scalar:buffer Hacl.UInt8.t{length scalar = 32 /\ disjoint result scalar} ->
  Stack unit
  (requires (fun h -> Buffer.live h scalar /\ live h result))
  (ensures (fun h0 _ h1 -> Buffer.live h0 scalar /\ live h0 result /\
    live h1 result /\ modifies_1 result h0 h1 /\ point_inv h1 result /\
    (let r = as_point h1 result in
     let n  = as_seq h0 scalar in
     r == Spec.Ed25519.point_mul n Spec.Ed25519.g) ))

let point_mul_g result scalar =
  push_frame();
  let h0 = ST.get() in
  let g = create 0uL 20ul in
  let h0' = ST.get() in
  Hacl.Impl.Ed25519.G.make_g g;
  let h1 = ST.get() in
  lemma_modifies_0_1' g h0 h0' h1;
  Hacl.Impl.Ed25519.Ladder.point_mul result scalar g;
  pop_frame()


val verify_step_4:
  s:buffer UInt8.t{length s = 32} ->
  h':buffer UInt8.t{length h' = 32} ->
  a':point ->
  r':point ->
  Stack bool
    (requires (fun h -> live h s  /\ live h h' /\ live h a' /\ live h r' /\ point_inv h a' /\ point_inv h r'))
    (ensures (fun h0 z h1 -> live h0 s /\ live h0 h' /\ live h0 a' /\ live h0 r' /\
      live h1 s /\ live h1 h' /\ live h1 a' /\ modifies_none h0 h1 /\ live h1 r' /\
      z == Spec.Ed25519.(
        let sB = point_mul (as_seq h0 s) g in
        let hA = point_mul (as_seq h0 h') (as_point h0 a') in
        point_equal sB (point_add (as_point h0 r') hA))))

#reset-options "--max_fuel 0 --z3rlimit 200"
let verify_step_4 s h' a' r' =
  let h00 = ST.get() in
  push_frame();
  let h0 = ST.get() in
  let tmp = Buffer.create 0uL 60ul in
  let hA   = Buffer.sub tmp  0ul  20ul in
  let rhA  = Buffer.sub tmp 20ul  20ul in
  let sB   = Buffer.sub tmp 40ul  20ul in
  let h1 = ST.get() in
  point_mul_g sB s;
  let h2 = ST.get() in
  no_upd_lemma_1 h1 h2 sB h';
  no_upd_lemma_1 h1 h2 sB a';
  no_upd_lemma_1 h1 h2 sB r';
  Hacl.Impl.Ed25519.Ladder.point_mul hA h' a';
  let h3 = ST.get() in
  no_upd_lemma_1 h2 h3 hA r';
  no_upd_lemma_1 h2 h3 hA sB;
  Hacl.Impl.Ed25519.PointAdd.point_add rhA r' hA;
  let h4 = ST.get() in
  no_upd_lemma_1 h3 h4 rhA sB;
  let b = Hacl.Impl.Ed25519.PointEqual.point_equal sB rhA in
  let h5 = ST.get() in
  pop_frame();
  let h01 = ST.get() in
  lemma_modifies_1_trans tmp h1 h2 h3;
  lemma_modifies_1_trans tmp h1 h3 h4;
  lemma_modifies_0_1' tmp h0 h1 h4;
  lemma_modifies_0_push_pop h00 h0 h5 h01;
  b
