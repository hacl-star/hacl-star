module Hacl.Impl.Ed25519.Verify

open FStar.Mul
open FStar.Buffer
open FStar.UInt32

open Hacl.Impl.Ed25519.ExtPoint

open Hacl.Impl.Ed25519.Verify.Steps

#reset-options "--max_fuel 0 --z3rlimit 20"


let uint8_p = buffer UInt8.t
let felem   = b:buffer UInt64.t{length b = 5}

#reset-options "--max_fuel 0 --z3rlimit 200"

private
val lemma_point_inv:
  h:HyperStack.mem -> p:point{live h p} -> h':HyperStack.mem -> p':point{live h' p'} ->
  Lemma (requires (as_seq h p == as_seq h' p' /\ point_inv h p))
        (ensures (point_inv h' p'))
let lemma_point_inv h p h' p' = ()


val verify__:
  public:uint8_p{length public = 32} ->
  msg:uint8_p ->
  len:UInt32.t{length msg = UInt32.v len /\ length msg < pow2 32 - 64} ->
  signature:uint8_p{length signature = 64} ->
  tmp:buffer UInt64.t{length tmp = 45 /\ disjoint tmp public /\ disjoint tmp msg /\ disjoint tmp signature} ->
  tmp':buffer UInt8.t{length tmp' = 32 /\ disjoint tmp tmp' /\ disjoint tmp' signature /\ disjoint tmp' public /\ disjoint tmp' msg} ->
  Stack bool
    (requires (fun h -> live h public /\ live h msg /\ live h signature /\ live h tmp /\ live h tmp'))
    (ensures (fun h0 z h1 -> modifies_1 tmp h0 h1 /\ live h0 msg /\ live h0 public /\ live h0 signature /\
      z == Spec.Ed25519.(verify (as_seq h0 public) (as_seq h0 msg) (as_seq h0 signature))
    ))

#reset-options "--max_fuel 0 --z3rlimit 500"

let verify__ public msg len signature tmp tmp' =
  assert_norm(Spec.Ed25519.q = 0x1000000000000000000000000000000014def9dea2f79cd65812631a5cf5d3ed);
  let a' = Buffer.sub tmp 0ul  20ul in
  let r' = Buffer.sub tmp 20ul 20ul in
  let s  = Buffer.sub tmp 40ul 5ul  in
  let h'  = tmp' in
  let h0 = ST.get() in
  let b = Hacl.Impl.Ed25519.PointDecompress.point_decompress a' public in
  let h1 = ST.get() in
  no_upd_lemma_1 h0 h1 a' msg;
  no_upd_lemma_1 h0 h1 a' signature;
  no_upd_lemma_1 h0 h1 a' public;
  let res =
  if b then (
    let h1' = ST.get() in
    assert(point_inv h1' a');
    let rs = Buffer.sub signature 0ul 32ul in
    (* let b' = Hacl.Impl.Ed25519.PointDecompress.point_decompress r' rs in *)
    let b' = verify_step_1 r' signature in
    let h2 = ST.get() in
    no_upd_lemma_1 h1 h2 r' a';
    no_upd_lemma_1 h1 h2 r' msg;
    no_upd_lemma_1 h1 h2 r' signature;
    no_upd_lemma_1 h1 h2 r' public;
    if b' then (
      let h2' = ST.get() in
      Seq.lemma_eq_intro (as_seq h2' (Buffer.sub signature 32ul 32ul)) (Seq.slice (as_seq h0 signature) 32 64);
      assert(point_inv h2' r');
      lemma_point_inv h1' a' h2' a';
      assert(point_inv h2' a');
      Hacl.Impl.Load56.load_32_bytes s (Buffer.sub signature 32ul 32ul);
      let h3 = ST.get() in
      no_upd_lemma_1 h2 h3 s a';
      no_upd_lemma_1 h2 h3 s r';
      no_upd_lemma_1 h2 h3 s msg;
      no_upd_lemma_1 h2 h3 s signature;
      no_upd_lemma_1 h2 h3 s public;
      lemma_point_inv h2' a' h3 a';
      lemma_point_inv h2' r' h3 r';
      let b'' = Hacl.Impl.Ed25519.PointEqual.gte_q s in
      if b'' then (
        (* assert( *)
        (* let public = as_seq h0 public in *)
        (* let msg = as_seq h0 msg in *)
        (* let signature = as_seq h0 signature in *)
        (* false == Spec.Ed25519.(verify public msg signature)); *)
        false)
      else (      
        verify_step_2 h' msg len rs public;
        let h4 = ST.get() in
        no_upd_lemma_1 h3 h4 h' a';
        no_upd_lemma_1 h3 h4 h' r';
        no_upd_lemma_1 h3 h4 h' msg;
        no_upd_lemma_1 h3 h4 h' signature;
        no_upd_lemma_1 h3 h4 h' public;
        lemma_point_inv h3 a' h4 a';
        lemma_point_inv h3 r' h4 r';        
        let b = verify_step_4 (Buffer.sub signature 32ul 32ul) h' a' r' in
        let h5 = ST.get() in
        b
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
    ) else (    
        assert(
        let public = as_seq h0 public in
        let msg = as_seq h0 msg in
        let signature = as_seq h0 signature in
        false == Spec.Ed25519.(verify public msg signature));
        false )
  ) else (
    let h = ST.get() in
    assert(
      let public = as_seq h0 public in
      let msg = as_seq h0 msg in
      let signature = as_seq h0 signature in
      false == Spec.Ed25519.(verify public msg signature));
    false) in
  let hfin = ST.get() in
  assume (modifies_1 tmp h0 hfin);
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
