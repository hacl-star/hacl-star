module Hacl.Impl.SHA512.ModQ

open FStar.Buffer
open Hacl.Impl.BignumQ.Mul
open Hacl.UInt64


#reset-options "--max_fuel 0 --z3rlimit 20"

[@ "substitute"]
private
val sha512_modq_:
  out:qelemB ->
  input:buffer Hacl.UInt8.t ->
  len  :UInt32.t{UInt32.v len = length input} ->
  tmp:buffer Hacl.UInt64.t{length tmp = 10 /\ disjoint out tmp} ->
  Stack unit
        (requires (fun h0 -> live h0 input /\ live h0 out /\ live h0 tmp))
        (ensures  (fun h0 _ h1 -> live h0 input /\ live h1 out /\ modifies_2 out tmp h0 h1 /\
          Hacl.Spec.BignumQ.Eval.eval_q (as_seq h1 out) == Spec.Ed25519.sha512_modq (as_seq h0 input) /\
          (let out = as_seq h1 out in let op_String_Access = Seq.index in
           v (out.[0]) < 0x100000000000000 /\ v (out.[1]) < 0x100000000000000 /\
           v (out.[2]) < 0x100000000000000 /\ v (out.[3]) < 0x100000000000000 /\
           v (out.[4]) < 0x100000000000000) ))
#reset-options "--max_fuel 0 --z3rlimit 200"
let sha512_modq_ out input len tmp =
  assert_norm(pow2 32 = 0x100000000);
  let h0 = ST.get() in
  push_frame();
  let hash = create (Hacl.Cast.uint8_to_sint8 0uy) 64ul in
  Hacl.Impl.Sha512.sha512 hash input len;
  Hacl.Impl.Load56.load_64_bytes tmp hash;
  pop_frame();
  let h1 = ST.get() in
  assert(modifies_1 tmp h0 h1);
  assert(let t = as_seq h1 tmp in Hacl.Spec.BignumQ.Mul.all_10_bellow_56 t);
  assert(let t = as_seq h1 tmp in let op_String_Access = Seq.index in
    Hacl.Spec.BignumQ.Eval.eval_q_10 t.[0] t.[1] t.[2] t.[3] t.[4] t.[5] t.[6] t.[7] t.[8] t.[9] < pow2 512);
  Hacl.Impl.BignumQ.Mul.barrett_reduction out tmp;
  assert_norm(pow2 252 + 27742317777372353535851937790883648493 =
    0x1000000000000000000000000000000014def9dea2f79cd65812631a5cf5d3ed)


private
val lemma_modifies_0_2: #a:Type -> #a':Type -> h0:HyperStack.mem -> h1:HyperStack.mem -> h2:HyperStack.mem -> b:buffer a -> b':buffer a' -> Lemma (requires (live h0 b /\ ~(contains h0 b') /\ live h1 b' /\ frameOf b' = FStar.HyperStack.(h0.tip)
    /\ modifies_0 h0 h1 /\ modifies_2 b b' h1 h2))
       (ensures (modifies_2_1 b h0 h2))
let lemma_modifies_0_2 #a #a' h0 h1 h2 b b' =
  lemma_reveal_modifies_0 h0 h1;
  lemma_reveal_modifies_2 b b' h1 h2;
  lemma_intro_modifies_2_1 b h0 h2


#reset-options "--max_fuel 0 --z3rlimit 200"

let sha512_modq out input len =
  push_frame();
  let h0 = ST.get() in
  let tmp = create (Hacl.Cast.uint64_to_sint64 0uL) 10ul in
  let h1 = ST.get() in
  sha512_modq_ out input len tmp;
  let h2 = ST.get() in
  lemma_modifies_0_2 h0 h1 h2 out tmp;
  pop_frame()
