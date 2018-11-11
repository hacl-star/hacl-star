module Hacl.Impl.SHA512.ModQ

module ST = FStar.HyperStack.ST

open FStar.HyperStack.All

open FStar.Buffer
open Hacl.Impl.BignumQ.Mul
open Hacl.UInt64


#reset-options "--max_fuel 0 --z3rlimit 20"

open Hacl.Spec.Endianness

private
val lemma_modifies_0_2: #a:Type -> #a':Type -> h0:HyperStack.mem -> h1:HyperStack.mem -> h2:HyperStack.mem -> b:buffer a -> b':buffer a' -> Lemma (requires (live h0 b /\ b' `unused_in` h0 /\ live h1 b' /\ frameOf b' = (FStar.HyperStack.get_tip h0)
    /\ modifies_0 h0 h1 /\ modifies_2 b b' h1 h2))
       (ensures (modifies_2_1 b h0 h2))
let lemma_modifies_0_2 #a #a' h0 h1 h2 b b' =
  lemma_reveal_modifies_0 h0 h1;
  lemma_reveal_modifies_2 b b' h1 h2;
  lemma_intro_modifies_2_1 b h0 h2


#reset-options "--max_fuel 0 --z3rlimit 20"

inline_for_extraction
private
val sha512_modq_pre_:
  out:qelemB ->
  prefix:buffer Hacl.UInt8.t{length prefix = 32 /\ disjoint prefix out} ->
  input:buffer Hacl.UInt8.t{disjoint input out} ->
  len  :UInt32.t{UInt32.v len = length input /\ length input < pow2 32 - 32} ->
  tmp:buffer Hacl.UInt64.t{length tmp = 10 /\ disjoint out tmp} ->
  Stack unit
        (requires (fun h0 -> live h0 input /\ live h0 out /\ live h0 tmp /\ live h0 prefix))
        (ensures  (fun h0 _ h1 -> live h0 input /\ live h1 out /\ modifies_2 out tmp h0 h1 /\
          live h0 prefix /\ live h1 prefix /\
          Hacl.Spec.BignumQ.Eval.eval_q (reveal_h64s (as_seq h1 out)) == Spec.Ed25519.sha512_modq FStar.Seq.(reveal_sbytes (as_seq h0 prefix @| as_seq h0 input)) /\
          (let out = as_seq h1 out in let op_String_Access = Seq.index in
           v (out.[0]) < 0x100000000000000 /\ v (out.[1]) < 0x100000000000000 /\
           v (out.[2]) < 0x100000000000000 /\ v (out.[3]) < 0x100000000000000 /\
           v (out.[4]) < 0x100000000000000) ))
#reset-options "--max_fuel 0 --z3rlimit 200"
let sha512_modq_pre_ out prefix input len tmp =
  (**) assert_norm(pow2 32 = 0x100000000);
  (**) let h0 = ST.get() in
  push_frame();
  (**) let h1 = ST.get() in
  let hash = create (Hacl.Cast.uint8_to_sint8 0uy) 64ul in
  (**) let h2 = ST.get() in
  (**) no_upd_lemma_0 h1 h2 prefix;
  (**) no_upd_lemma_0 h1 h2 input;
  Hacl.Impl.Sha512.sha512_pre_msg hash prefix input len;
  (**) let h3 = ST.get() in
  (**) lemma_modifies_0_1' hash h1 h2 h3;
  Hacl.Impl.Load56.load_64_bytes tmp hash;
  (**) let h4 = ST.get() in
  (**) lemma_modifies_0_1 tmp h1 h3 h4;
  pop_frame();
  let h5 = ST.get() in
  (**) modifies_popped_1 tmp h0 h1 h4 h5;
  (**) assert(modifies_1 tmp h0 h5);
  (**) assert(let t = as_seq h5 tmp in Hacl.Impl.BignumQ.Mul.all_10_bellow_56 t);
  (**) assert(let t = reveal_h64s (as_seq h5 tmp) in let op_String_Access = Seq.index in
    Hacl.Spec.BignumQ.Eval.eval_q_10 t.[0] t.[1] t.[2] t.[3] t.[4] t.[5] t.[6] t.[7] t.[8] t.[9] < pow2 512);
  Hacl.Impl.BignumQ.Mul.barrett_reduction out tmp;
  (**) let h6 = ST.get() in
  (**) lemma_modifies_1_1 tmp out h0 h5 h6;
  (**) assert_norm(pow2 252 + 27742317777372353535851937790883648493 =
    0x1000000000000000000000000000000014def9dea2f79cd65812631a5cf5d3ed)



#reset-options "--max_fuel 0 --z3rlimit 200"

let sha512_modq_pre out prefix input len =
  push_frame();
  let h0 = ST.get() in
  let tmp = create (Hacl.Cast.uint64_to_sint64 0uL) 10ul in
  let h1 = ST.get() in
  sha512_modq_pre_ out prefix input len tmp;
  let h2 = ST.get() in
  lemma_modifies_0_2 h0 h1 h2 out tmp;
  pop_frame()


#reset-options "--max_fuel 0 --z3rlimit 20"

inline_for_extraction
private
val sha512_modq_pre_pre2_:
  out:qelemB ->
  prefix:buffer Hacl.UInt8.t{length prefix = 32 /\ disjoint out prefix} ->
  prefix2:buffer Hacl.UInt8.t{length prefix2 = 32 /\ disjoint out prefix2} ->
  input:buffer Hacl.UInt8.t{disjoint out input} ->
  len  :UInt32.t{UInt32.v len = length input /\ length input < pow2 32 - 64} ->
  tmp:buffer Hacl.UInt64.t{length tmp = 10 /\ disjoint out tmp} ->
  Stack unit
        (requires (fun h -> live h input /\ live h out /\ live h tmp /\ live h prefix /\ live h prefix2))
        (ensures  (fun h0 _ h1 -> live h0 input /\ live h1 out /\ modifies_2 out tmp h0 h1 /\
          live h0 prefix /\ live h1 prefix /\ live h0 prefix2 /\ live h1 prefix2 /\
          Hacl.Spec.BignumQ.Eval.eval_q (reveal_h64s (as_seq h1 out)) == Spec.Ed25519.sha512_modq FStar.Seq.(reveal_sbytes (as_seq h0 prefix @| as_seq h0 prefix2 @| as_seq h0 input)) /\
          (let out = as_seq h1 out in let op_String_Access = Seq.index in
           v (out.[0]) < 0x100000000000000 /\ v (out.[1]) < 0x100000000000000 /\
           v (out.[2]) < 0x100000000000000 /\ v (out.[3]) < 0x100000000000000 /\
           v (out.[4]) < 0x100000000000000) ))
#reset-options "--max_fuel 0 --z3rlimit 200"
let sha512_modq_pre_pre2_ out prefix prefix2 input len tmp =
  assert_norm(pow2 32 = 0x100000000);
  let h0 = ST.get() in
  push_frame();
  let h1 = ST.get() in
  let hash = create (Hacl.Cast.uint8_to_sint8 0uy) 64ul in
  let h2 = ST.get() in
  Hacl.Impl.Sha512.sha512_pre_pre2_msg hash prefix prefix2 input len;  
  let h3 = ST.get() in
  (**) lemma_modifies_0_1' hash h1 h2 h3;
  Hacl.Impl.Load56.load_64_bytes tmp hash;
  let h4 = ST.get() in
  (**) lemma_modifies_0_1 tmp h1 h3 h4;
  pop_frame();
  (**) let hfin = ST.get() in
  (**) modifies_popped_1 tmp h0 h1 h4 hfin;
  let h1 = ST.get() in
  assert(modifies_1 tmp h0 h1);
  assert(let t = as_seq h1 tmp in Hacl.Impl.BignumQ.Mul.all_10_bellow_56 t);
  assert(let t = reveal_h64s (as_seq h1 tmp) in let op_String_Access = Seq.index in
    Hacl.Spec.BignumQ.Eval.eval_q_10 t.[0] t.[1] t.[2] t.[3] t.[4] t.[5] t.[6] t.[7] t.[8] t.[9] < pow2 512);
  Hacl.Impl.BignumQ.Mul.barrett_reduction out tmp;
  assert_norm(pow2 252 + 27742317777372353535851937790883648493 =
    0x1000000000000000000000000000000014def9dea2f79cd65812631a5cf5d3ed)



#reset-options "--max_fuel 0 --z3rlimit 200"

let sha512_modq_pre_pre2 out prefix prefix2 input len =
  push_frame();
  let h0 = ST.get() in
  let tmp = create (Hacl.Cast.uint64_to_sint64 0uL) 10ul in
  let h1 = ST.get() in
  sha512_modq_pre_pre2_ out prefix prefix2 input len tmp;
  let h2 = ST.get() in
  lemma_modifies_0_2 h0 h1 h2 out tmp;
  pop_frame()
