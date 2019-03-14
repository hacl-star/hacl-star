module Hacl.EC.Format

module ST = FStar.HyperStack.ST

open FStar.HyperStack.All


open FStar.Mul
open FStar.HyperStack
open FStar.Ghost
open FStar.Buffer

open Hacl.Cast
open Hacl.Bignum.Constants
open Hacl.Bignum.Parameters
open Hacl.Bignum.Limb
open Hacl.EC.Point


#reset-options "--initial_fuel 0 --max_fuel 0 --z3rlimit 5"

type uint8_p = buffer Hacl.UInt8.t

private inline_for_extraction let zero_8 = uint8_to_sint8 0uy


#reset-options "--initial_fuel 0 --max_fuel 0 --z3rlimit 100"

val point_inf: unit -> StackInline point
  (requires (fun h -> true))
  (ensures (fun h0 p h1 -> modifies_0 h0 h1 /\ live h1 p /\ disjoint (getx p) (getz p)
    /\ Hacl.Spec.EC.AddAndDouble.red_513 (as_seq h1 (getx p))
    /\ Hacl.Spec.EC.AddAndDouble.red_513 (as_seq h1 (getz p))
    /\ frameOf (getx p) = frameOf (getz p)
    /\ (let px = as_seq h1 (getx p) in let pz = as_seq h1 (getz p) in
       (px, pz) == Hacl.Spec.EC.Format.point_inf ())
    ))
let point_inf () =
  let buf = create limb_zero 10ul in
  let x = Buffer.sub buf 0ul 5ul in
  let y = x in
  let z = Buffer.sub buf 5ul 5ul in
  let h' = ST.get() in
  cut (v (get h' z 0) = 0);
  cut (v (get h' z 1) = 0);
  cut (v (get h' z 2) = 0);
  cut (v (get h' z 3) = 0);
  cut (v (get h' z 4) = 0);
  Seq.lemma_eq_intro (as_seq h' z) (Seq.create len limb_zero);
  cut (Hacl.Spec.EC.AddAndDouble.red_513 (as_seq h' z));
  cut (disjoint x z);
  x.(0ul) <- limb_one;
  let h = ST.get() in
  no_upd_lemma_1 h' h x z;
  cut (v (get h x 0) = 1);
  cut (v (get h x 1) = 0);
  cut (v (get h x 2) = 0);
  cut (v (get h x 3) = 0);
  cut (v (get h x 4) = 0);
  let p = make x y z in
  p


open Hacl.Endianness

#reset-options "--initial_fuel 0 --max_fuel 0 --z3rlimit 100"

[@"substitute"]
private val upd_5: output:felem ->
  o0:limb{v o0 < pow2 51} ->
  o1:limb{v o1 < pow2 51} ->
  o2:limb{v o2 < pow2 51} ->
  o3:limb{v o3 < pow2 51} ->
  o4:limb{v o4 < pow2 51} ->
  Stack unit
    (requires (fun h -> Buffer.live h output))
    (ensures (fun h0 _ h1 -> Buffer.live h1 output /\ modifies_1 output h0 h1
      /\ Hacl.Spec.EC.AddAndDouble.red_513 (as_seq h1 output)
      /\ as_seq h1 output == Hacl.Spec.EC.Format.seq_upd_5 o0 o1 o2 o3 o4
    ))
[@"substitute"]
private let upd_5 output output0 output1 output2 output3 output4 =
  output.(0ul) <- output0;
  output.(1ul) <- output1;
  output.(2ul) <- output2;
  output.(3ul) <- output3;
  output.(4ul) <- output4;
  let h1 = ST.get() in
  cut (get h1 output 0 == output0
      /\ get h1 output 1 == output1
      /\ get h1 output 2 == output2
      /\ get h1 output 3 == output3
      /\ get h1 output 4 == output4 );
  Seq.lemma_eq_intro (as_seq h1 output) (Hacl.Spec.EC.Format.seq_upd_5 output0 output1 output2 output3 output4)


[@"substitute"]
private val upd_5': output:felem ->
  o0:limb -> o1:limb -> o2:limb -> o3:limb -> o4:limb ->
  Stack unit
    (requires (fun h -> Buffer.live h output))
    (ensures (fun h0 _ h1 -> Buffer.live h1 output /\ modifies_1 output h0 h1
      /\ as_seq h1 output == Hacl.Spec.EC.Format.seq_upd_5 o0 o1 o2 o3 o4
    ))
[@"substitute"]
private let upd_5' output output0 output1 output2 output3 output4 =
  output.(0ul) <- output0;
  output.(1ul) <- output1;
  output.(2ul) <- output2;
  output.(3ul) <- output3;
  output.(4ul) <- output4;
  let h1 = ST.get() in
  cut (get h1 output 0 == output0
      /\ get h1 output 1 == output1
      /\ get h1 output 2 == output2
      /\ get h1 output 3 == output3
      /\ get h1 output 4 == output4 );
  Seq.lemma_eq_intro (as_seq h1 output) (Hacl.Spec.EC.Format.seq_upd_5 output0 output1 output2 output3 output4)


#reset-options "--initial_fuel 0 --max_fuel 0 --z3rlimit 400"

val fexpand: output:felem -> input:uint8_p{length input = 32} -> Stack unit
  (requires (fun h -> Buffer.live h output /\ Buffer.live h input))
  (ensures (fun h0 _ h1 -> Buffer.live h0 output /\ Buffer.live h0 input
    /\ Buffer.live h1 output /\ modifies_1 output h0 h1
    /\ Hacl.Spec.EC.AddAndDouble.red_513 (as_seq h1 output)
    /\ Hacl.Spec.EC.AddAndDouble.(bounds (as_seq h1 output) p51 p51 p51 p51 p51)
    /\ as_seq h1 output == Hacl.Spec.EC.Format.fexpand_spec (as_seq h0 input)))
let fexpand output input =
  let h = ST.get() in
  Seq.lemma_eq_intro (Seq.slice (as_seq h input) 0 8) (as_seq h (Buffer.sub input 0ul 8ul));
  Seq.lemma_eq_intro (Seq.slice (as_seq h input) 6 14) (as_seq h (Buffer.sub input 6ul 8ul));
  Seq.lemma_eq_intro (Seq.slice (as_seq h input) 12 20) (as_seq h (Buffer.sub input 12ul 8ul));
  Seq.lemma_eq_intro (Seq.slice (as_seq h input) 19 27) (as_seq h (Buffer.sub input 19ul 8ul));
  Seq.lemma_eq_intro (Seq.slice (as_seq h input) 24 32) (as_seq h (Buffer.sub input 24ul 8ul));
  let i0 = hload64_le (Buffer.sub input 0ul 8ul) in
  let i1 = hload64_le (Buffer.sub input 6ul 8ul) in
  let i2 = hload64_le (Buffer.sub input 12ul 8ul) in
  let i3 = hload64_le (Buffer.sub input 19ul 8ul) in
  let i4 = hload64_le (Buffer.sub input 24ul 8ul) in
  let output0 = (i0         ) &^ mask_51 in
  let output1 = (i1 >>^ 3ul ) &^ mask_51 in
  let output2 = (i2 >>^ 6ul ) &^ mask_51 in
  let output3 = (i3 >>^ 1ul ) &^ mask_51 in
  let output4 = (i4 >>^ 12ul) &^ mask_51 in
  UInt.logand_mask (v i0) (51);
  UInt.logand_mask (v (i1 >>^ 3ul)) (51);
  UInt.logand_mask (v (i2 >>^ 6ul )) (51);
  UInt.logand_mask (v (i3 >>^ 1ul )) (51);
  UInt.logand_mask (v (i4 >>^ 12ul)) (51);
  upd_5 output output0 output1 output2 output3 output4


open Hacl.Spec.Endianness
open FStar.Old.Endianness

[@"substitute"]
private val store_4:
  output:uint8_p{length output = 32} ->
  v1:limb -> v2:limb -> v3:limb -> v4:limb ->
  Stack unit
    (requires (fun h -> Buffer.live h output))
    (ensures (fun h0 _ h1 -> Buffer.live h1 output /\ modifies_1 output h0 h1
      /\ (let s = as_seq h1 output in
         s == FStar.Seq.(hlittle_bytes 8ul (v v1) @| hlittle_bytes 8ul (v v2)
                         @| hlittle_bytes 8ul (v v3) @| hlittle_bytes 8ul (v v4)))))
[@"substitute"]
private let store_4 output v0 v1 v2 v3 =
  let b0 = Buffer.sub output 0ul  8ul in
  let b1 = Buffer.sub output 8ul  8ul in
  let b2 = Buffer.sub output 16ul 8ul in
  let b3 = Buffer.sub output 24ul 8ul in
  let h0 = ST.get() in
  Seq.lemma_eq_intro (Seq.slice (as_seq h0 output) 0 8)   (as_seq h0 b0);
  Seq.lemma_eq_intro (Seq.slice (as_seq h0 output) 8 16)  (as_seq h0 b1);
  Seq.lemma_eq_intro (Seq.slice (as_seq h0 output) 16 24) (as_seq h0 b2);
  Seq.lemma_eq_intro (Seq.slice (as_seq h0 output) 24 32) (as_seq h0 b3);
  hstore64_le b0 v0;
  let h1 = ST.get() in
  no_upd_lemma_1 h0 h1 b0 b1;
  no_upd_lemma_1 h0 h1 b0 b2;
  no_upd_lemma_1 h0 h1 b0 b3;
  hstore64_le b1 v1;
  let h2 = ST.get() in
  no_upd_lemma_1 h1 h2 b1 b0;
  no_upd_lemma_1 h1 h2 b1 b2;
  no_upd_lemma_1 h1 h2 b1 b3;
  hstore64_le b2 v2;
  let h3 = ST.get() in
  no_upd_lemma_1 h2 h3 b2 b0;
  no_upd_lemma_1 h2 h3 b2 b1;
  no_upd_lemma_1 h2 h3 b2 b3;
  hstore64_le b3 v3;
  let h4 = ST.get() in
  no_upd_lemma_1 h3 h4 b3 b0;
  no_upd_lemma_1 h3 h4 b3 b1;
  no_upd_lemma_1 h3 h4 b3 b2;
  FStar.Old.Endianness.lemma_little_endian_inj (reveal_sbytes (as_seq h4 b0)) (little_bytes 8ul (v v0));
  FStar.Old.Endianness.lemma_little_endian_inj (reveal_sbytes (as_seq h4 b1)) (little_bytes 8ul (v v1));
  FStar.Old.Endianness.lemma_little_endian_inj (reveal_sbytes (as_seq h4 b2)) (little_bytes 8ul (v v2));
  FStar.Old.Endianness.lemma_little_endian_inj (reveal_sbytes (as_seq h4 b3)) (little_bytes 8ul (v v3));
  Seq.lemma_eq_intro (as_seq h4 output) 
                     FStar.Seq.(hlittle_bytes 8ul (v v0) @| hlittle_bytes 8ul (v v1)
                         @| hlittle_bytes 8ul (v v2) @| hlittle_bytes 8ul (v v3))


private val fcontract_first_carry_pass:
  input:felem ->
  Stack unit
    (requires (fun h -> Buffer.live h input /\ Hacl.Spec.EC.AddAndDouble.red_513 (as_seq h input)))
    (ensures (fun h0 _ h1 -> Buffer.live h0 input /\ Hacl.Spec.EC.AddAndDouble.red_513 (as_seq h0 input)
      /\ Buffer.live h1 input /\ modifies_1 input h0 h1
      /\ as_seq h1 input == Hacl.Spec.EC.Format.fcontract_first_carry_pass (as_seq h0 input) ))
private let fcontract_first_carry_pass input =
  assert_norm(pow2 51 + pow2 13 = 0x8000000002000);
  assert_norm(pow2 51 = 0x8000000000000);
  assert_norm(pow2 0 = 1);
  let t0 = input.(0ul) in
  let t1 = input.(1ul) in
  let t2 = input.(2ul) in
  let t3 = input.(3ul) in
  let t4 = input.(4ul) in
  let t1' = t1 +^ (t0 >>^ 51ul) in
  let t0' = t0 &^ Hacl.Spec.EC.Format.mask_51 in
  (* UInt.logand_mask (v t0) 51; *)
  (* lemma_carry_local (v t0) (v t1) 0; *)
  let t2' = t2 +^ (t1' >>^ 51ul) in
  let t1'' = t1' &^ Hacl.Spec.EC.Format.mask_51 in
  (* UInt.logand_mask (v t1') 51; *)
  (* lemma_carry_local (v t1') (v t2) 51; *)
  let t3' = t3 +^ (t2' >>^ 51ul) in
  let t2'' = t2' &^ Hacl.Spec.EC.Format.mask_51 in
  (* UInt.logand_mask (v t2') 51; *)
  (* lemma_carry_local (v t2') (v t3) 102; *)
  let t4' = t4 +^ (t3' >>^ 51ul) in
  let t3'' = t3' &^ Hacl.Spec.EC.Format.mask_51 in
  (* UInt.logand_mask (v t3') 51; *)
  (* lemma_carry_local (v t3') (v t4) 153; *)
  upd_5' input t0' t1'' t2'' t3'' t4'


private 
val fcontract_first_carry_full:
  input:felem ->
  Stack unit
    (requires (fun h -> Buffer.live h input /\ Hacl.Spec.EC.AddAndDouble.red_513 (as_seq h input)))
    (ensures (fun h0 _ h1 -> Buffer.live h0 input /\ Hacl.Spec.EC.AddAndDouble.red_513 (as_seq h0 input)
      /\ Buffer.live h1 input /\ modifies_1 input h0 h1
      /\ as_seq h1 input == Hacl.Spec.EC.Format.fcontract_first_carry_full (as_seq h0 input) ))
private let fcontract_first_carry_full input =
  fcontract_first_carry_pass input;
  assert_norm(19 * (pow2 64 / pow2 51) + pow2 51 < pow2 52);
  Hacl.Bignum.Modulo.carry_top input


private 
val fcontract_second_carry_pass:
  input:felem ->
  Stack unit
    (requires (fun h -> Buffer.live h input  /\ (let p51 = Hacl.Spec.EC.Format.p51 in
      Hacl.Spec.EC.AddAndDouble.bounds (as_seq h input) (pow2 52) p51 p51 p51 p51)))
    (ensures (fun h0 _ h1 -> Buffer.live h0 input /\ (let p51 = Hacl.Spec.EC.Format.p51 in
      Hacl.Spec.EC.AddAndDouble.bounds (as_seq h0 input) (pow2 52) p51 p51 p51 p51)
      /\ Buffer.live h1 input /\ modifies_1 input h0 h1
      /\ as_seq h1 input == Hacl.Spec.EC.Format.fcontract_second_carry_pass (as_seq h0 input) ))
private let fcontract_second_carry_pass input =
  assert_norm(pow2 52 = 0x10000000000000);
  assert_norm(pow2 51 = 0x8000000000000);
  assert_norm(pow2 0 = 1);
  let t0 = input.(0ul) in
  let t1 = input.(1ul) in
  let t2 = input.(2ul) in
  let t3 = input.(3ul) in
  let t4 = input.(4ul) in
  let t1' = t1 +^ (t0 >>^ 51ul) in
  let t0' = t0 &^ Hacl.Spec.EC.Format.mask_51 in
  let t2' = t2 +^ (t1' >>^ 51ul) in
  let t1'' = t1' &^ Hacl.Spec.EC.Format.mask_51 in
  let t3' = t3 +^ (t2' >>^ 51ul) in
  let t2'' = t2' &^ Hacl.Spec.EC.Format.mask_51 in
  let t4' = t4 +^ (t3' >>^ 51ul) in
  let t3'' = t3' &^ Hacl.Spec.EC.Format.mask_51 in
  upd_5' input t0' t1'' t2'' t3'' t4'


private 
val fcontract_second_carry_full:
  input:felem ->
  Stack unit
    (requires (fun h -> Buffer.live h input  /\ (let p51 = Hacl.Spec.EC.Format.p51 in
      Hacl.Spec.EC.AddAndDouble.bounds (as_seq h input) (pow2 52) p51 p51 p51 p51)))
    (ensures (fun h0 _ h1 -> Buffer.live h0 input /\ (let p51 = Hacl.Spec.EC.Format.p51 in
      Hacl.Spec.EC.AddAndDouble.bounds (as_seq h0 input) (pow2 52) p51 p51 p51 p51)
      /\ Buffer.live h1 input /\ modifies_1 input h0 h1
      /\ as_seq h1 input == Hacl.Spec.EC.Format.fcontract_second_carry_full (as_seq h0 input) ))
private let fcontract_second_carry_full input =
  fcontract_second_carry_pass input;
  let h = ST.get() in
  Hacl.Spec.Bignum.Modulo.lemma_carry_top_spec_ (as_seq h input);
  Hacl.Bignum.Modulo.carry_top input;
  Hacl.Bignum.Fproduct.carry_0_to_1 input


private 
val fcontract_trim:
  input:felem ->
  Stack unit
    (requires (fun h -> Buffer.live h input  /\ (let p51 = Hacl.Spec.EC.Format.p51 in
      Hacl.Spec.EC.AddAndDouble.bounds (as_seq h input) p51 p51 p51 p51 p51)))
    (ensures (fun h0 _ h1 -> Buffer.live h0 input /\ Buffer.live h1 input /\
      modifies_1 input h0 h1 /\
     (let p51 = Hacl.Spec.EC.Format.p51 in
      Hacl.Spec.EC.AddAndDouble.bounds (as_seq h0 input) p51 p51 p51 p51 p51)
     /\ (as_seq h1 input) == Hacl.Spec.EC.Format.fcontract_trim (as_seq h0 input)))
private let fcontract_trim input =
  let a0 = input.(0ul) in
  let a1 = input.(1ul) in
  let a2 = input.(2ul) in
  let a3 = input.(3ul) in
  let a4 = input.(4ul) in
  let open Hacl.Bignum.Limb in
  let mask0 = gte_mask a0 Hacl.Spec.EC.Format.p51m19 in
  let mask1 = eq_mask a1 Hacl.Spec.EC.Format.p51m1 in
  let mask2 = eq_mask a2 Hacl.Spec.EC.Format.p51m1 in
  let mask3 = eq_mask a3 Hacl.Spec.EC.Format.p51m1 in
  let mask4 = eq_mask a4 Hacl.Spec.EC.Format.p51m1 in
  let mask  = mask0 &^ mask1 &^ mask2 &^ mask3 &^ mask4 in
  UInt.logand_lemma_1 (v mask0); UInt.logand_lemma_1 (v mask1); UInt.logand_lemma_1 (v mask2);
  UInt.logand_lemma_1 (v mask3); UInt.logand_lemma_1 (v mask4);
  UInt.logand_lemma_2 (v mask0); UInt.logand_lemma_2 (v mask1); UInt.logand_lemma_2 (v mask2);
  UInt.logand_lemma_2 (v mask3); UInt.logand_lemma_2 (v mask4);
  UInt.logand_lemma_1 (v Hacl.Spec.EC.Format.p51m19); UInt.logand_lemma_1 (v Hacl.Spec.EC.Format.p51m1);
  UInt.logand_lemma_2 (v Hacl.Spec.EC.Format.p51m19); UInt.logand_lemma_2 (v Hacl.Spec.EC.Format.p51m1);
  let a0' = a0 -^ (Hacl.Spec.EC.Format.p51m19 &^ mask) in
  let a1' = a1 -^ (Hacl.Spec.EC.Format.p51m1 &^ mask) in
  let a2' = a2 -^ (Hacl.Spec.EC.Format.p51m1 &^ mask) in
  let a3' = a3 -^ (Hacl.Spec.EC.Format.p51m1 &^ mask) in
  let a4' = a4 -^ (Hacl.Spec.EC.Format.p51m1 &^ mask) in
  upd_5' input a0' a1' a2' a3' a4'


val reduce:
  input:felem ->
  Stack unit
    (requires (fun h -> Buffer.live h input /\ Hacl.Spec.EC.AddAndDouble.red_513 (as_seq h input)))
    (ensures (fun h0 _ h1 -> Buffer.live h0 input /\ Buffer.live h1 input /\ modifies_1 input h0 h1 /\
      Hacl.Spec.EC.AddAndDouble.red_513 (as_seq h0 input) /\
      (let p51 = Hacl.Spec.EC.Format.p51 in
      Hacl.Spec.EC.AddAndDouble.bounds (as_seq h1 input) p51 p51 p51 p51 p51) /\
      Hacl.Spec.Bignum.Bigint.seval (as_seq h1 input)
      == Hacl.Spec.Bignum.Bigint.seval (as_seq h0 input) % (pow2 255 - 19)))
let reduce out =
  fcontract_first_carry_full out;
  fcontract_second_carry_full out;
  fcontract_trim out


val fcontract_store:
  output:buffer Hacl.UInt8.t{Buffer.length output = 32} ->
  input:felem ->
  Stack unit
    (requires (fun h -> Buffer.live h input  /\ (let p51 = Hacl.Spec.EC.Format.p51 in
      Hacl.Spec.EC.AddAndDouble.bounds (as_seq h input) p51 p51 p51 p51 p51)
      /\ Buffer.live h output))
    (ensures (fun h0 _ h1 -> Buffer.live h0 input /\ Buffer.live h1 input /\
      modifies_1 output h0 h1 /\
     (let p51 = Hacl.Spec.EC.Format.p51 in
      Hacl.Spec.EC.AddAndDouble.bounds (as_seq h0 input) p51 p51 p51 p51 p51)
     /\ Buffer.live h1 output
     /\ (as_seq h1 output) == Hacl.Spec.EC.Format.fcontract_store (as_seq h0 input)))
let fcontract_store output input =
  let t0 = input.(0ul) in
  let t1 = input.(1ul) in
  let t2 = input.(2ul) in
  let t3 = input.(3ul) in
  let t4 = input.(4ul) in
  let o0 = (t1 <<^ 51ul) |^ t0 in
  let o1 = (t2 <<^ 38ul) |^ (t1 >>^ 13ul) in
  let o2 = (t3 <<^ 25ul) |^ (t2 >>^ 26ul) in
  let o3 = (t4 <<^ 12ul) |^ (t3 >>^ 39ul) in
  store_4 output o0 o1 o2 o3
  (* fcontract_store_lemma t0 0ul 0ul; *)
  (* fcontract_store_lemma t1 51ul 13ul; *)
  (* fcontract_store_lemma t2 38ul 26ul; *)
  (* fcontract_store_lemma t3 25ul 39ul; *)
  (* fcontract_store_lemma t4 12ul 0ul; *)
  (* UInt.logor_disjoint (v (t1 <<^ 51ul)) (v t0) 51; *)
  (* UInt.logor_disjoint (v (t2 <<^ 38ul)) (v (t1 >>^ 13ul)) 38; *)
  (* UInt.logor_disjoint (v (t3 <<^ 25ul)) (v (t2 >>^ 26ul)) 25; *)
  (* UInt.logor_disjoint (v (t4 <<^ 12ul)) (v (t3 >>^ 39ul)) 12; *)
  

private val fcontract: output:uint8_p{length output = 32} -> input:felem{disjoint output input} -> Stack unit
  (requires (fun h -> Buffer.live h output /\ Buffer.live h input
    /\ Hacl.Spec.EC.AddAndDouble.red_513 (as_seq h input)))
  (ensures (fun h0 _ h1 -> Buffer.live h0 output /\ Buffer.live h0 input
    /\ Buffer.live h1 output /\ modifies_2 output input h0 h1
    /\ Hacl.Spec.EC.AddAndDouble.red_513 (as_seq h0 input)
    /\ as_seq h1 output == Hacl.Spec.EC.Format.fcontract_spec (as_seq h0 input)
  ))
private let fcontract output input =
  fcontract_first_carry_full input;
  fcontract_second_carry_full input;
  fcontract_trim input;
  fcontract_store output input


#reset-options "--initial_fuel 0 --max_fuel 0 --z3rlimit 100"

val point_of_scalar: scalar:buffer Hacl.UInt8.t{length scalar = keylen} -> StackInline point
  (requires (fun h -> Buffer.live h scalar))
  (ensures (fun h0 p h1 -> modifies_0 h0 h1 /\ live h1 p /\ Buffer.live h0 scalar
    /\ Hacl.Spec.EC.AddAndDouble.red_513 (as_seq h1 (getx p))
    /\ Hacl.Spec.EC.AddAndDouble.red_513 (as_seq h1 (getz p))
    /\ (let px = as_seq h1 (getx p) in
       let pz = as_seq h1 (getz p) in
       let scalar = as_seq h0 scalar in
       (px, pz) == Hacl.Spec.EC.Format.point_of_scalar scalar)
  ))
#reset-options "--initial_fuel 0 --max_fuel 0 --z3rlimit 200"
let point_of_scalar scalar =
  let buf = create limb_zero 10ul in  
  let x = Buffer.sub buf 0ul 5ul in
  let z = Buffer.sub buf 5ul 5ul in
  let h = ST.get() in
  cut (get h z 0 == limb_zero);
  cut (get h z 1 == limb_zero);
  cut (get h z 2 == limb_zero);
  cut (get h z 3 == limb_zero);
  cut (get h z 4 == limb_zero);
  fexpand x scalar;
  let h' = ST.get() in
  no_upd_lemma_1 h h' x z;
  cut (get h z 0 == limb_zero);
  cut (get h z 1 == limb_zero);
  cut (get h z 2 == limb_zero);
  cut (get h z 3 == limb_zero);
  cut (get h z 4 == limb_zero);
  z.(0ul) <- limb_one;
  let h = ST.get() in
  cut (get h z 0 == limb_one);
  cut (get h z 1 == limb_zero);
  cut (get h z 2 == limb_zero);
  cut (get h z 3 == limb_zero);
  cut (get h z 4 == limb_zero);
  buf


val scalar_of_point: scalar:uint8_p{length scalar = keylen} -> p:point -> Stack unit
  (requires (fun h -> Buffer.live h scalar /\ live h p
    /\ Hacl.Spec.EC.AddAndDouble.red_513 (as_seq h (getx p))
    /\ Hacl.Spec.EC.AddAndDouble.red_513 (as_seq h (getz p))
  ))
  (ensures (fun h0 _ h1 -> Buffer.live h0 scalar /\ live h0 p
    /\ Hacl.Spec.EC.AddAndDouble.red_513 (as_seq h0 (getx p))
    /\ Hacl.Spec.EC.AddAndDouble.red_513 (as_seq h0 (getz p))
    /\ modifies_1 scalar h0 h1 /\ Buffer.live h1 scalar
    /\ (let px = as_seq h0 (getx p) in
       let pz = as_seq h0 (getz p) in
       as_seq h1 scalar == Hacl.Spec.EC.Format.scalar_of_point (px,pz))
  ))
let scalar_of_point scalar point =
  push_frame();
  let x = Hacl.EC.Point.getx point in
  let z = Hacl.EC.Point.getz point in
  let buf   = Buffer.create limb_zero 10ul in
  let zmone = Buffer.sub buf 0ul 5ul in
  let sc    = Buffer.sub buf 5ul 5ul in
  Hacl.Bignum.crecip zmone z;
  let h = ST.get() in
  Hacl.Spec.EC.AddAndDouble2.lemma_513_is_53 (as_seq h x);
  Hacl.Spec.EC.AddAndDouble2.lemma_513_is_55 (as_seq h zmone);
  Hacl.Spec.EC.AddAndDouble.fmul_53_55_is_fine (as_seq h x) (as_seq h zmone);
  Hacl.Bignum.fmul sc x zmone;
  fcontract scalar sc;
  pop_frame()


val format_secret:
  secret:uint8_p{length secret = keylen} ->
  StackInline (s:uint8_p{length s = keylen})
    (requires (fun h -> Buffer.live h secret))
    (ensures (fun h0 s h1 -> Buffer.live h0 secret
      /\ Buffer.live h1 secret /\ modifies_0 h0 h1 /\ Buffer.live h1 s
      /\ as_seq h1 s == Hacl.Spec.EC.Format.format_secret (as_seq h0 secret)
      ))
#reset-options "--initial_fuel 0 --max_fuel 0 --z3rlimit 100"
let format_secret secret =
  let hinit = ST.get() in
  assert_norm(pow2 8 = 256);
  let e   = create zero_8 32ul in
  let h = ST.get() in
  no_upd_lemma_0 hinit h secret;
  blit secret 0ul e 0ul 32ul;
  let h' = ST.get() in
  Hacl.Spec.Bignum.Fmul.lemma_whole_slice (as_seq h secret);
  Hacl.Spec.Bignum.Fmul.lemma_whole_slice (as_seq h' e);
  cut (as_seq h' e == as_seq hinit secret);
  let e0  = e.(0ul) in
  let e31 = e.(31ul) in
  cut (e0 == Seq.index (as_seq hinit secret) 0);
  cut (e31 == Seq.index (as_seq hinit secret) 31);
  let open Hacl.UInt8 in
  let e0  = e0 &^ (uint8_to_sint8 248uy) in
  let e31 = e31 &^ (uint8_to_sint8 127uy) in
  let e31 = e31 |^ (uint8_to_sint8 64uy) in
  e.(0ul) <- e0;
  e.(31ul) <- e31;
  e
