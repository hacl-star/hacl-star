module Hacl.Impl.Store51

open FStar.Buffer
open FStar.Endianness
open Hacl.UInt64
open Hacl.Spec.Endianness
open Hacl.Endianness

let uint8_p = buffer Hacl.UInt8.t
let felem = b:buffer t{length b = 5}

private val store_4:
  output:uint8_p{length output = 32} ->
  v1:t -> v2:t -> v3:t -> v4:t ->
  Stack unit
    (requires (fun h -> Buffer.live h output))
    (ensures (fun h0 _ h1 -> Buffer.live h1 output /\ modifies_1 output h0 h1
      (* /\ (let s = as_seq h1 output in *)
      (*    s == FStar.Seq.(hlittle_bytes 8ul (v v1) @| hlittle_bytes 8ul (v v2) *)
      (*                    @| hlittle_bytes 8ul (v v3) @| hlittle_bytes 8ul (v v4))))) *)
    ))
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
  FStar.Endianness.lemma_little_endian_inj (reveal_sbytes (as_seq h4 b0)) (little_bytes 8ul (v v0));
  FStar.Endianness.lemma_little_endian_inj (reveal_sbytes (as_seq h4 b1)) (little_bytes 8ul (v v1));
  FStar.Endianness.lemma_little_endian_inj (reveal_sbytes (as_seq h4 b2)) (little_bytes 8ul (v v2));
  FStar.Endianness.lemma_little_endian_inj (reveal_sbytes (as_seq h4 b3)) (little_bytes 8ul (v v3));
  Seq.lemma_eq_intro (as_seq h4 output) 
                     FStar.Seq.(hlittle_bytes 8ul (v v0) @| hlittle_bytes 8ul (v v1)
                         @| hlittle_bytes 8ul (v v2) @| hlittle_bytes 8ul (v v3))


val store_51:
  output:buffer Hacl.UInt8.t{Buffer.length output = 32} ->
  input:felem ->
  Stack unit
    (requires (fun h -> Buffer.live h input (* /\ (let p51 = Hacl.Spec.EC.Format.p51 in *)
      (* Hacl.Spec.EC.AddAndDouble.bounds (as_seq h input) p51 p51 p51 p51 p51) *)
      /\ Buffer.live h output))
    (ensures (fun h0 _ h1 -> Buffer.live h0 input /\ Buffer.live h1 input /\
      modifies_1 output h0 h1 (* /\ *)
     (* (let p51 = Hacl.Spec.EC.Format.p51 in *)
     (*  Hacl.Spec.EC.AddAndDouble.bounds (as_seq h0 input) p51 p51 p51 p51 p51) *)
     (* /\ Buffer.live h1 output *)
     (* /\ (as_seq h1 output) == Hacl.Spec.EC.Format.fcontract_store (as_seq h0 input))) *)
   ))
let store_51 output input =
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
