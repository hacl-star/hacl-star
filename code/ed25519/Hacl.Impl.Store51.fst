module Hacl.Impl.Store51

module ST = FStar.HyperStack.ST

open FStar.HyperStack.All

open FStar.Buffer
open FStar.Endianness
open Hacl.UInt64
open Hacl.Spec.Endianness
open Hacl.Endianness


#reset-options "--max_fuel 0 --z3rlimit 100"

let uint8_p = buffer Hacl.UInt8.t
let felem = b:buffer t{length b = 5}

[@ Substitute]
private
val store_4:
  output:uint8_p{length output = 32} ->
  v1:t -> v2:t -> v3:t -> v4:t ->
  Stack unit
    (requires (fun h -> Buffer.live h output))
    (ensures (fun h0 _ h1 -> Buffer.live h1 output /\ modifies_1 output h0 h1
      /\ (let s = as_seq h1 output in
         s == FStar.Seq.(hlittle_bytes 8ul (v v1) @| hlittle_bytes 8ul (v v2)
                         @| hlittle_bytes 8ul (v v3) @| hlittle_bytes 8ul (v v4)))))
[@ Substitute]
let store_4 output v0 v1 v2 v3 =
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


open FStar.Mul

private
val fcontract_store_lemma: x:Hacl.UInt64.t{v x < pow2 51} -> a:UInt32.t{UInt32.v a <= 51} -> b:UInt32.t{UInt32.v b <= 51} ->
  Lemma (v (x <<^ a) % pow2 (UInt32.v a) = 0 /\ v (x >>^ b) < pow2 (51 - UInt32.v b))
let fcontract_store_lemma x a b =
  Math.Lemmas.lemma_div_lt (v x) 51 (UInt32.v b);
  Math.Lemmas.pow2_multiplication_modulo_lemma_2 (v x) 64 (UInt32.v a);
  let a' = UInt32.v a in
  cut (v (x <<^ a) = (v x * pow2 a') % pow2 64);
  cut ((v x * pow2 a') % pow2 64 = (v x % pow2 (64 - a')) * pow2 a');
  Math.Lemmas.multiple_modulo_lemma (v x % pow2 (64 - a')) (pow2 a')


private
val store64_le_spec: z:Hacl.Bignum.Limb.t -> GTot (b:Seq.seq Hacl.UInt8.t{Seq.length b = 8 /\ hlittle_endian b = v z})
let store64_le_spec z =
  let b = little_bytes 8ul (v z) in
  intro_sbytes b


private
val fcontract_store: s:Hacl.Bignum25519.seqelem{Hacl.Bignum25519.red_51 s /\ FStar.Mul.(Hacl.UInt64.(v (Seq.index s 0)
                               + pow2 51 * v (Seq.index s 1)
                               + pow2 102 * v (Seq.index s 2)
                               + pow2 153 * v (Seq.index s 3)
                               + pow2 204 * v (Seq.index s 4) < pow2 255 - 19))} ->
  GTot (s':Seq.seq Hacl.UInt8.t{Seq.length s' = 32 /\ hlittle_endian s' = Hacl.Bignum25519.seval s})
let fcontract_store s =
  assert_norm(pow2 255 > 19);
  Hacl.Bignum25519.lemma_reveal_red_51 s;
  Hacl.Bignum25519.lemma_reveal_seval s;
  Math.Lemmas.nat_times_nat_is_nat (pow2 51) (v (Seq.index s 1));
  Math.Lemmas.nat_times_nat_is_nat (pow2 102) (v (Seq.index s 2));
  Math.Lemmas.nat_times_nat_is_nat (pow2 153) (v (Seq.index s 3));
  Math.Lemmas.nat_times_nat_is_nat (pow2 204) (v (Seq.index s 4));
  let vs:nat = Hacl.UInt64.(v (Seq.index s 0)
                               + pow2 51 * v (Seq.index s 1)
                               + pow2 102 * v (Seq.index s 2)
                               + pow2 153 * v (Seq.index s 3)
                               + pow2 204 * v (Seq.index s 4)) in
  Math.Lemmas.modulo_lemma vs (pow2 255 - 19);
  assert_norm(pow2 0 = 1);
  let t0 = Seq.index s 0 in
  let t1 = Seq.index s 1 in
  let t2 = Seq.index s 2 in
  let t3 = Seq.index s 3 in
  let t4 = Seq.index s 4 in
  assert_norm(pow2 51 = 0x8000000000000);
  assert(v t0 < 0x8000000000000);
  assert(v t1 < 0x8000000000000);
  assert(v t2 < 0x8000000000000);
  assert(v t3 < 0x8000000000000);
  assert(v t4 < 0x8000000000000);
  assert (Hacl.Bignum25519.seval s = (v t0 + pow2 51 * v t1 + pow2 102 * v t2 + pow2 153 * v t3 + pow2 204 * v t4));
  let o0 = (t1 <<^ 51ul) |^ t0 in
  let o1 = (t2 <<^ 38ul) |^ (t1 >>^ 13ul) in
  let o2 = (t3 <<^ 25ul) |^ (t2 >>^ 26ul) in
  let o3 = (t4 <<^ 12ul) |^ (t3 >>^ 39ul) in
  fcontract_store_lemma t0 0ul 0ul;
  fcontract_store_lemma t1 51ul 13ul;
  fcontract_store_lemma t2 38ul 26ul;
  fcontract_store_lemma t3 25ul 39ul;
  fcontract_store_lemma t4 12ul 0ul;
  UInt.logor_disjoint (v (t1 <<^ 51ul)) (v t0) 51;
  UInt.logor_disjoint (v (t2 <<^ 38ul)) (v (t1 >>^ 13ul)) 38;
  UInt.logor_disjoint (v (t3 <<^ 25ul)) (v (t2 >>^ 26ul)) 25;
  UInt.logor_disjoint (v (t4 <<^ 12ul)) (v (t3 >>^ 39ul)) 12;
  Hacl.Spec.EC.Format.Lemmas.lemma_fcontract (v t0) (v t1) (v t2) (v t3) (v t4);
  Hacl.Spec.Bignum.Modulo.lemma_seval_5 s;
  FStar.Seq.(store64_le_spec o0 @| store64_le_spec o1 @| store64_le_spec o2 @| store64_le_spec o3)


private
val store_51_:
  output:buffer Hacl.UInt8.t{Buffer.length output = 32} ->
  input:felem ->
  Stack unit
    (requires (fun h -> Buffer.live h input /\
      Hacl.Bignum25519.red_51 (as_seq h input) /\
      (let s = as_seq h input in v (Seq.index s 0) + pow2 51 * v (Seq.index s 1)
                               + pow2 102 * v (Seq.index s 2) + pow2 153 * v (Seq.index s 3)
                               + pow2 204 * v (Seq.index s 4) < pow2 255 - 19) /\
      Buffer.live h output))
    (ensures (fun h0 _ h1 -> Buffer.live h0 input /\ Buffer.live h1 input /\
      modifies_1 output h0 h1 /\
      Hacl.Bignum25519.red_51 (as_seq h0 input) /\
      (let s = as_seq h0 input in v (Seq.index s 0) + pow2 51 * v (Seq.index s 1)
                               + pow2 102 * v (Seq.index s 2) + pow2 153 * v (Seq.index s 3)
                               + pow2 204 * v (Seq.index s 4) < pow2 255 - 19) /\
      Buffer.live h1 output /\
      (as_seq h1 output) == fcontract_store (as_seq h0 input)))
let store_51_ output input =
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

[@ Substitute]
let store_51 output input =
  store_51_ output input
