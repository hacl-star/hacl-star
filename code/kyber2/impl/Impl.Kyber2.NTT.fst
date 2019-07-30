module Impl.Kyber2.NTT

open FStar.HyperStack
open FStar.HyperStack.ST
open FStar.Mul

open Impl.Kyber2.Group
open Impl.Kyber2.Ring
open Lib.Sequence
open Lib.Buffer

module ST = FStar.HyperStack.ST
module Buf = Lib.Buffer
module Seq = Lib.Sequence

open Spec.Kyber2.Params
open Impl.Kyber2.NumericTypes.MontgomeryInt16
open Lib.Arithmetic.Sums
module MGroup = Impl.Kyber2.GroupMontgomery
module Group = Impl.Kyber2.Group

open FStar.Math.Lemmas
open Lib.IntTypes

open Spec.Kyber2.NTT

noextract inline_for_extraction let zeta:t = i16 params_zeta

noextract inline_for_extraction let n2:(x:size_t{v x = params_n/2}) =
  size params_n >>. size 1

let modifies7 (#a0:Type0) (#a1:Type0) (#a2:Type0) (#a3:Type0) (#a4:Type0) (#a5:Type0) (#a6:Type0)
  (b0:buffer_t MUT a0) (b1:buffer_t MUT a1) (b2:buffer_t MUT a2) (b3:buffer_t MUT a3) (b4:buffer_t MUT a4) (b5:buffer_t MUT a5) (b6:buffer_t MUT a6) (h1 h2: FStar.HyperStack.mem) =
  modifies (loc b0 |+| loc b1 |+| loc b2 |+| loc b3 |+| loc b4 |+| loc b5 |+| loc b6) h1 h2


let modifies5 (#a0:Type0) (#a1:Type0) (#a2:Type0) (#a3:Type0) (#a4:Type0)
  (b0:buffer_t MUT a0) (b1:buffer_t MUT a1) (b2:buffer_t MUT a2) (b3:buffer_t MUT a3) (b4:buffer_t MUT a4) (h1 h2: FStar.HyperStack.mem) =
  modifies (loc b0 |+| loc b1 |+| loc b2 |+| loc b3 |+| loc b4) h1 h2

noextract
val cooley_tukey_for_1_inv:
  h0:mem
  -> p:poly{forall (x:size_nat{x<params_n}). v h0.[|p|].[x] <= params_q /\ v h0.[|p|].[x] >= - params_q}
  -> k:lbuffer size_t 1ul
  -> powbuf:lbuffer size_t 1ul
  -> lenbuf:lbuffer size_t 1ul
  -> startbuf:lbuffer size_t 1ul
  -> zeta:lbuffer MGroup.montgomery_t 1ul
  -> t:lbuffer MGroup.montgomery_t 1ul
  -> h:mem
  -> i:nat{i<=7}
  -> Type0

let cooley_tukey_for_1_inv h0 p k powbuf lenbuf startbuf zeta t h i =
  assert_norm(params_n = pow2 8);
  FStar.Math.Lemmas.pow2_minus 8 (8-i);
  let p0':lseq (lseq Group.t (pow2 i)) (pow2 (8-i)) = recursive_split_seq (Seq.map MGroup.int16_to_t h0.[|p|]) (8-i) (pow2 (8-i)) in
  let p':lseq (lseq Group.t (pow2 i)) (pow2 (8-i)) = recursive_split_seq (Seq.map MGroup.int16_to_t h.[|p|]) (8-i) (pow2 (8-i)) in
  modifies7 p k powbuf lenbuf startbuf zeta t h0 h /\ v h.[|powbuf|].[0] = pow2 i /\ v h.[|lenbuf|].[0] = pow2 (7-i) /\ (forall (m:size_nat{m<pow2 (8-i)}). p'.[br (8-i) m] == ntt1_reorg_rec (7-i) p0'.[br (8-i) m]) /\ uint_v h.[|k|].[0] = pow2 i /\ (forall (x:size_nat{x<params_n}). v h.[|p|].[x] <= (i+1) * params_q /\ v h.[|p|].[x] >= - (i + 1) * params_q)

noextract
val cooley_tukey_for_2_inv:
  h0:mem
  -> p:poly{forall (x:size_nat{x<params_n}). v h0.[|p|].[x] <= params_q /\ v h0.[|p|].[x] >= - params_q}
  -> k:lbuffer size_t 1ul
  -> powbuf:lbuffer size_t 1ul
  -> lenbuf:lbuffer size_t 1ul
  -> startbuf:lbuffer size_t 1ul
  -> zeta:lbuffer MGroup.montgomery_t 1ul
  -> t:lbuffer MGroup.montgomery_t 1ul
  -> i:nat{i < 7}
  -> h1:mem
  -> h:mem
  -> a:nat{a<=pow2 i}
  -> Type0

#reset-options "--z3rlimit 300 --max_fuel 0 --max_ifuel 0"

let cooley_tukey_for_2_inv h0 p k powbuf lenbuf startbuf zeta t i h1 h a =
  let start = v h.[|startbuf|].[0] in
  let len = v h.[|lenbuf|].[0] in
  assert_norm(params_n = pow2 8);
  FStar.Math.Lemmas.pow2_minus 8 (7-i);
  let p0':lseq (lseq Group.t (pow2 (i+1))) (pow2 (7-i)) = recursive_split_seq (Seq.map MGroup.int16_to_t h0.[|p|]) (7-i) (pow2 (7-i)) in
  let p':lseq (lseq Group.t (pow2 (i+1))) (pow2 (7-i)) = recursive_split_seq (Seq.map MGroup.int16_to_t h.[|p|]) (7-i) (pow2 (7-i)) in
  modifies5 p k startbuf zeta t h1 h /\ v h.[|powbuf|].[0] = pow2 i /\ v h.[|k|].[0] = pow2 i + a /\ v h.[|lenbuf|].[0] = pow2 (7-i) /\ start = 2*a*len /\ (forall (x:size_nat{x < pow2 (7-i)}) (y:size_nat{y<a}). p'.[br (7-i) x].[2*y] == (ntt1_reorg_rec (6-i) p0'.[br (7-i) x]).[2*y] /\ p'.[br (7-i) x].[2*y+1] == (ntt1_reorg_rec (6-i) p0'.[br (7-i) x]).[2*y+1]) /\ cooley_tukey_for_1_inv h0 p k powbuf lenbuf startbuf zeta t h1 i /\ (forall (x:size_nat{x >= 2 * a * pow2 (7-i) /\ x < params_n}). h.[|p|].[x] == h1.[|p|].[x]) /\ (forall (x:size_nat{x < 2 * a * pow2 (7 - i)}). v h.[|p|].[x] <= (i + 2) * params_q /\ v h.[|p|].[x] >= - (i+2) * params_q)

noextract
val cooley_tukey_for_3_inv:
  h0:mem
  -> p:poly{forall (x:size_nat{x<params_n}). v h0.[|p|].[x] <= params_q /\ v h0.[|p|].[x] >= - params_q}
  -> k:lbuffer size_t 1ul
  -> powbuf:lbuffer size_t 1ul
  -> lenbuf:lbuffer size_t 1ul
  -> startbuf:lbuffer size_t 1ul
  -> zeta:lbuffer MGroup.montgomery_t 1ul
  -> t:lbuffer MGroup.montgomery_t 1ul
  -> i:nat{i < 7}
  -> a:nat{a<pow2 i}
  -> h1:mem
  -> h2:mem
  -> h:mem
  -> j:nat{j >= 2*a*pow2 (7-i) /\ j<=(2*a+1)*pow2 (7-i)}
  -> Type0

let cooley_tukey_for_3_inv h0 p k powbuf lenbuf startbuf zeta t i a h1 h2 h j =
  assert_norm(params_n = pow2 8);
  FStar.Math.Lemmas.pow2_minus 8 (7-i);
  let start = v h.[|startbuf|].[0] in
  let len = pow2 (7-i) in
  let p0':lseq (lseq Group.t (pow2 (i+1))) (pow2 (7-i)) = recursive_split_seq (Seq.map MGroup.int16_to_t h0.[|p|]) (7-i) (pow2 (7-i)) in
  let p':lseq (lseq Group.t (pow2 (i+1))) (pow2 (7-i)) = recursive_split_seq (Seq.map MGroup.int16_to_t h.[|p|]) (7-i) (pow2 (7-i)) in
  modifies2 p t h2 h /\ MGroup.to_t (h.[|zeta|].[0]) == exp_t (Spec.Kyber2.Group.mk_t params_zeta) (br 7 (a + pow2 i)) /\ v h.[|powbuf|].[0] = pow2 i /\ v h.[|lenbuf|].[0] = len /\ v h.[|k|].[0] = pow2 i + a /\ start = 2*a*len /\ (forall (m:size_nat{m<(j%pow2 (7-i))}). p'.[br (7-i) m].[2*a] == (ntt1_reorg_rec (6-i) p0'.[br (7-i) m]).[2*a] /\ p'.[br (7-i) m].[2*a] == (ntt1_reorg_rec (6-i) p0'.[br (7-i) m]).[2*a]) /\ cooley_tukey_for_2_inv h0 p k powbuf lenbuf startbuf zeta t i h1 h2 a /\ (forall (b:size_nat{b < params_n /\ (b < start \/ (b >= j /\ b <start+len) \/ b >= len+j)}). h.[|p|].[b] == h2.[|p|].[b]) /\ (forall (x:size_nat{x < params_n /\ ((x >= start /\ x < j) \/ (x>= start+len /\ x < j + len))}). v h.[|p|].[x] <= (i+2) * params_q /\ v h.[|p|].[x] >= - (i + 2) * params_q)

inline_for_extraction
val cooley_tukey_for_3_inner:
  h0:mem
  -> p:poly{forall (x:size_nat{x<params_n}). v h0.[|p|].[x] <= params_q /\ v h0.[|p|].[x] >= - params_q}
  -> k:lbuffer size_t 1ul
  -> powbuf:lbuffer size_t 1ul
  -> lenbuf:lbuffer size_t 1ul
  -> startbuf:lbuffer size_t 1ul
  -> zeta:lbuffer MGroup.montgomery_t 1ul
  -> t:lbuffer MGroup.montgomery_t 1ul
  -> i:size_t{v i < 7}
  -> a:size_t{v a<pow2 (v i)}
  -> h1:mem
  -> h2:mem
  -> j:size_t{v j >= 2*(v a)*(pow2 (7-(v i))) /\ v j < (2*(v a)+1)*(pow2 (7-(v i)))}
  -> Stack unit
    (requires fun h -> cooley_tukey_for_3_inv h0 p k powbuf lenbuf startbuf zeta t (v i) (v a) h1 h2 h (v j))
    (ensures fun _ _ h -> cooley_tukey_for_3_inv h0 p k powbuf lenbuf startbuf zeta t (v i) (v a) h1 h2 h (v j + 1))

#reset-options "--z3rlimit 2000 --max_fuel 0 --max_ifuel 0"

let range_lemma1 (i:size_t{v i < 7}) (a:size_t{v a < pow2 (v i)}) (j:size_t{v j >= 2*(v a)*(pow2 (7-(v i))) /\ v j < (2*(v a)+1)*(pow2 (7-(v i)))}) : Lemma (v j < params_n /\ v j % pow2 (7 - (v i)) == v j % pow2 (8 - (v i)) /\ (v j) / pow2 (8 - (v i)) = ((v j) / pow2 (7 - (v i))) / 2) =
  assert_norm(2*(v a) + 1 <= 2* pow2 (v i) -1);
  lemma_mult_le_right (pow2 (7-(v i))) (2*(v a)+1) (2*pow2 (v i) - 1);
  pow2_double_mult (v i);
  distributivity_sub_left (pow2 (v i + 1)) 1 (pow2 (7 - (v i)));
  pow2_plus (v i + 1) (7 - v i);
  assert_norm(params_n = pow2 8);
  assert(v j < params_n);
  pow2_double_mult (7 - v i);
  if (v a = 0) then (modulo_lemma (v j) (pow2 (7 - v i)); modulo_lemma (v j) (pow2 (8 - v i)))
  else begin
  lemma_mod_sub (v j) (2 * v a) (pow2 (7 - v i));
  distributivity_add_left (2 * (v a)) 1 (pow2 (7 - v i));
  modulo_lemma (v j - (2 * (v a)) * pow2 (7 - v i)) (pow2 (7 - v i));
  assert(v j % (pow2 (7 - v i)) == (v j - (2 * (v a)) * pow2 (7 - v i)));
  assert(v a > 0);
  assert (pow2 (7 - v i) >= 0);
  lemma_mod_sub (v j) (v a) (pow2 (8 - v i));
  swap_mul 2 (v a);
  paren_mul_right (v a) 2 (pow2 (7-v i));
  assert ((2 * (v a)) * pow2 (7-v i) == (v a)*(2*pow2 (7-v i)));
  assert (v j - (2 * (v a)) * pow2 (7-v i) == v j - (v a) * pow2 (8-v i));
  modulo_lemma (v j - (v a) * pow2 (8 - v i)) (pow2 (8 - v i));
  assert(v j % (pow2 (7 - v i)) == (v j - (2 * (v a)) * pow2 (7 - v i)))
  end;
  assert(v j % (pow2 (7 - v i)) == v j % (pow2 (8 - v i)));
  pow2_double_mult (7 - v i);
  swap_mul (pow2 (7 - v i)) 2;
  division_multiplication_lemma (v j) (pow2 (7 - v i)) 2

let range_lemma2 (i:size_t{v i < 7}) (a:size_t{v a < pow2 (v i)}) (j:size_t{v j >= 2*(v a)*(pow2 (7-(v i))) /\ v j < (2*(v a)+1)*(pow2 (7-(v i)))}) : Lemma (v j + pow2 (7 - v i) < params_n /\ v j % pow2 (7 - (v i)) + pow2 (7 - (v i)) == (v j + pow2 (7 - v i)) % pow2 (8 - (v i)) /\ (v j + pow2 (7 - v i)) / pow2 (8 - (v i)) = ((v j) / pow2 (7 - (v i))) / 2) =
  assert_norm(2*(v a) + 1 <= 2* pow2 (v i) -1);
  lemma_mult_le_right (pow2 (7-(v i))) (2*(v a)+1) (2*pow2 (v i) - 1);
  pow2_double_mult (v i);
  distributivity_sub_left (pow2 (v i + 1)) 1 (pow2 (7 - (v i)));
  pow2_plus (v i + 1) (7 - v i);
  assert_norm(params_n = pow2 8);
  assert(v j + pow2 (7 - v i) < params_n);
  range_lemma1 i a j;
  lemma_mod_plus_distr_l (v j) (pow2 (7 - v i)) (pow2 (8 - v i));
  modulo_lemma (((v j) % pow2 (7 - v i)) + pow2 (7 - v i)) (pow2 (8 - v i));
  lemma_div_le (v j) (v j + pow2 (7 - v i)) (pow2 (8 - v i));
  pow2_double_sum (7 - v i);
  lemma_div_le (v j + pow2 (7 - v i)) (v j + pow2 (8 - v i)) (pow2 (8 - v i));
  lemma_div_plus (v j) 1 (pow2 (8 - v i));
  assert((v j) / pow2 (8 - v i) <= (v j + pow2 (7 - v i)) / pow2 (8 - v i) /\ (v j + pow2 (7 - v i)) / pow2 (8 - v i) <= (v j) / pow2 (8 - v i) + 1);
  pow2_double_mult (7 - v i);
  swap_mul (pow2 (7 - v i)) 2;
  division_multiplication_lemma (v j) (pow2 (7 - v i)) 2

#reset-options "--z3rlimit 2000 --max_fuel 1 --max_ifuel 0"

val for_3_content_lemma1:
  h0:mem
  -> p:poly{forall (x:size_nat{x<params_n}). v h0.[|p|].[x] <= params_q /\ v h0.[|p|].[x] >= - params_q}
  -> k:lbuffer size_t 1ul
  -> powbuf:lbuffer size_t 1ul
  -> lenbuf:lbuffer size_t 1ul
  -> startbuf:lbuffer size_t 1ul
  -> zeta:lbuffer MGroup.montgomery_t 1ul
  -> t:lbuffer MGroup.montgomery_t 1ul
  -> i:size_t{v i < 7}
  -> a:size_t{v a<pow2 (v i)}
  -> h1:mem
  -> h2:mem
  -> h:mem
  -> j:size_t{v j >= 2*(v a)*(pow2 (7-(v i))) /\ v j < (2*(v a)+1)*(pow2 (7-(v i)))}
  -> Lemma
    (requires  cooley_tukey_for_3_inv h0 p k powbuf lenbuf startbuf zeta t (v i) (v a) h1 h2 h (v j))
    (ensures params_n % pow2 (8 - v i) == 0 /\ (let p_ = Seq.map MGroup.int16_to_t h.[|p|] in
             let psplit0' : lseq (lseq Group.t (pow2 (v i))) (pow2 (8-v i)) = recursive_split_seq (Seq.map MGroup.int16_to_t h0.[|p|]) (8-v i) (pow2 (8-v i)) in
             v j / pow2 (8 - v i) == (v j / pow2 (7- v i))/2 /\ params_n / pow2 (8 - v i) == pow2 (v i) /\ p_.[v j] == (ntt1_reorg_rec (7 - v i) psplit0'.[br (8 - v i) ((v j) % pow2 (7 - v i))]).[v a] /\ v h.[|p|].[v j] <= (v i + 1) * params_q /\ v h.[|p|].[v j] >= - (v i + 1) * params_q))

#reset-options "--z3rlimit 3000 --max_fuel 0 --max_ifuel 0"

let for_3_content_lemma1 h0 p k powbuf lenbuf startbuf zeta t i a h1 h2 h j =
  assert_norm(params_n = pow2 8);
  assert(v j / pow2 (7 - v i) = 2*(v a));
  pow2_minus 8 (7 - v i);
  pow2_minus 8 (8 - v i);
  pow2_plus (v i + 1) (7 - v i);
  pow2_plus (v i) (8 - v i);
  multiple_modulo_lemma (pow2 (v i + 1)) (pow2 (7 - v i));
  multiple_modulo_lemma (pow2 (v i)) (pow2 (8 - v i));
  assert(params_n % pow2 (7 - v i) = 0 /\ params_n % pow2 (8 - v i) = 0);
  let psplit0' : lseq (lseq Group.t (pow2 (v i))) (pow2 (8-v i)) = recursive_split_seq (Seq.map MGroup.int16_to_t h0.[|p|]) (8-v i) (pow2 (8-v i)) in
  let psplit1' : lseq (lseq Group.t (pow2 (v i))) (pow2 (8-v i)) = recursive_split_seq (Seq.map MGroup.int16_to_t h1.[|p|]) (8-v i) (pow2 (8-v i)) in
  let p_ = Seq.map MGroup.int16_to_t h.[|p|] in
  let p1 = Seq.map MGroup.int16_to_t h1.[|p|] in
  range_lemma1 i a j;
  assert(p1.[v j] == psplit1'.[br (8-v i) ((v j) % pow2 (8 - v i))].[(v j / pow2 (8 - v i))]);
  assert(psplit1'.[br (8-v i) ((v j) % pow2 (8 - v i))] == ntt1_reorg_rec (7 - v i) psplit0'.[br (8 - v i) ((v j) % pow2 (7 - v i))]);
  assert(p1.[v j] == (ntt1_reorg_rec (7 - v i) psplit0'.[br (8 - v i) ((v j) % pow2 (7 - v i))]).[(v j / pow2 (7 - v i))/2]);
  assert(v j >= 2 * (v a) * pow2( 7 - v i));
  assert(h1.[|p|].[v j] == h2.[|p|].[v j]);
  distributivity_add_left (2*v a) 1 (pow2 (7 - v i));
  assert(v j < 2 * (v a) * pow2 (7 - v i) + pow2 (7 - v i));
  assert(v j >= v j /\ v j < 2 * (v a) * pow2 (7 - v i) + pow2 (7 - v i));
  assert(v j < params_n /\ (v j < 2 * (v a) * pow2 (7 - v i) \/ (v j >= v j /\ v j < 2 * (v a) * pow2 (7 - v i) + pow2 (7 - v i)) \/ (v j >= v j + pow2 (7 - v i))));
  assert(h2.[|p|].[v j] == h.[|p|].[v j]);
  assert(p1.[v j] == MGroup.int16_to_t h1.[|p|].[v j]);
  assert(p_.[v j] == MGroup.int16_to_t h.[|p|].[v j]);
  assert(p1.[v j] == p_.[v j])

val for_3_content_lemma2:
  h0:mem
  -> p:poly{forall (x:size_nat{x<params_n}). v h0.[|p|].[x] <= params_q /\ v h0.[|p|].[x] >= - params_q}
  -> k:lbuffer size_t 1ul
  -> powbuf:lbuffer size_t 1ul
  -> lenbuf:lbuffer size_t 1ul
  -> startbuf:lbuffer size_t 1ul
  -> zeta:lbuffer MGroup.montgomery_t 1ul
  -> t:lbuffer MGroup.montgomery_t 1ul
  -> i:size_t{v i < 7}
  -> a:size_t{v a<pow2 (v i)}
  -> h1:mem
  -> h2:mem
  -> h:mem
  -> j:size_t{v j >= 2*(v a)*(pow2 (7-(v i))) /\ v j < (2*(v a)+1)*(pow2 (7-(v i)))}
  -> Lemma
    (requires cooley_tukey_for_3_inv h0 p k powbuf lenbuf startbuf zeta t (v i) (v a) h1 h2 h (v j))
    (ensures params_n % pow2 (8 - v i) == 0 /\ (let p_ = Seq.map MGroup.int16_to_t h.[|p|] in
             let psplit0' : lseq (lseq Group.t (pow2 (v i))) (pow2 (8-v i)) = recursive_split_seq (Seq.map MGroup.int16_to_t h0.[|p|]) (8-v i) (pow2 (8-v i)) in
             (v j + pow2 (7 - v i)) / pow2 (8 - v i) == (v j / pow2 (7- v i))/2 /\ params_n / pow2 (8 - v i) == pow2 (v i) /\ p_.[v j + pow2 (7 - v i)] == (ntt1_reorg_rec (7 - v i) psplit0'.[br (8 - v i) ((v j) % pow2 (7 - v i) + pow2 (7 - v i))]).[v a] /\ v h.[|p|].[v j + pow2 (7 - v i)] <= (v i + 1) * params_q /\ v h.[|p|].[v j + pow2 (7 - v i)] >= - (v i + 1) * params_q))

#reset-options "--z3rlimit 3000 --max_fuel 0 --max_ifuel 0"

let for_3_content_lemma2 h0 p k powbuf lenbuf startbuf zeta t i a h1 h2 h j =
  assert_norm(params_n = pow2 8);
  assert(v j / pow2 (7 - v i) = 2*v a);
  pow2_minus 8 (7 - v i);
  pow2_minus 8 (8 - v i);
  pow2_plus (v i + 1) (7 - v i);
  pow2_plus (v i) (8 - v i);
  multiple_modulo_lemma (pow2 (v i + 1)) (pow2 (7 - v i));
  multiple_modulo_lemma (pow2 (v i)) (pow2 (8 - v i));
  assert(params_n % pow2 (7 - v i) = 0 /\ params_n % pow2 (8 - v i) = 0);
  let psplit0' : lseq (lseq Group.t (pow2 (v i))) (pow2 (8-v i)) = recursive_split_seq (Seq.map MGroup.int16_to_t h0.[|p|]) (8-v i) (pow2 (8-v i)) in
  let psplit1' : lseq (lseq Group.t (pow2 (v i))) (pow2 (8-v i)) = recursive_split_seq (Seq.map MGroup.int16_to_t h1.[|p|]) (8-v i) (pow2 (8-v i)) in
  let p_ = Seq.map MGroup.int16_to_t h.[|p|] in
  let p1 = Seq.map MGroup.int16_to_t h1.[|p|] in
  let len = pow2 (7 - v i) in
  range_lemma2 i a j;
  assert(p1.[v j + len] == psplit1'.[br (8-v i) ((v j + len) % pow2 (8 - v i))].[(v j + len) / pow2 (8 - v i)]);
  assert(psplit1'.[br (8-v i) ((v j + len) % pow2 (8 - v i))] == ntt1_reorg_rec (7 - v i) psplit0'.[br (8 - v i) ((v j) % pow2 (7 - v i) + len)]);
  assert(p1.[v j + len] == (ntt1_reorg_rec (7 - v i) psplit0'.[br (8 - v i) ((v j) % pow2 (7 - v i) + len)]).[(v j / pow2 (7 - v i))/2]);
  assert(v j + len < params_n /\ (v j + len < 2 * (v a) * pow2 (7 - v i) \/ (v j +len >= v j /\ v j + len < 2 * (v a) * pow2 (7 - v i) + pow2 (7 - v i)) \/ (v j + len >= v j + pow2 (7 - v i))));
  assert(h2.[|p|].[v j + len] == h.[|p|].[v j + len]);
  assert(p1.[v j + len] == MGroup.int16_to_t h1.[|p|].[v j + len]);
  assert(p_.[v j + len] == MGroup.int16_to_t h.[|p|].[v j + len]);
  assert(p1.[v j + len] == p_.[v j + len])

let cooley_tukey_for_3_inner h0 p k powbuf lenbuf startbuf zeta t i a h1 h2 j =
  assert_norm(params_n = pow2 8);
  pow2_minus 8 (7 - v i);
  pow2_minus 8 (8 - v i);
  pow2_plus (v i + 1) (7 - v i);
  pow2_plus (v i) (8 - v i);
  multiple_modulo_lemma (pow2 (v i + 1)) (pow2 (7 - v i));
  multiple_modulo_lemma (pow2 (v i)) (pow2 (8 - v i));
  assert(params_n % pow2 (7 - v i) = 0 /\ params_n % pow2 (8 - v i) = 0);
  let h_ = ST.get () in
  (let p0' : lseq (lseq Group.t (pow2 (v i+1))) (pow2 (7-v i)) = recursive_split_seq (Seq.map MGroup.int16_to_t h0.[|p|]) (7-v i) (pow2 (7-v i)) in
  let p' : lseq (lseq Group.t (pow2 (v i+1))) (pow2 (7-v i)) = recursive_split_seq (Seq.map MGroup.int16_to_t h_.[|p|]) (7-v i) (pow2 (7-v i)) in
  let psplit' : lseq (lseq Group.t (pow2 (v i))) (pow2 (8-v i)) = recursive_split_seq (Seq.map MGroup.int16_to_t h_.[|p|]) (8-v i) (pow2 (8-v i)) in
  let psplit0' : lseq (lseq Group.t (pow2 (v i))) (pow2 (8-v i)) = recursive_split_seq (Seq.map MGroup.int16_to_t h0.[|p|]) (8-v i) (pow2 (8-v i)) in
  let psplit1' : lseq (lseq Group.t (pow2 (v i))) (pow2 (8-v i)) = recursive_split_seq (Seq.map MGroup.int16_to_t h1.[|p|]) (8-v i) (pow2 (8-v i)) in
  let p_ = Seq.map MGroup.int16_to_t h_.[|p|] in
  let p1 = Seq.map MGroup.int16_to_t h1.[|p|] in
  let p2 = Seq.map MGroup.int16_to_t h2.[|p|] in
  range_lemma1 i a j;
  for_3_content_lemma1 h0 p k powbuf lenbuf startbuf zeta t i a h1 h2 h_ j;
  range_lemma2 i a j;
  for_3_content_lemma2 h0 p k powbuf lenbuf startbuf zeta t i a h1 h2 h_ j;
  pow2_double_mult (v i);
  multiple_modulo_lemma (pow2 (v i)) 2;
  let (l1,l2) = split_seq p0'.[br (7 - v i) (v j % pow2 (7 - v i))] in
  pow2_double_mult (7 - v i);
  assert(params_n % pow2 (7 - v i) = 0 /\ params_n % pow2 (8 - v i) = 0);
  swap_mul 2 (pow2 (7 - v i));
  division_multiplication_lemma params_n (pow2 (7 - v i)) 2;
  assert(params_n / (2*pow2 (7 - v i)) = (params_n / pow2 (7 - v i)) / 2);
  recursive_split_seq_step_lemma (7 - v i) (pow2 (7 - v i)) (Seq.map MGroup.int16_to_t h0.[|p|]) p0' psplit0' (v j % pow2 (7 - v i));
  assert (l1 == psplit0'.[br (8 - v i) (v j % pow2 (7 - v i))]);
  assert (l2 == psplit0'.[br (8 - v i) (v j % pow2 (7 - v i) + pow2 (7 - v i))]);
  assert(p_.[v j] == (ntt1_reorg_rec (7 - (v i)) l1).[v a]);
  assert(p_.[v j + pow2 (7 - v i)] == (ntt1_reorg_rec (7 - (v i)) l2).[v a]));
  assert(v h_.[|lenbuf|].[0] = pow2 (7 - v i));
  assert(range (v j + v h_.[|lenbuf|].[0]) U32); admit()
  (*
  t.(0ul) <- MGroup.mul_m_int16 p.(j+!lenbuf.(0)) zeta.(0);
  admit()
  assert_norm(8 * params_q < pow2 15);
  lemma_mult_le_right params_q (v i + 1) 8;
  lemma_mult_le_right params_q (-8) (- (v i + 1));
  
(*
let ntt_sequence1 (input:lbuffer t n2) (output:lbuffer t n2) (k:size_t{v k < params_n/2}) : Stack unit
  (requires fun h -> live h input /\ live h output /\ Buf.disjoint input output)
  (ensures fun h0 _ h1 -> modifies1 output h0 h1 /\ h1.[|output|] == Lib.Poly.NTT.lib_ntt_sequence #t #Spec.Kyber2.Ring.ring_t (Lib.Arithmetic.Ring.exp #t #Spec.Kyber2.Ring.ring_t zeta 2) zeta h0.[|input|] (v k)) = 
  let h = ST.get () in
  mapiT output (fun i g -> mul_t (exp_t 
(*
let ntt1 (input:lbuffer t (size params_n >>. size 2)) (output:lbuffer t (size params_n >>. size 2)) : Stack unit
  (requires fun h -> live h input /\ live h output /\ Buf.disjoint input output)
  (ensures fun h0 _ h1 -> modifies1 output h0 h1 /\ h1.[|output|] == Lib.Poly.NTT.lib_ntt #t #Spec.Kyber2.Ring.ring_t (Lib.Arithmetic.Ring.exp #t #Spec.Kyber2.Ring.ring_t (i16 params_zeta) 2) (i16 params_zeta) h0.[|input|]) =
  let h0 = ST.get () in
  Buf.mapiT (size params_n >>. size 2) output (fun j g -> 
*)
