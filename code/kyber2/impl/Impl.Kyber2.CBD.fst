module Impl.Kyber2.CBD

open FStar.Mul

open Spec.Kyber2.Params
open Lib.Poly
open Lib.NumericTypes

open Lib.Arithmetic.Group
open Lib.Arithmetic.Ring
open Lib.Arithmetic.Sums

open Spec.Kyber2.Group
open Spec.Kyber2.Ring
open Spec.Kyber2.CBD

//open Impl.Kyber2.Group

open Lib.Sequence
open Lib.ByteSequence
open Lib.IntTypes
open Lib.ModularArithmetic
open Lib.ModularArithmetic.Lemmas

open Impl.Kyber2.FunctionInstantiation

module Seq = Lib.Sequence

open Lib.Buffer

open FStar.HyperStack
open FStar.HyperStack.ST

module ST = FStar.HyperStack.ST

//module B = LowStar.Buffer
module Buf = Lib.Buffer
//module Loops = Lib.Loops

type lbits_p (l:secrecy_level) (len:size_t) = lbuffer (uint_t U1 l) len
type lbytes_p (l:secrecy_level) (len:size_t) = lbuffer (uint_t U8 l) len

val to_bits_inner:
  #l:secrecy_level
  -> #len:size_t{v len<max_size_t/8}
  -> input:lbytes_p l len
  -> output:lbits_p l (size 8)
  -> i:size_t{v i < v len}
  -> Stack unit
  (requires fun h0 -> live h0 input /\ live h0 output /\ Buf.disjoint input output)
  (ensures fun h0 _ h1 ->
    modifies1 output h0 h1 /\
    ( h1.[|input|], h1.[|output|] ) == Spec.Kyber2.CBD.to_bits_inner #l #(v len) (v i) h0.[|input|])

#reset-options "--z3rlimit 200 --max_fuel 2 --max_ifuel 2 --using_facts_from '* -FStar.Seq'"

let to_bits_inner #l #len input output i =
  let x = input.(i) in
  let h0 = ST.get () in
  assert (x == (as_seq h0 input).[(v i)]);
  let customprop (j:size_t{v j < 8}) : Type0 = (cast U1 l (x >>.j) == Spec.Kyber2.CBD.to_bits_inner_ #l x (v j)) in
  let customlemma (j:size_t{v j < 8}) : Lemma (customprop j) = () in
  FStar.Classical.forall_intro customlemma;
  let g (x:int_t U8 l) (j:size_t{v j < 8}) : Tot (r:int_t U1 l{r == Spec.Kyber2.CBD.to_bits_inner_ #l x (v j)}) =
    cast U1 l (x >>. j) in
  fillT (size 8) output (Spec.Kyber2.CBD.to_bits_inner_ #l x) (g x)

val to_bits:
  #l:secrecy_level
  -> #len:size_t{v len<max_size_t/8}
  -> bytes:lbytes_p l len
  -> output:lbits_p l ((size 8) *! len)
  ->  Stack unit
    (requires fun h0 -> live h0 bytes /\ live h0 output /\ Buf.disjoint bytes output)
    (ensures fun h0 _ h1 -> modifies1 output h0 h1 /\ h1.[|output|] == Spec.Kyber2.CBD.to_bits h0.[|bytes|])

#reset-options "--z3rlimit 100 --max_fuel 2 --max_ifuel 2 --using_facts_from '* -FStar.Seq'"

let to_bits #l #len bytes output =
  let h0 = ST.get () in
  fill_blocks_cst #_ h0 (size 8) len output
  Spec.Kyber2.CBD.a_spec
  (fun h _ -> as_seq h bytes)
  (fun _ -> Spec.Kyber2.CBD.to_bits_inner #l #(v len))
  (fun i -> to_bits_inner #l #len bytes (Buf.sub output (i *! (size 8)) (size 8)) i);
  let h1 = ST.get () in
  as_seq_gsub h1 output (size 0) (size 8 *! len);
  eq_intro h1.[|output|] (Seq.sub h1.[|output|] 0 (8 * v len))

val to_bytes_inner:
  #l:secrecy_level
  -> acc:lbytes_p l (size 1)
  -> input:lbits_p l (size 8)
  -> Stack unit
  (requires fun h0 -> live h0 input /\ live h0 acc /\ Buf.disjoint input acc)
  (ensures fun h0 _ h1 ->
    modifies1 acc h0 h1 /\ h1.[|acc|].[0] == Spec.Kyber2.CBD.to_bytes_inner #l h0.[|input|])

let to_bytes_inner #l acc input =
  acc.(size 0) <- uint #U8 #l 0;
  let h0 = ST.get () in
  eq_intro h0.[|acc|] (Seq.create 1 (uint #U8 #l 0));
  Buf.loop1 #(uint_t U8 l) #(size 1) h0 (size 8) acc (fun h -> Spec.Kyber2.CBD.to_bytes_inner_ h.[|input|])
    (fun j ->
      let h1 = ST.get () in
      let x = input.(j) in
      acc.(size 0) <- acc.(size 0) +. ((cast U8 l x) <<. j);
      let h2 = ST.get () in
      eq_intro h2.[|acc|] (Spec.Kyber2.CBD.to_bytes_inner_ h0.[|input|] (v j) h1.[|acc|]);
      Lib.LoopCombinators.unfold_repeati 8 (Spec.Kyber2.CBD.to_bytes_inner_ h0.[|input|]) (h0.[|acc|]) (v j))

val to_bytes:
  #l:secrecy_level
  -> #len:size_t{v len % 8 = 0}
  -> bits:lbits_p l len
  -> output:lbytes_p l (len >>. size 3)
  ->  Stack unit
    (requires fun h0 -> live h0 bits /\ live h0 output /\ Buf.disjoint bits output)
    (ensures fun h0 _ h1 -> modifies1 output h0 h1 /\ h1.[|output|] == Spec.Kyber2.CBD.to_bytes (as_seq h0 bits))


let to_bytes #l #len bits output =
  let h0 = ST.get () in
  Buf.fill_direct h0 (len >>. size 3) output (fun h -> Spec.Kyber2.CBD.to_bytes_fun h.[|bits|])
    (fun i ->
      as_seq_gsub h0 bits (size 8 *! i) (size 8);
      to_bytes_inner #l (Buf.sub output i (size 1)) (Buf.sub bits (size 8 *! i) (size 8));
      let h = ST.get () in
      as_seq_gsub h output i (size 1))

#reset-options "--z3rlimit 500 --max_fuel 2 --max_ifuel 2 --using_facts_from '* -FStar.Seq'"

let cbd_eta_inner_ (bits_a: lbuffer uint1 (size params_eta)) (bits_b:lbuffer uint1 (size params_eta)) (output:lbuffer int16 (size 1)) : Stack unit (requires fun h -> live h bits_a /\ live h bits_b /\ live h output /\ Buf.disjoint bits_a output /\ Buf.disjoint bits_b output) (ensures fun h0 _ h1 -> Group.int16_to_t (Seq.index h1.[|output|] 0) == cbd_eta_inner_ (Seq.map Group.int16_to_t (Seq.map to_i16 h0.[|bits_a|])) (Seq.map Group.int16_to_t (Seq.map to_i16 h0.[|bits_b|])) /\ (v h1.[|output|].[0] <= params_eta) /\ (v h1.[|output|].[0] >= - params_eta) /\ modifies1 output h0 h1) =
  push_frame ();
  let ab = create (size 2) (i16 0) in
  let ha = ST.get () in
  as_seq_gsub ha ab (size 0) (size 1);
  Impl.Kyber2.Arithmetic.Sums.sum_n_cbd bits_a (Buf.sub ab (size 0) (size 1));
  let hb = ST.get () in
  as_seq_gsub hb ab (size 1) (size 1);
  Impl.Kyber2.Arithmetic.Sums.sum_n_cbd bits_b (Buf.sub ab (size 1) (size 1));
  let h = ST.get () in
  assert(h.[|ab|].[0] == (Seq.sub h.[|ab|] 0 1).[0]);
  assert(v h.[|ab|].[0] <= params_eta);
  assert(h.[|ab|].[1] == (Seq.sub h.[|ab|] 1 1).[0]);
  assert(v h.[|ab|].[1] <= params_eta);

  assert_norm(params_eta < maxint S16);
  assert_norm(- params_eta > minint S16);

  assert(v h.[|ab|].[1] >= 0);
  assert(v h.[|ab|].[0] >= 0);
  assert (v h.[|ab|].[0] - v h.[|ab|].[1] <= params_eta);
  assert (v h.[|ab|].[0] - v h.[|ab|].[1] >= - params_eta);
  assert (range (v h.[|ab|].[0] - v h.[|ab|].[1]) S16);
  let a:int16 = ab.(size 0) in
  let b:(b:int16{range (v a - v b) S16}) = ab.(size 1) in
  output.(size 0) <- a -! b;
  opp_lemma_t (Group.int16_to_t b);
  plus_lemma_t (Group.int16_to_t a) (opp_t (Group.int16_to_t b));
  FStar.Math.Lemmas.lemma_mod_add_distr (v (Group.int16_to_t a)) (- v (Group.int16_to_t b)) params_q;
  assert (v (minus #Group.t #ring_t (Group.int16_to_t a) (Group.int16_to_t b)) == (v (Group.int16_to_t a) - v (Group.int16_to_t b)) % params_q);
  assert (int16_to_t (a -! b) == (minus #Group.t #ring_t (Group.int16_to_t a) (Group.int16_to_t b)));
  pop_frame ()

let cbd_eta_inner (bits:lbuffer uint1 ((size 2)*!(size params_n)*!(size params_eta))) (output:lbuffer int16 (size 1)) (i:size_t{v i < params_n}) : Stack unit (requires fun h -> live h bits /\ live h output /\ Buf.disjoint bits output) (ensures fun h0 _ h1 -> Group.int16_to_t (Seq.index h1.[|output|] 0) == cbd_eta_inner (Seq.map Group.int16_to_t (Seq.map to_i16 h0.[|bits|])) (v i) /\ (v h1.[|output|].[0] <= params_eta) /\ (v h1.[|output|].[0] >= - params_eta) /\ modifies1 output h0 h1) =
  let h = ST.get () in
  assert_norm (v ((size 2) *! i *! (size params_eta)) == 2*(v i)*params_eta);
  assert_norm (v (((size 2) *! i *! (size params_eta)) +! (size params_eta)) == 2*(v i)*params_eta+params_eta);
  as_seq_gsub h bits ((size 2) *! i *! (size params_eta)) (size params_eta);
  as_seq_gsub h bits (((size 2) *! i *! (size params_eta)) +! (size params_eta)) (size params_eta);
  cbd_eta_inner_ (sub bits ((size 2) *! i *! (size params_eta)) (size params_eta)) (sub bits (((size 2) *! i *! (size params_eta)) +! (size params_eta)) (size params_eta)) output;
  let h1 = ST.get () in
  assert(Group.int16_to_t (h1.[|output|].[0]) == Spec.Kyber2.CBD.cbd_eta_inner_ (Seq.map Group.int16_to_t (Seq.map to_i16 h.[|(gsub bits ((size 2) *!i*!(size params_eta)) (size params_eta))|])) (Seq.map Group.int16_to_t (Seq.map to_i16 h.[|gsub bits (((size 2)*!i*!(size params_eta)) +! (size params_eta)) (size params_eta)|])));
  assert(Group.int16_to_t (h1.[|output|].[0]) == Spec.Kyber2.CBD.cbd_eta_inner_ (Seq.map Group.int16_to_t (Seq.map to_i16 (Seq.sub h.[|bits|] (2*(v i)*params_eta) params_eta))) (Seq.map Group.int16_to_t (Seq.map to_i16 (Seq.sub h.[|bits|] (2*(v i)*params_eta + params_eta) params_eta))));
  eq_intro (Seq.map Group.int16_to_t (Seq.map to_i16 (Seq.sub h.[|bits|] (2*(v i)*params_eta) (params_eta)))) (Seq.sub (Seq.map Group.int16_to_t (Seq.map to_i16 h.[|bits|])) (2*(v i)*params_eta) (params_eta));
  eq_intro (Seq.map Group.int16_to_t (Seq.map to_i16 (Seq.sub h.[|bits|] (2*(v i)*params_eta+params_eta) (params_eta)))) (Seq.sub (Seq.map Group.int16_to_t (Seq.map to_i16 h.[|bits|])) (2*(v i)*params_eta+params_eta) (params_eta))

#reset-options "--z3rlimit 1000 --max_fuel 1 --max_ifuel 1 --using_facts_from '* -FStar.Seq'"

val cbd_eta:
  bytes:lbytes_p SEC (size (64*params_eta))
  -> output:lbuffer int16 (size params_n)
  -> Stack unit
  (requires fun h -> live h bytes /\ live h output /\ Buf.disjoint bytes output)
  (ensures fun h0 _ h1 -> modifies1 output h0 h1 /\ Seq.map Group.int16_to_t h1.[|output|] == Spec.Kyber2.CBD.cbd_eta h0.[|bytes|] /\ (forall (j:size_nat{j<params_n}). v h1.[|output|].[j] <= params_eta /\ v h1.[|output|].[j] >= - params_eta))

let cbd_eta bytes output =
  let h_begin = ST.get () in
  push_frame ();
  let len = (size 8)*!(size 64) *! (size params_eta) in
  let tmp0 = create len (u1 0) in
  to_bits bytes tmp0;
  let h_ = ST.get () in
  Lib.Loops.for (size 0) (size params_n) (fun h i -> live h tmp0 /\ live h output /\ Buf.disjoint tmp0 output /\ (forall (j:size_nat{j< i}). Group.int16_to_t h.[|output|].[j] == (Spec.Kyber2.CBD.cbd_eta h_begin.[|bytes|]).[j] /\ v h.[|output|].[j] <= params_eta /\ v h.[|output|].[j] >= - params_eta) /\ modifies1 output h_ h) (fun i ->
    let h0 = ST.get () in
    cbd_eta_inner tmp0 (sub output i (size 1)) i;
    let h1 = ST.get () in
    as_seq_gsub h1 output i (size 1);
    eq_intro (Seq.map Spec.Kyber2.Group.int16_to_t (Seq.map to_i16 (Spec.Kyber2.CBD.to_bits h_begin.[|bytes|]))) (Seq.map Group.int16_to_t (Seq.map to_i16 (Spec.Kyber2.CBD.to_bits h_begin.[|bytes|])));
    assert(Group.int16_to_t (h1.[|output|].[v i]) == Spec.Kyber2.CBD.cbd_eta_inner (Seq.map Spec.Kyber2.Group.int16_to_t (Seq.map to_i16 (Spec.Kyber2.CBD.to_bits h_begin.[|bytes|]))) (v i));
    Spec.Kyber2.CBD.cbd_eta_lemma h_begin.[|bytes|] (v i);
    assert(Group.int16_to_t (h1.[|output|].[v i]) == (Spec.Kyber2.CBD.cbd_eta h_begin.[|bytes|]).[v i]);
    as_seq_gsub h1 output (size 0) i;
    assert(Buf.disjoint (gsub output (size 0) i) (gsub output i (size 1)));
    let customprop (j:size_nat{j < v i}) : GTot Type = (Group.int16_to_t (h1.[|output|].[j]) == (Spec.Kyber2.CBD.cbd_eta h_begin.[|bytes|]).[j] /\ v h1.[|output|].[j] <= params_eta /\ v h1.[|output|].[j] >= - params_eta) in
    let customlemma (j:size_nat{j < v i}) : Lemma (customprop j) =
      assert(h1.[|output|].[j] == h1.[|(gsub output (size 0) i)|].[j]);
      assert(h1.[|gsub output (size 0) i|].[j] == h0.[|gsub output (size 0) i|].[j]);
      as_seq_gsub h0 output (size 0) i;
      assert(h0.[|output|].[j] == h0.[|(gsub output (size 0) i)|].[j]);
      assert(h1.[|output|].[j] == h0.[|output|].[j])
    in FStar.Classical.forall_intro customlemma;
    assert(forall (j:size_nat{j < v i + 1}). Group.int16_to_t (h1.[|output|].[j]) == (Spec.Kyber2.CBD.cbd_eta h_begin.[|bytes|]).[j]));
  let h_end = ST.get() in
  eq_intro (Seq.map Group.int16_to_t h_end.[|output|]) (Spec.Kyber2.CBD.cbd_eta h_begin.[|bytes|]);
  pop_frame()


val cbd_kyber: (s:lbytes_p SEC (size 32)) -> (b:uint_t U8 SEC) -> (output:lbuffer int16 (size params_n)) -> Stack unit (requires fun h -> live h s /\ live h output /\ Buf.disjoint s output) (ensures fun h0 _ h1 -> modifies1 output h0 h1 /\ Seq.map Group.int16_to_t h1.[|output|] == Spec.Kyber2.CBD.cbd_kyber h0.[|s|] b /\ (forall (j:size_nat{j < params_n}). v h1.[|output|].[j] <= params_eta /\ v h1.[|output|].[j] >= - params_eta))

let cbd_kyber s b output =
  push_frame ();
  let tmp = create ((size 64)*!(size params_eta)) (u8 0) in
  prf ((size 64)*!(size params_eta)) s b tmp;
  cbd_eta tmp output;
  pop_frame ()
