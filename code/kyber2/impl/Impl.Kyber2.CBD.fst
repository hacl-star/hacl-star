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

open Impl.Kyber2.Group

open Lib.Sequence
open Lib.ByteSequence
open Lib.IntTypes
open Lib.ModularArithmetic
open Lib.ModularArithmetic.Lemmas

open Spec.Kyber2.FunctionInstantiation

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

val cbd_eta:
  bytes:lbytes_p SEC (size (64*params_eta))
  -> output:lbuffer (Spec.Kyber2.Group.t) (size params_n)
  -> Stack unit
  (requires fun h -> live h bytes /\ live h output /\ Buf.disjoint bytes output)
  (ensures fun h0 _ h1 -> modifies1 output h0 h1 /\ h1.[|output|] == Spec.Kyber2.CBD.cbd_eta h0.[|bytes|])

let cbd_eta bytes output =
  push_frame ();
  let len = size (8*64*params_eta) in
  let tmp0 = create len (u1 0) in
  let tmp1 = create len (i16 0) in
  let tmp2 = create #(Group.t) len Group.zero_t in
  to_bits bytes tmp0;
  mapT len tmp1 to_i16 tmp0;
  mapT len tmp2 Group.int16_to_t tmp1;
  pop_frame (); admit()

val cbd_eta: (bytes:lbytes_l SEC (64*params_eta)) -> lseq (Group.t) params_n

let cbd_eta bytes =
  let bits = Seq.map int16_to_t (Seq.map to_i16 (to_bits bytes)) in
  let f (i:nat{i<params_n}) =
    let m = monoid_plus_t in
    let r = ring_t in
    let a = sum_n (Seq.sub bits (2*i*params_eta) params_eta) in
    let b = sum_n (Seq.sub bits (2*i*params_eta + params_eta) params_eta) in
    minus a b
  in
  createi params_n f

val cbd_kyber: (s:lbytes_l SEC 32) -> (b:uint_t U8 SEC) -> lseq (Group.t) params_n

let cbd_kyber s b = cbd_eta (prf (64*params_eta) s b)
