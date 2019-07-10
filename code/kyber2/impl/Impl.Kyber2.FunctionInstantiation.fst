module Impl.Kyber2.FunctionInstantiation

open FStar.Mul

open Spec.Kyber2.Params
open Lib.Poly
open Lib.NumericTypes

//open Lib.Arithmetic.Group
//open Lib.Arithmetic.Ring
//open Lib.Arithmetic.Sums

open Lib.Sequence
open Lib.ByteSequence
open Lib.IntTypes

open Hacl.SHA3

module Seq = Lib.Sequence
open Lib.Buffer
open Lib.ByteBuffer
open FStar.HyperStack
open FStar.HyperStack.ST

module ST = FStar.HyperStack.ST

//module B = LowStar.Buffer
module Buf = Lib.Buffer

//module Loops = Lib.Loops


#reset-options "--z3rlimit 50 --max_fuel 0 --max_ifuel 0"

type lbytes_p (l:secrecy_level) (len:size_t) = lbuffer (uint_t U8 l) len

val xof:
  (input_len:size_t{2+v input_len <= max_size_t})
  -> output_len:size_t
  -> input:lbytes_p SEC input_len
  -> b1:uint8 -> b2:uint8
  -> output:lbytes_p SEC output_len
  -> Stack unit
    (requires fun h -> live h input /\ live h output /\ Buf.disjoint input output)
    (ensures fun h0 _ h1 -> modifies1 output h0 h1 /\ h1.[|output|] == Spec.Kyber2.FunctionInstantiation.xof (v input_len) (v output_len) h0.[|input|] b1 b2)

let xof input_len output_len input b1 b2 output =
  push_frame ();
  let tmp_input = create #(uint8) (input_len +.size 2) (u8 0) in
  copy (Buf.sub tmp_input 0ul input_len) input;
  tmp_input.(input_len) <- b1;
  incr_lemma input_len;
  tmp_input.(incr input_len) <- b2;
  let h = ST.get () in
  as_seq_gsub h tmp_input 0ul input_len;
  eq_intro (Seq.sub h.[|tmp_input|] (v input_len) 1) (Seq.create 1 b1);
  eq_intro (Seq.sub h.[|tmp_input|] (v input_len + 1) 1) (Seq.create 1 b2);
  lemma_concat3 (v input_len) h.[|input|] 1 (Seq.create 1 b1) 1 (Seq.create 1 b2) h.[|tmp_input|];
  shake128_hacl (input_len +. 2ul) tmp_input output_len output;
  pop_frame ()

val prf:
  output_len:size_t
  -> s:lbytes_p SEC 32ul
  -> b:uint_t U8 SEC
  -> o:lbytes_p SEC output_len
  -> Stack unit
    (requires fun h -> live h s /\ live h o /\ Buf.disjoint s o)
    (ensures fun h0 _ h1 -> modifies1 o h0 h1 /\ h1.[|o|] == Spec.Kyber2.FunctionInstantiation.prf (v output_len) h0.[|s|] b)

let prf output_len s b o =
  push_frame ();
  let tmp = create #(uint8) (33ul) (u8 0) in
  copy (Buf.sub tmp 0ul 32ul) s;
  tmp.(32ul) <- b;
  let h = ST.get () in
  as_seq_gsub h tmp 0ul 32ul;
  eq_intro (Seq.sub h.[|tmp|] 32 1) (Seq.create 1 b);
  lemma_concat2 32 h.[|s|] 1 (Seq.create 1 b) h.[|tmp|];
  shake256_hacl 33ul tmp output_len o;
  pop_frame ()

val hash_h:
  input_len:size_t
  -> input:lbytes_p SEC input_len
  -> hash:lbytes_p SEC 32ul
  -> Stack unit
    (requires fun h -> live h input /\ live h hash /\ Buf.disjoint input hash)
    (ensures fun h0 _ h1 -> modifies1 hash h0 h1 /\ h1.[|hash|] == Spec.Kyber2.FunctionInstantiation.hash_h (v input_len) h0.[|input|])

let hash_h = sha3_256

val hash_g:
  input_len:size_t
  -> input:lbytes_p SEC input_len
  -> hash1:lbytes_p SEC 32ul
  -> hash2:lbytes_p SEC 32ul
  -> Stack unit
    (requires fun h -> live h input /\ live h hash1 /\ live h hash2 /\ Buf.disjoint input hash1 /\ Buf.disjoint input hash2 /\ Buf.disjoint hash1 hash2)
    (ensures fun h0 _ h1 -> modifies2 hash1 hash2 h0 h1 /\ (h1.[|hash1|], h1.[|hash2|]) == Spec.Kyber2.FunctionInstantiation.hash_g (v input_len) h0.[|input|])

let hash_g input_len input hash1 hash2 =
  push_frame ();
  let tmp = create #(uint8) 64ul (u8 0) in
  sha3_512 input_len input tmp;
  copy hash1 (Buf.sub tmp 0ul 32ul);
  copy hash2 (Buf.sub tmp 32ul 32ul);
  let h = ST.get () in
  as_seq_gsub h tmp 0ul 32ul;
  as_seq_gsub h tmp 32ul 32ul;
  pop_frame ()

val kdf:
  input_len:size_t
  -> output_len:size_t
  -> input:lbytes_p SEC input_len
  -> output:lbytes_p SEC output_len
  -> Stack unit
  (requires fun h -> live h input /\ live h output /\ Buf.disjoint input output)
  (ensures fun h0 _ h1 -> modifies1 output h0 h1 /\ h1.[|output|] == Spec.Kyber2.FunctionInstantiation.kdf (v input_len) (v output_len) h0.[|input|])

let kdf input_len output_len input =
  shake256_hacl input_len input output_len

let parse_inv (h0 h:mem) (s:lbytes_p SEC (size (4*168))) (out:lbuffer Group.t (size params_n)) (i:lbuffer (i:size_t{v i <= params_n}) 1ul) (j:lbuffer (j:size_t{v j <= 336}) 1ul) : GTot Type0 =
  match Spec.Kyber2.FunctionInstantiation.parse_inner h0.[|s|] h0.[|out|] 0 0 with
  |None -> (match Spec.Kyber2.FunctionInstantiation.parse_inner h.[|s|] h.[|out|] (v h.[|i|].[0]) (v h.[|j|].[0]) with
              |None -> (v h.[|i|].[0] < params_n)
              |Some _ -> False)
  |Some seq -> match Spec.Kyber2.FunctionInstantiation.parse_inner h.[|s|] h.[|out|] (v h.[|i|].[0]) (v h.[|j|].[0]) with
              |None -> False
              |Some seq' -> seq == seq'

val parse_inner:
  (h_:mem)
  -> s:lbytes_p SEC (size (4*168))
  -> out:lbuffer Group.t (size params_n)
  -> (i:lbuffer (i:size_t{v i <= params_n}) 1ul)
  -> (j:lbuffer (j:size_t{v j <= 336}) 1ul)
  -> Stack unit
    (requires fun h -> live h s /\ live h out /\ live h i /\ live h j /\
      Buf.disjoint s out /\ Buf.disjoint s i /\ Buf.disjoint s j /\
      Buf.disjoint out i /\ Buf.disjoint out j /\
      Buf.disjoint i j /\
      modifies3 out i j h_ h /\
      h.[|i|].[0] <. size params_n /\ h.[|j|].[0] <. size 336 /\
      parse_inv h_ h s out i j)
    (ensures fun h0 _ h1 -> ((h0.[|i|].[0] == h1.[|i|].[0]) <==> modifies1 j h0 h1) /\
                         modifies3 out i j h0 h1 /\ v h1.[|j|].[0] = v h0.[|j|].[0] + 1 /\
                         h1.[|i|].[0] <=. size params_n /\ h1.[|j|].[0] <=. size 336 /\
                         parse_inv h_ h1 s out i j)

#reset-options "--z3rlimit 500 --max_fuel 1 --max_ifuel 1"

let parse_inner h_ s out i j =
  let h0 = ST.get () in
  let a = s.(2ul *. j.(0ul)) in
  let b = s.((2ul *. j.(0ul)) +. 1ul) in
  let h_0 = ST.get () in assert(h0 == h_0);
  let d = ((to_u16 a) +! ((to_u16 b) <<. size 8)) in
  j.(0ul) <- j.(0ul) +. 1ul;
  let h_ = ST.get () in
  let mask = Lib.IntTypes.lt_mask d (u16 (19) *! u16 params_q) in
  lt_mask_lemma d (u16 19 *! u16 params_q);
  if (Lib.RawIntTypes.u16_to_UInt16 mask <>. mk_int #U16 #PUB 0) then
    (assert_norm(v d < 19 * params_q);
     assert_norm(v d == v a + (v b * pow2 8));
     assert(Spec.Kyber2.Group.v (Group.uint16_to_t d) = uint_v d % params_q);
    out.(i.(0ul)) <- Group.uint16_to_t d;
    i.(0ul) <- i.(0ul) +. 1ul;
    let h1 = ST.get () in
    assert(let s = h0.[|s|] in let i = v h0.[|i|].[0] in let j = v h0.[|j|].[0] in
             let d = v s.[2*j] + ((v s.[2*j+1]) * pow2 8) in
             d < 19 * params_q /\ h1.[|out|] == Seq.upd h0.[|out|] i (i16 (d % params_q)));
    assert(modifies2 out i h_ h1);
    assert(Spec.Kyber2.FunctionInstantiation.parse_inner h0.[|s|] h0.[|out|] (v h0.[|i|].[0]) (v h0.[|j|].[0]) == Spec.Kyber2.FunctionInstantiation.parse_inner h1.[|s|] h1.[|out|] (v h1.[|i|].[0]) (v h1.[|j|].[0])))
  else
    (let h1 = ST.get () in
     assert(modifies1 j h0 h1);
     assert(let s = h0.[|s|] in let out = h0.[|out|] in let i = v h0.[|i|].[0] in let j = v h0.[|j|].[0] in
             let d2 = to_u16 s.[2*j] +. ((to_u16 s.[2*j+1]) <<. size 8) in
             v d2 >= 19 * params_q /\ i < params_n /\ j < 336);
     assert(Spec.Kyber2.FunctionInstantiation.parse_inner h0.[|s|] h0.[|out|] (v h0.[|i|].[0]) (v h0.[|j|].[0]) == Spec.Kyber2.FunctionInstantiation.parse_inner h1.[|s|] h1.[|out|] (v h1.[|i|].[0]) (v h1.[|j|].[0])));
  let h1 = ST.get () in
  assert(modifies2 out i h_ h1);
  assert(modifies1 j h0 h_);
  assert(modifies3 out i j h0 h1)

val parse_xof:
  input_len:size_t{2+v input_len <= max_size_t}
  -> input:lbytes_p SEC input_len
  -> b1:uint_t U8 SEC
  -> b2:uint_t U8 SEC
  -> output:lbuffer Group.t (size params_n)
  -> Stack bool
    (requires fun h -> live h input /\ live h output /\ Buf.disjoint input output)
    (ensures fun h0 res h1 -> modifies1 output h0 h1 /\ (match (Spec.Kyber2.FunctionInstantiation.parse_xof (v input_len) h0.[|input|] b1 b2) with |None -> (res == false) |Some l -> (h1.[|output|] == l /\ res == true)))

#reset-options "--z3rlimit 500 --max_fuel 1 --max_ifuel 1"

let parse_xof input_len input b1 b2 output =
  let h_begin = ST.get() in
  push_frame ();
  let tmp = create (size (4*168)) (u8 0) in
  xof input_len (size (4*168)) input b1 b2 tmp;
  let i = create 1ul (size 0) in
  let j = create 1ul (size 0) in
  let h0 = ST.get () in
  Lib.Loops.while
    (fun h -> live h i /\ live h j /\ (v h.[|j|].[0] <= 336) /\ (v h.[|i|].[0] <= params_n) /\ modifies3 output i j h0 h /\ parse_inv h0 h tmp output i j)
    (fun h -> (v h.[|j|].[0] < 336) && (v h.[|i|].[0] < params_n))
    (fun () -> let a = (j.(0ul) <. size 336) in
      let c = (i.(0ul) <. size params_n) in
      a && c)
    (fun () -> parse_inner h0 tmp output i j);
  let h2 = ST.get () in
  Spec.Kyber2.FunctionInstantiation.parse_inner_cst_lemma h0.[|tmp|] h0.[|output|];
  let b = ( i.(0ul) =. size params_n) in
  pop_frame ();
  let h_end = ST.get () in
  assert(modifies1 output h_begin h_end);
  b

let parse_inv_no_modulo (h0 h:mem) (s:lbytes_p SEC (size (4*168))) (out:lbuffer uint16 (size params_n)) (i:lbuffer (i:size_t{v i <= params_n}) 1ul) (j:lbuffer (j:size_t{v j <= 336}) 1ul) : GTot Type0 =
  match Spec.Kyber2.FunctionInstantiation.parse_inner h0.[|s|] (Seq.map Group.uint16_to_t h0.[|out|]) 0 0 with
  |None -> (match Spec.Kyber2.FunctionInstantiation.parse_inner h.[|s|] (Seq.map Group.uint16_to_t h.[|out|]) (v h.[|i|].[0]) (v h.[|j|].[0]) with
              |None -> (v h.[|i|].[0] < params_n)
              |Some _ -> False)
  |Some seq -> match Spec.Kyber2.FunctionInstantiation.parse_inner h.[|s|] (Seq.map Group.uint16_to_t h.[|out|]) (v h.[|i|].[0]) (v h.[|j|].[0]) with
              |None -> False
              |Some seq' -> seq == seq'

val parse_inner_no_modulo:
  (h_:mem)
  -> s:lbytes_p SEC (size (4*168))
  -> out:lbuffer uint16 (size params_n)
  -> (i:lbuffer (i:size_t{v i <= params_n}) 1ul)
  -> (j:lbuffer (j:size_t{v j <= 336}) 1ul)
  -> Stack unit
    (requires fun h -> live h s /\ live h out /\ live h i /\ live h j /\
      Buf.disjoint s out /\ Buf.disjoint s i /\ Buf.disjoint s j /\
      Buf.disjoint out i /\ Buf.disjoint out j /\
      Buf.disjoint i j /\
      modifies3 out i j h_ h /\
      h.[|i|].[0] <. size params_n /\ h.[|j|].[0] <. size 336 /\
      parse_inv_no_modulo h_ h s out i j)
    (ensures fun h0 _ h1 -> ((h0.[|i|].[0] == h1.[|i|].[0]) <==> modifies1 j h0 h1) /\
                         modifies3 out i j h0 h1 /\ v h1.[|j|].[0] = v h0.[|j|].[0] + 1 /\
                         h1.[|i|].[0] <=. size params_n /\ h1.[|j|].[0] <=. size 336 /\
                         parse_inv_no_modulo h_ h1 s out i j)


#reset-options "--z3rlimit 1000 --max_fuel 1 --max_ifuel 1"

let parse_inner_no_modulo h_ s out i j =
  let h0 = ST.get () in
  let a = s.(2ul *. j.(0ul)) in
  let b = s.((2ul *. j.(0ul)) +. 1ul) in
  let h_0 = ST.get () in assert(h0 == h_0);
  let d = ((to_u16 a) +! ((to_u16 b) <<. size 8)) in
  j.(0ul) <- j.(0ul) +. 1ul;
  let h_ = ST.get () in
  let mask = Lib.IntTypes.lt_mask d (u16 (19) *! u16 params_q) in
  lt_mask_lemma d (u16 19 *! u16 params_q);
  if (Lib.RawIntTypes.u16_to_UInt16 mask <>. mk_int #U16 #PUB 0) then
    (assert_norm(v d < 19 * params_q);
     assert_norm(v d == v a + (v b * pow2 8));
    out.(i.(0ul)) <- d;
    i.(0ul) <- i.(0ul) +. 1ul;
    let h1 = ST.get () in
    assert(let s = h0.[|s|] in let i = v h0.[|i|].[0] in let j = v h0.[|j|].[0] in
             let d = v s.[2*j] + ((v s.[2*j+1]) * pow2 8) in
             d < 19 * params_q /\ h1.[|out|] == Seq.upd h0.[|out|] i (u16 d));
    eq_intro (h1.[|out|]) (Seq.upd h0.[|out|] (v h0.[|i|].[0]) d);
    let customprop (k:size_nat{k < params_n}) : GTot Type = (let a:Group.t = (Seq.map Group.uint16_to_t h1.[|out|]).[k] in let b:Group.t = (Seq.upd (Seq.map Group.uint16_to_t h0.[|out|]) (v h0.[|i|].[0]) (Group.uint16_to_t d)).[k] in a == b) in
    let customlemma (k:size_nat{k < params_n}) : Lemma (customprop k) =
      assert ((Seq.map Group.uint16_to_t h1.[|out|]).[k] == Group.uint16_to_t (h1.[|out|].[k]));
      if (k = v h0.[|i|].[0]) then (assert(h1.[|out|].[k] == d); assert((Seq.upd (Seq.map Group.uint16_to_t h0.[|out|]) (v h0.[|i|].[0]) (Group.uint16_to_t d)).[k] == Group.uint16_to_t d); assert ((Seq.map Group.uint16_to_t h1.[|out|]).[k] == Group.uint16_to_t d))
      else (assert((Seq.upd (Seq.map Group.uint16_to_t h0.[|out|]) (v h0.[|i|].[0]) (Group.uint16_to_t d)).[k] == (Seq.map Group.uint16_to_t h0.[|out|]).[k]))
    in FStar.Classical.forall_intro customlemma;
    eq_intro (Seq.map Group.uint16_to_t h1.[|out|]) (Seq.upd (Seq.map Group.uint16_to_t h0.[|out|]) (v h0.[|i|].[0]) (Group.uint16_to_t d));
    assert((Group.uint16_to_t d) == i16 (v d % params_q));
    let a () : GTot (lseq Group.t params_n) = Seq.map Group.uint16_to_t h0.[|out|] in
    eq_intro (Seq.map Group.uint16_to_t h1.[|out|]) (Seq.upd (a ()) (v h0.[|i|].[0]) (i16 (v d%params_q)));
    (*assert(let s = h0.[|s|] in let i = v h0.[|i|].[0] in let j = v h0.[|j|].[0] in
             let d = v s.[2*j] + ((v s.[2*j+1]) * pow2 8) in
             d < 19 * params_q /\ h1.[|out|] == Seq.upd h0.[|out|] i (u16 d));*)
    assert(modifies2 out i h_ h1);
    assert(Spec.Kyber2.FunctionInstantiation.parse_inner h0.[|s|] (Seq.map Group.uint16_to_t h0.[|out|]) (v h0.[|i|].[0]) (v h0.[|j|].[0]) == Spec.Kyber2.FunctionInstantiation.parse_inner h1.[|s|] (Seq.map Group.uint16_to_t h1.[|out|]) (v h1.[|i|].[0]) (v h1.[|j|].[0])))
  else
    (let h1 = ST.get () in
     assert(modifies1 j h0 h1);
     assert(let s = h0.[|s|] in let out = h0.[|out|] in let i = v h0.[|i|].[0] in let j = v h0.[|j|].[0] in
             let d2 = to_u16 s.[2*j] +. ((to_u16 s.[2*j+1]) <<. size 8) in
             v d2 >= 19 * params_q /\ i < params_n /\ j < 336);
     assert(Spec.Kyber2.FunctionInstantiation.parse_inner h0.[|s|] (Seq.map Group.uint16_to_t h0.[|out|]) (v h0.[|i|].[0]) (v h0.[|j|].[0]) == Spec.Kyber2.FunctionInstantiation.parse_inner h1.[|s|] (Seq.map Group.uint16_to_t h1.[|out|]) (v h1.[|i|].[0]) (v h1.[|j|].[0])));
  let h1 = ST.get () in
  assert(modifies2 out i h_ h1);
  assert(modifies1 j h0 h_);
  assert(modifies3 out i j h0 h1)

val parse_xof_no_modulo:
  input_len:size_t{2+v input_len <= max_size_t}
  -> input:lbytes_p SEC input_len
  -> b1:uint_t U8 SEC
  -> b2:uint_t U8 SEC
  -> output:lbuffer uint16 (size params_n)
  -> Stack bool
    (requires fun h -> live h input /\ live h output /\ Buf.disjoint input output)
    (ensures fun h0 res h1 -> modifies1 output h0 h1 /\ (match (Spec.Kyber2.FunctionInstantiation.parse_xof (v input_len) h0.[|input|] b1 b2) with |None -> (res == false) |Some l -> ((Seq.map Group.uint16_to_t h1.[|output|]) == l /\ res == true)))

#reset-options "--z3rlimit 500 --max_fuel 1 --max_ifuel 1"

let parse_xof_no_modulo input_len input b1 b2 output =
  let h_begin = ST.get() in
  push_frame ();
  let tmp = create (size (4*168)) (u8 0) in
  xof input_len (size (4*168)) input b1 b2 tmp;
  let i = create 1ul (size 0) in
  let j = create 1ul (size 0) in
  let h0 = ST.get () in
  Lib.Loops.while
    (fun h -> live h i /\ live h j /\ (v h.[|j|].[0] <= 336) /\ (v h.[|i|].[0] <= params_n) /\ modifies3 output i j h0 h /\ parse_inv_no_modulo h0 h tmp output i j)
    (fun h -> (v h.[|j|].[0] < 336) && (v h.[|i|].[0] < params_n))
    (fun () -> let a = (j.(0ul) <. size 336) in
      let c = (i.(0ul) <. size params_n) in
      a && c)
    (fun () -> parse_inner_no_modulo h0 tmp output i j);
  let h2 = ST.get () in
  Spec.Kyber2.FunctionInstantiation.parse_inner_cst_lemma h0.[|tmp|] (Seq.map Group.uint16_to_t h0.[|output|]);
  let b = ( i.(0ul) =. size params_n) in
  pop_frame ();
  let h_end = ST.get () in
  assert(modifies1 output h_begin h_end);
  b
