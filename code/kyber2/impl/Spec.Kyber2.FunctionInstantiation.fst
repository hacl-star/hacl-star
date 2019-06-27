module Spec.Kyber2.FunctionInstantiation

open FStar.Mul

open Spec.Kyber2.Params
open Lib.Poly
open Lib.NumericTypes

open Lib.Arithmetic.Group
open Lib.Arithmetic.Ring
open Lib.Arithmetic.Sums
open Lib.Arithmetic.Group.Uint_t
open Lib.Arithmetic.Ring.Uint_t

open Lib.Sequence
open Lib.ByteSequence
open Lib.IntTypes

open Spec.SHA3


module Seq = Lib.Sequence


#reset-options "--z3rlimit 50 --max_fuel 0 --max_ifuel 0"

val xof: (input_len:size_nat{2+input_len<=max_size_t}) -> (output_len:size_nat) -> lbytes_l SEC input_len -> uint_t U8 SEC -> uint_t U8 SEC -> lbytes_l SEC output_len

let xof input_len output_len l b1 b2 = shake128 (input_len+2) (concat (concat l (create 1 b1)) (create 1 b2)) output_len

val prf: output_len: size_nat -> (s:lbytes_l SEC 32) -> (b:uint_t U8 SEC) -> lbytes_l SEC output_len

let prf output_len s b = shake256 33 (concat s (create 1 b)) output_len

val hash_h: (input_len:size_nat) -> lbytes_l SEC input_len -> lbytes_l SEC 32

let hash_h = sha3_256

val hash_g: (input_len:size_nat) -> lbytes_l SEC input_len -> lbytes_l SEC 32 & lbytes_l SEC 32

let hash_g input_len s =
  let h = sha3_512 input_len s in
  (Seq.sub h 0 32, Seq.sub h 32 32)

val kdf: (input_len:size_nat) -> (output_len:size_nat) -> lbytes_l SEC input_len -> lbytes_l SEC output_len

let kdf input_len output_len s = shake256 input_len s output_len

val parse_xof: (input_len:size_nat{2+input_len<=max_size_t}) -> lbytes_l SEC input_len -> uint_t U8 SEC -> uint_t U8 SEC -> option (lseq Group.t params_n)

let rec parse_inner (s:lbytes_l SEC (4*168)) (out:lseq (Group.t) params_n) (i:nat{i<=params_n}) (j:nat{j<=336}) : Tot (option (lseq (Group.t) params_n)) (decreases ((params_n-i)+(336-j))) =
    if (i=params_n) then Some out
    else if (j=336) then None
    else let d = to_u16 s.[2*j] +. ((to_u16 s.[2*j+1]) <<. size 8) in
    if v d < 19 * params_q then parse_inner s (upd out i (to_i16 ((Lib.RawIntTypes.u16_to_UInt16 d) %. uint #U16 #PUB params_q))) (i+1) (j+1)
    else parse_inner s out i (j+1)

let parse_xof input_len l b1 b2 =
  parse_inner (xof input_len (4*168) l b1 b2) (create params_n (Group.zero_t)) 0 0


#reset-options "--z3rlimit 100 --max_fuel 1 --max_ifuel 1"

let rec parse_inner_lemma0 (s:lbytes_l SEC (4*168)) (out:lseq (Group.t) params_n) (i:nat{i<=params_n}) (j:nat{j<=336}) :
  Lemma (ensures (match parse_inner s out i j with
                 |None -> True
                 |Some seq -> forall (k:nat{k<i}). seq.[k] == out.[k])) (decreases (params_n - i + 336 - j)) =
   if (i=params_n) then ()
   else if (j=336) then ()
   else let d = to_u16 s.[2*j] +. ((to_u16 s.[2*j+1]) <<. size 8) in
    if v d < 19 * params_q then
    let out' = upd out i (to_i16 ((Lib.RawIntTypes.u16_to_UInt16 d) %. uint #U16 #PUB params_q)) in
    parse_inner_lemma0 s out' (i+1) (j+1)
    else parse_inner_lemma0 s out i (j+1)

let rec parse_inner_lemma (s:lbytes_l SEC (4*168)) (out:lseq (Group.t) params_n) (i:nat{i<=params_n}) (out2:lseq (Group.t) params_n{forall (k:nat{i<=k /\ k<params_n}). sint_v out2.[k] = 0}) (j:nat{j<=336}) : Lemma (ensures (match (parse_inner s out i j),(parse_inner s out2 i j) with
                 |None, None -> True
                 |Some seq, Some seq' -> (forall (k:nat{i<=k /\ k <params_n}). Seq.index #Group.t seq k == Seq.index #Group.t seq' k)
                 |_,_ -> False))
                 (decreases (params_n - i + 336 - j)) =
  if (i=params_n) then ()
  else if (j=336) then ()
  else let d = to_u16 s.[2*j] +. ((to_u16 s.[2*j+1]) <<. size 8) in
    if v d < 19 * params_q then
    let out' = upd out i (to_i16 ((Lib.RawIntTypes.u16_to_UInt16 d) %. uint #U16 #PUB params_q)) in
    let out2' = upd out2 i (to_i16 ((Lib.RawIntTypes.u16_to_UInt16 d) %. uint #U16 #PUB params_q)) in
    let customprop (k:nat{i+1<=k /\ k<params_n}) = sint_v out2'.[k] = 0 in
    let customlemma (k:nat{i+1<=k /\ k<params_n}) : Lemma (customprop k) = assert(k<>i); assert(out2'.[k] == out2.[k]) in
    (FStar.Classical.forall_intro customlemma;
    parse_inner_lemma s out' (i+1) out2' (j+1);
    parse_inner_lemma0 s out' (i+1) (j+1);
    parse_inner_lemma0 s out2' (i+1) (j+1);
    (match (parse_inner s out' (i+1) (j+1)),(parse_inner s out2' (i+1) (j+1)) with
         |None, None -> ()
         |Some seq, Some seq' -> (assert(seq.[i] == out'.[i]); assert(seq'.[i] == out2'.[i]))
         |_,_ -> ()))
    else (parse_inner_lemma s out i out2 (j+1))

let parse_inner_cst_lemma (s:lbytes_l SEC (4*168)) (out:lseq (Group.t) params_n) : Lemma (parse_inner s out 0 0 == parse_inner s (create params_n Group.zero_t) 0 0) =
  let zseq = create params_n Group.zero_t in
  parse_inner_lemma s out 0 zseq 0;
  match parse_inner s out 0 0, parse_inner s zseq 0 0 with
  |None, None -> ()
  |Some seq, Some seq' -> eq_intro seq seq'
  |_,_ -> ()
