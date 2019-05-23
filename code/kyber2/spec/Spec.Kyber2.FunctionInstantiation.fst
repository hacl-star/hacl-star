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

val parse_xof: (input_len:size_nat{2+input_len<=max_size_t}) -> lbytes_l SEC input_len -> uint_t U8 SEC -> uint_t U8 SEC -> option (lseq uint16 params_n)

let parse_xof input_len l b1 b2 =
  (*let s = create 25 (u64 0) in
  let s = absorb s 168 (input_len+2) (concat (concat l (create 1 b1)) (create 1 b2)) (byte 0x1F) in
  let a (i:nat{i<=4}) = state in
  let s, output = generate_blocks 168 4 a (squeeze_inner 168 (4*168)) s in
  let rec parse_inner (s:state) (len:size_nat{len%2=0}) (stream:lbytes_l SEC len) (out:lseq uint16 params_n) (i:nat{i<=params_n}) (j:nat{j%2=0}) : Tot (lseq uint16 params_n) (decreases (params_n - i))=
    admit();
    if (i=params_n) then out
    else if j>=len then let s,block = squeeze_inner 168 168 0 s in parse_inner s 168 block out i 0
    else let d = uint_v stream.[j] + 256 * uint_v stream.[j+1] in
    if d < 19 * params_q then parse_inner s len stream (upd out i (u16 (d%params_q))) (i+1) (j+2)
    else parse_inner s len stream out i (j+2)
  in parse_inner s (4*168) output (create params_n (u16 0)) 0 0*)
  let s=xof input_len (4*168) l b1 b2 in
  let rec parse_inner s out (i:nat{i<=params_n}) (j:nat{j<=84}) : Tot (option (lseq uint16 params_n)) (decreases ((params_n-i)+(84-j))) =
    if (i=params_n) then Some out
    else if (j=84) then None
    else let d = uint_v s.[2*j] + 256 * uint_v s.[2*j+1] in
    if d < 19 * params_q then parse_inner s (upd out i (u16 (d%params_q))) (i+1) (j+1)
    else parse_inner s out i (j+1)
  in parse_inner s (create params_n (u16 0)) 0 0

