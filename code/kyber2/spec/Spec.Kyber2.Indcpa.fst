module Spec.Kyber2.Indcpa

open FStar.Mul

open Spec.Kyber2.Params
open Spec.Powtwo.Lemmas
open Lib.Poly
open Lib.Poly.NTT2
open Lib.NumericTypes

open Lib.Arithmetic.Group
open Lib.Arithmetic.Ring
open Lib.Arithmetic.Sums
open Lib.Arithmetic.Group.Uint_t
open Lib.Arithmetic.Ring.Uint_t

open Lib.Sequence
open Lib.ByteSequence
open Lib.IntTypes
open Lib.NumericTypes

open Lib.ModularArithmetic
open Lib.ModularArithmetic.Lemmas

open Spec.Kyber2.FunctionInstantiation
open Spec.Kyber2.CBD

open FStar.Math.Lemmas

module Seq = Lib.Sequence

val convert_to_field: #t:inttype -> #l:secrecy_level -> #len:size_nat -> lseq (uint_t t l) len -> lseq (field params_q) len

let convert_to_field #t #l #len s =
  let f (i:nat{i<len}) : field params_q = (uint_v s.[i]) % params_q in 
  createi len f

val convert_to_u16: #len:size_nat -> lseq (field params_q) len -> lseq uint16 len

let convert_to_u16 #len s =
  let f (i:nat{i<len}) : uint16 = u16 s.[i] in
  createi len f

type num_t = Base (field params_q)
type poly_t = vector_t #num_t params_n
type vec_t = vector_t #poly_t params_k
type matrix_t = matrix_t #poly_t params_k params_k

type num = field params_q
type poly = vector_i #num_t params_n
type vec = vector_i #poly_t params_k
type matrix = matrix_i #poly_t params_k params_k

let ring_num = ring_mod #params_q
let ring_poly = lib_ntt_ring #num #ring_num #params_n 7 params_zeta

#reset-options "--z3rlimit 100 --max_fuel 2 --max_ifuel 2 --using_facts_from '* -FStar.Seq'"

val encode: l:nat{l*params_n<=max_size_t} -> x:poly -> lbytes_l SEC (l*params_n/8)

let encode l x =
  let a (i:nat{i<=params_n}) = int in
  let f (i:nat{i<params_n}) (acc: a i) : a (i+1) & lseq (uint_t U1 SEC) l =
    let u = (index #_ #params_n x i) in
    let g(j:nat{j<l}) = u1 ((u / (pow2 j))%2) in
    0, createi l g
  in let _,s= generate_blocks l params_n a f 0 in
  to_bytes s

val decode: l:nat{l*params_n<=max_size_t} -> s:lbytes_l SEC (l*params_n/8) -> x:poly{forall (i:nat{i<params_n}). (index #_ #params_n x i) < pow2 l}

#reset-options "--z3rlimit 300 --max_fuel 2 --max_ifuel 2 --using_facts_from '* -FStar.Seq'"

let decode l s =
  let bits = to_bits s in
  let f (i:nat{i<params_n}) : x:num =
    let a (j:nat{j<=l}) = acc:num{acc<pow2 j} in
    let g (j:nat{j<l}) (acc:a j) : a (j+1) =
      pow2_values 1;
      assert(maxint U1 == 1);
      assert_norm (8*(l*params_n/8) == l*params_n);
      let x:uint1 = bits.[l*i+j] in
      assert(uint_v x <= maxint U1);
      lemma_mult_le_right (pow2 j) (uint_v x) 1;
      assert(acc + ((uint_v x) * pow2 j)  <= acc + pow2 j);
      pow2_double_sum j;
      (acc + ((uint_v bits.[l*i+j]) * pow2 j))%params_q
    in Lib.LoopCombinators.repeat_gen l a g 0
  in createi params_n f

val encode_vec: l:nat{l*params_n*params_k<=max_size_t} -> x:vec -> lbytes_l SEC (params_k*l*params_n/8)

let encode_vec l x =
  let a (i:nat{i<=params_k}) = int in
  let f (i:nat{i<params_k}) (acc: a i) : a (i+1) & lbytes_l SEC (l*params_n/8) =
    0, encode l (index #_ #params_k x i)
  in let _,s = generate_blocks (l*params_n/8) params_k a f 0 in
  s

val decode_vec: l:nat{l*params_n*params_k<=max_size_t} -> s:lbytes_l SEC (params_k*l*params_n/8) -> vec

let decode_vec l s =
  let f (i:nat{i<params_k}) : poly =
    decode l (Seq.sub s (i*l*params_n/8) (l*params_n/8))
  in createi params_k f

val compress: d:nat{pow2 d < params_q} -> x:num -> y:nat{y<pow2 d}
let compress d x =
  (((x * pow2 d) + (params_q/2))/params_q)%(pow2 d)


#reset-options "--z3rlimit 200 --max_fuel 2 --max_ifuel 2 --using_facts_from '* -FStar.Seq'"

val decompress: d:nat{pow2 d < params_q} -> x:nat{x<pow2 d} -> num

let decompress d x =
    ((2*x*params_q)+(pow2 d))/pow2 (d+1)

val compress_poly: d:nat{pow2 d < params_q} -> x:poly -> y:poly{forall (i:nat{i<params_n}). (index #_ #params_n y i)<pow2 d}

let compress_poly d x =
  let f (z:interp_numeric num_t) : num = compress d z in
  Seq.map #_ #_ #params_n f x

val decompress_poly: d:nat{pow2 d < params_q} -> x:poly{forall (i:nat{i<params_n}). (index #_ #params_n x i)<pow2 d} -> poly

let decompress_poly d x =
  let f (z:num{z<pow2 d}) : num = decompress d z in
  createi params_n (fun i -> f (index #_ #params_n x i))

val compress_vec: d:nat{pow2 d < params_q} -> x:vec -> y:vec{forall (i:nat{i<params_k}). forall(j:nat{j<params_n}). (index #_ #params_n (index #_ #params_k y i) j)<pow2 d}

let compress_vec d x =
  let f (z:poly) = compress_poly d z in
  Seq.map #_ #_ #params_k f x

val decompress_vec: d:nat{pow2 d < params_q} -> x:vec{forall (i:nat{i<params_k}). forall(j:nat{j<params_n}). (index #_ #params_n (index #_ #params_k x i) j)<pow2 d} -> vec

let decompress_vec d x =
  let f z = decompress_poly d z in
  createi params_k (fun i -> f (index #_ #params_k x i))

let ntt (x:poly) = lib_ntt #_ #ring_num #params_n 7 params_zeta x
let ntt_vec (x:vec) = Seq.map #_ #_ #params_k ntt x
let ntt_matrix (x:matrix) = Seq.map #_ #_ #params_k (ntt_vec) x

let nttinv (x:poly) = lib_nttinv #_ #ring_num #params_n 7 params_halfninv params_zeta x
let nttinv_vec (x:vec) = Seq.map #_ #_ #params_k nttinv x
let nttinv_matrix (x:matrix) = Seq.map #_ #_ #params_k (nttinv_vec) x

let new_matrix () : matrix = create params_k (create params_k (create params_n 0))

let upd_matrix a i j x : matrix = upd #_ #params_k a i (upd #_ #params_k a.[i] j x)

#reset-options
val gen_Ahat: (rho:lbytes_l SEC 32) -> i:nat{i<params_k} -> j:nat{j<params_k} -> option poly

let gen_Ahat rho i j =
    match parse_xof 32 rho (u8 j) (u8 i) with
    |None -> None
    |Some out -> Some (convert_to_field out)


val gen_matrix: (f: (i:nat{i<params_k}) -> (j:nat{j<params_k}) -> option poly) -> option matrix

let gen_matrix f =
  let rec aux (m:matrix) (i:nat{i<=params_k}) (j:nat{j<=params_k}) : Tot (option matrix) (decreases ((params_k+1)*(params_k+1) -(params_k+1)*i-j)) =
  if (i=params_k) then Some m
  else if (j=params_k) then aux m (i+1) 0
  else let x = f i j in
  match x with
  |None -> None
  |Some p -> aux (upd_matrix m i j p) i (j+1)
  in aux (new_matrix ()) 0 0

let pklen:size_nat = (12*params_k*params_n/8)+32
let sklen:size_nat = 12*params_k*params_n/8
let ulen = params_du*params_k*params_n/8
let vlen = params_dv*params_n/8
let ciphertextlen:size_nat = ulen + vlen

val keygen: (coins:lbytes_l SEC 32) -> option (lbytes_l SEC pklen & lbytes_l SEC sklen)

#reset-options "--z3rlimit 300"
let keygen coins =
  let rho,sigma = hash_g 32 coins in
  match gen_matrix (gen_Ahat rho) with 
  |None -> None
  |Some a_hat -> begin
  let s:vec = Seq.createi params_k (fun i -> cbd_kyber sigma (u8 i)) in
  let e:vec = Seq.createi params_k (fun i -> cbd_kyber sigma (u8 (params_k+i))) in
  let s_hat = ntt_vec s in
  let e_hat = ntt_vec e in
  let ring_poly = ring_poly in
  let t_hat = vector_plus (matrix_vector_product a_hat s_hat) e_hat in
  Some ((concat (encode_vec 12 t_hat) rho),encode_vec 12 s_hat) 
end

val enc: (pk: lbytes_l SEC pklen) -> (msg: lbytes_l SEC 32) -> (msgcoins: lbytes_l SEC 32) -> option (lbytes_l SEC ciphertextlen)

let enc pk msg msgcoins =
  let t_hat = decode_vec 12 (Seq.sub pk 0 sklen) in
  let rho = Seq.sub pk sklen 32 in
  let gen_Athat rho i j = gen_Ahat rho j i in
  match gen_matrix (gen_Athat rho) with
  |None -> None
  |Some at_hat -> begin
    let ring_poly = ring_poly in
    let r:vec = Seq.createi params_k (fun i -> cbd_kyber msgcoins (u8 i)) in
    let e1:vec = Seq.createi params_k (fun i -> cbd_kyber msgcoins (u8 (i+params_k))) in
    let e2:poly = cbd_kyber msgcoins (u8 (2*params_k)) in
    let r_hat = ntt_vec r in
    let u:vec = vector_plus (nttinv_vec (matrix_vector_product at_hat r_hat)) e1 in
    let dmsg = decode 1 msg in
    let v:poly = plus (plus (nttinv (dot_product t_hat r_hat)) e2) (decompress_poly 1 (decode 1 msg)) in
    let c1 = encode_vec params_du (compress_vec params_du u) in
    let c2 = encode params_dv (compress_poly params_dv v) in
    Some (concat c1 c2) end

val dec: (sk:lbytes_l SEC sklen) -> (c:lbytes_l SEC ciphertextlen) -> lbytes_l SEC 32

let dec sk c =
  let ring_poly = ring_poly in
  let c1 = (Seq.sub c 0 ulen) in
  let c2 = (Seq.sub c ulen vlen) in
  let u:vec = decompress_vec params_du (decode_vec params_du c1) in
  let v:poly = decompress_poly params_dv (decode params_dv c2) in
  let s_hat = decode_vec 12 sk in
  let m = encode 1 (compress_poly 1 (minus v (dot_product #_ #ring_poly s_hat (ntt_vec u)))) in
  m
