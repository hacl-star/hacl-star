module Crypto.Symmetric.GF128.Spec

open FStar.Mul
open FStar.Seq
open FStar.UInt
open FStar.UInt8
open FStar.BitVector

open Crypto.Symmetric.Bytes

module Algebra = Crypto.Symmetric.GF128.Algebra

let nb = 8     // 8 bits in each byte.
let len = 16   // Length of GF128 in bytes.

type text = Seq.seq (lbytes len)
type elemS = lbytes len

#set-options "--z3timeout 10 --max_fuel 1 --initial_fuel 1"

abstract val lbytes_to_bv: #n:pos -> a:lbytes n ->
  Tot (r:bv_t (n * nb){forall (i:nat{i < n * nb}). index r i = index (to_vec (v (index a (i / nb)))) (i % nb)})
let rec lbytes_to_bv #n a = 
  if n = 1 then to_vec (v (index a 0)) else
  append (lbytes_to_bv #(n - 1) (slice a 0 (n - 1))) (to_vec (v (index a (n - 1))))

val add_loop: a:elemS -> b:elemS -> dep:nat{dep <= len} ->
  Tot (r:elemS{(forall (i:nat{i < dep}). index r i = (index a i) ^^ (index b i)) /\ (forall (i:nat{i >= dep /\ i < len}). index r i = index a i)}) (decreases dep)
let rec add_loop a b dep = 
  if dep = 0 then a
  else begin
    let i = dep - 1 in
    let na = add_loop a b i in
    upd na i ((index na i) ^^ (index b i))
  end

#reset-options "--z3timeout 5 --max_fuel 0 --initial_fuel 0"

val op_Plus_At: a:elemS -> b:elemS ->
  Tot (r:elemS{equal (lbytes_to_bv r) (Algebra.add (lbytes_to_bv a) (lbytes_to_bv b))})
let op_Plus_At a b = add_loop a b len


#set-options "--z3timeout 10 --max_fuel 1 --initial_fuel 1"

val shift_right_loop: a:elemS -> dep:nat{dep < len} ->
  Tot (r:elemS) (decreases dep)
let rec shift_right_loop a dep =
  if dep = 0 then upd a 0 ((index a 0) >>^ 1ul) else begin
    let i = dep - 1 in
    let na = upd a dep (((index a i) <<^ 7ul) +%^ ((index a dep) >>^ 1ul)) in
    shift_right_loop na i
  end

val shift_right_spec: a:elemS -> Tot (r:elemS)
let shift_right_spec a = shift_right_loop a (len - 1)


val ith_bit_mask: num:byte -> i:u32{FStar.UInt32.v i < nb} ->
  Tot byte
let ith_bit_mask num i =
  let proj = shift_right 128uy i in
  let res = logand num proj in
  eq_mask res proj

val apply_mask_loop: a:elemS -> msk:byte -> dep:nat{dep <= len} ->
  Tot (m:elemS{(forall (i:nat{i < dep}). index m i = ((index a i) &^ msk)) /\ (forall (i:nat{i >= dep /\ i < len}). index m i = index a i)}) (decreases dep)
let rec apply_mask_loop a msk dep =
  if dep = 0 then a else 
  begin
    let i = dep - 1 in
    let m = apply_mask_loop a msk i in
    upd m i ((index a i) &^ msk)
  end

val apply_mask: a:elemS -> msk:byte ->
  Tot (m:elemS{forall (i:nat{i < len}). index m i = ((index a i) &^ msk)})
let apply_mask a msk = apply_mask_loop a msk len

let r_mul = 225uy

val mul_loop: a:elemS -> b:elemS -> tmp:elemS -> dep:u32{FStar.UInt32.v dep <= 128} -> Tot elemS (decreases (128 - FStar.UInt32.v dep))
let rec mul_loop a b tmp dep =
  if FStar.UInt32.v dep = 128 then a else
  begin
    let num = index b (FStar.UInt32.v (FStar.UInt32.div dep 8ul)) in
    let msk = ith_bit_mask num (FStar.UInt32.rem dep 8ul) in
    let m = apply_mask a msk in
    let r = tmp +@ m in
    let num = index a 15 in
    let msk = ith_bit_mask num 7ul in
    let na = shift_right_spec a in
    let num = index a 0 in
    let na = upd na 0 (num ^^ (logand msk r_mul)) in
    mul_loop na b r (FStar.UInt32.add dep 1ul)
  end

let zero = Seq.create 16 0uy 

val op_Star_At: a:elemS -> b:elemS -> Tot (r:elemS)
let op_Star_At a b = mul_loop a b zero 0

open FStar.Seq
open FStar.SeqProperties 

let seq_head (vs:seq 'a {Seq.length vs > 0}) = Seq.slice vs 0 (Seq.length vs - 1)

let encode (x:lbytes 16): elemS = x

val poly: vs:text -> r:elemS -> Tot (a:elemS) (decreases (Seq.length vs))
let rec poly vs r =
  if Seq.length vs = 0 then zero
  else
    let v = SeqProperties.head vs in 
    (encode v +@ poly (SeqProperties.tail vs) r ) *@ r

let finish a s = a +@ s 
let mac vs r s = finish (poly vs r) s
