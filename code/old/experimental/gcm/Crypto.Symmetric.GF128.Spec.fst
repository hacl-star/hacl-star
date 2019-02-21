module Crypto.Symmetric.GF128.Spec

module ST = FStar.HyperStack.ST

open FStar.HyperStack.All

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

#set-options "--z3rlimit 15 --max_fuel 1 --initial_fuel 1"

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

#reset-options "--z3rlimit 5 --max_fuel 0 --initial_fuel 0"

val op_Plus_At: a:elemS -> b:elemS ->
  Tot (r:elemS{equal (lbytes_to_bv r) (Algebra.add (lbytes_to_bv a) (lbytes_to_bv b))})
let op_Plus_At a b = add_loop a b len


#reset-options "--z3rlimit 15 --max_fuel 1 --initial_fuel 1"

val shift_right_loop: a:elemS -> dep:nat{dep < len} ->
  Tot (r:elemS{(index r 0 = ((index a 0) >>^ 1ul)) /\
    (forall (i:pos{i <= dep}). index r i = ((index a (i - 1)) <<^ 7ul) +%^ ((index a i) >>^ 1ul)) /\
    (forall (i:pos{i > dep /\ i < len}). index r i = index a i)})
  (decreases dep)
let rec shift_right_loop a dep =
  if dep = 0 then upd a 0 ((index a 0) >>^ 1ul) else begin
    let i = dep - 1 in
    let na = upd a dep (((index a i) <<^ 7ul) +%^ ((index a dep) >>^ 1ul)) in
    shift_right_loop na i
  end

val shift_right_loop_lemma: a:elemS -> dep:nat{dep < len} -> i:pos{i <= dep} -> Lemma
  (requires True)
  (ensures (index (shift_right_loop a dep) i = logor ((index a (i - 1)) <<^ 7ul) ((index a i) >>^ 1ul)))
  [SMTPat (index (shift_right_loop a dep) i)]
let shift_right_loop_lemma a dep i = 
    FStar.Math.Lemmas.small_modulo_lemma_1 (v ((index a (i - 1)) <<^ 7ul) + v ((index a i) >>^ 1ul)) (pow2 8);
    assert(v (((index a (i - 1)) <<^ 7ul) +%^ ((index a i) >>^ 1ul)) = v ((index a (i - 1)) <<^ 7ul) + v ((index a i) >>^ 1ul));
    logor_disjoint (v ((index a (i - 1)) <<^ 7ul)) (v ((index a i) >>^ 1ul)) 7
    
#reset-options "--z3rlimit 10 --max_fuel 1 --initial_fuel 1"

val shift_right_spec: a:elemS ->
  Tot (r:elemS{(index r 0 = ((index a 0) >>^ 1ul)) /\
    (forall (i:pos{i < len}). index r i = logor ((index a (i - 1)) <<^ 7ul) ((index a i) >>^ 1ul))})
let shift_right_spec a = shift_right_loop a (len - 1)

#reset-options "--z3rlimit 30 --max_fuel 0 --initial_fuel 0"

val shift_right_spec_lemma_aux_1: a:elemS -> 
  Lemma (forall (i:pos{i < 128 /\ i % 8 = 0}). index (lbytes_to_bv (shift_right_spec a)) i = index (shift_right_vec (lbytes_to_bv a) 1) i)
let shift_right_spec_lemma_aux_1 a = 
  assert(forall (i:pos{i < 128 /\ i % 8 = 0}). index (lbytes_to_bv (shift_right_spec a)) i = index (to_vec (v (index a (i / 8 - 1)))) 7);
  assert(forall (i:pos). i % 8 = 0 ==> (i - 1) / 8 = i / 8 - 1 /\ (i - 1) % 8 = 7);
  assert(forall (i:pos{i < 128 /\ i % 8 = 0}). index (shift_right_vec (lbytes_to_bv a) 1) i = index (to_vec (v (index a (i / 8 - 1)))) 7)
  
val shift_right_spec_lemma_aux_2: a:elemS -> 
  Lemma (forall (i:pos{i < 128 /\ i % 8 > 0}). index (lbytes_to_bv (shift_right_spec a)) i = index (shift_right_vec (lbytes_to_bv a) 1) i)
let shift_right_spec_lemma_aux_2 a =
  assert(forall (i:pos{i < 128 /\ i % 8 > 0}). index (lbytes_to_bv (shift_right_spec a)) i = index (to_vec (v (index a (i / 8)))) (i % 8 - 1));
  assert(forall (i:pos). i % 8 > 0 ==> (i - 1) / 8 = i / 8 /\ (i - 1) % 8 = i % 8 - 1);
  assert(forall (i:pos{i < 128 /\ i % 8 > 0}). index (shift_right_vec (lbytes_to_bv a) 1) i = index (to_vec (v (index a (i / 8)))) (i % 8 - 1))

val shift_right_spec_lemma: a:elemS ->
  Lemma (lbytes_to_bv (shift_right_spec a) = shift_right_vec (lbytes_to_bv a) 1)
let shift_right_spec_lemma a =
  shift_right_spec_lemma_aux_1 a;
  shift_right_spec_lemma_aux_2 a;
  assert(equal (lbytes_to_bv (shift_right_spec a)) (shift_right_vec (lbytes_to_bv a) 1))


val ith_bit_mask: num:byte -> i:nat{i < nb} ->
  Tot (m:byte{(nth (v num) i ==> m = 255uy) /\ (not (nth (v num) i) ==> m = 0uy)})
let ith_bit_mask num i = if (nth (v num) i) then 255uy else 0uy

let zero = Seq.create 16 0uy 

val apply_mask_loop: a:elemS -> m:elemS -> msk:byte -> dep:nat{dep <= len} ->
  Tot (r:elemS{(forall (i:nat{i < dep}). index r i = ((index a i) &^ msk)) /\ (forall (i:nat{i >= dep /\ i < len}). index r i = index m i)}) (decreases dep)
let rec apply_mask_loop a m msk dep =
  if dep = 0 then m else 
  begin
    let i = dep - 1 in
    let nm = upd m i ((index a i) &^ msk) in
    apply_mask_loop a nm msk i
  end

abstract val apply_mask: a:elemS -> msk:byte ->
  Tot (r:elemS{forall (i:nat{i < len}). index r i = ((index a i) &^ msk)})
let apply_mask a msk = apply_mask_loop a a msk len

val apply_mask_lemma_aux: a:elemS -> msk:byte -> i:nat{i < len} -> Lemma
  (requires True)
  (ensures ((msk = 255uy ==> index (apply_mask a msk) i = index a i) /\ (msk = 0uy ==> index (apply_mask a msk) i = index zero i)))
  [SMTPat (index (apply_mask a msk) i)]
let apply_mask_lemma_aux a msk i =
  logand_lemma_1 #8 (v (index a i));
  logand_lemma_2 #8 (v (index a i))

val apply_mask_lemma: a:elemS -> msk:byte -> Lemma
  (requires True)
  (ensures ((msk = 255uy ==> apply_mask a msk = a) /\ (msk = 0uy ==> apply_mask a msk = zero)))
  [SMTPat (apply_mask a msk)]
let apply_mask_lemma a msk =
  assert(msk = 255uy ==> equal (apply_mask a msk) a);
  assert(msk = 0uy ==> equal (apply_mask a msk) zero)


let r_mul_0 = 225uy
let r_mul = upd zero 0 r_mul_0

val mask_add_spec: a:elemS -> b:elemS -> r:elemS -> dep:nat{dep < 128} -> Pure elemS
  (requires True)
  (ensures (fun s -> 
    index (lbytes_to_bv b) dep = true ==> s = r +@ a /\
    index (lbytes_to_bv b) dep = false ==> s = r))
  (decreases (128 - dep))
let mask_add_spec a b r dep =
  let num = index b (dep / 8) in
  let msk = ith_bit_mask num (dep % 8) in
  let m = apply_mask a msk in
  r +@ m

val shift_right_modulo: a:elemS -> Pure elemS
  (requires True)
  (ensures (fun r ->
    index (lbytes_to_bv a) 127 = true ==> r = (shift_right_spec a) +@ r_mul /\
    index (lbytes_to_bv a) 127 = false ==> r = shift_right_spec a))
let shift_right_modulo a =
  let num = index a 15 in
  let msk = ith_bit_mask num 7 in
  let na = shift_right_spec a in
  let num = index na 0 in
  upd na 0 (num ^^ (logand msk r_mul_0))

val mul_loop: a:elemS -> b:elemS -> r:elemS -> dep:nat{dep <= 128} -> Tot elemS
  (decreases (128 - dep))
let rec mul_loop a b r dep =
  if dep = 128 then r else
  begin
    let nr = mask_add_spec a b r dep in 
    let na = shift_right_modulo a in
    mul_loop na b nr (dep + 1)
  end

val op_Star_At: a:elemS -> b:elemS -> Tot (r:elemS)
let op_Star_At a b = mul_loop a b zero 0


open FStar.Seq
open FStar.Seq 

let seq_head (vs:seq 'a {Seq.length vs > 0}) = Seq.slice vs 0 (Seq.length vs - 1)

let encode (x:lbytes 16): elemS = x

val poly: vs:text -> r:elemS -> Tot (a:elemS) (decreases (Seq.length vs))
let rec poly vs r =
  if Seq.length vs = 0 then zero
  else
    let v = Seq.head vs in 
    (encode v +@ poly (Seq.tail vs) r ) *@ r

let finish a s = a +@ s 
let mac vs r s = finish (poly vs r) s
