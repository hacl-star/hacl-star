module Spec.RSA.Bignum

open FStar.Mul
open Spec.Lib.IntTypes
open Spec.Lib.IntSeq
open Spec.Lib.RawIntTypes

open FStar.Math.Lemmas
open Spec.RSA.Lemmas

(* BIGNUM *)
type bignum = nat
let bn_v n = n
let bn n = n
let bn_add a b = a + b
let bn_mul a b = a `op_Multiply` b
let bn_sub a b = a - b
let bn_mul_mod a b n = (a `op_Multiply` b) % n
let bn_is_even x = (x % 2) = 0
let bn_div2 x = x / 2
let bn_is_less x y = x < y

type elem (n:bignum) = e:bignum{bn_v e < bn_v n}

type sign =
     | Positive : sign
     | Negative : sign

(* a - b = (sign, |a - b|) *)
val abs_sub: 
    x:size_nat -> a:bignum -> b:bignum -> Pure (tuple2 sign bignum)
    (requires (a < pow2 (pow2 x) /\ b < pow2 (pow2 x)))
    (ensures (fun (s, res) -> res < pow2 (pow2 x) /\ res = abs (a - b) /\
			    s = (if a >= b then Positive else Negative)))
    
let abs_sub x a b =
    if (bn_is_less a b)
    then (Negative, b - a)
    else (Positive, a - b)

val add_sign:
    c0:bignum -> c1:bignum -> c2:bignum ->
    a0:bignum -> a1:bignum -> a2:bignum ->
    b0:bignum -> b1:bignum -> b2:bignum ->
    sa2:sign -> sb2:sign -> Pure bignum
    (requires (c0 == a0 * b0 /\ c1 == a1 * b1 /\ c2 == a2 * b2 /\
               a2 = abs (a0 - a1) /\ b2 = abs (b0 - b1) /\
	       sa2 = (if (a0 >= a1) then Positive else Negative) /\
	       sb2 = (if (b0 >= b1) then Positive else Negative)))
    (ensures (fun res -> res == a1 * b0 + a0 * b1))

#reset-options "--z3rlimit 150 --initial_fuel 0 --max_fuel 0"

let add_sign c0 c1 c2 a0 a1 a2 b0 b1 b2 sa2 sb2 =
    if ((sa2 = Positive && sb2 = Positive) || (sa2 = Negative && sb2 = Negative))
    then (c0 + c1) - c2
    else (c0 + c1) + c2

val karatsuba:
    x0:size_nat{0 < x0} -> a:bignum{a < pow2 (pow2 x0)} -> b:bignum{b < pow2 (pow2 x0)} -> Pure bignum
    (requires (True))
    (ensures (fun res -> res == a * b))
    (decreases x0)

#reset-options "--z3rlimit 300 --max_fuel 2"

let rec karatsuba x0 a b =
    if x0 < 9 then a * b
    else begin
        let x = x0 - 1 in
        let pow_x = pow2 (pow2 x) in
	
        let a0 = a % pow_x in let a1 = a / pow_x in
        assert (0 <= a0 /\ a0 < pow_x);
        lemma_pow_div_karatsuba x0 a;
        assert (0 <= a1 /\ a1 < pow_x);
        lemma_div_mod a pow_x;

        let b0 = b % pow_x in let b1 = b / pow_x in
        assert (0 <= b0 /\ b0 < pow_x);
        lemma_pow_div_karatsuba x0 b;
        assert (0 <= b1 /\ b1 < pow_x);
        lemma_div_mod b pow_x;

        let (sa2, a2) = abs_sub x a0 a1 in
        let (sb2, b2) = abs_sub x b0 b1 in
		
        let c0 = karatsuba x a0 b0 in
        assert (c0 == a0 * b0); //from ind hypo
        let c1 = karatsuba x a1 b1 in
        assert (c1 == a1 * b1); //from ind hypo
        let c2 = karatsuba x a2 b2 in
        assert (c2 == a2 * b2); //from ind hypo
		
        let pow_x1 = pow2 (pow2 (x + 1)) in
        let tmp = add_sign c0 c1 c2 a0 a1 a2 b0 b1 b2 sa2 sb2 in
        let c = c1 * pow_x1 + tmp * pow_x + c0 in
        lemma_karatsuba_mult x a a0 a1 b b0 b1;
        assert (c == a * b);
        c
    end

val mont_reduction:
    modBits:size_nat{1 < modBits} ->
    r:nat{r = pow2 (modBits + 2) /\ 0 < r} ->
    n:nat{1 < n /\ 4 * n < r} -> n':bignum ->
    c:nat{c < r * n} -> Pure (elem (n + n))
    (requires (True))
    (ensures (fun res -> res % n == (c / r) % n))

#reset-options "--z3rlimit 150 --max_fuel 0"

let mont_reduction modBits r n n' c =
    let m = (c * n') % r in
    assert (0 <= m /\ m < r);
    let m = r - m in
    assert (0 < m /\ m <= r);
    let res = (c + n * m) / r in
    assert (res >= 0);
    assert (c + n * m <= c + n * r);
    lemma_div_le (c + n * m) (c + n * r) r;
    assert (res <= (c + n * r) / r);
    division_addition_lemma c r n;
    assert (res <= c / r + n);
    assert (c < r * n);
    division_addition_lemma 0 r n;
    assert (res < n + n);
    lemma_mont_reduction res r c n m;
    res

val mul_mod_mont:
    x0:size_nat ->
    modBits:size_nat{1 < modBits} ->
    r:nat{r = pow2 (modBits + 2) /\ 0 < r} ->
    n:nat{1 < n /\ 4 * n < r /\ r <= pow2 (pow2 x0)} -> n':bignum ->
    a:elem (n + n) -> b:elem (n + n) -> Pure (elem (n + n))
    (requires (True))
    (ensures (fun res -> res % n == (a * b / r) % n))

#reset-options "--z3rlimit 50 --max_fuel 0"

let mul_mod_mont x0 modBits r n n' a b =
    //let c = karatsuba x0 a b in
    let c = a * b in
    assert (c < 4 * n * n);
    //assert (c < r * n);
    mont_reduction modBits r n n' c

val to_mont:
    modBits:size_nat{1 < modBits} ->
    r:nat{r = pow2 (modBits + 2) /\ 0 < r} ->
    n:nat{1 < n /\ 4 * n < r} -> n':bignum ->
    r2:elem n -> a:elem n -> Pure (elem (n + n))
    (requires (r2 == (r * r) % n))
    (ensures (fun res -> res % n == (a * r) % n))

#reset-options "--z3rlimit 150 --max_fuel 0"

let to_mont modBits r n n' r2 a =
    let c = a * r2 in
    assert (c == a * ((r * r) % n));
    assert (c < 4 * n * n);
    let res = mont_reduction modBits r n n' c in
    assert (res % n == ((a * ((r * r) % n)) / r) % n);
    lemma_mod_div_simplify res a r n;
    res

val from_mont:
    modBits:size_nat{1 < modBits} ->
    r:nat{r = pow2 (modBits + 2) /\ 0 < r} ->
    n:nat{1 < n /\ 4 * n < r} -> n':bignum ->
    a_r:elem (n + n) -> Pure (elem n)
    (requires (True))
    (ensures (fun res -> res == (a_r / r) % n))

#reset-options "--z3rlimit 150 --max_fuel 0"

let from_mont modBits r n n' a_r =
    let m = (a_r * n') % r in
    assert (0 <= m /\ m < r);
    let m = r - m in
    assert (0 < m /\ m <= r);
    let res = (a_r + n * m) / r in
    assert (a_r + n * m <= a_r + n * r);
    lemma_div_le (a_r + n * m) (a_r + n * r) r;
    assert (res <= (a_r + n * r) / r);
    division_addition_lemma a_r r n;
    assert (res <= a_r / r + n);
    small_division_lemma_1 a_r r;
    assert (res <= n);
    lemma_mont_reduction_1 res r a_r n m;
    res

val is_bit_set: a:bignum -> ind:size_nat -> Tot bool
let is_bit_set a ind = if (a / pow2 ind > 0) then true else false

val degree_: a:bignum -> i:size_nat -> Tot size_nat (decreases i)
let rec degree_ a i =
  if i = 0 then 0
  else
    if is_bit_set a (i - 1) then i
    else degree_ a (i - 1)

val degree: a:bignum -> aBits:size_nat -> Tot size_nat
let degree a aBits = degree_ a aBits

val bn_lshift: a:bignum -> b:size_nat -> Tot bignum
let bn_lshift a b = a * pow2 b

val shift_euclidean_mod_inv_f:
    m:bignum -> tmp:bignum{tmp <= m} -> f:size_nat -> i:size_nat -> Tot (res:bignum{res <= m}) 
    (decreases (f - i))
let rec shift_euclidean_mod_inv_f m tmp f i =
    if (i < f) then begin
      let tmp = tmp + tmp in
      let tmp = if (m < tmp) then tmp - m else tmp in
      shift_euclidean_mod_inv_f m tmp f (i + 1) end
    else tmp

// u >= v
val shift_euclidean_mod_inv_:
    du:size_nat -> u:bignum -> dv:size_nat{dv <= du} -> v:bignum{v <= u} ->
    r:bignum -> s:bignum -> m:bignum{s < m /\ r < m} -> Tot bignum
    (decreases (du + dv))
    
let rec shift_euclidean_mod_inv_ du u dv v r s m =
    if dv > 1 then begin
      let f = du - dv in
      let (u, f) =
         if (f > 0) then begin
            let v_lshift_f = bn_lshift v f in
            let f = if (u < v_lshift_f) then f - 1 else f in
            let v_lshift_f = bn_lshift v f in
            assume (0 <= u - v_lshift_f);
            let u = u - v_lshift_f in
            (u, f) end
          else (u - v, f) in
	 
      let tmp = if (f > 0) then shift_euclidean_mod_inv_f m s f 0 else s in
      assert (tmp <= m);
      let r = if (r < tmp) then r + m - tmp else r - tmp in
      assume (r < m);

      let du' = degree u du in
      assume (du' < du);
      if (u < v) then begin
        //swap (u, v); swap (r, s)
	assume (du' <= dv);
        shift_euclidean_mod_inv_ dv v du' u s r m end
      else begin
        assume (dv <= du');
        shift_euclidean_mod_inv_ du' u dv v r s m end
    end
    else s
          
//res = a^(-1) % m
val shift_euclidean_mod_inv:
    aBits:size_nat -> a:bignum -> 
    mBits:size_nat{aBits < mBits} -> m:bignum{1 < m /\ a < m} -> Tot bignum
let shift_euclidean_mod_inv aBits a mBits m =
    let r = 0 in
    let s = 1 in
    shift_euclidean_mod_inv_ mBits m aBits a r s m

val mod_exp_:
    x0:size_nat ->
    modBits:size_nat{1 < modBits /\ modBits < pow2 32} ->
    r:nat{r = pow2 (modBits + 2) /\ r > 0} ->
    n:nat{1 < n /\ 4 * n < r /\ r < pow2 (pow2 x0)} -> n':bignum ->
    a:elem (n + n) -> b:nat -> acc:elem (n + n) -> Pure (elem (n + n))
    (requires True)
    (ensures (fun res -> res % n == ((pow a b) * acc / pow r b) % n))
    (decreases b)

#reset-options "--z3rlimit 150 --max_fuel 2"

let rec mod_exp_ x0 modBits r n n' a b acc =
    if b = 0
    then acc
    else begin
        let a2 = mul_mod_mont x0 modBits r n n' a a in
        let b2 = bn_div2 b in
        lemma_div_mod b 2;
        if (bn_is_even b) then begin
            assert (b = 2 * b2);
            let res = mod_exp_ x0 modBits r n n' a2 b2 acc in
            assert (res % n == ((pow a2 b2) * acc / pow r b2) % n); //from ind hypo
            lemma_mod_exp n a a2 b b2 acc r res;
            res end
        else begin
            assert (b = 2 * b2 + 1);
            let acc' = mul_mod_mont x0 modBits r n n' a acc in
            let res = mod_exp_ x0 modBits r n n' a2 b2 acc' in
            assert (res % n == ((pow a2 b2) * acc' / pow r b2) % n); //from ind hypo
            lemma_mod_exp_1 n a a2 b b2 acc acc' r res;
            res end
        end

val mod_exp:
    x0:size_nat ->
    modBits:size_nat{1 < modBits /\ modBits + 3 < pow2 32} ->
    n:bignum{1 < n /\ n < pow2 modBits /\ pow2 (modBits + 2) < pow2 (pow2 x0)} ->
    a:elem n -> b:bignum -> Pure (elem n)
    (requires True)
    (ensures (fun res -> res == (pow a b) % n))

#reset-options "--z3rlimit 150 --max_fuel 0"

let mod_exp x0 modBits n a b =
    let r = pow2 (2 + modBits) in
    lemma_r_n modBits r n;
    let n' = shift_euclidean_mod_inv modBits n (3 + modBits) r in
    let r2 = (r * r) % n in
    let a_r = to_mont modBits r n n' r2 a in
    let acc_r = to_mont modBits r n n' r2 1 in
    let res_r = mod_exp_ x0 modBits r n n' a_r b acc_r in
    lemma_mod_exp_2 n a a_r b acc_r r res_r;
    let res = from_mont modBits r n n' res_r in
    lemma_mod_mult_div_1 res_r r n;
    lemma_mod_mult_div_1 ((pow a b) * r) r n;
    multiple_division_lemma (pow a b) r;
    res

val rsa_blinding:
    x0:size_nat ->
    modBits:size_nat{1 < modBits /\ modBits + 3 < pow2 32} ->
    n:bignum{1 < n /\ n < pow2 modBits /\ pow2 (modBits + 2) < pow2 (pow2 x0)} ->
    p:elem n{1 < p} ->
    q:elem n{1 < q /\ n = p * q} ->
    d:elem n{1 < d} ->
    m:elem n ->
    rBlind:bignum{rBlind < pow2 64} -> Tot (s:bignum{s == (pow m d) % n})

let rsa_blinding x0 modBits n p q d m rBlind =
    let phi_n:nat = (p - 1) * (q - 1) in
    let d':nat = d + rBlind * phi_n in
    let s = mod_exp x0 modBits n m d' in
    assert (s == (pow m d') % n);
    lemma_exp_blinding n phi_n p q d m rBlind;
    assert (s == (pow m d) % n);
    s

(* BIGNUM CONVERT FUNCTIONS *)
val os2ip:bLen:size_nat{bLen > 0} -> b:lbytes bLen -> Tot (res:bignum{res < pow2 (8 * bLen)})
let os2ip bLen b = nat_from_intseq_be #U8 #bLen b

val i2osp:n:bignum -> bLen:size_nat{n < pow2 (8 * bLen)} -> b:lbytes bLen -> Tot (lbytes bLen)
let i2osp n bLen b = nat_to_bytes_be bLen n
