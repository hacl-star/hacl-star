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

#reset-options "--z3rlimit 150 --max_ifuel 0 --max_fuel 0"

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

val get_ci: c:bignum -> i:size_nat -> Tot (res:bignum{res < pow2 64})
let rec get_ci c i =
    if (i = 0) then c % pow2 64
    else get_ci (c / pow2 64) (i - 1)

let beta = pow2 64

val beta_i: i:size_nat -> Tot (res:bignum{res = pow2 (64 * i) /\ res > 0})
let beta_i i = pow2 (64 * i)

val lemma_beta_mul_by_beta_i: i:size_nat{i + 1 < max_size_t} -> Lemma
    (requires (True))
    (ensures (beta * beta_i i == beta_i (i + 1)))
let lemma_beta_mul_by_beta_i i = admit()

val lemma_beta_ij_lq: i:size_nat -> j:size_nat -> Lemma
    (requires (i <= j))
    (ensures (beta_i i <= beta_i j))
let lemma_beta_ij_lq i j = admit()

val lemma_mul_lt: a:bignum -> b:bignum{b > 0} -> c:bignum{c > 0} -> Lemma
    (requires (a < b))
    (ensures (a * c < b * c))
let lemma_mul_lt a b c = ()

val mont_reduction_:
    n:bignum{n > 0} -> nInv_u64:bignum{nInv_u64 < beta} ->
    exp_r:size_nat{0 < exp_r /\ exp_r + 1 < max_size_t} ->
    c:bignum ->
    i:size_nat{i <= exp_r}-> Pure bignum
    (requires (True)) //c < c + (beta_i i) * n))
    (ensures (fun res -> res % n == c % n /\ res < c + (beta_i i) * n))
    (decreases (exp_r - i))
    #reset-options "--z3rlimit 150 --max_fuel 2"
let rec mont_reduction_ n nInv_u64 exp_r c i =
    if (i < exp_r) then begin
      let qi = (nInv_u64 * (get_ci c i)) % beta in
      assert (0 <= qi /\ qi < beta);
      let res = c + qi * (beta_i i) * n in
      lemma_mod_plus c (qi * beta_i i) n; // res % n == c % n
      lemma_mul_lt qi beta ((beta_i i) * n);
      assert (res < c + beta * (beta_i i) * n);
      lemma_beta_mul_by_beta_i i;
      assert (res < c + (beta_i (i + 1)) * n); admit();
      //lemma_beta_ij_lq (i + 1) exp_r;
      //assert (beta_i (i + 1) <= beta_i exp_r);
      //assert (res < c + (beta_i exp_r) * n);
      mont_reduction_ n nInv_u64 exp_r res (i + 1)
      end
    else c

val mont_reduction:
    n:bignum{n > 0} -> nInv_u64:bignum{nInv_u64 < beta} ->
    exp_r:size_nat{0 < exp_r /\ exp_r + 1 < max_size_t} -> r:bignum{r == beta_i exp_r} ->
    c:bignum{c < r * n} -> Pure (elem (n + n))
    (requires (True))
    (ensures (fun res -> res % n == (c / r) % n))
    #reset-options "--z3rlimit 150 --max_fuel 0 --max_ifuel 0"
let mont_reduction n nInv_u64 exp_r r c =
    let tmp = mont_reduction_ n nInv_u64 exp_r c 0 in
    assert (tmp % n == c % n /\ tmp < c + (beta_i exp_r) * n);
    let res = tmp / r in
    assert (res % n = (tmp / r) % n);
    lemma_mod_mult_div_1 tmp r n;
    assert ((tmp / r) % n == ((c % n) / r) % n);
    lemma_mod_mult_div_1 c r n;
    //assert (res % n == (c / r) % n);
    assert (tmp < r * n + r * n);
    assert (tmp < r * (n + n));
    division_addition_lemma 0 r (n + n);
    assert (res < n + n);
    res

val mul_mod_mont:
    x0:size_nat ->
    n:bignum{n > 0} -> nInv_u64:bignum{nInv_u64 < beta} ->
    exp_r:size_nat{0 < exp_r /\ exp_r + 1 < max_size_t} -> r:bignum{r == beta_i exp_r /\ 4 * n < r} ->
    a:elem (n + n) -> b:elem (n + n) -> Pure (elem (n + n))
    (requires (True))
    (ensures (fun res -> res % n == (a * b / r) % n))
let mul_mod_mont x0 n nInv_u64 exp_r r a b =
    //let c = karatsuba x0 a b in
    let c = a * b in
    assert (c < 4 * n * n);
    mont_reduction n nInv_u64 exp_r r c

val to_mont:
    x0:size_nat ->
    n:bignum{n > 0} -> nInv_u64:bignum{nInv_u64 < beta} ->
    exp_r:size_nat{0 < exp_r /\ exp_r + 1 < max_size_t} -> r:bignum{r == beta_i exp_r /\ 4 * n < r} ->
    r2:elem n -> a:elem n -> Pure (elem (n + n))
    (requires (r2 == (r * r) % n))
    (ensures (fun res -> res % n == (a * r) % n))

let to_mont x0 n nInv_u64 exp_r r r2 a =
    let c = a * r2 in
    assert (c < n * n);
    assert (c == a * ((r * r) % n));
    let res = mont_reduction n nInv_u64 exp_r r c in
    assert (res % n == ((a * ((r * r) % n)) / r) % n);
    lemma_mod_div_simplify res a r n;
    res

val from_mont:
    x0:size_nat ->
    n:bignum{n > 0} -> nInv_u64:bignum{nInv_u64 < beta} ->
    exp_r:size_nat{0 < exp_r /\ exp_r + 1 < max_size_t} -> r:bignum{r == beta_i exp_r /\ 4 * n < r} ->
    a_r:elem (n + n) -> Pure (elem n)
    (requires (True))
    (ensures (fun res -> res == (a_r / r) % n))

let from_mont x0 n nInv_u64 exp_r r a_r =
    let tmp = mont_reduction_ n nInv_u64 exp_r a_r 0 in
    assert (tmp % n == a_r % n /\ tmp < a_r + (beta_i exp_r) * n);
    let res = tmp / r in
    assert (res % n = (tmp / r) % n);
    lemma_mod_mult_div_1 tmp r n;
    assert ((tmp / r) % n == ((a_r % n) / r) % n);
    lemma_mod_mult_div_1 a_r r n;
    assert (tmp < r + r * n);
    assert (tmp < r * (1 + n));
    division_addition_lemma 0 r (1 + n);
    assert (res < 1 + n); admit(); //todo: if res < n then small_modulo_lemma_1
    res

val mod_inv_u64_:
    alpha:uint64 -> beta:uint64 ->
    ub:uint64 -> vb:uint64 -> i:size_nat{i <= 64} -> Tot uint64
    (decreases (64 - i))
let rec mod_inv_u64_ alpha beta ub vb i =
    if (i < 64) then begin
      let u_is_odd = u64 0 -. (ub &. u64 1) in
      let beta_if_u_is_odd = beta &. u_is_odd in
      let ub = ((ub ^. beta_if_u_is_odd) >>. (u32 1)) +. (ub &. beta_if_u_is_odd) in

      let alpha_if_u_is_odd = alpha &. u_is_odd in
      let vb = (shift_right #U64 vb (u32 1)) +. alpha_if_u_is_odd in
      mod_inv_u64_ alpha beta ub vb (i + 1) end 
    else vb

val mod_inv_u64: n0:uint64 -> Tot uint64
let mod_inv_u64 n0 =
    let alpha = shift_left #U64 (u64 1) (u32 63) in
    let beta = n0 in

    let ub = u64 1 in
    let vb = u64 0 in
    mod_inv_u64_ alpha beta ub vb 0
  
val mod_exp_:
    x0:size_nat ->
    n:bignum{n > 1} -> nInv_u64:bignum{nInv_u64 < beta} ->
    exp_r:size_nat{0 < exp_r /\ exp_r + 1 < max_size_t} -> r:bignum{r == beta_i exp_r /\ 4 * n < r} ->
    a:elem (n + n) -> b:bignum -> acc:elem (n + n) -> Pure (elem (n + n))
    (requires True)
    (ensures (fun res -> res % n == ((pow a b) * acc / pow r b) % n))
    (decreases b)
    #reset-options "--z3rlimit 150 --max_fuel 2"
let rec mod_exp_ x0 n nInv_u64 exp_r r a b acc =
    if b = 0
    then acc
    else begin
        let a2 = mul_mod_mont x0 n nInv_u64 exp_r r a a in
        let b2 = bn_div2 b in
        lemma_div_mod b 2;
        if (bn_is_even b) then begin
            assert (b = 2 * b2);
	    let res = mod_exp_ x0 n nInv_u64 exp_r r a2 b2 acc in
            assert (res % n == ((pow a2 b2) * acc / pow r b2) % n); //from ind hypo
            lemma_mod_exp n a a2 b b2 acc r res;
            res end
        else begin
            assert (b = 2 * b2 + 1);
            let acc' = mul_mod_mont x0 n nInv_u64 exp_r r a acc in
            let res = mod_exp_ x0 n nInv_u64 exp_r r a2 b2 acc' in
            assert (res % n == ((pow a2 b2) * acc' / pow r b2) % n); //from ind hypo
            lemma_mod_exp_1 n a a2 b b2 acc acc' r res;
            res end
        end

val mod_exp:
    x0:size_nat -> modBits:size_nat{modBits > 0} ->
    n:bignum{n > 1} -> a:elem n -> b:bignum -> Pure (elem n)
    (requires True)
    (ensures (fun res -> res == (pow a b) % n))
    #reset-options "--z3rlimit 150 --max_fuel 0"
let mod_exp x0 modBits n a b =
    let nLen = (modBits - 1) / 64 + 1 in
    let exp_r = nLen + 1 in
    let r = beta_i exp_r in
    assume (4 * n < r);
    let n0 = n % pow2 64 in
    let n' = mod_inv_u64 (u64 n0) in
    let nInv_u64 = uint_to_nat #U64 n' in
    let r2 = (r * r) % n in
    let a_r = to_mont x0 n nInv_u64 exp_r r r2 a in
    let acc_r = to_mont x0 n nInv_u64 exp_r r r2 1 in
    let res_r = mod_exp_ x0 n nInv_u64 exp_r r a_r b acc_r in
    lemma_mod_exp_2 n a a_r b acc_r r res_r;
    let res = from_mont x0 n nInv_u64 exp_r r res_r in
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
