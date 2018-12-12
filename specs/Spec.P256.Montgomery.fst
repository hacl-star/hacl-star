module Spec.P256.Montgomery

open FStar.Math.Lib
open FStar.Math.Lemmas

open FStar.Mul
open Lib.IntTypes
open Lib.RawIntTypes
open Lib.Sequence
open Lib.ByteSequence
open Lib.NatMod
open Lib.LoopCombinators



#reset-options "--max_fuel 0 --z3rlimit 20"


val p256_prime_value: n : nat -> Lemma
  (requires (n = 256))
  (ensures (pow2 n - pow2 224 + pow2 192 + pow2 96 -1 = 0xffffffff00000001000000000000000000000000ffffffffffffffffffffffff))
  [SMTPat (pow2 n - pow2 224 + pow2 192 + pow2 96 - 1)]

let p256_prime_value n =
  assert_norm(pow2 256 - pow2 224 + pow2 192 + pow2 96 - 1 = 0xffffffff00000001000000000000000000000000ffffffffffffffffffffffff)



let prime = pow2 256 - pow2 224 + pow2 192 + pow2 96 - 1

val p256_prime_value_inverse: prime : nat ->  Lemma
  (requires (prime = 0xffffffff00000001000000000000000000000000ffffffffffffffffffffffff))
  (ensures (prime - 2 = 0xffffffff00000001000000000000000000000000fffffffffffffffffffffffd))
  [SMTPat (prime - 2)]


let p256_prime_value_inverse prime =
  assert_norm(pow2 256 - pow2 224 + pow2 192 + pow2 96 - 3 = 0xffffffff00000001000000000000000000000000fffffffffffffffffffffffd)






let ( +% ) a b = (a + b) % prime
let ( -% ) a b = (a - b) % prime
let ( *% ) a b = (a * b) % prime



unfold type elem = nat_mod prime

let to_elem x = x `modulo` prime
let from_elem (x:elem) = nat_mod_v x
let zero : elem = to_elem 0
let one  : elem = to_elem 1

val ( **% ) : e: nat -> n: nat{n > 0} -> Tot (r: nat) (decreases n)

let rec ( **% ) e n =
  if n = 1 then e
  else
    if n % 2 = 0 then
    begin
      (e *% e) **% (n / 2)
    end
    else e *% ((e *% e) **% ((n-1)/2))


let modp_inv (x: nat {x < prime}) : Tot (r: nat{r < prime}) =
  (x **% (prime - 2)) % prime


let modp_inv2 (x: nat) : Tot (r: nat {r < prime}) =
  let x = x % prime in
  modp_inv x


type scalar = lbytes 32

type jacobianNat = | JacobianNat: xN: elem -> yN: elem -> zN: elem -> jacobianNat

let point_compare p q =
  p.xN = q.xN && p.yN = q.yN && p.zN = q.zN

let pointAtInfinity = JacobianNat 1 1 0



(* P256 multipplication parameters *)

let l: elem = to_elem 256
let s: elem = to_elem 64
let k: elem = to_elem 4
let k0: elem = to_elem 1
let mask: elem = to_elem 18446744073709551615

let a: elem = to_elem (0xffffffff00000001000000000000000000000000fffffffffffffffffffffffc)
let ( >> ) a b = arithmetic_shift_right a b



val toDomain: value: elem -> Tot (r: elem)
let toDomain value =  value *% (pow2 l)


val pointToDomain: p: jacobianNat -> Tot jacobianNat
let pointToDomain p =
  let x = toDomain p.xN in
  let y = toDomain p.yN in
  let z = toDomain p.zN in
  JacobianNat x y z


#reset-options "--max_fuel 0 --z3rlimit 1000"

(* prime = 2 ** 256 - 2**  224 + 2** 192 + 2**  96 -1

bn1 = prime * prime
t2Bound = 2**64 * prime

bn2 = bn1 + t2Bound
tFirstIterationBound = bn2 >> 64

bn3 = tFirstIterationBound + t2Bound
tSecondIterationBound = bn3 >> 64

bn4 = tSecondIterationBound + t2Bound
tThirdIterationBound = bn4 >> 64

bn5 = tThirdIterationBound + t2Bound
tForthIterationBound = bn5 >> 64

tForthIterationBound - prime >= prime *)

(*)
val k0_correct: unit -> Lemma(ensures (-1 * p_inv) % pow2 s = 1)
let k0_correct () = ()



val k0_correct2: a: nat-> Lemma(ensures (forall (a: nat). (((a * 1) % pow2 s) * prime)% pow2 s = (-a) % pow2 s))

let k0_correct2 a =
  assert_norm((((a * 1) % pow2 s) * prime)%pow2 s = (a * 1 * prime) % pow2 s);
  assert(1 = (-1 * p_inv) % pow2 s);
  assert(a * 1 * prime = a * ((-1 * p_inv)%pow2 s) * prime);
  assert((((a * 1) % pow2 s) * prime) % pow2 s = (-1 * a) % pow2 s);
  assert((a * prime)%pow2 s = (-1 * a) % pow2 s);
  assert((((a * 1) % pow2 s) * prime) % pow2 s = (-1 * a) % pow2 s);
  ()

*)

assume val lemma1: a: nat -> b: nat ->c: nat ->
  Lemma (requires (a % prime = b % prime)) (ensures ((a * c) % prime = (b * c) % prime))

#reset-options "--max_fuel 0 --z3rlimit 100"


assume val modulo_distributivity_mult: a: int -> b: int -> c: pos -> Lemma ((a * b) % c = ((a % c) * (b % c)) % c)

val lemma2: t3: nat{ exists (k: nat) . k * pow2 64 = t3} -> Lemma (ensures (t3 * modp_inv2 (pow2 64) % prime = (t3 / pow2 64) % prime))

let lemma2 t3 =
  let t_new = t3 * modp_inv2 (pow2 64) % prime in
  let remainder = t3 / pow2 64 in
  assert(remainder * pow2 64 = t3);
  assert(t_new = t3 * modp_inv2 (pow2 64) % prime);
  assert(t_new = remainder * pow2 64 * modp_inv2 (pow2 64) % prime);
  assert_norm(modp_inv2 (pow2 64) * pow2 64 % prime = 1);
  modulo_distributivity_mult remainder (modp_inv2 (pow2 64) * pow2 64) prime;
  assert(t_new = remainder * ((modp_inv2 (pow2 64) * pow2 64) % prime) % prime);
  assert(t_new = remainder % prime);
  assert(t_new = (t3 / pow2 64) % prime);
  assert(t3 * modp_inv2 (pow2 64) % prime = (t3/ pow2 64) % prime);
  ()


#reset-options "--z3rlimit 1000"

(*)
val mult_one_round: a: elem -> b: elem -> Tot unit

let mult_one_round a b =
  let inv_value = modp_inv2 (pow2 s) in
  let t = a * b in
  let k0 = 1 in
  let t1 = t % pow2 s in
  let t2 = t1 * prime in
  let t3 = t + t2 in
    assert(t3 % prime = (a * b) % prime);
  let t = t3 / pow2 s in
    assert(let rem = t3 / pow2 s in rem * pow2 s = t3);
    assert(exists (k: nat). k * pow2 64 = t3);
    lemma2 t3;
    assert(t3 * modp_inv2 (pow2 64) % prime = (t3 / pow2 64) % prime);
    lemma1 t3 (a * b) (modp_inv2 (pow2 64));
    assert(a * b * modp_inv2 (pow2 64) % prime = t3 * modp_inv2 (pow2 64) % prime);
    assert(a * b * modp_inv2 (pow2 64) % prime = (t3/ pow2 64) % prime);
  ()
*)

val mult_one_round2: t: nat -> co: nat {t % prime = co % prime} -> Lemma(ensures (let result = (t + (t % pow2 s) * prime) / pow2 64 % prime in result = (co * modp_inv2 (pow2 64)) % prime))

let mult_one_round2 t co =
    let t1 = t % pow2 s in
    let t2 = t1 * prime in
    let t3 = t + t2 in
      assert(t3 % prime = (co % prime));
    let t = t3/ pow2 s in
      assert(let rem = t3/ pow2 s in rem * pow2 s = t3);
      assert(exists (k: nat). k * pow2 64 = t3);
      lemma2 t3;
      assert(t3 * modp_inv2 (pow2 64) % prime = (t3/ pow2 64) % prime);
      lemma1 t3 co (modp_inv2 (pow2 64));
      assert(co * modp_inv2 (pow2 64) % prime = t3 * modp_inv2 (pow2 64) % prime);
      assert(co * modp_inv2 (pow2 64) % prime = (t3/ pow2 64) % prime)

assume val lemma_pow2: a: nat{pow2 a < prime /\ pow2 (2 * a) < prime} -> Lemma (ensures modp_inv2 (pow2 a) * modp_inv2 (pow2 a)= modp_inv2 (pow2 (2 * a)))

assume val lemma_decrease_pow: a: nat -> Lemma (ensures a * modp_inv2 (pow2 64) * modp_inv2 (pow2 64) * modp_inv2 (pow2 64) * modp_inv2 (pow2 64)  % prime = a * modp_inv2 (pow2 256) % prime)


val lemma3: a: nat{a >= prime} -> Lemma (ensures (a - prime) % prime = a % prime)

let lemma3 a =
    let a1 = a - prime in
    assert(a1 % prime = a % prime)


#reset-options "--z3rlimit 1000"

val mult_4: a: elem -> b: elem -> Tot (r: nat {r % prime = a * b * modp_inv2 (pow2 256) % prime})


let mult_4 a b =
  let t = a * b in

  let t1 = t % pow2 s in
  let t2 = t1 * prime in
  let t3 = t + t2 in
  let tU = t3 / pow2 s in

      mult_one_round2 t (a * b);
      assert(tU % prime = (a * b) * modp_inv2 (pow2 64) % prime);

  let t = tU in
  let t1 = t % pow2 s in
  let t2 = t1 * prime in
  let t3 = t + t2 in
  let tU = t3 / pow2 s in

      mult_one_round2 t (a * b * modp_inv2 (pow2 64));
      assert(tU % prime = a * b * modp_inv2 (pow2 64) * modp_inv2 (pow2 64)  % prime);

    let t = tU in
    let t1 = t % pow2 s in
    let t2 = t1 * prime in
    let t3 = t + t2 in
    let tU = t3 / pow2 s in

  mult_one_round2 t (a * b * modp_inv2 (pow2 64) * modp_inv2 (pow2 64));
  assert(tU % prime = a * b * modp_inv2 (pow2 64) * modp_inv2 (pow2 64) * modp_inv2 (pow2 64)  % prime);

    let t = tU in
    let t1 = t % pow2 s in
    let t2 = t1 * prime in
    let t3 = t + t2 in
    let tU = t3 / pow2 s in

        mult_one_round2 t (a * b * modp_inv2 (pow2 64) * modp_inv2 (pow2 64) * modp_inv2 (pow2 64));
  lemma_decrease_pow (a * b);
  assert(tU % prime = a * b * modp_inv2 (pow2 256) % prime);

    if tU >=prime then begin
      lemma3 tU;
      tU - prime
      end
    else
      tU


(*

val multWithoutRepeat: a: elem -> b: elem -> Tot (r: elem)

let multWithoutRepeat a b =
  let bn1 = 13407807923699100001122556707991011683559799356310572525877692089795444101264856492920909653436852883666100269727622878890045236257577588884142429726310401 in
  let bn2 = 13407807923699100001122556707991011683559799356310572525879828076830867688110957520074161139498732338333366615756263173668010836255337225357436353790345217 in
  let tFirstIterationBound = 726838723957146234646922543795459345351915123539634693411699540093192885385534438191647176751948911063920718317292499507107740990308351 in
  let bn3 = 726838723957146234646922543795459345354051110575058280257800567246444371447413892858913522780589205841886318315052135980401665054343167 in
  let tSecondIterationBound = 39402006178046490290766429114025130417260119756792410939630808911027561397078807211848557717238602867147307258740734 in
  let bn4 = 39402006178046490292902416149448717263361146910043897001510263578293907425719101989814157714998239340441231322775550 in
  let tThirdIterationBound = 2135987034926263610038616778727172560020726168014112598433205490770927735290563605870411323015166 in
  let bn5 = 4271974070349850456139643931978658621900180835280458627073500268736527733050200079164335387049982 in
  let tForthIterationBound = 231584178393752550877075559305923669353688162772718244109075031233358785937406 in

  let t2Bound = 2135987035423586846101027153251486061879454667266346028640294777965599997759636473293924064034816 in

  assert_norm (prime * prime = bn1);

  let pow512 = pow2 512 in
  let mask = pow2 s in

  let t = a * b in
    lemma_mult_lt_sqr a b prime;
    assert(t < bn1);
  let t1 = t % mask in
    assert(t1 < pow2 64);
  let t2 = t1 * prime in
    assert_norm(pow2 64 * prime = t2Bound);
    assert(t2 < t2Bound);
  let t3 = t + t2 in
    assert_norm(bn1 + t2Bound = bn2);
    assert(t3 < bn2);
  let t = t3 >> s in
    assert_norm(bn2 >> 64 = tFirstIterationBound);
    assert(t < tFirstIterationBound);



  let t1 = t % mask in
    assert(t1 < pow2 64);
  let t2 = t1 * prime in
    assert_norm(pow2 64 * prime = t2Bound);
    assert(t2 < t2Bound);
  let t3 = t + t2 in
    assert_norm(tFirstIterationBound + t2Bound = bn3);
    assert(t3 < bn3);
  let t = t3 >> s in
    assert_norm(bn3 >> s = tSecondIterationBound);
    assert(t < tSecondIterationBound);


  let t1 = t % mask in
    assert(t1 < pow2 64);
  let t2 = t1 * prime in
    assert_norm(pow2 64 * prime = t2Bound);
    assert(t2 < t2Bound);
  let t3 = t + t2 in
    assert_norm(tSecondIterationBound + t2Bound = bn4);
    assert(t3 < bn4);
  let t = t3 >> s in
    assert_norm(bn4 >> 64 = tThirdIterationBound);
    assert(t < tThirdIterationBound);


  let t1 = t % mask in
    assert(t1 < pow2 64);
  let t2 = t1 * prime in
    assert_norm(pow2 64 * prime = t2Bound);
    assert(t2 < t2Bound);
  let t3 = t + t2 in
    assert_norm(tThirdIterationBound + t2Bound = bn5);
    assert(t3 < bn5);
  let t = t3 >> s in
    assert_norm(bn5 >> 64 = tForthIterationBound);
    assert(t < tForthIterationBound);

  if t >=prime then
    begin
      assert(t - prime < prime);
      t - prime
    end
  else
    t
*)

val multWithoutRepeat: a: elem -> b: elem -> Tot nat

let multWithoutRepeat a b =
  mult_4 a b

val mult1 : a: elem -> b: elem -> Tot (r: elem)

let mult1 a b = mult_4 a b


val fromDomain: p : jacobianNat -> Tot jacobianNat

let fromDomain p =
  let x = mult1 p.xN 1 in
  let y = mult1 p.yN 1 in
  let z = mult1 p.zN 1 in
  JacobianNat x y z


val square: a: elem -> Tot (r: elem)

let square a =
  multWithoutRepeat a a


val cube: a: elem -> Tot (r: elem)

let cube a =
  multWithoutRepeat a (square a)


val quatre: a: elem -> Tot (r: elem)

let quatre a =
  square (square a)


val multByTwo: value: elem -> Tot (r: elem{r = (value * 2) % prime})

let multByTwo value =
  let shiftedValue = shift_left value 1 in
  if shiftedValue < prime then
    shiftedValue
  else
    shiftedValue - prime


val multByThree: value: elem -> Tot (r: elem{r = (value * 3) % prime})

let multByThree value =
  let byTwo = multByTwo value in
  let byThree = byTwo + value in
  if byThree < prime then
    byThree
  else
    byThree - prime


val multByFour: value: elem -> Tot (r: elem {r = (value * 4) % prime})

let multByFour value =
  let shiftedValue = shift_left value 2 in
  assert(shiftedValue < 4 * prime);
  if shiftedValue < prime then shiftedValue else
    let shiftedValue = shiftedValue - prime in
    assert(shiftedValue < 3 * prime);
    if shiftedValue < prime then shiftedValue else
      let shiftedValue = shiftedValue - prime in
      assert(shiftedValue < 2* prime);
      if shiftedValue < prime then shiftedValue else
        let shiftedValue = shiftedValue - prime in
        assert(shiftedValue < prime);
        shiftedValue


val multByEight: value: elem -> Tot (r: elem {r = (value * 8) % prime})

let multByEight value =
  let shiftedValue = shift_left value 3 in
  assert(shiftedValue < 8 * prime);
  if shiftedValue < prime then shiftedValue else
    let shiftedValue = shiftedValue - prime in
    assert(shiftedValue < 7 * prime);
    if shiftedValue < prime then shiftedValue else
      let shiftedValue = shiftedValue - prime in
      assert(shiftedValue < 6 * prime);
      if shiftedValue < prime then shiftedValue else
        let shiftedValue = shiftedValue - prime in
        assert(shiftedValue < 5 * prime);
        if shiftedValue < prime then shiftedValue else
          let shiftedValue = shiftedValue - prime in
          assert(shiftedValue < 4 * prime);
          if shiftedValue < prime then shiftedValue else
            let shiftedValue = shiftedValue - prime in
            assert(shiftedValue < 3 * prime);
            if shiftedValue < prime then shiftedValue else
              let shiftedValue = shiftedValue - prime in
              assert(shiftedValue < 2 * prime);
              if shiftedValue < prime then shiftedValue else
                let shiftedValue = shiftedValue - prime in
                assert(shiftedValue < prime);
                shiftedValue


val multByMinusThree: value: elem -> Tot (r: elem {r = (-3 * value) % prime})
let multByMinusThree value =
  let byThree = multByThree value in
  prime -% byThree


val _point_double: p: jacobianNat-> Tot jacobianNat
let _point_double p =
  if p = pointAtInfinity then p else

  let x = p.xN in
  let y = p.yN in
  let z = p.zN in

  let s = multByFour (multWithoutRepeat x (square y)) in
  let m = multByThree (square x) +% multByMinusThree (quatre z) in
  let x3 = square m -% multByTwo s in
  let y3 = multWithoutRepeat m (s -% x3) -% multByEight (quatre y) in
  let z3 = multByTwo (multWithoutRepeat y z) in
  JacobianNat x3 y3 z3


val _point_add: p: jacobianNat -> q: jacobianNat -> Tot jacobianNat

let _point_add p q =
  if p = pointAtInfinity then q else
  if q = pointAtInfinity then p else
  let x1 = p.xN in
  let y1 = p.yN in
  let z1 = p.zN in

  let x2 = q.xN in
  let y2 = q.yN in
  let z2 = q.zN in

  let u1 = multWithoutRepeat x1 (square z2) in
  let u2 = multWithoutRepeat x2 (square z1) in
  let s1 = multWithoutRepeat y1 (cube z2) in
  let s2 = multWithoutRepeat y2 (cube z1) in

  if u1 = u2 then
    if s1 <> s2 then
      pointAtInfinity
    else
      _point_double p
  else
    let h = u2 -% u1 in
    let r = s2 -% s1 in
    let x3 = square r -% cube h -%   multByTwo (multWithoutRepeat u1 (square h)) in
    let y3 = multWithoutRepeat r ((multWithoutRepeat u1 (square h))  -% x3) -% multWithoutRepeat s1 (cube h) in
    let z3 = multWithoutRepeat h (multWithoutRepeat z1 z2) in
    JacobianNat x3 y3 z3


#reset-options "--max_fuel 0 --z3rlimit 100"

let ith_bit (k:scalar) (i:nat{i < 256}) : uint8 =
  let (&.) = logand #U8 in
  let q = i / 8 in let r = size (i % 8) in
  (k.[q] >>. r) &. u8 1


val montgomery_ladder_ : r0: jacobianNat ->  r1: jacobianNat ->
  k: scalar -> counter: nat{counter < 256} -> Tot jacobianNat (decreases counter)

let rec montgomery_ladder_ r0 r1 k counter =
  let (r0, r1) =
    if uint_to_nat #U8 (ith_bit k counter) = 1 then
      (_point_add r0 r1, _point_double r1)
    else
      (_point_double r0, _point_add r0 r1)
    in
  if counter > 0 then
    montgomery_ladder_ r0 r1 k (counter - 1)
  else
    r0


val montgomery_ladder: point: jacobianNat -> k: scalar -> Tot jacobianNat

let montgomery_ladder point k =
  let r0 = pointAtInfinity in
  let r1 = pointToDomain point in
  let r0 = montgomery_ladder_ r0 r1 k 255 in
  fromDomain r0


let norm p =
  let z2 = (p.zN * p.zN) % prime in
  let z2i = modp_inv2 z2 in
  let z3 = (p.zN * p.zN * p.zN) % prime in
  let z3i = modp_inv2 z3 in
  JacobianNat (p.xN *% z2i) (p.yN *% z3i) 1
