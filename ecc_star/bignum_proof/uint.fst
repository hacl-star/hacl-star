module UInt

open Parameters
open FStar.Ghost
open IntLib

// Coercion function between Ghost + unit and lemma
effect GLemma (a:Type) (pre:Type) (post:Type) (pats:list pattern) =
       Ghost a pre (fun r -> post)

assume val coerce: pre:Type -> post:Type -> g:(unit -> Ghost unit pre (fun r -> post)) -> Pure unit pre (fun r -> post)

(* Machine integers as abstract type *)
type sint

(* Mathematical value of the machine integer *)
assume val v: sint -> GTot int

(* Bound on a natural integer *)
val bitsize: x:int -> n:nat -> GTot bool
let bitsize x n = (x >= 0 && x < pow2 n)

(* Unsigned integers of n bits *)
type usint (n:nat) = x:sint{bitsize (v x) n}

(* Concrete types (realized in concrete modules) *)
type limb = usint platform_size
type wide = usint platform_wide
type byte = usint 8

(* Zeros of various sizes *)
assume val zero_byte: z:byte{v z = 0 }
assume val zero_limb: z:limb{v z = 0 }
assume val zero_wide: z:wide{v z = 0 }

(* Ones of various sizes *)
assume val one_byte: o:byte{v o = 1 }
assume val one_limb: o:limb{v o = 1 }
assume val one_wide: o:wide{v o = 1 }

(* All-ones of various sizes *)
assume val ones_byte: o:byte{v o = pow2 8 - 1 }
assume val ones_limb: o:limb{v o = pow2 platform_size - 1 }
assume val ones_wide: o:wide{v o = pow2 platform_wide -1 }

(* Conversion functions *)
assume val byte_to_limb: x:byte -> Tot (y:limb{v y = v x})
assume val limb_to_byte: x:limb -> Tot (y:byte{v y = v x % pow2 8})
assume val byte_to_wide: x:byte -> Tot (y:wide{v y = v x})
assume val wide_to_byte: x:wide -> Tot (y:byte{v y = v x % pow2 8})
assume val limb_to_wide: x:limb -> Tot (y:wide{v y = v x})
assume val wide_to_limb: x:wide -> Tot (y:limb{v y = v x % pow2 platform_size})

(* Hardcoding of constants *)
assume val to_limb: string -> Tot limb
assume val to_wide: string -> Tot wide

(* Mathematical representation of those values *)
val byte_to_nat: byte -> GTot nat
let byte_to_nat b = v b
val limb_to_nat: limb -> GTot nat
let limb_to_nat l = v l
val wide_to_nat: wide -> GTot nat
let wide_to_nat w = v w

(* Operations for bytes *)
assume val add_byte: byte -> byte -> Tot byte
assume val mul_byte: byte -> byte -> Tot byte
assume val sub_byte: byte -> byte -> Tot byte
assume val div_byte: byte -> byte -> Tot byte
assume val mod_byte: byte -> byte -> Tot byte
assume val neg_byte: byte -> Tot byte
assume val log_and_byte: byte  -> byte -> Tot byte
assume val log_or_byte: byte  -> byte -> Tot byte
assume val log_xor_byte: byte  -> byte -> Tot byte
assume val log_not_byte: byte  -> byte -> Tot byte
assume val to_byte: int -> Tot byte
assume val shift_left_byte: a:byte -> shift:nat -> Tot byte
assume val shift_right_byte: a:byte -> shift:nat -> Tot byte

(* Operations for limbs, no overflow allowed *)
assume val add_limb: 
  x:limb -> y:limb{v x + v y < pow2 platform_size} -> 
  Tot (z:limb{v z = v x + v y})
assume val mul_limb: 
  x:limb -> y:limb{v x * v y < pow2 platform_size} -> 
  Tot (z:limb{v z = v x * v y})
assume val mul_limb_to_wide: 
  x:limb -> y:limb{v x * v y < pow2 platform_wide} -> 
  Tot (z:wide{v z = v x * v y})
assume val sub_limb: 
  x:limb -> y:limb{v y <= v x} -> 
  Tot (z:limb{v z = v x - v y})
assume val sub_mod_limb: 
  x:limb -> y:limb -> 
  Tot (z:limb{v z = (v x - v y) % pow2 platform_size})
assume val div_limb: 
  limb -> y:limb{v y <> 0} -> 
  Tot limb
assume val mod_limb: 
  limb -> y:limb{v y <> 0} -> 
  Tot limb
assume val neg_limb: x:limb -> Tot (z:limb{v x + v z = 0})
assume val log_and_limb: limb  -> limb -> Tot limb
assume val log_or_limb: limb  -> limb -> Tot limb
assume val log_xor_limb: limb  -> limb -> Tot limb
assume val log_not_limb: limb -> Tot limb
assume val shift_left_limb: a:limb -> shift:nat -> Tot (b:limb{v b = (pow2 shift * v a) % pow2 platform_size})
assume val shift_right_limb: a:limb -> shift:nat -> Tot (b:limb{v b = v a / pow2 shift})

(* Operations on the wide words *)
assume val add_wide: 
  x:wide  -> y:wide{v x + v y < pow2 platform_wide} -> 
  Tot (z:wide{v z = v x + v y})
assume val mul_wide:
  x:wide  -> y:wide{v x * v y < pow2 platform_wide} -> 
  Tot (z:wide{v z = v x * v y})
assume val sub_wide: 
  x:wide -> y:wide{v y <= v x} -> 
  Tot (z:wide{v z = v x - v y})
assume val sub_mod_wide: 
  x:wide -> y:wide -> 
  Tot (z:wide{v z = (v x - v y) % pow2 platform_wide})
assume val div_wide: wide -> wide -> Tot wide
assume val mod_wide: wide -> wide -> Tot wide
assume val neg_wide: wide -> Tot wide
assume val log_and_wide: wide -> wide -> Tot wide
assume val log_or_wide: wide -> wide -> Tot wide
assume val log_xor_wide: wide -> wide -> Tot wide
assume val log_not_wide: wide -> Tot wide
assume val shift_left_wide: a:wide -> shift:nat -> Tot (b:wide{v b = (pow2 shift * v a) % pow2 platform_wide})
assume val shift_right_wide: a:wide -> shift:nat -> Tot (b:wide{v b = v a / pow2 shift})

(* Constant time equality tests *)
assume val eq_limb: 
  x:limb -> y:limb -> 
  Tot (z:limb{(v z = 0 /\ v x <> v y) \/ (v z = pow2 platform_size - 1 /\ v x = v y)})
assume val eq_wide: 
  x:wide -> y:wide -> 
  Tot (z:wide{(v z = 0 /\ v x <> v y) \/ (v z = pow2 platform_wide - 1 /\ v x = v y)})
assume val gte_limb: 
  x:limb -> y:limb -> 
  Tot (z:limb{(v z = 0 /\ v x < v y) \/ (v z = pow2 platform_size - 1 /\ v x >= v y)})
assume val gte_wide: 
  x:wide -> y:wide ->
  Tot (z:wide{(v x < pow2 127 /\ v y < pow2 127) ==> ((v z = 0 /\ v x < v y) \/ (v z = pow2 platform_wide - 1 /\ v x >= v y))})

assume val int_to_limb: int -> Tot limb
assume val int_to_wide: int -> Tot wide

(* Abstract values *)
assume val zero: size:pos -> Tot (z:usint size{v z = 0})
assume val one: size:pos -> Tot (o:usint size{v o = 1})

(* Lemmas *)
assume val add_lemma: m:nat -> a:int -> n:nat -> b:int ->
  Lemma (requires (bitsize a m /\ bitsize b n)) (ensures (bitsize (a+b) (max m n + 1)))
assume val sub_lemma: m:nat -> a:int -> b:int ->
  Lemma (requires (bitsize a m /\ b >= 0 /\ b <= a)) (ensures (bitsize (a-b) m))
assume val mul_lemma: m:nat -> a:int -> n:nat -> b:int -> 
  Lemma (requires (bitsize a m /\ bitsize b n)) (ensures (bitsize (a*b) (m+n)))
assume val shift_left_lemma: m:nat -> a:int -> n:nat ->
  Lemma (requires (bitsize a m)) (ensures (bitsize (a * pow2 n) (m+n)))
assume val shift_right_lemma: m:nat -> a:nat -> n:nat ->
  Lemma (requires (bitsize a m)) (ensures (bitsize (a / pow2 n) (max (m-n) 0)))

assume val log_and_wide_lemma_1: a:wide -> b:wide -> Lemma (v (log_and_wide a b) = v (log_and_wide b a))
assume val log_and_wide_lemma_2: a:wide -> b:wide -> Lemma (v (log_and_wide a zero_wide) = 0)
assume val log_and_wide_lemma_3: a:wide -> b:wide -> n:nat -> 
  Lemma (requires (v b = pow2 n - 1)) (ensures (v (log_and_wide a b) = v a % pow2 n))
