module Hacl.Argmax.GM

open FStar.ST
open FStar.Array
open FStar.Bytes
open FStar.Math.Lemmas
open FStar.Mul

(* Basic algebra *)

type big = x:int{x > 1}

val fieldEl: #n:big -> a:int -> bool
let fieldEl #n a = a >= 0 && a < n

val prodBigger: p:big -> q:big -> Lemma (p * q > p /\ p * q > q)
let prodBigger p q = ()

val toBigger: n:big -> m:big{m >= n} -> a:int -> Lemma (fieldEl #n a ==> fieldEl #m a)
let toBigger n m a = ()

type fe n = x:int{fieldEl #n x}

val toFe: #n:big -> a:pos -> r:fe n{ r = a % n }
let toFe #n a = lemma_mod_lt a n; a % n

type binop = #n:big -> fe n -> fe n -> fe n
val ( +% ): binop
val ( *% ): binop
let ( +% ) #n n1 n2 = (n1 + n2) % n
let ( *% ) #n n1 n2 = (n1 * n2) % n

val ( **% ): #n:big -> fe n -> e:fe n -> Tot (fe n) (decreases e)
let rec ( **% ) #n g e =
  if e = 1 then g
  else if e = 0 then 1
  else
     if n % 2 = 0
       then (g *% g) **% (e / 2)
       else g *% ((g *% g) **% ((e - 1) / 2))

(* Quadratic reciprocity *)

val isSquare: #p:big -> s:fe p -> a:fe p -> r:bool
let isSquare #p s a = (op_Multiply s s) % p = a % p

val isLegSymbol: #p:big -> a:fe p -> l:int -> Type0
let isLegSymbol #p a l =
  if l = 1
  then exists s. b2t(isSquare s a)
  else if l = (-1)
  then forall s. ~(b2t(isSquare s a))
  else if l = 0
  then b2t(a = 0)
  else b2t(false)

val legSymbol: #p:big -> a:fe p -> res:int{isLegSymbol a res}
let legSymbol #p a = admit(); ( **% ) #p a ((p-1)/2)

(* Parameters *)

type secret =
  | Secret: p:big
         -> q:big{q <> p}
         -> y:fe (p * q){forall s. ~(isSquare s y)}
         -> secret

type public =
  | Public: n:big{exists (p:big) (q:big). n = p * q}
         -> y:fe n{forall s. ~(isSquare s y)}
         -> public

val s2p: secret -> public
let s2p sec =
  Public (Secret?.p sec * Secret?.q sec)
         (Secret?.y sec)

(* Enc/Dec *)

type ciphertext (n:big) = c:fe n{c > 0 && legSymbol c <> 0}

val encrypt:
     p:public
  -> r:fe (Public?.n p){r>0}
  -> m:bool
  -> c:ciphertext (Public?.n p)
let encrypt p r m =
  let c = (r *% r) *% (if m then Public?.y p else 1) in
  assume(c > 0 && legSymbol c <> 0);
  c

val decrypt: s:secret -> c:ciphertext (Public?.n (s2p s)) -> m:bool
let decrypt s c =
  let v1 = legSymbol #(Secret?.p s) (toFe c) in
  let v2 = legSymbol #(Secret?.q s) (toFe c) in
  v1 = 1 && v2 = 1
