module Hacl.Argmax.GM

open FStar.Array
open FStar.Bytes
open FStar.Classical
open FStar.Math.Lemmas
open FStar.Math.Lib
open FStar.Mul
open FStar.ST


(* Primes and composite numbers *)

type big = x:int{x > 1}

val isprm: p:big -> bool
let isprm _ = admit()

type prm = n:big{isprm n}

val iscomp: n:big -> Type0
let iscomp n = exists (p:prm) (q:prm). n = p * q

type comp = n:big{iscomp n}


(* Basic algebra *)

val fieldEl: #n:big -> a:int -> bool
let fieldEl #n a = a >= 0 && a < n

val prodBigger: p:big -> q:big -> Lemma (p * q > p /\ p * q > q)
let prodBigger p q = ()

val toBigger: n:big -> m:big{m >= n} -> a:int -> Lemma (fieldEl #n a ==> fieldEl #m a)
let toBigger n m a = ()

type fe n = x:int{fieldEl #n x}

val toFe: #n:big -> a:nat -> r:fe n
let toFe #n a = lemma_mod_lt a n; a % n

type binop = #n:big -> fe n -> fe n -> fe n
val ( +% ): binop
val ( *% ): binop
let ( +% ) #n n1 n2 = (n1 + n2) % n
let ( *% ) #n n1 n2 = (n1 * n2) % n

val sqr: #n:big -> fe n -> fe n
let sqr #n a = a *% a

val mulOne: #n:big -> a:fe n -> Lemma (ensures (a *% 1 = a)) [SMTPat (a *% a)]
let mulOne #n a = ()

val fexp: #n:big -> fe n -> e:fe n -> Tot (fe n) (decreases e)
let rec fexp #n g e =
  if e = 1 then g
  else if e = 0 then 1
  else
     if n % 2 = 0
     then fexp (g *% g) (e / 2)
     else fexp (g *% g) ((e - 1) / 2) *% g

(* Quadratic reciprocity *)

val isSq: #n:big -> a:fe n -> Type0
let isSq #n a = exists s . b2t(sqr s = a)

val isNonsq: #n:big -> a:fe n -> Type0
let isNonsq #n a = forall s. b2t(sqr s <> a)

// Legendre/Jacobi symbol
val legSymbol: #n:big -> a:fe n -> res:int
let legSymbol #n a = fexp a ((n-1)/2)

val isLegSymbol: #n:big -> a:fe n -> Lemma
  (ensures (let l = legSymbol a in
              //(l = 1 \/ l = 0 \/ l = -1) \/
              (l = 1 <==> (isSq a /\ a <> 0)) \/
              (l = (-1) <==> (isNonsq a /\ a <> 0)) \/
              (l = 0 \/ b2t(a = 0))))
  [SMTPat (legSymbol a)]
let isLegSymbol #n _ = admit()

val legSymbolComp: p:prm -> q:prm -> a:fe (p * q) -> Lemma
  (ensures (legSymbol a = legSymbol #p (toFe #p a) * legSymbol #q (toFe #q a)))
let legSymbolComp _ _ _ = admit()

#reset-options

val canSplitMulSq: #n:comp -> a:fe n{isSq a /\ a <> 0} -> b:fe n{b <> a && b <> 0} -> Lemma
  (ensures (isSq (a *% b) ==> isSq b))
let canSplitMulSq #n a b =
  assert(forall (x: fe n). (isLegSymbol #n x; legSymbol x = 1) <==> isSq x);
  admit();
  //assert(isSq (a *% b) ==> legSymbol (a *% b) = 1);
  admit()

val mulSqNonsq: #n:big -> a:fe n{isSq a} -> b:fe n{isNonsq b} -> Lemma
  (ensures (isNonsq (a *% b)))
  [SMTPat (a *% b)]
let mulSqNonsq #n a b =
  assert(~(exists s. b2t (sqr s = b)));
  assert((exists s. b2t (sqr s = b)) ==> false);
  canSplitMulSq a b;
  assert(isSq (a *% b) ==> isSq b)

(* Parameters *)

type secret =
  | Secret: p:prm
         -> q:prm{q <> p}
         -> y:fe (p * q){isNonsq y}
         -> secret

type public =
  | Public: n:comp
         -> y:fe n{isNonsq y}
         -> public

val s2p: secret -> public
let s2p sec =
  Public (Secret?.p sec * Secret?.q sec)
         (Secret?.y sec)

(* Enc/Dec *)

type ciphertext (n:big) = c:fe n{c > 0 && legSymbol c <> 0}

#reset-options
// #set-options "--z3rlimit 100 --initial_fuel 5 --max_fuel 5 --initial_ifuel 2 --max_ifuel 2"

val encrypt:
     p:public
  -> r:fe (Public?.n p){r>0}
  -> m:bool
  -> c:ciphertext (Public?.n p)
let encrypt p r m =
  let n = Public?.n p in
  let extra: fe n = if m then Public?.y p else 1 in
  let c = (r *% r) *% extra in
  assert(if m then isNonsq c else isSq c);
  assert(if m then isNonsq c else isSq c);

  assume(c > 0 && legSymbol c <> 0);
  c

val decrypt: s:secret -> c:ciphertext (Public?.n (s2p s)) -> m:bool
let decrypt s c =
  let v1 = legSymbol #(Secret?.p s) (toFe c) in
  let v2 = legSymbol #(Secret?.q s) (toFe c) in
  v1 = 1 && v2 = 1

val encDecId: s:secret -> r:fe (Public?.n (s2p s)){r>0} -> m:bool -> Lemma
  (decrypt s (encrypt (s2p s) r m) = m)
let encDecId s r m = admit()
