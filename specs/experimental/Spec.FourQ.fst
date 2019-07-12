module Spec.FourQ

open FStar.Mul
open Lib.IntTypes
open Lib.RawIntTypes
open Lib.Sequence
open Lib.ByteSequence
open Lib.NatMod


#reset-options "--max_fuel 0 --z3rlimit 20"

(* Field types and parameters *)
let prime = pow2 127 - 1
unfold type elem = nat_mod prime



(* // Define twisted Edwards curves E, Ehat and the isogenous Weierstrass curve W *)
(* p:=2^127-1; Fp:=GF(p); Fp2<i>:=ExtensionField<Fp,x|x^2+1>; AS<x,y>:=AffineSpace(Fp2,2); *)

let d = 125317048443780598345676279555970305165 * i + 4205857648805777768770

E:=Curve(AS,[-x^2+y^2-(1+d*x^2*y^2)]);

let dhat = -1 / (d + 1)

Ehat:=Curve(AS,[-x^2+y^2-(1+dhat*x^2*y^2)]);

let rt2 = pow2 64;
let rt5 = 87392807087336976318005368820707244464 * i

A:=-(30-8*rt5); B:=56-32*rt5;
W:=EllipticCurve([Fp2|A,B]);

let mu = pow2 256

DBL:=function(Q)       // a=-1 twisted Edwards doubling

    x:=Q[1]; y:=Q[2];
    X:=2*x*y/(1+d*x^2*y^2);
    Y:=(y^2+x^2)/(1-d*x^2*y^2);
    return E![X,Y];

end function;

ADD:=function(Q,R)     // a=-1 twisted Edwards addition

let add (q) (r) =
  let x1 = q.[1] in
  let y1 = q.[2] in
  let x2 = r.[1] in
  let y2 = r.[2] in
  let x = (x1 * y2 + y1 * x2) / (1 + d * x1 * x2 * y1 * y2) in
  let y = (y1 * y2 + x1 * x2) / (1 - d * x1 * x2 * y1 * y2) in
  return E![X,Y]

let tau (p) =
  let x = p.[1] in
  let y = p.[2] in
  let x' = 2 * x * y / ((pow2 x + pow2 y) * (sqrt dhat)) in
  let y' = (pow2 x - pow2 y + 2) / (pow2 y - pow2 x) in
  return Ehat![X',Y'];


tau_dual:=function(P)  // Isogeny tau_dual: Ehat->E

  x:=P[1]; y:=P[2];
  X:=2*x*y*Sqrt(dhat)/(x^2-y^2+2);
  Y:=(y^2-x^2)/(y^2+x^2);
  return E![X,Y];

end function;

delta:=function(P)     // Isomorphism delta: W->Ehat

  x:=P[1]; y:=P[2];
  X:=Sqrt(-12-4*rt2-2*rt5*rt2)*(x-4)/y;
  Y:=(x-4-(2*rt2+rt2*rt5))/(x-4+(2*rt2+rt2*rt5));
  return Ehat![X,Y];

end function;

delta_inv:=function(P) // Isomorphism delta_inv: Ehat->W

  x:=P[1]; y:=P[2];
  X:=(2*rt2+rt2*rt5)*(y+1)/(1-y)+4;
  Y:=(2*rt2+rt2*rt5)*(y+1)/(1-y)*Sqrt(-12-4*rt2-2*rt5*rt2)/x;
  return W![X,Y];

end function;

phiW:=function(P)      // Endomorphism phiW on the Weierstrass curve

  x:=P[1]; y:=P[2];
  X:=x^5+8*rt5*x^4+(40*rt5+260)*x^3+(720*rt5+640)*x^2+(656*rt5+4340)*x+(1920*rt5+960);
  X:=X/(5*(x^2+4*rt5*x-1/5*(4*rt5-90))^2);
  Y:=-y*(x^2+(4*rt5-8)*x-(12*rt5-26))*(x^4+(8*rt5+8)*x^3+28*x^2-(48*rt5+112)*x-32*rt5-124);
  Y:=Y/(rt5*(x^2+4*rt5*x-1/5*(4*rt5-90)))^3;
  return W![X^p,Y^p];

end function;

psiW:=function(P)      // Endomorphism psiW on the Weierstrass curve

  x:=P[1]; y:=P[2];
  X:=-x/2-(9+4*rt5)/(x-4);
  Y:=-y/(i*rt2)*(-1/2+(9+4*rt5)/(x-4)^2);
  return W![X^p,Y^p];

end function;

phi:=function(P);      // Endomorphism phi on E via composition
  return tau_dual(delta(phiW(delta_inv(tau(P)))));
end function;

psi:=function(P);      // Endomorphism psi on E via composition
  return tau_dual(delta(psiW(delta_inv(tau(P)))));
end function;

decomposition:=function(m) // Scalar decomposition

  alpha1:=Floor(50127518246259276682880317011538934615153226543083896339791*m/mu);
  alpha2:=Floor(22358026531042503310338016640572204942053343837521088510715*m/mu);
  alpha3:=Floor(5105580562119000402467322500999592531749084507000101675068*m/mu);
  alpha4:=Floor(19494034873545274265741574254707851381713530791194721254848*m/mu);

  a1:=m-alpha1*650487742939046294-alpha2*2110318963211420372-alpha3*1705647224544756482-alpha4*1400113754146392127+8234880650715616668;

  a2:=alpha1*1397215820276968864+alpha2-alpha3*199320682881407569-alpha4*3540637644719456050+6483313240794689388;

  a3:=-alpha1*523086274270593807-alpha2+alpha3*3336360048424633503+alpha4*471270406870313397+9066539331533273720;

  a4:=alpha1*598824378691085905-alpha2*2727991412926801872-alpha3*765171327772315031+alpha4*1789345740969872106+7765751599377320055;

  a1hat:=a1+1400113754146392127;
  a2hat:=a2+3540637644719456050;
  a3hat:=a3-471270406870313397;
  a4hat:=a4-1789345740969872106;

  if IsEven(a1) then
    a1:=a1hat; a2:=a2hat; a3:=a3hat; a4:=a4hat;
  end if;

  a1:=IntegerToSequence(a1,2);
  a2:=IntegerToSequence(a2,2);
  a3:=IntegerToSequence(a3,2);
  a4:=IntegerToSequence(a4,2);

  // Padding
  while #a1 ne 65 do Append(~a1,0); end while;
  while #a2 ne 65 do Append(~a2,0); end while;
  while #a3 ne 65 do Append(~a3,0); end while;
  while #a4 ne 65 do Append(~a4,0); end while;

  return a1,a2,a3,a4;

end function;

recode:=function(a1,a2,a3,a4) // Scalar recoding

  a:=[a1,a2,a3,a4];
  b:=[[0: i in [1..65]]: j in [1..4]];

  b[1][65]:=1;

  for i:=1 to 65 do
    if i ne 65 then
      b[1][i]:=2*a[1][i+1]-1;
    end if;
    for j:=2 to 4 do
      b[j][i]:=b[1][i]*a[j][1];
      aj:=SequenceToInteger(a[j],2);
      aj:=Floor(aj div 2)-Floor(b[j][i] div 2);
      if aj ne 0 then
        a[j]:=IntegerToSequence(aj,2);
      else
        a[j]:=[0];
      end if;
    end for;
  end for;

  m:=b[1]; d:=[];
  for i:=1 to 65 do
    Append(~d,SequenceToInteger([Abs(b[2][i]),Abs(b[3][i]),Abs(b[4][i])],2)+1);
  end for;

  return m,d;

end function;

lookup_table:=function(P,phiP,psiP,psiphiP)  // Building the lookup table

  T:=[];
  Append(~T,P);
  Append(~T,ADD(phiP,T[1]));
  Append(~T,ADD(psiP,T[1]));
  Append(~T,ADD(psiP,T[2]));
  Append(~T,ADD(psiphiP,T[1]));
  Append(~T,ADD(psiphiP,T[2]));
  Append(~T,ADD(psiphiP,T[3]));
  Append(~T,ADD(psiphiP,T[4]));

  return T;

end function;

generic_scalar_multiplication:=function(P,k) // Generic scalar multiplication used for testing

    bits:=IntegerToSequence(k,2);
    Q:=P;

    for i:=#bits-1 to 1 by -1 do
      Q:=DBL(Q);
      if bits[i] eq 1 then
        Q:=ADD(Q,P);
      end if;
    end for;

    return Q;

end function;

fourQ_scalar_multiplication:=function(P,m)   // Regular four-dimensional scalar multiplication

  // Step 1 - Compute endomorphisms:
  phiP:=phi(P); psiP:=psi(P); psiphiP:=psi(phiP);

  // Step 2 - Precompute lookup table:
  T:=lookup_table(P,phiP,psiP,psiphiP);

  // Step 3 - Scalar decomposition:
  a1,a2,a3,a4:=decomposition(m);

  // Step 4 - Scalar recoding:
  masks,indexes:=recode(a1,a2,a3,a4);

  // Step 5 - Initialize
  Q:=T[indexes[65]];

  // Steps 6,7,8 - Main loop:
  for i:=64 to 1 by -1 do
    Q:=DBL(Q);
    Ti:=T[indexes[i]];
    if masks[i] eq -1 then
      Ti:=E![-Ti[1],Ti[2]];
    end if;
    Q:=ADD(Q,Ti);
  end for;

  return Q; // no (Step 9) normalize here as Q is affine throughout

end function;

// Testing the full FourQ routine against a generic scalar multiplication

while true do

  P:=generic_scalar_multiplication(tau_dual(delta(Random(W))),392);  // Random N-torsion point
  m:=Random(0,mu);  // Random scalar

  if (fourQ_scalar_multiplication(P,m) ne generic_scalar_multiplication(P,m)) then;
    break;
  else
    printf "passed\n";
  end if;

end while;

printf "failed";
