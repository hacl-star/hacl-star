(* -------------------------------------------------------------------- *)
Require Import ssreflect ssrnat ssrbool eqtype div ssrint ssrnum tuple.
Require Import fintype ssralg ssrfun choice seq bigop ec.
Require Import generic_quotient fraction fracfield polyall polydec ec.
Require Import ssrring.

Import GRing.Theory.

Open Local Scope ring_scope.
Open Local Scope quotient_scope.

Set Implicit Arguments.
Unset Strict Implicit.

(* ------------------------------------------------------------------ *)
Reserved Notation "{ 'ppoint' K }"  (at level 0, format "{ 'ppoint'  K }").

Reserved Notation "<[ x : y : z ]>"
  (at level 0, x, y, z at level 8, format "<[ x  :  y  :  z ]>").

(* ------------------------------------------------------------------ *)
Section LinEq.
Variable K : fieldType.
Variable n : nat.

Implicit Types p : n.-tuple K.

(* Soit p1, p2 \in K^n
*   Soit i tq p1[i] != 0, s'il existe.
*     Alors, vérifier que [ p1[j]/p1[i] | j ] = [ p2[j]/p2[i] | j ]
*   Sinon, p1[i] = 0 pour tout i.
*     Alors, vérifier que p1 = p2, i.e. que p2[i] = 0 pour tout i.
*)

(* equivalence relation for triplets   *)
(* lineq p1 p2 <=> exists l, p1 = l*p2 *)
Definition lineq p1 p2 :=
  let P := [pred i : 'I_n | tnth p1 i != 0] in

  match [pick i : 'I_n | P i] with
  | None   => p1 == p2
  | Some i =>
         [tuple tnth p1 j / tnth p1 i | j < n]
      == [tuple tnth p2 j / tnth p2 i | j < n]
  end.

Lemma lineqP p1 p2:
  reflect
    (exists2 x, x != 0 & forall i, tnth p1 i = x * (tnth p2 i))
    (lineq p1 p2).
Proof.
  apply: (iffP idP).
  + rewrite /lineq; set P := [pred i : 'I_n | tnth p1 i != 0].
    case: pickP => [|_ /eqP ->]; last first.
      by exists 1 => /= [|i]; rewrite ?oner_eq0 // mul1r.
    move=> x Px; case: (tnth p2 x =P 0).
      move=> p2x_eq0 /eqP /(congr1 ((@tnth _ _)^~ x)).
      rewrite !tnth_map p2x_eq0 invr0 mulr0 => /eqP.
      by rewrite mulf_eq0 invr_eq0 tnth_ord_tuple orbb (negbTE Px).
    move=> /eqP nz_p2x h; pose y := (tnth p1 x) / (tnth p2 x).
    exists y; first by rewrite mulf_neq0 ?invr_eq0.
    move=> i; rewrite {}/y; move/eqP: h => /(congr1 ((@tnth _ _)^~ i)).
    rewrite !tnth_map tnth_ord_tuple => /(congr1 (( *%R)^~ (tnth p1 x))).
    rewrite mulrAC -mulrA divff // !mulr1 => ->.
    by rewrite mulrAC -mulrA mulrC.
  + case=> x nz_x h; have ->: p2 = [tuple of (map (( *%R) x^-1) p1)].
      apply/eq_from_tnth=> i; rewrite tnth_map h mulrA.
      by rewrite mulVf // mul1r.
    rewrite /lineq; case: pickP; last first.
      move=> {h} h; apply/eqP/eq_from_tnth => i.
      by rewrite tnth_map; move: (h i)=> /= /eqP ->; rewrite mulr0.
    move=> j {h} h; apply/eqP/eq_from_tnth=> k.
    rewrite !tnth_map tnth_ord_tuple invfM invrK.
    by rewrite mulrACA mulVf // mul1r.
Qed.

Lemma lineq_refl: reflexive lineq.
Proof.
  move=> p; apply/lineqP; exists 1; rewrite ?oner_eq0 //.
  by move=> i; rewrite mul1r.
Qed.

Lemma lineq_sym: symmetric lineq.
Proof.
  have h p q: lineq p q -> lineq q p.
    case/lineqP=> [c nz_c h]; apply/lineqP.
    exists c^-1; first by rewrite invr_eq0.
    by move=> i; rewrite h mulrA mulVf // mul1r.
  by move=> p q; apply/idP/idP=> /h.
Qed.

Lemma lineq_trans: transitive lineq.
Proof.
  move=> q p r /lineqP [c1 nz_c1 h1] /lineqP [c2 nz_c2 h2].
  apply/lineqP; exists (c1 * c2); first by rewrite mulf_neq0.
  by move=> i; rewrite h1 h2 mulrA.
Qed.
End LinEq.

(* -------------------------------------------------------------------- *)
Module ProjPlane.
Section Defs.

Variable K : fieldType.

(* subtype of K^3 i.e. prepoint = K^3 - {(0, 0, 0)} *)
Inductive prepoint: Type :=
| PrePoint (t : K * K * K) of t != (0, 0, 0).

Definition tuple_of_prepoint (p : prepoint) :=
  let: PrePoint p _ := p in p.

Local Coercion tuple_of_prepoint: prepoint >-> prod.

Canonical  prepoint_subType := Eval hnf in [subType for tuple_of_prepoint].

Definition prepoint_eqMixin     := Eval hnf in [eqMixin of prepoint by <:].
Canonical  prepoint_eqType      := Eval hnf in EqType prepoint prepoint_eqMixin.
Definition prepoint_choiceMixin := [choiceMixin of prepoint by <:].
Canonical  prepoint_choiceType  := Eval hnf in ChoiceType prepoint prepoint_choiceMixin.

Definition prepoint_of of phant K := prepoint.
Identity Coercion type_prepoint_of : prepoint_of >-> prepoint.

(* -------------------------------------------------------------------- *)
(* the equivalence relation for K^3       *)
(* projeq (x, y, z) (x', y', z') <=>      *)
(* exists l, x'=l*x and y'=l*y and z'=l*z *)
Definition projeq (p1 p2 : K * K * K) :=
  let: (x1, y1, z1) := p1 in
  let: (x2, y2, z2) := p2 in
  lineq [tuple x1; y1; z1] [tuple x2; y2; z2].

Lemma projeqP (p1 p2 : K * K * K):
  let: (x1, y1, z1) := p1 in
  let: (x2, y2, z2) := p2 in
  reflect
    (exists2 l, l != 0 & [&& x1 == l * x2, y1 == l * y2 & z1 == l * z2])
    (projeq p1 p2).
Proof.
  case: p1 p2 => [[x1 y1] z1] [[x2 y2] z2]; rewrite /projeq.
  apply: (iffP idP) => [/lineqP|[x nz_x /and3P []]].
  + case=> x nz_x h; exists x => //.
    have:= (h (inord 0)); rewrite /tnth inordK //= => ->.
    have:= (h (inord 1)); rewrite /tnth inordK //= => ->.
    have:= (h (inord 2)); rewrite /tnth inordK //= => ->.
    by rewrite !eqxx.
  + do 3! (move/eqP=> ->); apply/lineqP; exists x => //.
    by case; case=> [|[|[|//]]] /= h.
Qed.

Lemma projeq_refl: reflexive projeq.
Proof. by case=> [[x y z]]; apply/lineq_refl. Qed.

Lemma projeq_sym: symmetric projeq.
Proof. by case=> [[x1 y1] z1] [[x2 y2] z2]; apply/lineq_sym. Qed.

Lemma projeq_trans: transitive projeq.
Proof.
  case=> [[x2 y2] z2] [[x1 y1] z1] [[x3 y3] z3].
  by apply/lineq_trans.
Qed.

(* without the let directly for the coordinates *)
Lemma tprojeqP (x1 y1 z1 x2 y2 z2 : K):
  reflect
    (exists2 x, x != 0 & [&& x1 == x * x2, y1 == x * y2 & z1 == x * z2])
    (lineq [tuple x1; y1; z1] [tuple x2; y2; z2]).
Proof. by move: (projeqP (x1, y1, z1) (x2, y2, z2)). Qed.

(* equivalence relation restricted to {K^3 - (0,0,0)} *)
Definition ppequiv (p1 p2 : prepoint) := projeq p1 p2.

Lemma ppind (P : prepoint -> Prop):
     (forall x y z (e : (x, y, z) != (0, 0, 0)), P (@PrePoint (x, y, z) e))
  -> forall p, P p.
Proof. by move=> h [[[x y] z] nz]; apply: h. Qed.

Lemma ppequiv_refl: reflexive ppequiv.
Proof. by elim/ppind=> x y z e; apply/lineq_refl. Qed.

Lemma ppequiv_sym: symmetric ppequiv.
Proof.
  elim/ppind=> x1 y1 z1 e1; elim/ppind=> x2 y2 z2 e2.
  by rewrite /ppequiv /= lineq_sym.
Qed.

Lemma ppequiv_trans: transitive ppequiv.
Proof.
  elim/ppind=> x1 y1 z1 e1.
  elim/ppind=> x2 y2 z2 e2.
  elim/ppind=> x3 y3 z3 e3.
  by apply/lineq_trans.
Qed.

Canonical prepoint_equiv :=
  EquivRel ppequiv ppequiv_refl ppequiv_sym ppequiv_trans.
Canonical prepoint_equiv_direct :=
  defaultEncModRel ppequiv.

Definition type := {eq_quot ppequiv}.
Definition type_of of phant K := type.

Notation "{ 'ppoint' K }" := (type_of (Phant K)).

Canonical ppoint_quotType   := [quotType of type].
Canonical ppoint_eqType     := [eqType of type].
Canonical ppoint_choiceType := [choiceType of type].
Canonical ppoint_eqQuotType := [eqQuotType ppequiv of type].

Canonical ppoint_of_quotType   := [quotType of {ppoint K}].
Canonical ppoint_of_eqType     := [eqType of {ppoint K}].
Canonical ppoint_of_choiceType := [choiceType of {ppoint K}].
Canonical ppoint_of_eqQuotType := [eqQuotType ppequiv of {ppoint K}].
End Defs.

Module Exports.
Coercion tuple_of_prepoint: prepoint >-> prod.

Identity Coercion type_prepoint_of: prepoint_of >-> prepoint.

Canonical prepoint_equiv.
Canonical prepoint_equiv_direct.

Canonical prepoint_subType.
Canonical prepoint_eqType.
Canonical prepoint_choiceType.

Canonical ppoint_quotType.
Canonical ppoint_eqType.
Canonical ppoint_choiceType.
Canonical ppoint_eqQuotType.

Canonical ppoint_of_quotType.
Canonical ppoint_of_eqType.
Canonical ppoint_of_choiceType.
Canonical ppoint_of_eqQuotType.

Notation "{ 'ppoint' K }" := (type_of (Phant K)).

Notation prepoint := prepoint.
Notation ppequiv  := ppequiv.
Notation ppind    := ppind.
Notation projeqP  := projeqP.
Notation tprojeqP := tprojeqP.

Definition projeq_refl  := projeq_refl.
Definition projeq_sym   := projeq_sym.
Definition projeq_trans := projeq_trans.

Definition ppequiv_refl  := ppequiv_refl.
Definition ppequiv_sym   := ppequiv_sym.
Definition ppequiv_trans := ppequiv_trans.
End Exports.
End ProjPlane.

Export ProjPlane.Exports.

Notation PrePoint := (@ProjPlane.PrePoint _).

(* -------------------------------------------------------------------- *)
Lemma zero_proof (K : ringType): (0, 0, 1) != (0, 0, 0) :> K * K * K.
Proof. by rewrite eqE /= oner_eq0 andbF. Qed.

(* read it something like *)
(* if p != (0,0,0) then (Prepoint p != (0,0,0)) else (PrePoint (@zero_proof K)) *)
(* Point is the same as prepoint just you can apply it also to (0,0,0) and return (0,0,1) *)
(* takes a triplet and return an element of type prepoint *)
(* at least the name is DEFINITELY NOT A GOOD CHOICE *)
Definition Point (K : fieldType) (p : K * K * K) :=
  insubd (PrePoint (@zero_proof K)) p.

Notation "(| x , y , z |)" := (Point (x, y, z)) (at level 8, x, y at level 15).
Notation "<[ x : y : z ]>" := (\pi_{ppoint _} (|x, y, z|)).

(* -------------------------------------------------------------------- *)
Lemma PointK (K : fieldType) (p : prepoint K): Point p = p.
Proof. by case: p=> p e; rewrite /Point /insubd insubT. Qed.

(* -------------------------------------------------------------------- *)
Lemma ppvalK (K : fieldType) (x y z : K):
     has (predC1 0) [:: x; y; z]
 -> (|x, y, z|) = (x, y, z) :> (K * K * K).
Proof.
  move=> h; rewrite /Point /insubd insubT //.
  apply/eqP=> nz; move: h; case: nz.
  by do 3! move=> ->; rewrite /= eqxx.
Qed.

(* -------------------------------------------------------------------- *)
Section EC_projective.

Variable K : ecuFieldType.
Variable E : ecuType K.

Local Notation a := (E#a).
Local Notation b := (E#b).

Lemma ppequiv_repr (p : prepoint K): ppequiv (repr (\pi_{ppoint K} p)) p.
Proof. by apply/eqmodP; rewrite reprK. Qed.

Definition pponcurve_r (p : prepoint K) :=
  let: (x, y, z) := val p in
    y^+2 * z == x^+3 + a*x*z^+2 + b*z^+3.

Definition pponcurve := lift_fun1 {ppoint K} pponcurve_r.

Lemma pponcurve_mod (p q : prepoint K):
  ppequiv p q -> pponcurve_r q -> pponcurve_r p.
Proof.
  elim/ppind: p=> [x1 y1 z1 e1]; elim/ppind: q => [x2 y2 z2 e2].
  rewrite /pponcurve_r /=; case/tprojeqP=> c nz_c /and3P.
  case; do 3! move/eqP=> ->; move/eqP=> h.
  by rewrite exprMn mulrCA -mulrA h; apply/eqP; ssring.
Qed.

Lemma pponcurve_mod_eq (p q : prepoint K):
  ppequiv p q -> pponcurve_r q = pponcurve_r p.
Proof.
  move=> h; apply/idP/idP; apply/pponcurve_mod=> //.
  by rewrite ppequiv_sym.
Qed.

Lemma pi_pponcurve:
  {mono \pi_{ppoint K} : p / pponcurve_r p >-> pponcurve p}.
Proof.
  move=> p; unlock pponcurve; rewrite !piE /=.
  apply/idP/idP => /pponcurve_mod -> //.
    by rewrite ppequiv_sym ppequiv_repr.
  by rewrite ppequiv_repr.
Qed.

Lemma ppequiv_Point (x y z c : K): c != 0 ->
  ppequiv (|x, y, z|) (|c * x, c * y, c * z|).
Proof.
  move=> nz_c; rewrite {1}/Point /insubd; case: insubP=> /=.
    elim/ppind=> /= x' y' z' e' _ [<- <- <-].
    rewrite /Point /insubd insubT.
      rewrite !xpair_eqE in e' |- *.
      by rewrite !(mulf_eq0, negbTE nz_c).
    move=> ce'; rewrite ppequiv_sym; apply/tprojeqP.
    by exists c=> //; rewrite !eqxx.
  rewrite negbK=> /eqP [-> -> ->]; rewrite !mulr0.
  by rewrite /Point /insubd insubF ?eqxx.
Qed.

Canonical pi_pponcurve_morph := PiMono1 pi_pponcurve.

(* The type for the points of the projective plane *)
(* Inductive ec_proj : Type :=
    | EC_proj : forall p : {ppoint K}, pponcurve p -> ec_proj *)
Inductive ec_proj : Type :=
| EC_proj p of pponcurve p.

Coercion ppoint_of_ec_proj p := let: EC_proj p _ := p in p.

Canonical Structure ec_proj_subType :=
  [subType for ppoint_of_ec_proj by ec_proj_rect].

Definition ec_proj_eqMixin := [eqMixin of ec_proj by <:].
Canonical Structure ec_proj_eqType := Eval hnf in EqType ec_proj ec_proj_eqMixin.

Definition ec_proj_choiceMixin := [choiceMixin of ec_proj by <:].
Canonical Structure ec_proj_choiceType := Eval hnf in ChoiceType ec_proj ec_proj_choiceMixin.

Lemma oncurve_ec_proj (p : ec_proj): pponcurve p.
Proof. exact: valP. Qed.

Hint Resolve oncurve_ec_proj.
End EC_projective.

Section Bijection.
Variable K : ecuFieldType.
Variable E : ecuType K.

Local Notation a := (E#a).
Local Notation b := (E#b).

Lemma pponcurveP (x y : K):
  pponcurve E <[x : y : 1]> = oncurve E (|x, y|).
Proof.
  rewrite !piE /pponcurve_r insubdK /=.
    by rewrite !expr1n !mulr1.
  by rewrite /in_mem /= eqE /= oner_eq0 andbF.
Qed.

Lemma pponcurve0: pponcurve E <[0 : 1 : 0]>.
Proof.
  rewrite !piE /pponcurve_r insubdK /=.
    by rewrite !expr0n /= !mulr0 !addr0.
  rewrite /in_mem; do 2! rewrite /= eqE => /=.
    by rewrite oner_eq0 andbF.
Qed.

Definition a2p (p : point K) : {ppoint K} :=
  if p is (|x, y|) then <[ x : y : 1 ]> else <[ 0 : 1 : 0 ]>.

Definition p2a_r (p : prepoint K) : point K :=
  if p.2 == 0%R then ∞ else (| p.1.1 / p.2, p.1.2 / p.2 |).

Definition p2a := lift_fun1 {ppoint K} p2a_r.

Lemma pi_p2a: {mono \pi_{ppoint K} : p / p2a_r p >-> p2a p}.
Proof.
  move=> p; unlock p2a; have := ppequiv_repr p.
  move: p (repr (\pi p)); elim/ppind=> px py pz hp.
  elim/ppind=> qx qy qz hq; rewrite /ppequiv /=.
  move/tprojeqP=> [c nz_c /and3P []]; rewrite /p2a_r /=.
  do 3! move/eqP=> ->; rewrite mulf_eq0 (negbTE nz_c) /=.
  by rewrite !divf_mull.
Qed.

Canonical pi_p2a_morph := PiMono1 pi_p2a.

Definition a2p_r (p : point K) : K * K * K :=
  if p is (|x, y|) then (x, y, 1) else (0, 1, 0).

Lemma a2pE (p : point K): a2p p = \pi_{ppoint K} (Point (a2p_r p)).
Proof. by case: p. Qed.

Lemma a2pK: cancel a2p p2a.
Proof.
  case=> [|x y] /=; rewrite piE /p2a_r /=.
  + by rewrite ppvalK ?eqxx //= oner_eq0 /= orbT.
  + by rewrite ppvalK /= oner_eq0 ?orbT // !divr1.
Qed.

Lemma p2aK: {in pponcurve E, cancel p2a a2p}.
Proof.
  move=> p /=; elim/quotW: p; elim/ppind=> x y z e /= h.
  rewrite /a2p piE /p2a_r /=; case: eqP; last first.
    move/eqP=> nz_z; apply/eqmodP=> /=; rewrite /ppequiv /=.
    rewrite ppvalK /= ?oner_eq0 ?orbT //.
    apply/tprojeqP; exists z^-1; rewrite ?invr_eq0 //.
    by rewrite ![z^-1*_]mulrC divff // !eqxx.
  move=> z_eq0; apply/eqmodP; rewrite /= /ppequiv /=.
  rewrite ppvalK /= ?oner_eq0 ?orbT //; move: h.
  rewrite /in_mem /= piE /pponcurve_r /= z_eq0.
  rewrite !(expr0n, mulr0, addr0) eq_sym.
  have [x_eq0 _|] := eqVneq x 0; last first.
    by move/(expf_neq0 3)=> /negbTE ->.
  have nz_y: y != 0.
    apply/eqP=> y_eq0; move: e.
    by rewrite x_eq0 y_eq0 z_eq0 eqxx.
  rewrite x_eq0; apply/tprojeqP; exists y^-1.
    by rewrite invr_eq0.
  by rewrite !mulr0 mulVf // !eqxx.
Qed.

Lemma bij_a2p: {on pponcurve E, bijective a2p}.
Proof.
  exists p2a; last by apply/p2aK.
  by move=> p /= h; rewrite a2pK //; move: h.
Qed.  

(* -------------------------------------------------------------------- *)
(* if p not oncurve, pdouble_t and padd_t return weird results          *)
(* and I suppose that's why have to define                              *)
(* padd_tr that sends prepoints not oncurve at the point at infinity    *)
(* now if z=0 and we use the formulas in pdouble_t we get (0,0,0)       *)
(* that is why it has to be a separate case                             *)
(* -------------------------------------------------------------------- *)


Definition pdouble_t (p : K * K * K): K * K * K := nosimpl (
  let: (x, y, z) := p in
    if (y == 0) || (z == 0) then (0, 1, 0) else
      let u  := 3%:R * x^+2 + a * z^+2 in
      let v  := 2%:R * y * z in 
      let r  := u^+2 * z - (2%:R) * v^+2 * x in 
      let xs := v * r in 
      let ys := -u * (r - v^+2 * x) - y * v^+3 in 
      let zs := z * v^+3 in 
      (xs , ys , zs)).

Definition padd_t (p q : K * K * K): K * K * K := nosimpl (
  let: (xp, yp, zp) := p in
  let: (xq, yq, zq) := q in
    if zp == 0 then q else
    if zq == 0 then p else

    if xp / zp == xq / zq then
      if yp / zp == yq / zq then pdouble_t p else (0, 1, 0)
    else
      let u  := yq * zp - yp * zq in 
      let v  := xq * zp - xp * zq in 
      let r  := u^+2 * zp * zq - v^+2 * (xp * zq + xq * zp) in 
      let xs := v * r in 
      let ys := -u * (r - xp * zq * v^+2) - yp * zq * v^+3 in 
      let zs := zp * zq * v^+3 in 
      (xs , ys , zs)).

(* -------------------------------------------------------------------- *)
Definition padd_tr (p q : prepoint K): K * K * K :=
  if pponcurve_r E p && pponcurve_r E q then
    padd_t p q
  else
    (0, 1, 0).

Definition padd_r (p q : prepoint K) := Point (padd_tr p q).
Definition padd := lift_op2 {ppoint K} padd_r.

(* -------------------------------------------------------------------- *)
Lemma projeq_pdouble_t (c x y z : K) (nz_c : c != 0):
  ProjPlane.projeq
    (pdouble_t (x, y, z))
    (pdouble_t (c * x, c * y, c * z)).
Proof.
  case e1: (pdouble_t _)=> [[x1 y1] z1];
  case e2: (pdouble_t _)=> [[x2 y2] z2].
  rewrite /=; rewrite lineq_sym; apply/tprojeqP.
  move: e1 e2; rewrite /pdouble_t !mulf_eq0 (negbTE nz_c) /=.
  case: eqP=> _=> /=; last case: eqP=> _ /=; do 2! case=> <- <- <-.
  + by exists 1; rewrite ?oner_eq0 // !(mulr0, mulr1) !eqxx.
  + by exists 1; rewrite ?oner_eq0 // !(mulr0, mulr1) !eqxx.
  exists (c^+7); first by rewrite expf_eq0.
  by apply/and3P; split; apply/eqP; ssring.
Qed.

Lemma projeq_padd_t (cp cq xp yp zp xq yq zq : K): cp != 0 -> cq != 0 ->
  ProjPlane.projeq
    (padd_t (     xp,      yp,      zp) (     xq,      yq,      zq))
    (padd_t (cp * xp, cp * yp, cp * zp) (cq * xq, cq * yq, cq * zq)).
Proof.
  move=> nz_cp nz_cq; rewrite projeq_sym /padd_t.
  rewrite !mulf_eq0 (negbTE nz_cp) (negbTE nz_cq) !divf_mull //=.
  case: eqP=> _; first by apply/tprojeqP; exists cq=> //; rewrite !eqxx.
  case: eqP=> _; first by apply/tprojeqP; exists cp=> //; rewrite !eqxx.
  case: eqP=> _; first case: eqP=> _.
  + by rewrite projeq_sym; apply/projeq_pdouble_t.
  + by apply/projeq_refl.
  apply/tprojeqP; exists ((cp * cq)^+4).
    by rewrite expf_eq0 /= mulf_neq0.
  by apply/and3P; split; apply/eqP; ssring.
Qed.

(* -------------------------------------------------------------------- *)
Lemma pi_padd: {morph \pi : p q / padd_r p q >-> padd p q}.
Proof.
  elim/ppind=> xp1 yp1 zp1 nz_p1; elim/ppind=> xq1 yq1 zq1 nz_q1.
  unlock padd=> /=; set p1 := PrePoint _; set q1 := PrePoint _.
  set p2 := repr _; set q2 := repr _; apply/eqmodP=> /=.
  have eq_p: ppequiv p2 p1 by apply/ppequiv_repr.
  have eq_q: ppequiv q2 q1 by apply/ppequiv_repr.
  rewrite /padd_r /padd_tr -!(pponcurve_mod_eq _ eq_p, pponcurve_mod_eq _ eq_q).
  case: (boolP (_ && _))=> // /andP [oncve_p oncve_q].
  move: eq_p; elim/ppind: p2=> xp2 yp2 zp2 nz_p2 /=.
  case/tprojeqP=> cp nz_cp /and3P []; do 3! move/eqP=> ->.
  move: eq_q; elim/ppind: q2=> xq2 yq2 zq2 nz_q2 /=.
  case/tprojeqP=> cq nz_cq /and3P []; do 3! move/eqP=> ->.
  case e1: padd_t=> [[dx1 dy1 dz1]].
  case e2: padd_t=> [[dx2 dy2 dz2]].
  move: (projeq_padd_t xp1 yp1 zp1 xq1 yq1 zq1 nz_cp nz_cq).
  rewrite e1 e2 /= => /tprojeqP [c nz_c] /and3P []; do 3! move/eqP=> ->.
  by rewrite -/(ppequiv _ _) ppequiv_sym ppequiv_Point.
Qed.

Canonical pi_padd_morph := PiMorph2 pi_padd.

(* -------------------------------------------------------------------- *)
Definition popp_tr (p : prepoint K) : K * K * K :=
  let: (x, y, z) := val p in (x, -y, z).

Definition popp_r (p : prepoint K) := Point (popp_tr p).
Definition popp := lift_op1 {ppoint K} popp_r.

Lemma pi_popp: {morph \pi : p / popp_r p >-> popp p}.
Proof. 
  elim/ppind=> x1 y1 z1 nz_p1; unlock popp; apply/eqmodP=> /=.
  set p1 := PrePoint _; set p2 := repr _.
  have: ppequiv p2 p1 by apply/ppequiv_repr.
  elim/ppind: p2=> x2 y2 z2 nz_p2; rewrite /p1 /ppequiv /=.
  rewrite /popp_r /popp_tr /=; case/tprojeqP=> [c] nz_c; case/and3P.
  by do 3! move/eqP=> ->; rewrite -mulrN; apply/ppequiv_Point.
Qed.

Canonical pi_popp_morph := PiMorph1 pi_popp.

(* -------------------------------------------------------------------- *)
Lemma nz_padd_tr (p q : prepoint K): padd_tr p q != (0, 0, 0).
Proof.
  pose simpr := (mulr0, mul0r, expr0n, add0r, addr0, sub0r, oppr0).
  rewrite /padd_tr; case: (boolP (_ && _)); last first.
    by move=> _; rewrite !xpair_eqE !eqxx oner_eq0.
  elim/ppind: p=> xp yp zp nz_p; elim/ppind: q => xq yq zq nz_q.
  case/andP=> oncve_p oncve_q; rewrite /padd_t /=.
  case: (zp =P 0)=> // /eqP nz_zp; case: (zq =P 0)=> // /eqP nz_zq.
  case: (_ / _ =P _) => [_|/eqP ne_pq].
  + case: (_ / _ =P _)=> _; last by rewrite !xpair_eqE oner_eq0 eqxx.
    rewrite /pdouble_t; case: (yp =P 0) => [|/eqP nz_yp] /=.
      by rewrite !xpair_eqE oner_eq0 eqxx.
    rewrite (negbTE nz_zp); rewrite !xpair_eqE !negb_and -!orbA.
    by apply/or3P; apply Or33; rewrite !mulf_neq0 // ecu_chi2.
  + rewrite !xpair_eqE !negb_and -!orbA; apply/or3P; apply Or33.
    move: ne_pq; rewrite divff_eq; last by rewrite !mulf_neq0.
    by rewrite eq_sym -subr_eq0=> nz_x; rewrite !mulf_neq0.
Qed.

(* -------------------------------------------------------------------- *)
Lemma nz_popp_tr (p : prepoint K): popp_tr p != (0, 0, 0).
Proof. by elim/ppind: p=> x y z; rewrite /popp_tr /= !xpair_eqE oppr_eq0. Qed.

(* -------------------------------------------------------------------- *)
Lemma padd_rE (p q : prepoint K): padd_r p q = PrePoint (nz_padd_tr p q).
Proof.
  apply/eqP; rewrite /padd_r /Point /insubd insubT ?nz_padd_tr //=.
  by move=> e; rewrite eqE /=.
Qed.

(* -------------------------------------------------------------------- *)
Lemma popp_rE (p : prepoint K): popp_r p = PrePoint (nz_popp_tr p).
Proof.
  apply/eqP; rewrite /popp_r /Point /insubd insubT ?nz_popp_tr //=.
  by move=> e; rewrite eqE /=.
Qed.

(* -------------------------------------------------------------------- *)
Delimit Scope ecaff with A.
Bind    Scope ecaff with ec.

Local Notation "\- x"   := (popp x)               : ecaff.
Local Notation "x \+ y" := (padd x y)             : ecaff.
Local Notation "x \- y" := (x \+ (\- y))%A        : ecaff.

(* -------------------------------------------------------------------- *)
Delimit Scope ecproj with P.
Bind    Scope ecproj with ProjPlane.type_of.

Local Notation "\- x"   := (@ECGroup.neg _ x)     : ecproj.
Local Notation "x \+ y" := (@ECGroup.add _ E x y) : ecproj.
Local Notation "x \- y" := (x \+ (\- y))%P        : ecproj.

(* -------------------------------------------------------------------- *)
Lemma Point_insub (x y z : K) (e : (x, y, z) != (0, 0, 0)):
  (|x, y, z|) = PrePoint e.
Proof. by rewrite /Point /insubd insubT. Qed.

Lemma oncurve_p2a (p : {ppoint K}): pponcurve E p -> oncurve E (p2a p).
Proof.
  elim/quotW: p; elim/ppind=> x y z nz_p; rewrite !piE /=.
  rewrite /p2a_r /=; case: (z =P 0)=> [|/eqP nz_z] // => oncve.
  rewrite -pponcurveP piE /=; have: z^-1 != 0 by rewrite invr_eq0.
  move/(ppequiv_Point x y z); rewrite mulVf // ![z^-1*_]mulrC.
  by move/pponcurve_mod_eq=> ->; rewrite Point_insub.
Qed.

Lemma isomorph (p q : {ppoint K}):
     pponcurve E p -> pponcurve E q
  -> (p \- q)%A = a2p (p2a p \- p2a q)%P.
Proof.
  pose simpr := (mulr0, mul0r, expr0n, add0r, addr0, sub0r, oppr0).
  move=> oncve_p oncve_q; have [] := (oncurve_p2a oncve_p, oncurve_p2a oncve_q).
  move: oncve_p oncve_q; elim/quotW: p=> p; elim/quotW: q=> q; rewrite !piE /=.
  move=> oncve_p oncve_q oncve_pa oncve_qa; rewrite a2pE.
  apply/eqmodP=> /=; rewrite padd_rE popp_rE /= /Point /insubd insubT.
    case: (_ \- _)%P => /= [|x y];
      by rewrite !xpair_eqE ?oner_eq0 !(andbF, andFb).
  move=> e /=; rewrite /ppequiv /= {e}.
  elim/ppind: q oncve_q oncve_qa => xq yq zq nz_q => oncve_q oncve_qa.
  elim/ppind: p oncve_p oncve_pa => xp yp zp nz_p => oncve_p oncve_pa.
  rewrite /padd_tr /popp_tr oncve_p /pponcurve_r /= sqrrN.
  move: (oncve_q); rewrite /pponcurve_r /= => ->.
  rewrite /ECGroup.add -oncurveN oncve_pa oncve_qa /p2a_r /=.
  rewrite /p2a_r /padd_t /=; case: (zp =P 0)=> [_|].
    case: (zq =P 0)=> [eq0_zq|]; first rewrite eq0_zq.
      move: {oncve_qa} oncve_q; rewrite /pponcurve_r /= eq0_zq !simpr.
      rewrite eq_sym expf_eq0 /= => /eqP eq0_xq.
      move: nz_q; rewrite eq0_xq eq0_zq !xpair_eqE !eqxx /=.
      rewrite andbT=> nz_yq; apply/tprojeqP; exists (-yq).
      by rewrite oppr_eq0. by rewrite !mulr0 mulr1 !eqxx.
    move/eqP=> nz_zq; apply/tprojeqP; exists zq=> //.
    by apply/and3P; split; apply/eqP; ssfield.
  move/eqP=> nz_zp; case: eqP=> /= [eq0_zq|].
    apply/tprojeqP; exists zp => //.
    by apply/and3P; split; apply/eqP; ssfield.
  move/eqP=> nz_zq; case: eqP => [|/eqP]; last first.
    rewrite divff_eq ?mulf_neq0 // eq_sym -subr_eq0 => ne.
    apply/tprojeqP; exists (zp * zq * (xq * zp - xp * zq) ^+ 3).
      by rewrite !mulf_neq0.
    by apply/and3P; split; apply/eqP; ssfield; rewrite ?mulNr.
  move=> eq_x; rewrite -[-(_/_)]mulNr; case: eqP=> //=; last first.
    by move=> _; apply/lineq_refl.
  move=> eq_y; case: eqP => /eqP /=.
    rewrite mulf_eq0 invr_eq0 (negbTE nz_zp) orbF.
    by rewrite /pdouble_t=> -> /=; apply/lineq_refl.
  rewrite mulf_eq0 invr_eq0 (negbTE nz_zp) orbF => nz_yp.
  rewrite /pdouble_t (negbTE nz_yp) (negbTE nz_zp) /=.
  have nz_yq: yq != 0.
    apply/eqP=> eq0_yq; move/eqP: eq_y; rewrite eq0_yq.
    rewrite oppr0 mul0r mulf_eq0 invr_eq0 (negbTE nz_zp) orbF.
    by rewrite (negbTE nz_yp).
  apply/tprojeqP; exists ((2%:R * yp * zp)^+3 * zp).
    rewrite mulf_neq0 // expf_eq0 /= !mulf_neq0 //.
    by rewrite ecu_chi2.
  move/(congr1 ( *%R^~ zp)): eq_x.
    rewrite mulrAC -mulrA divff // mulr1 => ->.
  move/(congr1 ( *%R^~ zp)): eq_y.
    rewrite mulrAC -mulrA divff // mulr1 => ->.
  apply/and3P; split; apply/eqP; ssfield;
    by rewrite ?(mulf_neq0, mulNr, mulrN, oppr_eq0, ecu_chi2).
Qed.

End Bijection.


(*
*** Local Variables: ***
*** coq-load-path: ("ssreflect" "common" ".") ***
*** End: ***
 *)
