(* --------------------------------------------------------------------
 * (c) Copyright 2011--2012 Microsoft Corporation and Inria.
 * (c) Copyright 2012--2014 Inria.
 * (c) Copyright 2012--2014 IMDEA Software Institute.
 * -------------------------------------------------------------------- *)

(* -------------------------------------------------------------------- *)
Require Import ssreflect ssrnat ssrbool eqtype fintype tuple.
Require Import seq fintype bigop ssralg finalg ssrfun choice.
Require Import zmodp fingroup polyall polydec viete ssrring.

Import GRing.Theory.

Open Local Scope ring_scope.

Set Implicit Arguments.
Unset Strict Implicit.

(* -------------------------------------------------------------------- *)
Local Notation simp := Monoid.simpm.

Reserved Notation "\- x" (at level 50).

(* -------------------------------------------------------------------- *)
Module ECUFieldType.
  Record mixin_of (K : ringType) : Type := Mixin {
    _ : 2%:R != 0 :> K;
    _ : 3%:R != 0 :> K
  }.

  Section ClassDef.
    Record class_of (K : Type) := Class {
      base  : GRing.Field.class_of K;
      mixin : mixin_of (GRing.Field.Pack base K)
    }.

    Local Coercion base : class_of >-> GRing.Field.class_of.

    Structure type := Pack {sort; _ : class_of sort; _ : Type}.

    Local Coercion sort : type >-> Sortclass.

    Variables (T : Type) (cT : type).

    Definition class := let: Pack _ c _ as cT' := cT return class_of cT' in c.
    Definition clone c of phant_id class c := @Pack T c T.

    Definition pack b0 (m0 : mixin_of (@GRing.Field.Pack T b0 T)) :=
      fun bT b & phant_id (@GRing.Field.class bT) b =>
      fun    m & phant_id m0 m => Pack (@Class T b m) T.

    Definition eqType          := Equality.Pack             class cT.
    Definition choiceType      := Choice.Pack               class cT.
    Definition zmodType        := GRing.Zmodule.Pack        class cT.
    Definition ringType        := GRing.Ring.Pack           class cT.
    Definition comRingType     := GRing.ComRing.Pack        class cT.
    Definition unitRingType    := GRing.UnitRing.Pack       class cT.
    Definition comUnitRingType := GRing.ComUnitRing.Pack    class cT.
    Definition idomainType     := GRing.IntegralDomain.Pack class cT.
    Definition fieldType       := GRing.Field.Pack          class cT.
  End ClassDef.

  Module Exports.
    Coercion base  : class_of >-> GRing.Field.class_of.
    Coercion mixin : class_of >-> mixin_of.
    Coercion sort  : type     >-> Sortclass.

    Bind Scope ring_scope with sort.

    Coercion eqType : type >-> Equality.type.
    Canonical eqType.
    Coercion choiceType : type >-> Choice.type.
    Canonical choiceType.
    Coercion zmodType : type >-> GRing.Zmodule.type.
    Canonical zmodType.
    Coercion ringType : type >-> GRing.Ring.type.
    Canonical ringType.
    Coercion comRingType : type >-> GRing.ComRing.type.
    Canonical comRingType.
    Coercion unitRingType : type >-> GRing.UnitRing.type.
    Canonical unitRingType.
    Coercion comUnitRingType : type >-> GRing.ComUnitRing.type.
    Canonical comUnitRingType.
    Coercion idomainType : type >-> GRing.IntegralDomain.type.
    Canonical idomainType.
    Coercion fieldType : type >-> GRing.Field.type.
    Canonical fieldType.

    Notation ecuFieldType := type.
    Notation ECUFieldType T m := (@pack T _ m _ _ id _ id).
    Notation ECUFieldMixin := Mixin.

    Notation "[ 'ecuFieldType' 'of' T ]" := (@clone T _ _ id)
      (at level 0, format "[ 'ecuFieldType'  'of'  T ]") : form_scope.
  End Exports.
End ECUFieldType.

Export ECUFieldType.Exports.

Section ECUFieldTypeTheory.
  Variable K : ecuFieldType.

  Lemma ecu_chi2: 2%:R != 0 :> K.
  Proof. by case: K => [? [? []]]. Qed.

  Lemma ecu_chi3: 3%:R != 0 :> K.
  Proof. by case: K => [? [? []]]. Qed.

  Lemma ecu_eq_oppr:
    forall (x : K), x = -x -> x = 0.
  Proof.
    move=> x; move/(congr1 (+%R x)); rewrite subrr -mulr2n => /eqP.
    by rewrite -mulr_natl mulf_eq0 (negbTE ecu_chi2) => /eqP.
  Qed.
End ECUFieldTypeTheory.

(* -------------------------------------------------------------------- *)
Module ECUFinField.
  Local Notation mixin_of T b := (Finite.mixin_of (EqType T b)).
  Local Notation fin_ c := (@Finite.Class _ c c).
  Local Notation do_pack pack T := (pack T _ _ id _ _ id).

  Local Notation base_group T vT fT :=
    (@FinGroup.PackBase T (FinRing.groupMixin vT) (Finite.class fT)).
  Local Notation fin_group B V := (@FinGroup.Pack B (@addNr V)).

  Section ClassDef.
    Record class_of R := Class {
      base  : ECUFieldType.class_of R;
      mixin : mixin_of R base
    }.

    Definition base2 R (c : class_of R) := FinRing.Field.Class (mixin c).

    Local Coercion base  : class_of >-> ECUFieldType.class_of.
    Local Coercion base2 : class_of >-> FinRing.Field.class_of.

    Structure type := Pack {sort; _ : class_of sort; _ : Type}.
    Local Coercion sort : type >-> Sortclass.

    Definition pack := FinRing.gen_pack Pack Class ECUFieldType.class.

    Variable cT : type.

    Definition class := let: Pack _ c _ as cT' := cT return class_of cT' in c.

    Let xT := let: Pack T _ _ := cT in T.
    Notation xclass := (class : class_of xT).

    Definition eqType := @Equality.Pack cT xclass xT.
    Definition choiceType := @Choice.Pack cT xclass xT.
    Definition countType := @Countable.Pack cT (fin_ xclass) xT.
    Definition finType := @Finite.Pack cT (fin_ xclass) xT.
    Definition zmodType := @GRing.Zmodule.Pack cT xclass xT.
    Definition finZmodType := @FinRing.Zmodule.Pack cT xclass xT.
    Definition ringType := @GRing.Ring.Pack cT xclass xT.
    Definition finRingType := @FinRing.Ring.Pack cT xclass xT.
    Definition comRingType := @GRing.ComRing.Pack cT xclass xT.
    Definition finComRingType := @FinRing.ComRing.Pack cT xclass xT.
    Definition unitRingType := @GRing.UnitRing.Pack cT xclass xT.
    Definition finUnitRingType := @FinRing.UnitRing.Pack cT xclass xT.
    Definition comUnitRingType := @GRing.ComUnitRing.Pack cT xclass xT.
    Definition finComUnitRingType := @FinRing.ComUnitRing.Pack cT xclass xT.
    Definition idomainType := @GRing.IntegralDomain.Pack cT xclass xT.
    Definition finIdomainType := @FinRing.IntegralDomain.Pack cT xclass xT.
    Definition fieldType := @GRing.Field.Pack cT xclass xT.
    Definition finFieldType := @FinRing.Field.Pack cT xclass xT.
    Definition ecuFieldType := @ECUFieldType.Pack cT xclass xT.

    Definition join_finType := @Finite.Pack fieldType (fin_ xclass) xT.
    Definition join_finZmodType := @FinRing.Zmodule.Pack fieldType xclass xT.
    Definition join_finRingType := @FinRing.Ring.Pack fieldType xclass xT.
    Definition join_finUnitRingType := @FinRing.UnitRing.Pack fieldType xclass xT.
    Definition join_finComRingType := @FinRing.ComRing.Pack fieldType xclass xT.
    Definition join_finComUnitRingType := @FinRing.ComUnitRing.Pack fieldType xclass xT.
    Definition join_finIdomainType := @FinRing.IntegralDomain.Pack fieldType xclass xT.
    Definition join_finFieldType := @FinRing.Field.Pack fieldType xclass xT.

    Definition baseFinGroupType := base_group cT zmodType finType.
    Definition finGroupType := fin_group baseFinGroupType zmodType.
    Definition join_baseFinGroupType := base_group zmodType zmodType finType.
    Definition join_finGroupType := fin_group join_baseFinGroupType zmodType.
  End ClassDef.

  Module Exports.
    Coercion base  : class_of >-> ECUFieldType.class_of.
    Coercion base2 : class_of >-> FinRing.Field.class_of.
    Coercion sort  : type >-> Sortclass.

    Bind Scope ring_scope with sort.

    Coercion eqType : type >-> Equality.type.
    Canonical eqType.
    Coercion choiceType : type >-> Choice.type.
    Canonical choiceType.
    Coercion countType : type >-> Countable.type.
    Canonical countType.
    Coercion finType : type >-> Finite.type.
    Canonical finType.
    Coercion zmodType : type >-> GRing.Zmodule.type.
    Canonical zmodType.
    Coercion finZmodType : type >-> FinRing.Zmodule.type.
    Canonical finZmodType.
    Coercion ringType : type >-> GRing.Ring.type.
    Canonical ringType.
    Coercion finRingType : type >-> FinRing.Ring.type.
    Canonical finRingType.
    Coercion comRingType : type >-> GRing.ComRing.type.
    Canonical comRingType.
    Coercion finComRingType : type >-> FinRing.ComRing.type.
    Canonical finComRingType.
    Coercion unitRingType : type >-> GRing.UnitRing.type.
    Canonical unitRingType.
    Coercion finUnitRingType : type >-> FinRing.UnitRing.type.
    Canonical finUnitRingType.
    Coercion comUnitRingType : type >-> GRing.ComUnitRing.type.
    Canonical comUnitRingType.
    Coercion finComUnitRingType : type >-> FinRing.ComUnitRing.type.
    Canonical finComUnitRingType.
    Coercion idomainType : type >-> GRing.IntegralDomain.type.
    Canonical idomainType.
    Coercion finIdomainType : type >-> FinRing.IntegralDomain.type.
    Canonical finIdomainType.
    Coercion fieldType : type >-> GRing.Field.type.
    Canonical fieldType.
    Coercion finFieldType : type >-> FinRing.Field.type.
    Canonical finFieldType.
    Coercion ecuFieldType : type >-> ECUFieldType.type.
    Canonical ecuFieldType.

    Canonical fieldType.
    Canonical join_finType.
    Canonical join_finZmodType.
    Canonical join_finRingType.
    Canonical join_finComRingType.
    Canonical join_finUnitRingType.
    Canonical join_finComUnitRingType.
    Canonical join_finIdomainType.
    Canonical join_finFieldType.

    Notation finECUFieldType := ECUFinField.type.

    Notation "[ 'finECUFieldType' 'of' T ]" := (do_pack pack T)
      (at level 0, format "[ 'finECUFieldType'  'of'  T ]") : form_scope.

    Canonical baseFinGroupType.
    Canonical finGroupType.
    Canonical join_baseFinGroupType.
    Canonical join_finGroupType.
  End Exports.
End ECUFinField.

Export ECUFinField.Exports.

(* -------------------------------------------------------------------- *)
Module ECUDecFieldType.
  Section ClassDef.
    Record class_of (K : Type) := Class {
      base  : ECUFieldType.class_of K;
      mixin : GRing.DecidableField.mixin_of (GRing.UnitRing.Pack base K)
    }.

    Local Coercion base : class_of >-> ECUFieldType.class_of.

    Definition base2 F m := GRing.DecidableField.Class (@mixin F m).
    Local Coercion base2 : class_of >-> GRing.DecidableField.class_of.

    Structure type := Pack {sort; _ : class_of sort; _ : Type}.

    Local Coercion sort : type >-> Sortclass.

    Variables (T : Type) (cT : type).

    Definition class := let: Pack _ c _ as cT' := cT return class_of cT' in c.
    Definition clone c of phant_id class c := @Pack T c T.

    Definition pack b0 (m0 : GRing.DecidableField.mixin_of (@GRing.UnitRing.Pack T b0 T)) :=
      fun bT b  & phant_id (@ECUFieldType.class bT) b =>
      fun    m  & phant_id m0 m =>
        Pack (@Class T b m) T.

    Definition eqType             := Equality.Pack             class cT.
    Definition choiceType         := Choice.Pack               class cT.
    Definition zmodType           := GRing.Zmodule.Pack        class cT.
    Definition ringType           := GRing.Ring.Pack           class cT.
    Definition comRingType        := GRing.ComRing.Pack        class cT.
    Definition unitRingType       := GRing.UnitRing.Pack       class cT.
    Definition comUnitRingType    := GRing.ComUnitRing.Pack    class cT.
    Definition idomainType        := GRing.IntegralDomain.Pack class cT.
    Definition fieldType          := GRing.Field.Pack          class cT.
    Definition decFieldType       := GRing.DecidableField.Pack class cT.
    Definition ecuFieldType       := ECUFieldType.Pack         class cT.
  End ClassDef.

  Module Exports.
    Coercion base  : class_of >-> ECUFieldType.class_of.
    Coercion sort  : type     >-> Sortclass.

    Bind Scope ring_scope with sort.

    Coercion eqType : type >-> Equality.type.
    Canonical eqType.
    Coercion choiceType : type >-> Choice.type.
    Canonical choiceType.
    Coercion zmodType : type >-> GRing.Zmodule.type.
    Canonical zmodType.
    Coercion ringType : type >-> GRing.Ring.type.
    Canonical ringType.
    Coercion comRingType : type >-> GRing.ComRing.type.
    Canonical comRingType.
    Coercion unitRingType : type >-> GRing.UnitRing.type.
    Canonical unitRingType.
    Coercion comUnitRingType : type >-> GRing.ComUnitRing.type.
    Canonical comUnitRingType.
    Coercion idomainType : type >-> GRing.IntegralDomain.type.
    Canonical idomainType.
    Coercion fieldType : type >-> GRing.Field.type.
    Canonical fieldType.
    Coercion decFieldType : type >-> GRing.DecidableField.type.
    Canonical decFieldType.
    Coercion ecuFieldType : type >-> ECUFieldType.type.
    Canonical ecuFieldType.

    Notation ecuDecFieldType := ECUDecFieldType.type.
    Notation EcuDecFieldMixin := GRing.DecidableField.Mixin.
    Notation EcuDecFieldType T m := (@pack T _ m _ _ id _ id).

    Notation "[ 'ecuDecFieldType' 'of' T ]" := (@pack T _ _ _ id _ id)
      (at level 0, format "[ 'ecuDecFieldType'  'of'  T ]") : form_scope.
  End Exports.
End ECUDecFieldType.

Export ECUDecFieldType.Exports.

(* -------------------------------------------------------------------- *)
Record ecuType (K : ringType) := {
  cA : K;
  cB : K;
  _  : 4%:R * cA^+3 + 27%:R * cB^+2 != 0
}.

Notation "K '#a'" := (K.(cA)) (at level 30).
Notation "K '#b'" := (K.(cB)) (at level 30).

Section ECUTypeTheory.
  Variable K : ringType.
  Variable E : ecuType K.

  Lemma ecu_DN0: 4%:R * (E#a)^+3 + 27%:R * (E#b)^+2 != 0 :> K.
  Proof. by case: E. Qed.
End ECUTypeTheory.

(* -------------------------------------------------------------------- *)
Section PointDef.
  Inductive point (K : Type) : Type :=
  | EC_Inf : point K
  | EC_In  : K -> K -> point K.
End PointDef.

Section PointEq.
  Variable T : eqType.

  Local Notation point := (point T).

  Definition point_eq (p1 p2 : point) :=
    match p1, p2 with
    | EC_Inf     , EC_Inf      => true
    | EC_In x1 y1, EC_In x2 y2 => [&& (x1 == x2) & (y1 == y2)]
    | _          , _           => false
    end.

  Lemma point_eqP:
    forall (p1 p2 : point), reflect (p1 = p2) (point_eq p1 p2).
  Proof.
    move=> p1 p2; apply: (iffP idP); last first.
    + by move=> {p2} <-; case: p1 => //= *; rewrite !eqxx.
    move: p1 p2 => [|x1 y1] [|x2 y2] //=.
    by case/andP; do 2! (move/eqP=> ->).
  Qed.

  Definition point_eqMixin := EqMixin point_eqP.

  Canonical Structure point_eqType :=
    Eval hnf in (EqType _ point_eqMixin).
End PointEq.

(* -------------------------------------------------------------------- *)
Notation "∞"           := (@EC_Inf _)    (at level 8).
Notation "(| x , y |)" := (@EC_In _ x y) (at level 8, x, y at level 15).

(* -------------------------------------------------------------------- *)
Section PointChoice.
  Variable T : choiceType.

  Definition encode (p : point T) :=
    match p with
    | EC_Inf    => [::]
    | EC_In x y => [:: x; y]
    end.

  Definition decode (c : seq T) :=
    match c with
    | [::]      => Some (EC_Inf _)
    | [:: x; y] => Some (EC_In x y)
    | _         => None
    end.

  Lemma codeK : pcancel encode decode.
  Proof. by case. Qed.

  Definition point_choiceMixin := PcanChoiceMixin codeK.

  Canonical Structure point_choiceType :=
    Eval hnf in (ChoiceType _ point_choiceMixin).
End PointChoice.

(* -------------------------------------------------------------------- *)
Section PointCount.
  Variable T : countType.

  Definition pickle (p : point T) :=
    match p with
    | EC_Inf    => None
    | EC_In x y => Some (x, y)
    end.

  Definition unpickle (p : option (T * T)) :=
    match p with
    | None        => EC_Inf _
    | Some (x, y) => EC_In x y
    end.

  Definition pickleK: cancel pickle unpickle.
  Proof. by case. Qed.

  Definition point_countMixin := CanCountMixin pickleK.

  Canonical Structure point_countType :=
    Eval hnf in (CountType _ point_countMixin).
End PointCount.

(* -------------------------------------------------------------------- *)
Section PointFinType.
  Variable T : finType.

  Definition points := (EC_Inf T) :: [seq (|x.1, x.2|) | x : T*T].

  Lemma uniq_points: uniq points.
  Proof.
    rewrite /points /=; apply/andP; split.
    + by apply/memPn=> P /mapP [x _ ->].
    + rewrite map_inj_uniq ?enum_uniq //.
      by case=> [x1 y1] [x2 y2]; case => -> ->.
  Qed.

  Lemma total_points : points =i {: point T}.
  Proof.
    case=> [|x y] //; rewrite /points inE /=.
    pose xy := (x, y); have ->: (|x, y|) = (|xy.1, xy.2|) by [].
    by apply: map_f; rewrite {}/xy; apply: mem_enum.
  Qed.

  Definition point_finMixin := UniqFinMixin uniq_points total_points.
  Canonical point_finType := FinType (point T) point_finMixin.

  Lemma npoints: #|{: point T}| = (#|T|^2).+1.
  Proof.
    rewrite /= cardT enumT unlock /=.
    by rewrite size_map -cardT /= card_prod.
  Qed.
End PointFinType.

(* -------------------------------------------------------------------- *)
Section EC.
  Variable K : ringType.
  Variable E : ecuType K.

  Definition oncurve (p : point K) := (
    match p with
    | EC_Inf    => true
    | EC_In x y => y^+2 == x^+3 + E#a * x + E#b
    end).

  Inductive ec : Type := EC p of oncurve p.

  Coercion point_of_ec p := let: EC p _ := p in p.

  Canonical Structure ec_subType := [subType for point_of_ec by ec_rect].

  Definition ec_eqMixin := [eqMixin of ec by <:].
  Canonical Structure ec_eqType := Eval hnf in EqType ec ec_eqMixin.

  Definition ec_choiceMixin := [choiceMixin of ec by <:].
  Canonical Structure ec_choiceType := Eval hnf in ChoiceType ec ec_choiceMixin.

  Lemma oncurve_ec: forall p : ec, oncurve p.
  Proof. exact: valP. Qed.

  Hint Resolve oncurve_ec.
End EC.

Notation "[ 'oc' 'of' p ]" := (oncurve_ec p).

(* -------------------------------------------------------------------- *)
Section ECCountType.
  Variable K : finRingType.
  Variable E : ecuType K.

  Definition ec_countMixin := [countMixin of (ec_subType E) by <:].
  Canonical Structure ec_countType := Eval hnf in CountType (ec E) ec_countMixin.

  Canonical ec_subCountType := Eval hnf in [subCountType of ec E].
End ECCountType.

(* -------------------------------------------------------------------- *)
Section ECFinType.
  Variable K : finFieldType.
  Variable E : ecuType K.

  Local Notation ec := (@ec K E).

  Definition ec_finMixin := [finMixin of ec by <:].
  Canonical ec_finType := Eval hnf in (FinType ec ec_finMixin).
End ECFinType.

(* -------------------------------------------------------------------- *)
Section XPoly.
  Variable K : ringType.
  Variable E : ecuType K.

  Local Notation a := (E#a).
  Local Notation b := (E#b).

  Definition Xpoly := locked (Poly [:: b; a; 0; 1]).

  Lemma size_Xpoly : size Xpoly = 4.
  Proof.
    by unlock Xpoly; rewrite (@PolyK _ 0) //= oner_neq0.
  Qed.

  Lemma XpolyE: Xpoly = 'X^3 + a *: 'X + b%:P.
  Proof.
    apply/polyP=> i; unlock Xpoly; rewrite (@PolyK _ 0) //= ?oner_neq0 //.
    rewrite !coef_add_poly coefXn coefC coefZ coefX; move: i.
    by do 5! (case; first by rewrite !simp); move=> ?; rewrite /= !simp.
  Qed.

  Lemma XpolyN0: Xpoly != 0.
  Proof. by rewrite -size_poly_eq0 size_Xpoly. Qed.

  Lemma horner_Xpoly:
    forall x, Xpoly.[x] = x ^+ 3 + a * x + b.
  Proof. by move=> x; rewrite XpolyE !(hornerXn, hornerE). Qed.

  Lemma Xpoly_oncurve c:
    (root Xpoly c) = oncurve E (|c, 0|).
  Proof.
    by rewrite rootE horner_Xpoly /= expr2 mulr0 eq_sym.
  Qed.

  Lemma oncurve_root x y: oncurve E (|x, y|) = root ('X ^+ 2 - (Xpoly.[x])%:P) y.
  Proof.
    by rewrite rootE !(hornerE, hornerXn, horner_Xpoly) subr_eq0.
  Qed.

  Lemma Xpoly_monic: Xpoly \is monic.
  Proof.
    apply/monicP; unlock lead_coef Xpoly.
    by rewrite !(PolyK (c := 0)) //= oner_eq0.
  Qed.

  Lemma map_XpolyE (rT : ringType) (f : {rmorphism K -> rT}):
    map_poly f Xpoly = 'X^3 + (f (E#a)) *: 'X + (f (E#b))%:P.
  Proof.
    pose rwE := (rmorphD, map_polyC, map_polyZ, map_polyXn, map_polyX).
    by rewrite XpolyE; do! rewrite !rwE /=.
  Qed.
End XPoly.

(* -------------------------------------------------------------------- *)
Module ECGroup.
  Section Defs.
    Variable K : ecuFieldType.
    Variable E : ecuType K.

    Local Notation Xpoly := (@Xpoly _ E).

    Lemma eqrN_eq0 (y : K): (y == -y) = (y == 0).
    Proof.
      rewrite -addr_eq0 -{1 2}[y]mul1r -mulrDl.
      by rewrite mulf_eq0 (negbTE (ecu_chi2 K)).
    Qed.

    Definition neg (p : point K) :=
      if p is (|x, y|) then (|x, -y|) else ∞.

    Definition add (p1 p2 : point K) :=
      let p1 := if oncurve E p1 then p1 else ∞ in
      let p2 := if oncurve E p2 then p2 else ∞ in

        match p1, p2 with
        | ∞, _ => p2 | _, ∞ => p1

        | (|x1, y1|), (|x2, y2|) =>
          if   x1 == x2
          then if   (y1 == y2) && (y1 != 0)
               then
                 let s  := (3%:R * x1^+2 + E#a) / (2%:R * y1) in
                 let xs := s^+2 - 2%:R * x1 in
                   (| xs, - s * (xs - x1) - y1 |)
               else
                 ∞
          else
            let s  := (y2 - y1) / (x2 - x1) in
            let xs := s^+2 - x1 - x2 in
              (| xs, - s * (xs - x1) - y1 |)
        end.

    Lemma zeroO : oncurve E ∞.
    Proof. by []. Qed.

    Lemma negO : forall p, oncurve E p -> oncurve E (neg p).
    Proof. by case=> [|x y] //=; rewrite sqrrN. Qed.

    Lemma oncurveN p: (oncurve E p) = (oncurve E (neg p)).
    Proof.
      apply/idP/idP; move/negO => //.
      by case: p => [|x y] //=; rewrite opprK.
    Qed.

    Lemma oncurveN_fin x y: oncurve E (|x, -y|) = oncurve E (|x, y|).
    Proof. by move: (oncurveN (|x, y|)). Qed.

    Local Notation sizep := (size : {poly _} -> _).

    Definition line (p q : K * K) : K * K * K :=
      let: (x1, y1) := p in
      let: (x2, y2) := q in

      match oncurve E (|x1, y1|) && oncurve E (|x2, y2|) with
      | false => (0, 0, 0)
      | true  =>
          if   x1 == x2
          then if   (y1 == y2) && (y1 != 0)
               then
                 let s := (3%:R * x1^+2 + E#a) / (2%:R * y1) in
                   (1, -s, y2 - s * x2)
               else
                 (0, 1, x1)
          else
            let s := (y2 - y1) / (x2 - x1) in
              (1, -s, y2 - s * x2)
      end.

    Definition ladd (p1 p2 : point K) :=
      let p1 := if oncurve E p1 then p1 else ∞ in
      let p2 := if oncurve E p2 then p2 else ∞ in

        match p1, p2 with
        | ∞, _ => neg p2 | _, ∞ => neg p1
        | (|x1, y1|), (|x2, y2|) =>
            let: (u, v, c) := line (x1, y1) (x2, y2) in
              if u == 0 then ∞ else
                let: x := u^-2 * v ^+ 2 - (x1 + x2) in
                let: y := u^-1 * (c - v * x) in
                  (|x, y|)
        end.

    Lemma ladd_addE p q: ladd p q = neg (add p q).
    Proof.
      rewrite /ladd /add;
        set pp := if oncurve E p then _ else _;
        set qq := if oncurve E q then _ else _.
      have oncve_pp: oncurve E pp by rewrite {}/pp; case h: (oncurve E p).
      have oncve_qq: oncurve E qq by rewrite {}/qq; case h: (oncurve E q).
      move: {p q} pp oncve_pp qq oncve_qq.
      case=> [|x1 y1] oncve_1 [|x2 y2] oncve_2 //.
      rewrite /line oncve_1 oncve_2 /=.
      case: (x1 =P x2); first (case: andP; first last).
      + by move=> _ _; rewrite eqxx.
      + case=> /eqP <- nz_y1 <-; rewrite oner_eq0.
        rewrite !(simp, expr1n, invr1, opprD, opprK) /=.
        by set s := ((_ + E#a) / _); congr (|_, _|); ssring.
      + move/eqP => ne_x1x2; rewrite oner_eq0.
        rewrite !(simp, expr1n, invr1, opprD, opprK) /=.
        set s := (y2 - y1) / _; congr (|_, _|); first by ssring.
        set l := (y2 - _ - _); set r := - _.
          have {l}->: l = s^+3 - s * (x1 + x2) + (y2 - s * x2) by ssring.
          have {r}->: r = s^+3 - s * (x1 + x2) + (y1 - s * x1) by ssring.
        have nz_x2Bx1: x2 - x1 != 0 by rewrite subr_eq0 eq_sym.
        congr (_ + _); apply/(@mulfI _ (x2 - x1)) => //.
        by rewrite !mulrBr !mulrA [_ / _]mulrAC divff // !simp; ssring.
    Qed.

    Lemma line_outcveE p q:
         ~~ (oncurve E (|p.1, p.2|) && oncurve E (|q.1, q.2|))
      -> line p q = (0, 0, 0).
    Proof. by case: p q => [x1 y1] [x2 y2]; rewrite /line => /negbTE ->. Qed.

    Lemma line_sym p q: line p q = line q p.
    Proof.
      case: p q => [x1 y1] [x2 y2]; rewrite /line;
        have [oncve_1 | outcve_1] := (boolP (oncurve E (|x1, y1|)));
        have [oncve_2 | outcve_2] := (boolP (oncurve E (|x2, y2|))) => //=.
      rewrite ![x2==_]eq_sym; case: (x1 =P x2) => [<-|/eqP ne_x1x2]; last first.
        rewrite -![y2 - y1]opprB -![x2 - x1]opprB !invrN !mulrNN.
        congr (_, _, _); rewrite [X in _-X=_]mulrAC [X in _=_-X]mulrAC.
        rewrite -[X in X+_=_]divr1 -[X in _=X+_]divr1 -!mulNr.
        rewrite !addf_div ?(oner_neq0, subr_eq0, ne_x1x2) // !simp.
        by congr (_ / _); rewrite !opprB !(mulrDl, mulrDr); ssring.
      rewrite ![y2==_]eq_sym; case: (y1 =P y2) => [<-|/eqP ne_y1y2] => //=.
      by rewrite [0==y1]eq_sym; have [->|->] := (eqVneq y1 0); rewrite ?eqxx.
    Qed.

    Lemma line_okl p q:
      let: (u, v, c) := line p q in
        u * p.2 + v * p.1 - c = 0.
    Proof.
      case: p q => [x1 y1] [x2 y2]; rewrite /line;
        have [oncve_1 | outcve_1] := (boolP (oncurve E (|x1, y1|)));
        have [oncve_2 | outcve_2] := (boolP (oncurve E (|x2, y2|)));
          rewrite ?(simp, oppr0) //=.
      case: (x1 =P x2) => [<-|/eqP ne_x1x2]; last first.
        rewrite !simp /= mulNr ![_ / _ * _]mulrAC opprD opprK !addrA.
        rewrite [_-y2]addrAC -!addrA -mulNr -mulrDl !addrA.
        rewrite -[y1-y2]divr1 addf_div ?(oner_eq0, subr_eq0) 1?eq_sym //.
        apply/eqP; rewrite !simp /=.
        rewrite mulf_eq0 invr_eq0 orbC subr_eq0 eq_sym (negbTE ne_x1x2) /=.
        by apply/eqP; ssring.
      case: (y1 =P y2) => [<-|/eqP ne_y1y2] /=; last by rewrite !simp subrr.
      have [->|nz_y1] := eqVneq y1 0; first by rewrite eqxx /= !simp subrr.
      by rewrite nz_y1 !simp; ssring.
    Qed.

    Lemma line_okr p q:
      let: (u, v, c) := line p q in
        u * q.2 + v * q.1 - c = 0.
    Proof. by rewrite line_sym; apply: line_okl. Qed.

    Lemma thdimp p q:
      let: (u, v, c) := line p q in
      let: r := Xpoly - (u^-1 *: (v *: 'X - c%:P)) ^+ 2 in
      let: z := u ^- 2 * v ^+ 2 - (p.1 + q.1) in
        u != 0 -> r = ('X - p.1%:P) * ('X - q.1%:P) * ('X - z%:P).
    Proof.
      set pp := (|p.1, p.2|); set qq := (|q.1, q.2|).
      case: (boolP (oncurve E pp && oncurve E qq)); last first.
        by move/line_outcveE=> ->; rewrite eqxx.
      case/andP=> oncve_p oncve_q; case lE: (line p q) => [[u v] c].
      move=> nz_u; set r := (Xpoly - _);
        set c0 := E#b - u^-2 * c^+2;
        set c1 := E#a + (u^-2 * v * c) *+ 2;
        set c2 := - u^-2 * v^+2;
          have Er: r = Poly [:: c0; c1; c2; 1].
      + apply/polyP=> i; unlock Xpoly; rewrite (@PolyK _ 0) //= ?oner_neq0 //.
        pose coefE := (coefMC, coefCM, coefE).
        rewrite /r XpolyE !(exprZn, sqrrB) !coefE; move: i.
        do 4! (case; first by rewrite !(simp, oppr0, exprVn, eqxx) //=; ssring).
        by move=> i; rewrite !(simp, oppr0, exprVn, eqxx) /= nth_nil.
      have sz_r: size r = 4 by rewrite Er (@PolyK _ 0) // oner_eq0.
      have nz_r: r != 0 by rewrite -size_poly_eq0 sz_r.
      have monic_r: r \is monic.
        apply/monicP; rewrite Er lead_coefE -{2}Er sz_r.
        by rewrite (@PolyK _ 0) // oner_neq0.
      have root_pVq: forall s, (s == p) || (s == q) -> root r s.1.
        move=> s eq_s_pq; have oncve_s: oncurve E (|s.1, s.2|).
          by case/orP: eq_s_pq => /eqP ->.
        have: u * s.2 + v * s.1 - c = 0.
          case/orP: eq_s_pq => /eqP->.
          + by move: (line_okl p q); rewrite lE.
          + by move: (line_okr p q); rewrite lE.
        move/eqP; rewrite -addrA addrC addr_eq0 => /eqP vsBcE.
        rewrite rootE /r !(horner_exp, hornerE) /= vsBcE.
        rewrite !mulrN sqrrN mulrA mulVf // mul1r.
        by rewrite horner_Xpoly -(eqP oncve_s) subrr.
      have h: forall x, count (pred1 x) [:: p.1; q.1] <= \mu_x r.
        move=> x /=; rewrite addn0; case: (p.1 =P x); last first.
          move/eqP=> ne_p1x; rewrite add0n; case: (q.1 =P x) => //=.
          move=> <-; rewrite mu_gt0 //; apply: root_pVq.
          by rewrite eqxx orbT.
        move=> /esym Exp; case: (q.1 =P x); last first.
          move/eqP=> ne_q1x; rewrite addn0 /= mu_gt0 // Exp.
          by apply: root_pVq; rewrite eqxx.
        move=> /esym Exq /=; rewrite addn1; move: lE.
        have pairE: forall x, (x.1, x.2) = x by move=> ?? [].
        rewrite /line -[p]pairE -[q]pairE {pairE} oncve_p oncve_q /=.
        rewrite -Exp -Exq eqxx /=; case: andP; last first.
          by move=> _ [/esym z_u _ _]; rewrite z_u eqxx in nz_u.
        case=> [/eqP eq_p2q2 nz_q2] [/esym one_u /esym Ev /esym Ec].
        apply: ltn_pred; rewrite /= -subn1 -mu_deriv_char; first last.
        + by rewrite Exp; apply: root_pVq; rewrite eqxx.
        + rewrite sz_r; case => [|[|[|[|i]]]] // _.
          * by rewrite inE /= ecu_chi2.
          * by rewrite inE /= ecu_chi3.
        rewrite mu_gt0; last first.
          rewrite Er /deriv -{1}Er sz_r -size_poly_eq0.
          by rewrite polyseq_poly // (@PolyK _ 0) //= ?(oner_neq0, ecu_chi3).
        rewrite rootE /deriv /horner sz_r polyseq_poly; last first.
          by rewrite Er (@PolyK _ 0) ?(oner_neq0, ecu_chi3).
        rewrite Er (@PolyK _ 0) ?oner_eq0 //= mul0r add0r mulr1n.
        rewrite /c2 /c1 one_u expr1n invr1 !(mul1r, mulN1r).
        set w := (_ + _ : K); pose k := (3%:R * x^+2 + E#a).
        have {w} ->: w = k - 2%:R * x * v^+2 + 2%:R * (c * v) by ssring.
        pose w := (2%:R * p.2); apply/eqP/(@mulIf _ (w^+2)).
          by rewrite expf_neq0 // mulf_neq0 // ecu_chi2.
        rewrite mul0r 2!mulrDl !mulNr.
        have ->:  2%:R * (c * v) * w ^+ 2 = 2%:R * (c * w) * (v * w) by ssring.
        have ->: (2%:R * x * v ^+ 2) * w ^+ 2 = 2%:R * x * (v * w)^+2 by ssring.
        have ->: v * w = - (3%:R * x ^+ 2 + E #a).
          rewrite Ev /w -mulNr -mulrA mulVf ?mulr1 //.
          by rewrite mulf_neq0 // ecu_chi2.
        have ->: c * w = q.2 * w - (3%:R * x ^+ 2 + E #a) * x.
          rewrite Ec /w mulrBl; congr (_ - _); rewrite mulrAC.
          congr (_ * _); rewrite -mulrA mulVf ?mulr1 //.
          by rewrite mulf_neq0 // ecu_chi2.
        by rewrite -eq_p2q2 {}/w {}/k Exp; ssring.
      have: ('X - p.1%:P) * ('X - q.1%:P) %| r.
        move: (@roots_dvdp _ r [:: p.1; q.1]).
        rewrite !big_cons big_nil mulr1; apply.
        by apply/allP=> x _; rewrite inE; apply: h.
      case/dvdpP=> qr Er'; have/(congr1 sizep) := Er'.
      have := nz_r; rewrite {1}Er' mulf_eq0 => /norP [nz_qr _].
      rewrite sz_r !size_mul // ?(mulf_neq0, polyXsubC_eq0) //.
      rewrite !size_XsubC /= addn3 /=; case=> /esym/eqP.
      case/size_polyf2P=> k; rewrite eqp_monic ?monicXsubC //; last first.
        by move: monic_r; rewrite Er' !(monicMr, monicXsubC) //.
      move/eqP=> Eqr {nz_qr}; move: Er'; rewrite {}Eqr => Er'.
      have/(congr1 (fun (x : {poly K})=> x`_2)) := Er'.
      set cs := [tuple k; p.1; q.1]; move/esym/eqP: (viete0 cs).
      rewrite 3!big_cons big_nil mulr1 eqr_oppLR => /eqP->.
      rewrite {1}Er (@PolyK _ 0) ?oner_neq0 // unlock /= !simp /=.
      move=> Ec2; have: k = - (c2 + p.1 + q.1) by rewrite Ec2; ssring.
      move=> Ek; move: Er'; rewrite Ek=> ->.
      rewrite !mulrA [X in _ = X]mulrC !mulrA; congr (_ * _ * _).
      by rewrite -!polyC_opp opprK /c2; congr ('X + _%:P); ssring.
    Qed.

    Lemma negK: involutive neg.
    Proof. by case=> [|x y] //=; rewrite opprK. Qed.

    Lemma addO p q: oncurve E (add p q).
    Proof.
      rewrite oncurveN -ladd_addE /ladd;
        set pp := if oncurve E p then _ else _;
        set qq := if oncurve E q then _ else _.
      have oncve_pp: oncurve E pp by rewrite {}/pp; case h: (oncurve E p).
      have oncve_qq: oncurve E qq by rewrite {}/qq; case h: (oncurve E q).
      move: {p q} pp oncve_pp qq oncve_qq.
      case=> [|x1 y1] oncve_1 [|x2 y2] oncve_2; rewrite -?oncurveN //.
      case h: (line _ _) => [[u v] c]; case: (u =P 0) => //.
      move/eqP=> nz_u; set z := u ^- 2 * v ^+ 2 - (x1 + x2).
      move: (thdimp (x1, y1) (x2, y2)); rewrite h => /(_ nz_u) /=.
      move/(congr1 (fun p => p.[z]))/esym; rewrite -/z.
      rewrite hornerM hornerXsubC subrr mulr0 => /esym/eqP.
      rewrite 2!hornerE subr_eq0 horner_Xpoly => /eqP->.
      apply/eqP; rewrite -mul_polyC !(horner_exp, hornerE) /=.
      by rewrite !exprMn; congr (_ * _); rewrite -[c-_]opprK opprB sqrrN.
    Qed.

    Lemma add0o : {in (oncurve E), left_id ∞ add}.
    Proof.
      move=> p; rewrite /in_mem /= => oncve_p.
      by rewrite /add /= oncve_p.
    Qed.

    Lemma addNo : left_inverse ∞ neg add.
    Proof.
      move=> p; rewrite /add -oncurveN.
      have [|] := (boolP (oncurve E p)) => // _.
      case: p=> [|x y] //=; rewrite eqxx /= eq_sym; case Hy0: (y == 0).
      + by rewrite (eqP Hy0) oppr0 eqxx //.
      + rewrite oppr_eq0 Hy0 andbT; case HyN: (y == -y) => //=.
        by absurd false=> //; rewrite -Hy0 -eqrN_eq0 HyN.
    Qed.

    Lemma addoC : commutative add.
    Proof.
      move=> p1 p2; rewrite /add;
        have [|] := (boolP (oncurve E p1)) => // _;
        have [|] := (boolP (oncurve E p2)) => // _; first last.
      + by case: p2.
      + by case: p1.
      case: p1 p2 => [|x1 y1] [|x2 y2] //=.
      rewrite [x2 == _]eq_sym [y2 == _]eq_sym.
      case Ex: (x1 == x2); first (case Ey: (y1 == y2)) => //=.
      + by rewrite -(eqP Ey) -(eqP Ex); case Ey0: (y1 == 0).
      + congr (| _, _ |); first (rewrite -!addrA; congr (_^+2 + _)).
        * by rewrite -[y2 - _]opprB -[x2 - _]opprB invrN mulrNN.
        * by rewrite addrC.
      rewrite -[y2 - _]opprB -[x2 - _]opprB invrN mulrNN.
      set Dx := (x1 - x2); set Dy := (y1 - y2); set a := Dy / Dx.
      have HDx: Dx != 0 by apply/negP; rewrite subr_eq0 Ex.
      rewrite !mulrDr -!addrA; congr (-a * a ^+ 2 + _); rewrite !mulrNN.
      rewrite ![a * x1 + _]addrCA; congr (_ + (_ + _)).
      rewrite ![a * _]mulrC /a !mulrA -[y1]mul1r -[y2]mul1r.
      rewrite -[1](divff HDx) ![Dx / Dx * _]mulrAC.
      rewrite -!mulrBl; congr (_ / _).
      rewrite /Dx /Dy !mulrDl !mulrDr !mulNr !mulrN.
      rewrite !opprB !addrA [_ - (_ * y1)]addrC !addrA addNr add0r.
      symmetry; rewrite -[_ - _ + _]addrA addNr addr0.
      by rewrite addrC.
    Qed.

    Notation   zeroec := (EC zeroO).
    Definition negec  := [fun p     : ec E => EC (negO [oc of p])].
    Definition addec  := [fun p1 p2 : ec E => EC (addO p1 p2)].

    Lemma addNe : left_inverse zeroec negec addec.
    Proof. by move=> [p Hp]; apply/eqP; rewrite eqE /= addNo. Qed.

    Lemma add0e : left_id zeroec addec.
    Proof. by move=> [p Hp]; apply/eqP; rewrite eqE /= add0o. Qed.

    Lemma addeC : commutative addec.
    Proof.
      move=> [p1 Hp1] [p2 Hp2]; apply/eqP=> /=.
      by rewrite eqE /= addoC.
    Qed.
  End Defs.
End ECGroup.

Local Notation "\- x" := (@ECGroup.neg _ x).

(* -------------------------------------------------------------------- *)
Section ECGroupTheory.
  Variable K : ecuFieldType.
  Variable E : ecuType K.

  Lemma oncurveN p: (oncurve E p) = (oncurve E (\- p)).
  Proof. by apply: ECGroup.oncurveN. Qed.

  Lemma oncurveN_fin x y: oncurve E (|x, -y|) = oncurve E (|x, y|).
  Proof. by apply: ECGroup.oncurveN_fin. Qed.
End ECGroupTheory.

(* -------------------------------------------------------------------- *)
Section ECTheory.
  Variable K : idomainType.
  Variable E : ecuType K.

  Local Notation a := (E#a).
  Local Notation b := (E#b).

  Lemma smooth : forall x, \mu_x (Xpoly E) <= 1.
  Proof.
    move=> x; rewrite leqNgt -root_le_mu ?XpolyN0 //.
    apply/negP; case/Pdiv.IdomainMonic.dvdpP.
    + by rewrite monic_exp ?monicXsubC.
    move=> /= p Hfactor; move: (congr1 (size : {poly _} -> _) Hfactor).
    have HpN0: p != 0.
    + by apply/negP => /eqP Hp; move/eqP: Hfactor;
        rewrite Hp mul0r (negbTE (XpolyN0 _)).
    rewrite size_Xpoly size_proper_mul; last first.
    + rewrite mulf_neq0 // lead_coef_eq0 //.
      by rewrite expf_neq0 ?polyXsubC_eq0.
    rewrite size_exp_XsubC addnC /=; case/esym; case/polyseq2.
    move=> [p2 p1] /= Hp1N0 Ep; move/polyP: Hfactor => EC.
    + move: (EC 3); unlock Xpoly; rewrite coef_Poly coefM.
      rewrite !big_ord_recr /= big_ord0 add0r Ep sqpp_sub_polyseq /=.
      rewrite !simp => Ep1; rewrite -!Ep1 in Ep => {Ep1 Hp1N0}.
    + move: (EC 2); unlock Xpoly; rewrite coef_Poly coefM.
      rewrite !big_ord_recr /= big_ord0 add0r Ep sqpp_sub_polyseq /=.
      rewrite !simp => /esym /eqP; rewrite subr_eq0=> /eqP Ep2.
      rewrite Ep2 in Ep => {Ep2}.
    + move: (EC 1%N); unlock Xpoly; rewrite coef_Poly coefM.
      rewrite !big_ord_recr /= big_ord0 add0r Ep sqpp_sub_polyseq /=.
      rewrite mul1r -mulrN mulrCA 2!mulrA -natrM /=.
      rewrite mulrN -mulrA -expr2; move/(congr1 -%R).
      rewrite opprD opprK -{2}[x^+2]mul1r -mulrBl.
      rewrite -(@natrB _ _ 1) //; move/(congr1 -%R); rewrite opprK=> Ea.
    + move: (EC 0%N); unlock Xpoly; rewrite coef_Poly coefM.
      rewrite !big_ord_recr /= big_ord0 add0r Ep sqpp_sub_polyseq /=.
      rewrite -mulrA -exprS => Eb.
    move: (ecu_DN0 E).
    rewrite Ea Eb exprNn exprMn -exprM -signr_odd expr1.
    rewrite mulN1r mulrN -natrX mulrA -natrM.
    rewrite exprMn -exprM -natrX [27%:R * _]mulrA -natrM.
    by rewrite addrC subrr eqxx.
  Qed.
End ECTheory.

(* -------------------------------------------------------------------- *)
Section XPolyClosed.
  Variable K : ecuDecFieldType.
  Variable E : ecuType K.

  Hypothesis closedK : GRing.ClosedField.axiom K.

  Local Notation clK := (ClosedFieldType K closedK).

  Lemma Xpoly_factor:
    exists2 cs : 3.-tuple K,
      (uniq cs) & Xpoly E = \prod_(c <- cs) ('X - c%:P).
  Proof.
    move: (PolyClosed.roots_factor_theorem_f closedK (Xpoly E)).
    rewrite (monicP (Xpoly_monic E)) scale1r; set cs := roots _ => ->.
    have size_cs: size cs == 3 by rewrite (@roots_size clK) size_Xpoly.
    exists (Tuple size_cs)=> //=; apply: count_mem_uniq.
    move=> k; rewrite -roots_mu ?XpolyN0 //; move: (smooth E k).
    rewrite leq_eqVlt ltnS leqn0 rootsP ?XpolyN0 // mem_root -rootE.
    by rewrite -mu_gt0 ?XpolyN0 //; case/orP=> /eqP->.
  Qed.
End XPolyClosed.

(*
*** Local Variables: ***
*** coq-load-path: ("ssreflect" "common" ".") ***
*** End: ***
 *)

