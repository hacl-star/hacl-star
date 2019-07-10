(set-option :global-decls false)
(set-option :smt.mbqi false)
(set-option :auto_config false)
(set-option :produce-unsat-cores true)
(set-option :model true)
(set-option :smt.case_split 3)
(set-option :smt.relevancy 2)
(declare-sort FString)
(declare-fun FString_constr_id (FString) Int)

(declare-sort Term)
(declare-fun Term_constr_id (Term) Int)
(declare-sort Dummy_sort)
(declare-fun Dummy_value () Dummy_sort)
(declare-datatypes () ((Fuel 
(ZFuel) 
(SFuel (prec Fuel)))))
(declare-fun MaxIFuel () Fuel)
(declare-fun MaxFuel () Fuel)
(declare-fun PreType (Term) Term)
(declare-fun Valid (Term) Bool)
(declare-fun HasTypeFuel (Fuel Term Term) Bool)
(define-fun HasTypeZ ((x Term) (t Term)) Bool
(HasTypeFuel ZFuel x t))
(define-fun HasType ((x Term) (t Term)) Bool
(HasTypeFuel MaxIFuel x t))
(declare-fun IsTotFun (Term) Bool)

                ;;fuel irrelevance
(assert (forall ((f Fuel) (x Term) (t Term))
(! (= (HasTypeFuel (SFuel f) x t)
(HasTypeZ x t))
:pattern ((HasTypeFuel (SFuel f) x t)))))
(declare-fun NoHoist (Term Bool) Bool)
;;no-hoist
(assert (forall ((dummy Term) (b Bool))
(! (= (NoHoist dummy b)
b)
:pattern ((NoHoist dummy b)))))
(define-fun  IsTyped ((x Term)) Bool
(exists ((t Term)) (HasTypeZ x t)))
(declare-fun ApplyTF (Term Fuel) Term)
(declare-fun ApplyTT (Term Term) Term)
(declare-fun Rank (Term) Int)
(declare-fun Closure (Term) Term)
(declare-fun ConsTerm (Term Term) Term)
(declare-fun ConsFuel (Fuel Term) Term)
(declare-fun Tm_uvar (Int) Term)
(define-fun Reify ((x Term)) Term x)
(declare-fun Prims.precedes (Term Term Term Term) Term)
(declare-fun Range_const (Int) Term)
(declare-fun _mul (Int Int) Int)
(declare-fun _div (Int Int) Int)
(declare-fun _mod (Int Int) Int)
(declare-fun __uu__PartialApp () Term)
(assert (forall ((x Int) (y Int)) (! (= (_mul x y) (* x y)) :pattern ((_mul x y)))))
(assert (forall ((x Int) (y Int)) (! (= (_div x y) (div x y)) :pattern ((_div x y)))))
(assert (forall ((x Int) (y Int)) (! (= (_mod x y) (mod x y)) :pattern ((_mod x y)))))
(declare-fun _rmul (Real Real) Real)
(declare-fun _rdiv (Real Real) Real)
(assert (forall ((x Real) (y Real)) (! (= (_rmul x y) (* x y)) :pattern ((_rmul x y)))))
(assert (forall ((x Real) (y Real)) (! (= (_rdiv x y) (/ x y)) :pattern ((_rdiv x y)))))
; <start constructor FString_const>

;;;;;;;;;;;;;;;;Constructor
(declare-fun FString_const (Int) FString)
;;;;;;;;;;;;;;;;Constructor distinct
;;; Fact-ids: 
(assert (! (forall ((@u0 Int))
 (! (= 0
(FString_constr_id (FString_const @u0)))
 

:pattern ((FString_const @u0))
:qid constructor_distinct_FString_const))
:named constructor_distinct_FString_const))
;;;;;;;;;;;;;;;;Projector
(declare-fun FString_const_proj_0 (FString) Int)
;;;;;;;;;;;;;;;;Projection inverse
;;; Fact-ids: 
(assert (! (forall ((@u0 Int))
 (! (= (FString_const_proj_0 (FString_const @u0))
@u0)
 

:pattern ((FString_const @u0))
:qid projection_inverse_FString_const_proj_0))
:named projection_inverse_FString_const_proj_0))
;;;;;;;;;;;;;;;;Discriminator definition
(define-fun is-FString_const ((__@u0 FString)) Bool
 (and (= (FString_constr_id __@u0)
0)
(= __@u0
(FString_const (FString_const_proj_0 __@u0)))))

; </end constructor FString_const>


; <start constructor Tm_type>

;;;;;;;;;;;;;;;;Constructor
(declare-fun Tm_type () Term)
;;;;;;;;;;;;;;;;Constructor distinct
;;; Fact-ids: 
(assert (! (= 2
(Term_constr_id Tm_type))
:named constructor_distinct_Tm_type))
;;;;;;;;;;;;;;;;Discriminator definition
(define-fun is-Tm_type ((__@x0 Term)) Bool
 (and (= (Term_constr_id __@x0)
2)
(= __@x0
Tm_type)))

; </end constructor Tm_type>


; <start constructor Tm_arrow>

;;;;;;;;;;;;;;;;Constructor
(declare-fun Tm_arrow (Int) Term)
;;;;;;;;;;;;;;;;Constructor distinct
;;; Fact-ids: 
(assert (! (forall ((@u0 Int))
 (! (= 3
(Term_constr_id (Tm_arrow @u0)))
 

:pattern ((Tm_arrow @u0))
:qid constructor_distinct_Tm_arrow))
:named constructor_distinct_Tm_arrow))
;;;;;;;;;;;;;;;;Projector
(declare-fun Tm_arrow_id (Term) Int)
;;;;;;;;;;;;;;;;Projection inverse
;;; Fact-ids: 
(assert (! (forall ((@u0 Int))
 (! (= (Tm_arrow_id (Tm_arrow @u0))
@u0)
 

:pattern ((Tm_arrow @u0))
:qid projection_inverse_Tm_arrow_id))
:named projection_inverse_Tm_arrow_id))
;;;;;;;;;;;;;;;;Discriminator definition
(define-fun is-Tm_arrow ((__@x0 Term)) Bool
 (and (= (Term_constr_id __@x0)
3)
(= __@x0
(Tm_arrow (Tm_arrow_id __@x0)))))

; </end constructor Tm_arrow>


; <start constructor Tm_unit>

;;;;;;;;;;;;;;;;Constructor
(declare-fun Tm_unit () Term)
;;;;;;;;;;;;;;;;Constructor distinct
;;; Fact-ids: 
(assert (! (= 6
(Term_constr_id Tm_unit))
:named constructor_distinct_Tm_unit))
;;;;;;;;;;;;;;;;Discriminator definition
(define-fun is-Tm_unit ((__@x0 Term)) Bool
 (and (= (Term_constr_id __@x0)
6)
(= __@x0
Tm_unit)))

; </end constructor Tm_unit>


; <start constructor BoxInt>

;;;;;;;;;;;;;;;;Constructor
(declare-fun BoxInt (Int) Term)
;;;;;;;;;;;;;;;;Constructor distinct
;;; Fact-ids: 
(assert (! (forall ((@u0 Int))
 (! (= 7
(Term_constr_id (BoxInt @u0)))
 

:pattern ((BoxInt @u0))
:qid constructor_distinct_BoxInt))
:named constructor_distinct_BoxInt))
;;;;;;;;;;;;;;;;Projector
(declare-fun BoxInt_proj_0 (Term) Int)
;;;;;;;;;;;;;;;;Projection inverse
;;; Fact-ids: 
(assert (! (forall ((@u0 Int))
 (! (= (BoxInt_proj_0 (BoxInt @u0))
@u0)
 

:pattern ((BoxInt @u0))
:qid projection_inverse_BoxInt_proj_0))
:named projection_inverse_BoxInt_proj_0))
;;;;;;;;;;;;;;;;Discriminator definition
(define-fun is-BoxInt ((__@x0 Term)) Bool
 (and (= (Term_constr_id __@x0)
7)
(= __@x0
(BoxInt (BoxInt_proj_0 __@x0)))))

; </end constructor BoxInt>


; <start constructor BoxBool>

;;;;;;;;;;;;;;;;Constructor
(declare-fun BoxBool (Bool) Term)
;;;;;;;;;;;;;;;;Constructor distinct
;;; Fact-ids: 
(assert (! (forall ((@u0 Bool))
 (! (= 8
(Term_constr_id (BoxBool @u0)))
 

:pattern ((BoxBool @u0))
:qid constructor_distinct_BoxBool))
:named constructor_distinct_BoxBool))
;;;;;;;;;;;;;;;;Projector
(declare-fun BoxBool_proj_0 (Term) Bool)
;;;;;;;;;;;;;;;;Projection inverse
;;; Fact-ids: 
(assert (! (forall ((@u0 Bool))
 (! (= (BoxBool_proj_0 (BoxBool @u0))
@u0)
 

:pattern ((BoxBool @u0))
:qid projection_inverse_BoxBool_proj_0))
:named projection_inverse_BoxBool_proj_0))
;;;;;;;;;;;;;;;;Discriminator definition
(define-fun is-BoxBool ((__@x0 Term)) Bool
 (and (= (Term_constr_id __@x0)
8)
(= __@x0
(BoxBool (BoxBool_proj_0 __@x0)))))

; </end constructor BoxBool>


; <start constructor BoxString>

;;;;;;;;;;;;;;;;Constructor
(declare-fun BoxString (FString) Term)
;;;;;;;;;;;;;;;;Constructor distinct
;;; Fact-ids: 
(assert (! (forall ((@u0 FString))
 (! (= 9
(Term_constr_id (BoxString @u0)))
 

:pattern ((BoxString @u0))
:qid constructor_distinct_BoxString))
:named constructor_distinct_BoxString))
;;;;;;;;;;;;;;;;Projector
(declare-fun BoxString_proj_0 (Term) FString)
;;;;;;;;;;;;;;;;Projection inverse
;;; Fact-ids: 
(assert (! (forall ((@u0 FString))
 (! (= (BoxString_proj_0 (BoxString @u0))
@u0)
 

:pattern ((BoxString @u0))
:qid projection_inverse_BoxString_proj_0))
:named projection_inverse_BoxString_proj_0))
;;;;;;;;;;;;;;;;Discriminator definition
(define-fun is-BoxString ((__@x0 Term)) Bool
 (and (= (Term_constr_id __@x0)
9)
(= __@x0
(BoxString (BoxString_proj_0 __@x0)))))

; </end constructor BoxString>


; <start constructor BoxReal>

;;;;;;;;;;;;;;;;Constructor
(declare-fun BoxReal (Real) Term)
;;;;;;;;;;;;;;;;Constructor distinct
;;; Fact-ids: 
(assert (! (forall ((@u0 Real))
 (! (= 10
(Term_constr_id (BoxReal @u0)))
 

:pattern ((BoxReal @u0))
:qid constructor_distinct_BoxReal))
:named constructor_distinct_BoxReal))
;;;;;;;;;;;;;;;;Projector
(declare-fun BoxReal_proj_0 (Term) Real)
;;;;;;;;;;;;;;;;Projection inverse
;;; Fact-ids: 
(assert (! (forall ((@u0 Real))
 (! (= (BoxReal_proj_0 (BoxReal @u0))
@u0)
 

:pattern ((BoxReal @u0))
:qid projection_inverse_BoxReal_proj_0))
:named projection_inverse_BoxReal_proj_0))
;;;;;;;;;;;;;;;;Discriminator definition
(define-fun is-BoxReal ((__@x0 Term)) Bool
 (and (= (Term_constr_id __@x0)
10)
(= __@x0
(BoxReal (BoxReal_proj_0 __@x0)))))

; </end constructor BoxReal>


; <start constructor LexCons>

;;;;;;;;;;;;;;;;Constructor
(declare-fun LexCons (Term Term Term) Term)
;;;;;;;;;;;;;;;;Constructor distinct
;;; Fact-ids: 
(assert (! (forall ((@x0 Term) (@x1 Term) (@x2 Term))
 (! (= 11
(Term_constr_id (LexCons @x0
@x1
@x2)))
 

:pattern ((LexCons @x0
@x1
@x2))
:qid constructor_distinct_LexCons))
:named constructor_distinct_LexCons))
;;;;;;;;;;;;;;;;Projector
(declare-fun LexCons_0 (Term) Term)
;;;;;;;;;;;;;;;;Projection inverse
;;; Fact-ids: 
(assert (! (forall ((@x0 Term) (@x1 Term) (@x2 Term))
 (! (= (LexCons_0 (LexCons @x0
@x1
@x2))
@x0)
 

:pattern ((LexCons @x0
@x1
@x2))
:qid projection_inverse_LexCons_0))
:named projection_inverse_LexCons_0))
;;;;;;;;;;;;;;;;Projector
(declare-fun LexCons_1 (Term) Term)
;;;;;;;;;;;;;;;;Projection inverse
;;; Fact-ids: 
(assert (! (forall ((@x0 Term) (@x1 Term) (@x2 Term))
 (! (= (LexCons_1 (LexCons @x0
@x1
@x2))
@x1)
 

:pattern ((LexCons @x0
@x1
@x2))
:qid projection_inverse_LexCons_1))
:named projection_inverse_LexCons_1))
;;;;;;;;;;;;;;;;Projector
(declare-fun LexCons_2 (Term) Term)
;;;;;;;;;;;;;;;;Projection inverse
;;; Fact-ids: 
(assert (! (forall ((@x0 Term) (@x1 Term) (@x2 Term))
 (! (= (LexCons_2 (LexCons @x0
@x1
@x2))
@x2)
 

:pattern ((LexCons @x0
@x1
@x2))
:qid projection_inverse_LexCons_2))
:named projection_inverse_LexCons_2))
;;;;;;;;;;;;;;;;Discriminator definition
(define-fun is-LexCons ((__@x0 Term)) Bool
 (and (= (Term_constr_id __@x0)
11)
(= __@x0
(LexCons (LexCons_0 __@x0)
(LexCons_1 __@x0)
(LexCons_2 __@x0)))))

; </end constructor LexCons>

(define-fun is-Prims.LexCons ((t Term)) Bool 
(is-LexCons t))
(declare-fun Prims.lex_t () Term)
(assert (forall ((t1 Term) (t2 Term) (x1 Term) (x2 Term) (y1 Term) (y2 Term))
(iff (Valid (Prims.precedes Prims.lex_t Prims.lex_t (LexCons t1 x1 x2) (LexCons t2 y1 y2)))
(or (Valid (Prims.precedes t1 t2 x1 y1))
(and (= x1 y1)
(Valid (Prims.precedes Prims.lex_t Prims.lex_t x2 y2)))))))
(assert (forall ((t1 Term) (t2 Term) (e1 Term) (e2 Term))
(! (iff (Valid (Prims.precedes t1 t2 e1 e2))
(Valid (Prims.precedes Prims.lex_t Prims.lex_t e1 e2)))
:pattern (Prims.precedes t1 t2 e1 e2))))
(assert (forall ((t1 Term) (t2 Term))
(! (iff (Valid (Prims.precedes Prims.lex_t Prims.lex_t t1 t2)) 
(< (Rank t1) (Rank t2)))
:pattern ((Prims.precedes Prims.lex_t Prims.lex_t t1 t2)))))
(assert (forall ((e Term) (t Term))
(! (implies (HasType e t)
(Valid t))
:pattern ((HasType e t)
(Valid t))
:qid __prelude_valid_intro)))


;;; Start module Prims

; <Start encoding Prims.attribute>

(declare-fun Prims.attribute () Term)

; </end encoding Prims.attribute>


; <Start encoding Prims.cps>

(declare-fun Prims.cps () Term)

; </end encoding Prims.cps>


; <Start encoding Prims.hasEq>

(declare-fun Prims.hasEq (Term) Term)
(declare-fun Tm_arrow_ef9cb512a25ee351fa5536d617490497 () Term)
(declare-fun Prims.hasEq@tok () Term)

; </end encoding Prims.hasEq>


; <Start encoding Prims.eqtype>

(declare-fun Prims.eqtype () Term)
(declare-fun Tm_refine_414d0a9f578ab0048252f8c8f552b99f () Term)

; </end encoding Prims.eqtype>


; <Start encoding Prims.bool>

(declare-fun Prims.bool () Term)

; </end encoding Prims.bool>


; <Start encoding Prims.c_False>

;;;;;;;;;;;;;;;;Constructor
(declare-fun Prims.c_False () Term)

; <Start encoding Prims.c_False>


; <start constructor Prims.c_False>

;;;;;;;;;;;;;;;;Discriminator definition
(define-fun is-Prims.c_False ((__@x0 Term)) Bool
 (and (= (Term_constr_id __@x0)
111)
(= __@x0
Prims.c_False)))

; </end constructor Prims.c_False>


; </end encoding Prims.c_False>


; </end encoding Prims.c_False>


; <Start encoding >

;;;;;;;;;;;;;;;;Constructor
(declare-fun Prims.c_True () Term)
;;;;;;;;;;;;;;;;Constructor
(declare-fun Prims.T () Term)
;;;;;;;;;;;;;;;;data constructor proxy: T
(declare-fun Prims.T@tok () Term)

; <Start encoding Prims.c_True>


; <start constructor Prims.c_True>

;;;;;;;;;;;;;;;;Discriminator definition
(define-fun is-Prims.c_True ((__@x0 Term)) Bool
 (and (= (Term_constr_id __@x0)
116)
(= __@x0
Prims.c_True)))

; </end constructor Prims.c_True>


; </end encoding Prims.c_True>


; <Start encoding Prims.T>


; <start constructor Prims.T>

;;;;;;;;;;;;;;;;Discriminator definition
(define-fun is-Prims.T ((__@x0 Term)) Bool
 (and (= (Term_constr_id __@x0)
122)
(= __@x0
Prims.T)))

; </end constructor Prims.T>


; </end encoding Prims.T>


; </end encoding >


; <Start encoding Prims.uu___is_T>

(declare-fun Prims.uu___is_T (Term) Term)
(declare-fun Tm_arrow_1ca40bedfbd5ea31ac81af74c119a09e () Term)
(declare-fun Prims.uu___is_T@tok () Term)

; </end encoding Prims.uu___is_T>


; <Start encoding Prims.unit>

(declare-fun Prims.unit () Term)

; </end encoding Prims.unit>


; <Start encoding Prims.squash>

(declare-fun Prims.squash (Term) Term)

(declare-fun Prims.squash@tok () Term)
(declare-fun Tm_refine_2de20c066034c13bf76e9c0b94f4806c (Term) Term)

; </end encoding Prims.squash>


; <Start encoding Prims.auto_squash>

(declare-fun Prims.auto_squash (Term) Term)

(declare-fun Prims.auto_squash@tok () Term)

; </end encoding Prims.auto_squash>


; <Start encoding Prims.logical>

(declare-fun Prims.logical () Term)

; </end encoding Prims.logical>


; <Start encoding Prims.smt_theory_symbol>

(declare-fun Prims.smt_theory_symbol () Term)

; </end encoding Prims.smt_theory_symbol>


; <Start encoding Prims.l_True>

(declare-fun Prims.l_True () Term)

; </end encoding Prims.l_True>


; <Start encoding Prims.l_False>

(declare-fun Prims.l_False () Term)

; </end encoding Prims.l_False>


; <Start encoding >

;;;;;;;;;;;;;;;;Constructor
(declare-fun Prims.equals (Term Term Term) Term)
;;;;;;;;;;;;;;;;Projector
(declare-fun Prims.equals@x0 (Term) Term)
;;;;;;;;;;;;;;;;Projector
(declare-fun Prims.equals@x1 (Term) Term)
;;;;;;;;;;;;;;;;Projector
(declare-fun Prims.equals@x2 (Term) Term)
;;;;;;;;;;;;;;;;token
(declare-fun Prims.equals@tok () Term)
;;;;;;;;;;;;;;;;Constructor
(declare-fun Prims.Refl (Term Term) Term)
;;;;;;;;;;;;;;;;Projector
(declare-fun Prims.Refl_a (Term) Term)
;;;;;;;;;;;;;;;;Projector
(declare-fun Prims.Refl_x (Term) Term)
;;;;;;;;;;;;;;;;data constructor proxy: Refl
(declare-fun Prims.Refl@tok () Term)
(declare-fun Tm_arrow_8e00c6263684633abbc1d1a87608e391 () Term)

; <Start encoding Prims.equals>


; <start constructor Prims.equals>

;;;;;;;;;;;;;;;;Discriminator definition
(define-fun is-Prims.equals ((__@x0 Term)) Bool
 (and (= (Term_constr_id __@x0)
134)
(exists ((@x0 Term) (@x1 Term) (@x2 Term))
 (! (= __@x0
(Prims.equals @x0
@x1
@x2))
 
;;no pats
:qid is-Prims.equals))))

; </end constructor Prims.equals>


; </end encoding Prims.equals>


; <Start encoding Prims.Refl>


; <start constructor Prims.Refl>

;;;;;;;;;;;;;;;;Discriminator definition
(define-fun is-Prims.Refl ((__@x0 Term)) Bool
 (and (= (Term_constr_id __@x0)
141)
(= __@x0
(Prims.Refl (Prims.Refl_a __@x0)
(Prims.Refl_x __@x0)))))

; </end constructor Prims.Refl>


; </end encoding Prims.Refl>


; </end encoding >


; <Start encoding Prims.uu___is_Refl>

(declare-fun Prims.uu___is_Refl (Term Term Term Term) Term)
(declare-fun Tm_arrow_2a4540f76c8969717ea911077d7b4d15 () Term)
(declare-fun Prims.uu___is_Refl@tok () Term)

; </end encoding Prims.uu___is_Refl>


; <Start encoding Prims.eq2>

(declare-fun Prims.eq2 (Term Term Term) Term)
(declare-fun Tm_arrow_1ec40cec1da281b45a559c74dd57f3b7 () Term)
(declare-fun Prims.eq2@tok () Term)

; </end encoding Prims.eq2>


; <Start encoding >

;;;;;;;;;;;;;;;;Constructor
(declare-fun Prims.h_equals (Term Term Term Term) Term)
;;;;;;;;;;;;;;;;Projector
(declare-fun Prims.h_equals@x0 (Term) Term)
;;;;;;;;;;;;;;;;Projector
(declare-fun Prims.h_equals@x1 (Term) Term)
;;;;;;;;;;;;;;;;Projector
(declare-fun Prims.h_equals@x2 (Term) Term)
;;;;;;;;;;;;;;;;Projector
(declare-fun Prims.h_equals@x3 (Term) Term)
;;;;;;;;;;;;;;;;token
(declare-fun Prims.h_equals@tok () Term)
;;;;;;;;;;;;;;;;Constructor
(declare-fun Prims.HRefl (Term Term) Term)
;;;;;;;;;;;;;;;;Projector
(declare-fun Prims.HRefl_a (Term) Term)
;;;;;;;;;;;;;;;;Projector
(declare-fun Prims.HRefl_x (Term) Term)
;;;;;;;;;;;;;;;;data constructor proxy: HRefl
(declare-fun Prims.HRefl@tok () Term)
(declare-fun Tm_arrow_88c25e785888d4e0c2c73392ffd9505d () Term)

; <Start encoding Prims.h_equals>


; <start constructor Prims.h_equals>

;;;;;;;;;;;;;;;;Discriminator definition
(define-fun is-Prims.h_equals ((__@x0 Term)) Bool
 (and (= (Term_constr_id __@x0)
149)
(exists ((@x0 Term) (@x1 Term) (@x2 Term) (@x3 Term))
 (! (= __@x0
(Prims.h_equals @x0
@x1
@x2
@x3))
 
;;no pats
:qid is-Prims.h_equals))))

; </end constructor Prims.h_equals>


; </end encoding Prims.h_equals>


; <Start encoding Prims.HRefl>


; <start constructor Prims.HRefl>

;;;;;;;;;;;;;;;;Discriminator definition
(define-fun is-Prims.HRefl ((__@x0 Term)) Bool
 (and (= (Term_constr_id __@x0)
156)
(= __@x0
(Prims.HRefl (Prims.HRefl_a __@x0)
(Prims.HRefl_x __@x0)))))

; </end constructor Prims.HRefl>


; </end encoding Prims.HRefl>


; </end encoding >


; <Start encoding Prims.uu___is_HRefl>

(declare-fun Prims.uu___is_HRefl (Term Term Term Term Term) Term)
(declare-fun Tm_arrow_985220cbab27fbd2cc6dbc457b76b91a () Term)
(declare-fun Prims.uu___is_HRefl@tok () Term)

; </end encoding Prims.uu___is_HRefl>


; <Start encoding Prims.eq3>

(declare-fun Prims.eq3 (Term Term Term Term) Term)
(declare-fun Tm_arrow_7fcb145b23c2ac843afd9b126c4f71a9 () Term)
(declare-fun Prims.eq3@tok () Term)

; </end encoding Prims.eq3>


; <Skipped Prims.op_Equals_Equals_Equals/>


; <Start encoding Prims.b2t>

(declare-fun Prims.b2t (Term) Term)

; </end encoding Prims.b2t>


; <Start encoding >

;;;;;;;;;;;;;;;;Constructor
(declare-fun Prims.c_and (Term Term) Term)
;;;;;;;;;;;;;;;;Projector
(declare-fun Prims.c_and@x0 (Term) Term)
;;;;;;;;;;;;;;;;Projector
(declare-fun Prims.c_and@x1 (Term) Term)
;;;;;;;;;;;;;;;;token
(declare-fun Prims.c_and@tok () Term)
;;;;;;;;;;;;;;;;Constructor
(declare-fun Prims.And (Term Term Term Term) Term)
;;;;;;;;;;;;;;;;Projector
(declare-fun Prims.And_p (Term) Term)
;;;;;;;;;;;;;;;;Projector
(declare-fun Prims.And_q (Term) Term)
;;;;;;;;;;;;;;;;Projector
(declare-fun Prims.And__0 (Term) Term)
;;;;;;;;;;;;;;;;Projector
(declare-fun Prims.And__1 (Term) Term)
;;;;;;;;;;;;;;;;data constructor proxy: And
(declare-fun Prims.And@tok () Term)
(declare-fun Tm_arrow_c964acbbcf3ac1f157b4be52412de0f2 () Term)

; <Start encoding Prims.c_and>


; <start constructor Prims.c_and>

;;;;;;;;;;;;;;;;Discriminator definition
(define-fun is-Prims.c_and ((__@x0 Term)) Bool
 (and (= (Term_constr_id __@x0)
164)
(exists ((@x0 Term) (@x1 Term))
 (! (= __@x0
(Prims.c_and @x0
@x1))
 
;;no pats
:qid is-Prims.c_and))))

; </end constructor Prims.c_and>


; </end encoding Prims.c_and>


; <Start encoding Prims.And>


; <start constructor Prims.And>

;;;;;;;;;;;;;;;;Discriminator definition
(define-fun is-Prims.And ((__@x0 Term)) Bool
 (and (= (Term_constr_id __@x0)
171)
(= __@x0
(Prims.And (Prims.And_p __@x0)
(Prims.And_q __@x0)
(Prims.And__0 __@x0)
(Prims.And__1 __@x0)))))

; </end constructor Prims.And>


; </end encoding Prims.And>


; </end encoding >


; <Start encoding Prims.uu___is_And>

(declare-fun Prims.uu___is_And (Term Term Term) Term)
(declare-fun Tm_arrow_98dc03784ff39a101fb534007f473933 () Term)
(declare-fun Prims.uu___is_And@tok () Term)

; </end encoding Prims.uu___is_And>


; <Start encoding Prims.__proj__And__item___0>

(declare-fun Prims.__proj__And__item___0 (Term Term Term) Term)
(declare-fun Tm_arrow_62000c87a2ac04dc4129db0bf2e4a484 () Term)
(declare-fun Prims.__proj__And__item___0@tok () Term)

; </end encoding Prims.__proj__And__item___0>


; <Start encoding Prims.__proj__And__item___1>

(declare-fun Prims.__proj__And__item___1 (Term Term Term) Term)
(declare-fun Tm_arrow_74ecbc1aa6be8c1f078b3f4a04e85892 () Term)
(declare-fun Prims.__proj__And__item___1@tok () Term)

; </end encoding Prims.__proj__And__item___1>


; <Start encoding Prims.l_and>

(declare-fun Prims.l_and (Term Term) Term)
(declare-fun Tm_arrow_289ee2cc5874944bf725b9e3db8c0fd6 () Term)
(declare-fun Prims.l_and@tok () Term)

; </end encoding Prims.l_and>


; <Start encoding >

;;;;;;;;;;;;;;;;Constructor
(declare-fun Prims.c_or (Term Term) Term)
;;;;;;;;;;;;;;;;Projector
(declare-fun Prims.c_or@x0 (Term) Term)
;;;;;;;;;;;;;;;;Projector
(declare-fun Prims.c_or@x1 (Term) Term)
;;;;;;;;;;;;;;;;token
(declare-fun Prims.c_or@tok () Term)
;;;;;;;;;;;;;;;;Constructor
(declare-fun Prims.Left (Term Term Term) Term)
;;;;;;;;;;;;;;;;Projector
(declare-fun Prims.Left_p (Term) Term)
;;;;;;;;;;;;;;;;Projector
(declare-fun Prims.Left_q (Term) Term)
;;;;;;;;;;;;;;;;Projector
(declare-fun Prims.Left__0 (Term) Term)
;;;;;;;;;;;;;;;;data constructor proxy: Left
(declare-fun Prims.Left@tok () Term)
;;;;;;;;;;;;;;;;Constructor
(declare-fun Prims.Right (Term Term Term) Term)
;;;;;;;;;;;;;;;;Projector
(declare-fun Prims.Right_p (Term) Term)
;;;;;;;;;;;;;;;;Projector
(declare-fun Prims.Right_q (Term) Term)
;;;;;;;;;;;;;;;;Projector
(declare-fun Prims.Right__0 (Term) Term)
;;;;;;;;;;;;;;;;data constructor proxy: Right
(declare-fun Prims.Right@tok () Term)
(declare-fun Tm_arrow_fd80693647ee9c426b2ca647008a9d5a () Term)
(declare-fun Tm_arrow_e817f0b7fc30ff1a4a48917b36fbcdd7 () Term)

; <Start encoding Prims.c_or>


; <start constructor Prims.c_or>

;;;;;;;;;;;;;;;;Discriminator definition
(define-fun is-Prims.c_or ((__@x0 Term)) Bool
 (and (= (Term_constr_id __@x0)
183)
(exists ((@x0 Term) (@x1 Term))
 (! (= __@x0
(Prims.c_or @x0
@x1))
 
;;no pats
:qid is-Prims.c_or))))

; </end constructor Prims.c_or>


; </end encoding Prims.c_or>


; <Start encoding Prims.Left>


; <start constructor Prims.Left>

;;;;;;;;;;;;;;;;Discriminator definition
(define-fun is-Prims.Left ((__@x0 Term)) Bool
 (and (= (Term_constr_id __@x0)
190)
(= __@x0
(Prims.Left (Prims.Left_p __@x0)
(Prims.Left_q __@x0)
(Prims.Left__0 __@x0)))))

; </end constructor Prims.Left>


; </end encoding Prims.Left>


; <Start encoding Prims.Right>


; <start constructor Prims.Right>

;;;;;;;;;;;;;;;;Discriminator definition
(define-fun is-Prims.Right ((__@x0 Term)) Bool
 (and (= (Term_constr_id __@x0)
195)
(= __@x0
(Prims.Right (Prims.Right_p __@x0)
(Prims.Right_q __@x0)
(Prims.Right__0 __@x0)))))

; </end constructor Prims.Right>


; </end encoding Prims.Right>


; </end encoding >


; <Start encoding Prims.uu___is_Left>

(declare-fun Prims.uu___is_Left (Term Term Term) Term)
(declare-fun Tm_arrow_0f4b00d5a737ef6de69227e014837c34 () Term)
(declare-fun Prims.uu___is_Left@tok () Term)

; </end encoding Prims.uu___is_Left>


; <Start encoding Prims.__proj__Left__item___0>

(declare-fun Tm_refine_51387c0a7ef77e43ab89d4ae2b6b464d (Term Term) Term)
(declare-fun Prims.__proj__Left__item___0 (Term Term Term) Term)

(declare-fun Tm_arrow_e072c573e2fe374200b0390c4a6c5fa4 () Term)
(declare-fun Prims.__proj__Left__item___0@tok () Term)

; </end encoding Prims.__proj__Left__item___0>


; <Start encoding Prims.uu___is_Right>

(declare-fun Prims.uu___is_Right (Term Term Term) Term)

(declare-fun Prims.uu___is_Right@tok () Term)

; </end encoding Prims.uu___is_Right>


; <Start encoding Prims.__proj__Right__item___0>

(declare-fun Tm_refine_95f078f2b9cfbd740f9afd162814a526 (Term Term) Term)
(declare-fun Prims.__proj__Right__item___0 (Term Term Term) Term)

(declare-fun Tm_arrow_9ffbbc9e6859bf06a2b5db4593c4f0d9 () Term)
(declare-fun Prims.__proj__Right__item___0@tok () Term)

; </end encoding Prims.__proj__Right__item___0>


; <Start encoding Prims.l_or>

(declare-fun Prims.l_or (Term Term) Term)

(declare-fun Prims.l_or@tok () Term)

; </end encoding Prims.l_or>


; <Start encoding Prims.l_imp>

(declare-fun Prims.l_imp (Term Term) Term)

(declare-fun Prims.l_imp@tok () Term)
(declare-fun Tm_ghost_arrow_0283b8a2a36bbec52abac4e3d837674a (Term Term) Term)

; </end encoding Prims.l_imp>


; <Start encoding Prims.l_iff>

(declare-fun Prims.l_iff (Term Term) Term)

(declare-fun Prims.l_iff@tok () Term)

; </end encoding Prims.l_iff>


; <Start encoding Prims.l_not>

(declare-fun Prims.l_not (Term) Term)
(declare-fun Tm_arrow_8178e3b6934aa50ea45bb0ccea2d9711 () Term)
(declare-fun Prims.l_not@tok () Term)

; </end encoding Prims.l_not>


; <Skipped Prims.l_ITE/>


; <Skipped Prims.precedes/>


; <Start encoding Prims.has_type>

(declare-fun Prims.has_type (Term Term Term) Term)
(declare-fun Tm_arrow_b5d8ed0243b8c7c893f2b329de57c62b () Term)
(declare-fun Prims.has_type@tok () Term)

; </end encoding Prims.has_type>


; <Start encoding Prims.l_Forall>

(declare-fun Tm_arrow_2eaa01e78f73e9bab5d0955fc1a662da (Term) Term)
(declare-fun Prims.l_Forall (Term Term) Term)

(declare-fun Tm_arrow_977ec6901669a051ac66211b8e72666a () Term)
(declare-fun Prims.l_Forall@tok () Term)

(declare-fun Tm_ghost_arrow_3aa447697277bb40c9738c9125c3e80f (Term Term) Term)

; </end encoding Prims.l_Forall>


; <Start encoding Prims.subtype_of>

(declare-fun Prims.subtype_of (Term Term) Term)
(declare-fun Tm_arrow_28becc0427b69ebf63ea956148504d97 () Term)
(declare-fun Prims.subtype_of@tok () Term)

(declare-fun Tm_abs_2319c8dded71dc14c3f65c301c18a7ca (Term Term) Term)

; </end encoding Prims.subtype_of>


; <Start encoding Prims.prop>

(declare-fun Prims.prop () Term)
(declare-fun Tm_refine_73f210ca6e0061ed4a3150f69b8f33bf () Term)

; </end encoding Prims.prop>


; <Start encoding Prims.range>

(declare-fun Prims.range () Term)

; </end encoding Prims.range>


; <Start encoding Prims.string>

(declare-fun Prims.string () Term)

; </end encoding Prims.string>


; <Start encoding Prims.pure_pre>

(declare-fun Prims.pure_pre () Term)

; </end encoding Prims.pure_pre>


; <Start encoding Prims.pure_post'>

(declare-fun Prims.pure_post_ (Term Term) Term)
(declare-fun Tm_arrow_e4cf09589736facd1137944a1f5a00a6 () Term)
(declare-fun Prims.pure_post_@tok () Term)
(declare-fun Tm_refine_8d65e998a07dd53ec478e27017d9dba5 (Term Term) Term)
(declare-fun Tm_arrow_92458cff82f9ffee1f6e26a1c0c579f3 (Term Term) Term)

; </end encoding Prims.pure_post'>


; <Start encoding Prims.pure_post>

(declare-fun Prims.pure_post (Term) Term)

(declare-fun Prims.pure_post@tok () Term)

; </end encoding Prims.pure_post>


; <Start encoding Prims.pure_wp>

(declare-fun Prims.pure_wp (Term) Term)

(declare-fun Prims.pure_wp@tok () Term)
(declare-fun Tm_arrow_e5c03abbf8b0946a9aa7ee31bb7999a4 (Term) Term)

; </end encoding Prims.pure_wp>


; <Start encoding Prims.guard_free>

(declare-fun Prims.guard_free (Term) Term)

(declare-fun Prims.guard_free@tok () Term)

; </end encoding Prims.guard_free>


; <Skipped Prims.pure_return/>


; <Skipped Prims.pure_bind_wp/>


; <Skipped Prims.pure_if_then_else/>


; <Skipped Prims.pure_ite_wp/>


; <Skipped Prims.pure_stronger/>


; <Skipped Prims.pure_close_wp/>


; <Skipped Prims.pure_assert_p/>


; <Skipped Prims.pure_assume_p/>


; <Skipped Prims.pure_null_wp/>


; <Skipped Prims.pure_trivial/>


; <Skipped Prims.PURE/>


; <Skipped Prims.Pure/>


; <Skipped Prims.Admit/>


; <Skipped Prims.Tot/>


; <Skipped Prims.GHOST/>


; <Skipped Prims.purewp_id/>


; <Skipped />


; <Skipped Prims.GTot/>


; <Skipped Prims.Ghost/>


; <Start encoding >

;;;;;;;;;;;;;;;;Constructor
(declare-fun Prims.dtuple2 (Term Term) Term)
;;;;;;;;;;;;;;;;Projector
(declare-fun Prims.dtuple2@x0 (Term) Term)
;;;;;;;;;;;;;;;;Projector
(declare-fun Prims.dtuple2@x1 (Term) Term)
;;;;;;;;;;;;;;;;token
(declare-fun Prims.dtuple2@tok () Term)
;;;;;;;;;;;;;;;;Constructor
(declare-fun Prims.Mkdtuple2 (Term Term Term Term) Term)
;;;;;;;;;;;;;;;;Projector
(declare-fun Prims.Mkdtuple2_a (Term) Term)
;;;;;;;;;;;;;;;;Projector
(declare-fun Prims.Mkdtuple2_b (Term) Term)
;;;;;;;;;;;;;;;;Projector
(declare-fun Prims.Mkdtuple2__1 (Term) Term)
;;;;;;;;;;;;;;;;Projector
(declare-fun Prims.Mkdtuple2__2 (Term) Term)
;;;;;;;;;;;;;;;;data constructor proxy: Mkdtuple2
(declare-fun Prims.Mkdtuple2@tok () Term)



(declare-fun Tm_arrow_22a50f5c5c9bb74bac4384fb8999be8b () Term)


; <Start encoding Prims.dtuple2>


; <start constructor Prims.dtuple2>

;;;;;;;;;;;;;;;;Discriminator definition
(define-fun is-Prims.dtuple2 ((__@x0 Term)) Bool
 (and (= (Term_constr_id __@x0)
260)
(exists ((@x0 Term) (@x1 Term))
 (! (= __@x0
(Prims.dtuple2 @x0
@x1))
 
;;no pats
:qid is-Prims.dtuple2))))

; </end constructor Prims.dtuple2>


; </end encoding Prims.dtuple2>


; <Start encoding Prims.Mkdtuple2>


; <start constructor Prims.Mkdtuple2>

;;;;;;;;;;;;;;;;Discriminator definition
(define-fun is-Prims.Mkdtuple2 ((__@x0 Term)) Bool
 (and (= (Term_constr_id __@x0)
269)
(= __@x0
(Prims.Mkdtuple2 (Prims.Mkdtuple2_a __@x0)
(Prims.Mkdtuple2_b __@x0)
(Prims.Mkdtuple2__1 __@x0)
(Prims.Mkdtuple2__2 __@x0)))))

; </end constructor Prims.Mkdtuple2>


; </end encoding Prims.Mkdtuple2>


; </end encoding >


; <Start encoding Prims.dtuple2__uu___haseq>



; </end encoding Prims.dtuple2__uu___haseq>


; <Start encoding Prims.uu___is_Mkdtuple2>


(declare-fun Prims.uu___is_Mkdtuple2 (Term Term Term) Term)

(declare-fun Tm_arrow_e6f9f7cb1936ec43b52469e706dcadcc () Term)
(declare-fun Prims.uu___is_Mkdtuple2@tok () Term)

; </end encoding Prims.uu___is_Mkdtuple2>


; <Skipped Prims.uu___is_Mkdtuple2/>


; <Start encoding Prims.__proj__Mkdtuple2__item___1>


(declare-fun Prims.__proj__Mkdtuple2__item___1 (Term Term Term) Term)

(declare-fun Tm_arrow_26c013ffba39d4f7eeb4bcc80d2d4e22 () Term)
(declare-fun Prims.__proj__Mkdtuple2__item___1@tok () Term)

; </end encoding Prims.__proj__Mkdtuple2__item___1>


; <Skipped Prims.__proj__Mkdtuple2__item___1/>


; <Start encoding Prims.__proj__Mkdtuple2__item___2>


(declare-fun Prims.__proj__Mkdtuple2__item___2 (Term Term Term) Term)

(declare-fun Tm_arrow_870cc7701a0d9a8a2d6fb92427a97d66 () Term)
(declare-fun Prims.__proj__Mkdtuple2__item___2@tok () Term)

; </end encoding Prims.__proj__Mkdtuple2__item___2>


; <Skipped Prims.__proj__Mkdtuple2__item___2/>


; <Start encoding Prims.l_Exists>


(declare-fun Prims.l_Exists (Term Term) Term)


(declare-fun Prims.l_Exists@tok () Term)



; </end encoding Prims.l_Exists>


; <Start encoding Prims.int>

(declare-fun Prims.int () Term)
;;;;;;;;;;;;;;;;int typing
;;; Fact-ids: Name Prims.int; Namespace Prims
(assert (! (forall ((@u0 Int))
 (! (HasType (BoxInt @u0)
Prims.int)
 

:pattern ((BoxInt @u0))
:qid int_typing))
:named int_typing))
;;;;;;;;;;;;;;;;int inversion
;;; Fact-ids: Name Prims.int; Namespace Prims
(assert (! (forall ((@u0 Fuel) (@x1 Term))
 (! (implies (HasTypeFuel @u0
@x1
Prims.int)
(is-BoxInt @x1))
 

:pattern ((HasTypeFuel @u0
@x1
Prims.int))
:qid int_inversion))
:named int_inversion))

; </end encoding Prims.int>


; <Start encoding Prims.range_0>

(declare-fun Prims.range_0 () Term)

; </end encoding Prims.range_0>


; <Start encoding Prims.mk_range>

(declare-fun Prims.mk_range (Term Term Term Term Term) Term)
(declare-fun Tm_arrow_5f96b500c0940697aac1b5a6625b2368 () Term)
(declare-fun Prims.mk_range@tok () Term)

; </end encoding Prims.mk_range>


; <Start encoding Prims.op_AmpAmp>

(declare-fun Prims.op_AmpAmp (Term Term) Term)
(declare-fun Prims.op_AmpAmp@tok () Term)

; </end encoding Prims.op_AmpAmp>


; <Start encoding Prims.op_BarBar>

(declare-fun Prims.op_BarBar (Term Term) Term)
(declare-fun Prims.op_BarBar@tok () Term)

; </end encoding Prims.op_BarBar>


; <Start encoding Prims.op_Negation>

(declare-fun Prims.op_Negation (Term) Term)
(declare-fun Prims.op_Negation@tok () Term)

; </end encoding Prims.op_Negation>


; <Start encoding Prims.op_Multiply>

(declare-fun Prims.op_Multiply (Term Term) Term)
(declare-fun Prims.op_Multiply@tok () Term)
;;; Fact-ids: Name Prims.op_Multiply; Namespace Prims
(assert (! 
;; def=prims.fst(299,4-299,15); use=prims.fst(299,4-299,15)
(forall ((@x0 Term) (@x1 Term))
 (! (= (Prims.op_Multiply @x0
@x1)
(BoxInt (* (BoxInt_proj_0 @x0)
(BoxInt_proj_0 @x1))))
 

:pattern ((Prims.op_Multiply @x0
@x1))
:qid primitive_Prims.op_Multiply))

:named primitive_Prims.op_Multiply))

; </end encoding Prims.op_Multiply>


; <Start encoding Prims.op_Subtraction>

(declare-fun Prims.op_Subtraction (Term Term) Term)
(declare-fun Prims.op_Subtraction@tok () Term)
;;; Fact-ids: Name Prims.op_Subtraction; Namespace Prims
(assert (! 
;; def=prims.fst(303,4-303,18); use=prims.fst(303,4-303,18)
(forall ((@x0 Term) (@x1 Term))
 (! (= (Prims.op_Subtraction @x0
@x1)
(BoxInt (- (BoxInt_proj_0 @x0)
(BoxInt_proj_0 @x1))))
 

:pattern ((Prims.op_Subtraction @x0
@x1))
:qid primitive_Prims.op_Subtraction))

:named primitive_Prims.op_Subtraction))

; </end encoding Prims.op_Subtraction>


; <Start encoding Prims.op_Addition>

(declare-fun Prims.op_Addition (Term Term) Term)
(declare-fun Prims.op_Addition@tok () Term)
;;; Fact-ids: Name Prims.op_Addition; Namespace Prims
(assert (! 
;; def=prims.fst(307,4-307,15); use=prims.fst(307,4-307,15)
(forall ((@x0 Term) (@x1 Term))
 (! (= (Prims.op_Addition @x0
@x1)
(BoxInt (+ (BoxInt_proj_0 @x0)
(BoxInt_proj_0 @x1))))
 

:pattern ((Prims.op_Addition @x0
@x1))
:qid primitive_Prims.op_Addition))

:named primitive_Prims.op_Addition))

; </end encoding Prims.op_Addition>


; <Start encoding Prims.op_Minus>

(declare-fun Prims.op_Minus (Term) Term)
(declare-fun Prims.op_Minus@tok () Term)
;;; Fact-ids: Name Prims.op_Minus; Namespace Prims
(assert (! 
;; def=prims.fst(311,4-311,12); use=prims.fst(311,4-311,12)
(forall ((@x0 Term))
 (! (= (Prims.op_Minus @x0)
(BoxInt (- (BoxInt_proj_0 @x0))))
 

:pattern ((Prims.op_Minus @x0))
:qid primitive_Prims.op_Minus))

:named primitive_Prims.op_Minus))

; </end encoding Prims.op_Minus>


; <Start encoding Prims.op_LessThanOrEqual>

(declare-fun Prims.op_LessThanOrEqual (Term Term) Term)
(declare-fun Prims.op_LessThanOrEqual@tok () Term)
;;; Fact-ids: Name Prims.op_LessThanOrEqual; Namespace Prims
(assert (! 
;; def=prims.fst(315,4-315,22); use=prims.fst(315,4-315,22)
(forall ((@x0 Term) (@x1 Term))
 (! (= (Prims.op_LessThanOrEqual @x0
@x1)
(BoxBool (<= (BoxInt_proj_0 @x0)
(BoxInt_proj_0 @x1))))
 

:pattern ((Prims.op_LessThanOrEqual @x0
@x1))
:qid primitive_Prims.op_LessThanOrEqual))

:named primitive_Prims.op_LessThanOrEqual))

; </end encoding Prims.op_LessThanOrEqual>


; <Start encoding Prims.op_GreaterThan>

(declare-fun Prims.op_GreaterThan (Term Term) Term)
(declare-fun Prims.op_GreaterThan@tok () Term)

; </end encoding Prims.op_GreaterThan>


; <Start encoding Prims.op_GreaterThanOrEqual>

(declare-fun Prims.op_GreaterThanOrEqual (Term Term) Term)
(declare-fun Prims.op_GreaterThanOrEqual@tok () Term)

; </end encoding Prims.op_GreaterThanOrEqual>


; <Start encoding Prims.op_LessThan>

(declare-fun Prims.op_LessThan (Term Term) Term)
(declare-fun Prims.op_LessThan@tok () Term)

; </end encoding Prims.op_LessThan>


; <Start encoding Prims.op_Equality>

(declare-fun Prims.op_Equality (Term Term Term) Term)
(declare-fun Prims.op_Equality@tok () Term)

; </end encoding Prims.op_Equality>


; <Start encoding Prims.op_disEquality>

(declare-fun Prims.op_disEquality (Term Term Term) Term)
(declare-fun Prims.op_disEquality@tok () Term)

; </end encoding Prims.op_disEquality>


; <Start encoding Prims.exn>

(declare-fun Prims.exn () Term)

; </end encoding Prims.exn>


; <Start encoding Prims.array>

(declare-fun Prims.array (Term) Term)

(declare-fun Prims.array@tok () Term)

; </end encoding Prims.array>


; <Start encoding Prims.deprecated>

(declare-fun Prims.deprecated (Term) Term)
(declare-fun Tm_arrow_2863eb88d7490a9c3cf347c16ca04740 () Term)
(declare-fun Prims.deprecated@tok () Term)

; </end encoding Prims.deprecated>


; <Start encoding Prims.strcat>

(declare-fun Prims.strcat (Term Term) Term)
(declare-fun Tm_arrow_b66cecec1d56111347abe61e89557dd1 () Term)
(declare-fun Prims.strcat@tok () Term)

; </end encoding Prims.strcat>


; <Skipped Prims.op_Hat/>


; <Start encoding >

;;;;;;;;;;;;;;;;Constructor
(declare-fun Prims.list (Term) Term)
;;;;;;;;;;;;;;;;Projector
(declare-fun Prims.list@x0 (Term) Term)
;;;;;;;;;;;;;;;;token
(declare-fun Prims.list@tok () Term)
;;;;;;;;;;;;;;;;Constructor
(declare-fun Prims.Nil (Term) Term)
;;;;;;;;;;;;;;;;Projector
(declare-fun Prims.Nil_a (Term) Term)
;;;;;;;;;;;;;;;;data constructor proxy: Nil
(declare-fun Prims.Nil@tok () Term)
;;;;;;;;;;;;;;;;Constructor
(declare-fun Prims.Cons (Term Term Term) Term)
;;;;;;;;;;;;;;;;Projector
(declare-fun Prims.Cons_a (Term) Term)
;;;;;;;;;;;;;;;;Projector
(declare-fun Prims.Cons_hd (Term) Term)
;;;;;;;;;;;;;;;;Projector
(declare-fun Prims.Cons_tl (Term) Term)
;;;;;;;;;;;;;;;;data constructor proxy: Cons
(declare-fun Prims.Cons@tok () Term)
(declare-fun Tm_arrow_3864bd5fbb999b4fe4487408df9b3401 () Term)
(declare-fun Tm_arrow_02c072760cbad0f5a4706f6cffab6c94 () Term)

; <Start encoding Prims.list>


; <start constructor Prims.list>

;;;;;;;;;;;;;;;;Discriminator definition
(define-fun is-Prims.list ((__@x0 Term)) Bool
 (and (= (Term_constr_id __@x0)
326)
(exists ((@x0 Term))
 (! (= __@x0
(Prims.list @x0))
 
;;no pats
:qid is-Prims.list))))

; </end constructor Prims.list>


; </end encoding Prims.list>


; <Start encoding Prims.Nil>


; <start constructor Prims.Nil>

;;;;;;;;;;;;;;;;Discriminator definition
(define-fun is-Prims.Nil ((__@x0 Term)) Bool
 (and (= (Term_constr_id __@x0)
333)
(= __@x0
(Prims.Nil (Prims.Nil_a __@x0)))))

; </end constructor Prims.Nil>


; </end encoding Prims.Nil>


; <Start encoding Prims.Cons>


; <start constructor Prims.Cons>

;;;;;;;;;;;;;;;;Discriminator definition
(define-fun is-Prims.Cons ((__@x0 Term)) Bool
 (and (= (Term_constr_id __@x0)
338)
(= __@x0
(Prims.Cons (Prims.Cons_a __@x0)
(Prims.Cons_hd __@x0)
(Prims.Cons_tl __@x0)))))

; </end constructor Prims.Cons>


; </end encoding Prims.Cons>


; </end encoding >


; <Start encoding Prims.list__uu___haseq>


; </end encoding Prims.list__uu___haseq>


; <Start encoding Prims.uu___is_Nil>

(declare-fun Prims.uu___is_Nil (Term Term) Term)
(declare-fun Tm_arrow_606904b0fa72729a20285beb231f9f2e () Term)
(declare-fun Prims.uu___is_Nil@tok () Term)

; </end encoding Prims.uu___is_Nil>


; <Skipped Prims.uu___is_Nil/>


; <Start encoding Prims.uu___is_Cons>

(declare-fun Prims.uu___is_Cons (Term Term) Term)

(declare-fun Prims.uu___is_Cons@tok () Term)

; </end encoding Prims.uu___is_Cons>


; <Skipped Prims.uu___is_Cons/>


; <Start encoding Prims.__proj__Cons__item__hd>

(declare-fun Tm_refine_7aac12c24449a22c34d98a0ea8ed4a32 (Term) Term)
(declare-fun Prims.__proj__Cons__item__hd (Term Term) Term)

(declare-fun Tm_arrow_27c3547831737e5a63950f3d18bf3d22 () Term)
(declare-fun Prims.__proj__Cons__item__hd@tok () Term)

; </end encoding Prims.__proj__Cons__item__hd>


; <Skipped Prims.__proj__Cons__item__hd/>


; <Start encoding Prims.__proj__Cons__item__tl>


(declare-fun Prims.__proj__Cons__item__tl (Term Term) Term)

(declare-fun Tm_arrow_4e740085106d54d8b48ffe3c6c20ef21 () Term)
(declare-fun Prims.__proj__Cons__item__tl@tok () Term)

; </end encoding Prims.__proj__Cons__item__tl>


; <Skipped Prims.__proj__Cons__item__tl/>


; <Start encoding Prims.pattern>

(declare-fun Prims.pattern () Term)

; </end encoding Prims.pattern>


; <Start encoding Prims.smt_pat>

(declare-fun Prims.smt_pat (Term Term) Term)
(declare-fun Tm_arrow_0aa9cf6007f3c3c3d83246810119b1b8 () Term)
(declare-fun Prims.smt_pat@tok () Term)

; </end encoding Prims.smt_pat>


; <Start encoding Prims.smt_pat_or>

(declare-fun Prims.smt_pat_or (Term) Term)
(declare-fun Tm_arrow_98fcd1996d7c86df5c892339bd436c5e () Term)
(declare-fun Prims.smt_pat_or@tok () Term)

; </end encoding Prims.smt_pat_or>


; <Start encoding Prims.decreases>

(declare-fun Prims.decreases (Term Term) Term)
(declare-fun Tm_arrow_9e007179360e2932d75ab29019e3d7fa () Term)
(declare-fun Prims.decreases@tok () Term)

; </end encoding Prims.decreases>


; <Skipped Prims.Lemma/>


; <Skipped Prims.M/>


; <Start encoding Prims.returnM>

(declare-fun Prims.returnM (Term Term) Term)
(declare-fun Tm_arrow_99724436653747ac6f5a6a00c64ff8bc () Term)
(declare-fun Prims.returnM@tok () Term)

; </end encoding Prims.returnM>


; <Start encoding >

;;;;;;;;;;;;;;;;Constructor
(declare-fun Prims.LexTop () Term)
;;;;;;;;;;;;;;;;data constructor proxy: LexTop
(declare-fun Prims.LexTop@tok () Term)

; <Start encoding Prims.lex_t>


; </end encoding Prims.lex_t>


; <Start encoding Prims.LexTop>


; <start constructor Prims.LexTop>

;;;;;;;;;;;;;;;;Discriminator definition
(define-fun is-Prims.LexTop ((__@x0 Term)) Bool
 (and (= (Term_constr_id __@x0)
368)
(= __@x0
Prims.LexTop)))

; </end constructor Prims.LexTop>


; </end encoding Prims.LexTop>


; <Skipped Prims.LexCons/>


; </end encoding >


; <Skipped Prims.as_requires/>


; <Skipped Prims.as_ensures/>


; <Start encoding Prims._assume>

(declare-fun Prims._assume (Term) Term)
(declare-fun Non_total_Tm_arrow_Prims_370 () Term)
(declare-fun Prims._assume@tok () Term)

; </end encoding Prims._assume>


; <Start encoding Prims.admit>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun Prims.admit (Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun Prims.admit@tok () Term)

; </end encoding Prims.admit>


; <Start encoding Prims.magic>

(declare-fun Prims.magic (Term Term) Term)
(declare-fun Tm_arrow_f5df98ce82fbcebbbdb844c958bee4fb () Term)
(declare-fun Prims.magic@tok () Term)

; </end encoding Prims.magic>


; <Start encoding Prims.unsafe_coerce>

(declare-fun Prims.unsafe_coerce (Term Term Term) Term)
(declare-fun Tm_arrow_443ab41008720460b7a09e280558a60f () Term)
(declare-fun Prims.unsafe_coerce@tok () Term)

; </end encoding Prims.unsafe_coerce>


; <Start encoding Prims.admitP>

(declare-fun Prims.admitP (Term) Term)
(declare-fun Non_total_Tm_arrow_Prims_376 () Term)
(declare-fun Prims.admitP@tok () Term)

; </end encoding Prims.admitP>


; <Start encoding Prims._assert>

(declare-fun Prims._assert (Term) Term)
(declare-fun Non_total_Tm_arrow_Prims_378 () Term)
(declare-fun Prims._assert@tok () Term)

; </end encoding Prims._assert>


; <Start encoding Prims.spinoff>

(declare-fun Prims.spinoff (Term) Term)

(declare-fun Prims.spinoff@tok () Term)

; </end encoding Prims.spinoff>


; <Start encoding Prims.assert_spinoff>

(declare-fun Prims.assert_spinoff (Term) Term)
(declare-fun Non_total_Tm_arrow_Prims_382 () Term)
(declare-fun Prims.assert_spinoff@tok () Term)

; </end encoding Prims.assert_spinoff>


; <Start encoding Prims.cut>

(declare-fun Prims.cut (Term) Term)
(declare-fun Non_total_Tm_arrow_Prims_384 () Term)
(declare-fun Prims.cut@tok () Term)

; </end encoding Prims.cut>


; <Start encoding Prims.nat>

(declare-fun Prims.nat () Term)
(declare-fun Tm_refine_542f9d4f129664613f2483a6c88bc7c2 () Term)
;;;;;;;;;;;;;;;;refinement_interpretation
;;; Fact-ids: Name Prims.nat; Namespace Prims
(assert (! 
;; def=prims.fst(441,11-441,24); use=prims.fst(441,11-441,24)
(forall ((@u0 Fuel) (@x1 Term))
 (! (iff (HasTypeFuel @u0
@x1
Tm_refine_542f9d4f129664613f2483a6c88bc7c2)
(and (HasTypeFuel @u0
@x1
Prims.int)

;; def=prims.fst(441,17-441,23); use=prims.fst(441,17-441,23)
(>= (BoxInt_proj_0 @x1)
(BoxInt_proj_0 (BoxInt 0)))
))
 

:pattern ((HasTypeFuel @u0
@x1
Tm_refine_542f9d4f129664613f2483a6c88bc7c2))
:qid refinement_interpretation_Tm_refine_542f9d4f129664613f2483a6c88bc7c2))

:named refinement_interpretation_Tm_refine_542f9d4f129664613f2483a6c88bc7c2))
;;;;;;;;;;;;;;;;Equation for Prims.nat
;;; Fact-ids: Name Prims.nat; Namespace Prims
(assert (! (= Prims.nat
Tm_refine_542f9d4f129664613f2483a6c88bc7c2)
:named equation_Prims.nat))

; </end encoding Prims.nat>


; <Start encoding Prims.pos>

(declare-fun Prims.pos () Term)
(declare-fun Tm_refine_774ba3f728d91ead8ef40be66c9802e5 () Term)
;;;;;;;;;;;;;;;;refinement_interpretation
;;; Fact-ids: Name Prims.pos; Namespace Prims
(assert (! 
;; def=prims.fst(442,11-442,23); use=prims.fst(442,11-442,23)
(forall ((@u0 Fuel) (@x1 Term))
 (! (iff (HasTypeFuel @u0
@x1
Tm_refine_774ba3f728d91ead8ef40be66c9802e5)
(and (HasTypeFuel @u0
@x1
Prims.int)

;; def=prims.fst(442,17-442,22); use=prims.fst(442,17-442,22)
(> (BoxInt_proj_0 @x1)
(BoxInt_proj_0 (BoxInt 0)))
))
 

:pattern ((HasTypeFuel @u0
@x1
Tm_refine_774ba3f728d91ead8ef40be66c9802e5))
:qid refinement_interpretation_Tm_refine_774ba3f728d91ead8ef40be66c9802e5))

:named refinement_interpretation_Tm_refine_774ba3f728d91ead8ef40be66c9802e5))
;;;;;;;;;;;;;;;;Equation for Prims.pos
;;; Fact-ids: Name Prims.pos; Namespace Prims
(assert (! (= Prims.pos
Tm_refine_774ba3f728d91ead8ef40be66c9802e5)
:named equation_Prims.pos))

; </end encoding Prims.pos>


; <Start encoding Prims.nonzero>

(declare-fun Prims.nonzero () Term)
(declare-fun Tm_refine_0766302b68bb44ab7aff8c4d8be0b46f () Term)

; </end encoding Prims.nonzero>


; <Start encoding Prims.op_Modulus>

(declare-fun Prims.op_Modulus (Term Term) Term)
(declare-fun Prims.op_Modulus@tok () Term)

; </end encoding Prims.op_Modulus>


; <Start encoding Prims.op_Division>

(declare-fun Prims.op_Division (Term Term) Term)
(declare-fun Prims.op_Division@tok () Term)
;;; Fact-ids: Name Prims.op_Division; Namespace Prims
(assert (! 
;; def=prims.fst(455,4-455,15); use=prims.fst(455,4-455,15)
(forall ((@x0 Term) (@x1 Term))
 (! (= (Prims.op_Division @x0
@x1)
(BoxInt (div (BoxInt_proj_0 @x0)
(BoxInt_proj_0 @x1))))
 

:pattern ((Prims.op_Division @x0
@x1))
:qid primitive_Prims.op_Division))

:named primitive_Prims.op_Division))

; </end encoding Prims.op_Division>


; <Start encoding Prims.pow2>

;;;;;;;;;;;;;;;;Fuel-instrumented function name
(declare-fun Prims.pow2.fuel_instrumented (Fuel Term) Term)
;;;;;;;;;;;;;;;;Token for fuel-instrumented partial applications
(declare-fun Prims.pow2.fuel_instrumented_token () Term)
(declare-fun Prims.pow2 (Term) Term)
(declare-fun Prims.pow2@tok () Term)
(declare-fun Tm_arrow_c331a0e032e021e1eaa359b3983de4f2 () Term)
;;;;;;;;;;;;;;;;free var typing
;;; Fact-ids: Name Prims.pow2; Namespace Prims
(assert (! 
;; def=prims.fst(457,8-457,12); use=prims.fst(457,8-457,12)
(forall ((@x0 Term))
 (! (implies (HasType @x0
Prims.nat)
(HasType (Prims.pow2 @x0)
Prims.pos))
 

:pattern ((Prims.pow2 @x0))
:qid typing_Prims.pow2))

:named typing_Prims.pow2))
;;;;;;;;;;;;;;;;Fuel irrelevance
;;; Fact-ids: Name Prims.pow2; Namespace Prims
(assert (! 
;; def=prims.fst(457,8-457,12); use=prims.fst(457,8-457,12)
(forall ((@u0 Fuel) (@x1 Term))
 (! (= (Prims.pow2.fuel_instrumented (SFuel @u0)
@x1)
(Prims.pow2.fuel_instrumented ZFuel
@x1))
 

:pattern ((Prims.pow2.fuel_instrumented (SFuel @u0)
@x1))
:qid @fuel_irrelevance_Prims.pow2.fuel_instrumented))

:named @fuel_irrelevance_Prims.pow2.fuel_instrumented))
;;;;;;;;;;;;;;;;Correspondence of recursive function to instrumented version
;;; Fact-ids: Name Prims.pow2; Namespace Prims
(assert (! 
;; def=prims.fst(457,8-457,12); use=prims.fst(457,8-457,12)
(forall ((@x0 Term))
 (! (= (Prims.pow2 @x0)
(Prims.pow2.fuel_instrumented MaxFuel
@x0))
 

:pattern ((Prims.pow2 @x0))
:qid @fuel_correspondence_Prims.pow2.fuel_instrumented))

:named @fuel_correspondence_Prims.pow2.fuel_instrumented))

; </end encoding Prims.pow2>


; <Start encoding Prims.min>

(declare-fun Prims.min (Term Term) Term)
(declare-fun Tm_arrow_47fc285d7b44e13bcb7e420cbfc55623 () Term)
(declare-fun Prims.min@tok () Term)

; </end encoding Prims.min>


; <Start encoding Prims.abs>

(declare-fun Prims.abs (Term) Term)
(declare-fun Tm_arrow_35447810753695c4fe25c93af1251992 () Term)
(declare-fun Prims.abs@tok () Term)

; </end encoding Prims.abs>


; <Start encoding Prims.string_of_bool>

(declare-fun Prims.string_of_bool (Term) Term)
(declare-fun Tm_arrow_e86b54405c2a58719f5e8112efd48c09 () Term)
(declare-fun Prims.string_of_bool@tok () Term)

; </end encoding Prims.string_of_bool>


; <Start encoding Prims.string_of_int>

(declare-fun Prims.string_of_int (Term) Term)
(declare-fun Tm_arrow_2bc066ec63734c94a3c008e1e72cae2b () Term)
(declare-fun Prims.string_of_int@tok () Term)

; </end encoding Prims.string_of_int>


; <Start encoding Prims.labeled>

(declare-fun Prims.labeled (Term Term Term) Term)
(declare-fun Tm_arrow_04aa773f28f907e6a0b5741576bf5493 () Term)
(declare-fun Prims.labeled@tok () Term)

; </end encoding Prims.labeled>


; <Start encoding Prims.__cache_version_number__>

(declare-fun Prims.__cache_version_number__ () Term)

; </end encoding Prims.__cache_version_number__>


; UNSAT CORE: @MaxFuel_assumption, @MaxIFuel_assumption, @fuel_correspondence_Prims.pow2.fuel_instrumented, @query, constructor_distinct_Lib.IntTypes.S16, constructor_distinct_Lib.IntTypes.S32, constructor_distinct_Lib.IntTypes.SEC, equality_tok_Lib.IntTypes.S16@tok, equality_tok_Lib.IntTypes.S32@tok, equality_tok_Lib.IntTypes.SEC@tok, equation_Lib.IntTypes.bits, equation_Lib.IntTypes.range, equation_Lib.IntTypes.signed, equation_Lib.IntTypes.unsigned, equation_Lib.IntTypes.v, equation_Prims.nat, equation_Prims.pos, equation_Spec.Kyber2.Params.params_q, int_inversion, int_typing, lemma_FStar.UInt.pow2_values, primitive_Prims.op_Addition, primitive_Prims.op_Division, primitive_Prims.op_LessThanOrEqual, primitive_Prims.op_Minus, primitive_Prims.op_Multiply, primitive_Prims.op_Subtraction, projection_inverse_BoxBool_proj_0, projection_inverse_BoxInt_proj_0, refinement_interpretation_Tm_refine_2b320913041b873fce938dd17eebb3e2, refinement_interpretation_Tm_refine_542f9d4f129664613f2483a6c88bc7c2, refinement_interpretation_Tm_refine_774ba3f728d91ead8ef40be66c9802e5, refinement_interpretation_Tm_refine_83845a86f2550cdf941eeb1d9b59602b, refinement_interpretation_Tm_refine_9d3fd79fd314167f1a9c213a188da3ec, refinement_interpretation_Tm_refine_b2401a8cabe2f9a01538f32548fa9f6c, typing_Lib.IntTypes.mk_int, typing_Prims.pow2, typing_tok_Lib.IntTypes.S32@tok, typing_tok_Lib.IntTypes.SEC@tok

;;; End module Prims (699 decls; total size 39153)

;;; Start module FStar.Pervasives.Native

; <Start encoding >

;;;;;;;;;;;;;;;;Constructor
(declare-fun FStar.Pervasives.Native.option (Term) Term)
;;;;;;;;;;;;;;;;Projector
(declare-fun FStar.Pervasives.Native.option@x0 (Term) Term)
;;;;;;;;;;;;;;;;token
(declare-fun FStar.Pervasives.Native.option@tok () Term)
;;;;;;;;;;;;;;;;Constructor
(declare-fun FStar.Pervasives.Native.None (Term) Term)
;;;;;;;;;;;;;;;;Projector
(declare-fun FStar.Pervasives.Native.None_a (Term) Term)
;;;;;;;;;;;;;;;;data constructor proxy: None
(declare-fun FStar.Pervasives.Native.None@tok () Term)
;;;;;;;;;;;;;;;;Constructor
(declare-fun FStar.Pervasives.Native.Some (Term Term) Term)
;;;;;;;;;;;;;;;;Projector
(declare-fun FStar.Pervasives.Native.Some_a (Term) Term)
;;;;;;;;;;;;;;;;Projector
(declare-fun FStar.Pervasives.Native.Some_v (Term) Term)
;;;;;;;;;;;;;;;;data constructor proxy: Some
(declare-fun FStar.Pervasives.Native.Some@tok () Term)
(declare-fun Tm_arrow_48b914114ec9f2f1caadf0f6848a9741 () Term)
(declare-fun Tm_arrow_b93a364b5144c2a5f3e9d1ea7b881752 () Term)

; <Start encoding FStar.Pervasives.Native.option>


; <start constructor FStar.Pervasives.Native.option>

;;;;;;;;;;;;;;;;Discriminator definition
(define-fun is-FStar.Pervasives.Native.option ((__@x0 Term)) Bool
 (and (= (Term_constr_id __@x0)
101)
(exists ((@x0 Term))
 (! (= __@x0
(FStar.Pervasives.Native.option @x0))
 
;;no pats
:qid is-FStar.Pervasives.Native.option))))

; </end constructor FStar.Pervasives.Native.option>


; </end encoding FStar.Pervasives.Native.option>


; <Start encoding FStar.Pervasives.Native.None>


; <start constructor FStar.Pervasives.Native.None>

;;;;;;;;;;;;;;;;Discriminator definition
(define-fun is-FStar.Pervasives.Native.None ((__@x0 Term)) Bool
 (and (= (Term_constr_id __@x0)
108)
(= __@x0
(FStar.Pervasives.Native.None (FStar.Pervasives.Native.None_a __@x0)))))

; </end constructor FStar.Pervasives.Native.None>


; </end encoding FStar.Pervasives.Native.None>


; <Start encoding FStar.Pervasives.Native.Some>


; <start constructor FStar.Pervasives.Native.Some>

;;;;;;;;;;;;;;;;Discriminator definition
(define-fun is-FStar.Pervasives.Native.Some ((__@x0 Term)) Bool
 (and (= (Term_constr_id __@x0)
113)
(= __@x0
(FStar.Pervasives.Native.Some (FStar.Pervasives.Native.Some_a __@x0)
(FStar.Pervasives.Native.Some_v __@x0)))))

; </end constructor FStar.Pervasives.Native.Some>


; </end encoding FStar.Pervasives.Native.Some>


; </end encoding >


; <Start encoding FStar.Pervasives.Native.option__uu___haseq>


; </end encoding FStar.Pervasives.Native.option__uu___haseq>


; <Start encoding FStar.Pervasives.Native.uu___is_None>

(declare-fun FStar.Pervasives.Native.uu___is_None (Term Term) Term)
(declare-fun Tm_arrow_f1a97bcd6ba9b40d22609b756f183afa () Term)
(declare-fun FStar.Pervasives.Native.uu___is_None@tok () Term)

; </end encoding FStar.Pervasives.Native.uu___is_None>


; <Skipped FStar.Pervasives.Native.uu___is_None/>


; <Start encoding FStar.Pervasives.Native.uu___is_Some>

(declare-fun FStar.Pervasives.Native.uu___is_Some (Term Term) Term)

(declare-fun FStar.Pervasives.Native.uu___is_Some@tok () Term)

; </end encoding FStar.Pervasives.Native.uu___is_Some>


; <Skipped FStar.Pervasives.Native.uu___is_Some/>


; <Start encoding FStar.Pervasives.Native.__proj__Some__item__v>

(declare-fun Tm_refine_4d5241eb6fe198666a8101195bbd4a2a (Term) Term)
(declare-fun FStar.Pervasives.Native.__proj__Some__item__v (Term Term) Term)

(declare-fun Tm_arrow_1b1398c011ff53e4194fc2ec00c7b411 () Term)
(declare-fun FStar.Pervasives.Native.__proj__Some__item__v@tok () Term)

; </end encoding FStar.Pervasives.Native.__proj__Some__item__v>


; <Skipped FStar.Pervasives.Native.__proj__Some__item__v/>


; <Start encoding >

;;;;;;;;;;;;;;;;Constructor
(declare-fun FStar.Pervasives.Native.tuple2 (Term Term) Term)
;;;;;;;;;;;;;;;;Projector
(declare-fun FStar.Pervasives.Native.tuple2@x0 (Term) Term)
;;;;;;;;;;;;;;;;Projector
(declare-fun FStar.Pervasives.Native.tuple2@x1 (Term) Term)
;;;;;;;;;;;;;;;;token
(declare-fun FStar.Pervasives.Native.tuple2@tok () Term)
;;;;;;;;;;;;;;;;Constructor
(declare-fun FStar.Pervasives.Native.Mktuple2 (Term Term Term Term) Term)
;;;;;;;;;;;;;;;;Projector
(declare-fun FStar.Pervasives.Native.Mktuple2__a (Term) Term)
;;;;;;;;;;;;;;;;Projector
(declare-fun FStar.Pervasives.Native.Mktuple2__b (Term) Term)
;;;;;;;;;;;;;;;;Projector
(declare-fun FStar.Pervasives.Native.Mktuple2__1 (Term) Term)
;;;;;;;;;;;;;;;;Projector
(declare-fun FStar.Pervasives.Native.Mktuple2__2 (Term) Term)
;;;;;;;;;;;;;;;;data constructor proxy: Mktuple2
(declare-fun FStar.Pervasives.Native.Mktuple2@tok () Term)
(declare-fun Tm_arrow_4054cc0a51327db54c2ed9ba3376a093 () Term)

; <Start encoding FStar.Pervasives.Native.tuple2>


; <start constructor FStar.Pervasives.Native.tuple2>

;;;;;;;;;;;;;;;;Discriminator definition
(define-fun is-FStar.Pervasives.Native.tuple2 ((__@x0 Term)) Bool
 (and (= (Term_constr_id __@x0)
125)
(exists ((@x0 Term) (@x1 Term))
 (! (= __@x0
(FStar.Pervasives.Native.tuple2 @x0
@x1))
 
;;no pats
:qid is-FStar.Pervasives.Native.tuple2))))

; </end constructor FStar.Pervasives.Native.tuple2>


; </end encoding FStar.Pervasives.Native.tuple2>


; <Start encoding FStar.Pervasives.Native.Mktuple2>


; <start constructor FStar.Pervasives.Native.Mktuple2>

;;;;;;;;;;;;;;;;Discriminator definition
(define-fun is-FStar.Pervasives.Native.Mktuple2 ((__@x0 Term)) Bool
 (and (= (Term_constr_id __@x0)
132)
(= __@x0
(FStar.Pervasives.Native.Mktuple2 (FStar.Pervasives.Native.Mktuple2__a __@x0)
(FStar.Pervasives.Native.Mktuple2__b __@x0)
(FStar.Pervasives.Native.Mktuple2__1 __@x0)
(FStar.Pervasives.Native.Mktuple2__2 __@x0)))))

; </end constructor FStar.Pervasives.Native.Mktuple2>


; </end encoding FStar.Pervasives.Native.Mktuple2>


; </end encoding >


; <Start encoding FStar.Pervasives.Native.tuple2__uu___haseq>


; </end encoding FStar.Pervasives.Native.tuple2__uu___haseq>


; <Start encoding FStar.Pervasives.Native.uu___is_Mktuple2>

(declare-fun FStar.Pervasives.Native.uu___is_Mktuple2 (Term Term Term) Term)
(declare-fun Tm_arrow_eff71eeee4474e017e02350f86f54756 () Term)
(declare-fun FStar.Pervasives.Native.uu___is_Mktuple2@tok () Term)

; </end encoding FStar.Pervasives.Native.uu___is_Mktuple2>


; <Skipped FStar.Pervasives.Native.uu___is_Mktuple2/>


; <Start encoding FStar.Pervasives.Native.__proj__Mktuple2__item___1>

(declare-fun FStar.Pervasives.Native.__proj__Mktuple2__item___1 (Term Term Term) Term)
(declare-fun Tm_arrow_b8cce376a4a678a51298a0f3945f25ce () Term)
(declare-fun FStar.Pervasives.Native.__proj__Mktuple2__item___1@tok () Term)

; </end encoding FStar.Pervasives.Native.__proj__Mktuple2__item___1>


; <Skipped FStar.Pervasives.Native.__proj__Mktuple2__item___1/>


; <Start encoding FStar.Pervasives.Native.__proj__Mktuple2__item___2>

(declare-fun FStar.Pervasives.Native.__proj__Mktuple2__item___2 (Term Term Term) Term)
(declare-fun Tm_arrow_d952d001575ecb20c572af535c88dd2d () Term)
(declare-fun FStar.Pervasives.Native.__proj__Mktuple2__item___2@tok () Term)

; </end encoding FStar.Pervasives.Native.__proj__Mktuple2__item___2>


; <Skipped FStar.Pervasives.Native.__proj__Mktuple2__item___2/>


; <Start encoding FStar.Pervasives.Native.fst>

(declare-fun FStar.Pervasives.Native.fst (Term Term Term) Term)

(declare-fun FStar.Pervasives.Native.fst@tok () Term)

; </end encoding FStar.Pervasives.Native.fst>


; <Start encoding FStar.Pervasives.Native.snd>

(declare-fun FStar.Pervasives.Native.snd (Term Term Term) Term)

(declare-fun FStar.Pervasives.Native.snd@tok () Term)

; </end encoding FStar.Pervasives.Native.snd>


; <Start encoding >

;;;;;;;;;;;;;;;;Constructor
(declare-fun FStar.Pervasives.Native.tuple3 (Term Term Term) Term)
;;;;;;;;;;;;;;;;Projector
(declare-fun FStar.Pervasives.Native.tuple3@x0 (Term) Term)
;;;;;;;;;;;;;;;;Projector
(declare-fun FStar.Pervasives.Native.tuple3@x1 (Term) Term)
;;;;;;;;;;;;;;;;Projector
(declare-fun FStar.Pervasives.Native.tuple3@x2 (Term) Term)
;;;;;;;;;;;;;;;;token
(declare-fun FStar.Pervasives.Native.tuple3@tok () Term)
;;;;;;;;;;;;;;;;Constructor
(declare-fun FStar.Pervasives.Native.Mktuple3 (Term Term Term Term Term Term) Term)
;;;;;;;;;;;;;;;;Projector
(declare-fun FStar.Pervasives.Native.Mktuple3__a (Term) Term)
;;;;;;;;;;;;;;;;Projector
(declare-fun FStar.Pervasives.Native.Mktuple3__b (Term) Term)
;;;;;;;;;;;;;;;;Projector
(declare-fun FStar.Pervasives.Native.Mktuple3__c (Term) Term)
;;;;;;;;;;;;;;;;Projector
(declare-fun FStar.Pervasives.Native.Mktuple3__1 (Term) Term)
;;;;;;;;;;;;;;;;Projector
(declare-fun FStar.Pervasives.Native.Mktuple3__2 (Term) Term)
;;;;;;;;;;;;;;;;Projector
(declare-fun FStar.Pervasives.Native.Mktuple3__3 (Term) Term)
;;;;;;;;;;;;;;;;data constructor proxy: Mktuple3
(declare-fun FStar.Pervasives.Native.Mktuple3@tok () Term)
(declare-fun Tm_arrow_1bedda193f13e939931cf5d46ad84216 () Term)

; <Start encoding FStar.Pervasives.Native.tuple3>


; <start constructor FStar.Pervasives.Native.tuple3>

;;;;;;;;;;;;;;;;Discriminator definition
(define-fun is-FStar.Pervasives.Native.tuple3 ((__@x0 Term)) Bool
 (and (= (Term_constr_id __@x0)
146)
(exists ((@x0 Term) (@x1 Term) (@x2 Term))
 (! (= __@x0
(FStar.Pervasives.Native.tuple3 @x0
@x1
@x2))
 
;;no pats
:qid is-FStar.Pervasives.Native.tuple3))))

; </end constructor FStar.Pervasives.Native.tuple3>


; </end encoding FStar.Pervasives.Native.tuple3>


; <Start encoding FStar.Pervasives.Native.Mktuple3>


; <start constructor FStar.Pervasives.Native.Mktuple3>

;;;;;;;;;;;;;;;;Discriminator definition
(define-fun is-FStar.Pervasives.Native.Mktuple3 ((__@x0 Term)) Bool
 (and (= (Term_constr_id __@x0)
153)
(= __@x0
(FStar.Pervasives.Native.Mktuple3 (FStar.Pervasives.Native.Mktuple3__a __@x0)
(FStar.Pervasives.Native.Mktuple3__b __@x0)
(FStar.Pervasives.Native.Mktuple3__c __@x0)
(FStar.Pervasives.Native.Mktuple3__1 __@x0)
(FStar.Pervasives.Native.Mktuple3__2 __@x0)
(FStar.Pervasives.Native.Mktuple3__3 __@x0)))))

; </end constructor FStar.Pervasives.Native.Mktuple3>


; </end encoding FStar.Pervasives.Native.Mktuple3>


; </end encoding >


; <Start encoding FStar.Pervasives.Native.tuple3__uu___haseq>


; </end encoding FStar.Pervasives.Native.tuple3__uu___haseq>


; <Start encoding FStar.Pervasives.Native.uu___is_Mktuple3>

(declare-fun FStar.Pervasives.Native.uu___is_Mktuple3 (Term Term Term Term) Term)
(declare-fun Tm_arrow_f03c6dc5b30146aaca49ed4bf6f332a7 () Term)
(declare-fun FStar.Pervasives.Native.uu___is_Mktuple3@tok () Term)

; </end encoding FStar.Pervasives.Native.uu___is_Mktuple3>


; <Skipped FStar.Pervasives.Native.uu___is_Mktuple3/>


; <Start encoding FStar.Pervasives.Native.__proj__Mktuple3__item___1>

(declare-fun FStar.Pervasives.Native.__proj__Mktuple3__item___1 (Term Term Term Term) Term)
(declare-fun Tm_arrow_592c45439d32a71e1933eacb9776c9ed () Term)
(declare-fun FStar.Pervasives.Native.__proj__Mktuple3__item___1@tok () Term)

; </end encoding FStar.Pervasives.Native.__proj__Mktuple3__item___1>


; <Skipped FStar.Pervasives.Native.__proj__Mktuple3__item___1/>


; <Start encoding FStar.Pervasives.Native.__proj__Mktuple3__item___2>

(declare-fun FStar.Pervasives.Native.__proj__Mktuple3__item___2 (Term Term Term Term) Term)
(declare-fun Tm_arrow_9c9b0c5ac9b0fbfc367f406af296ecab () Term)
(declare-fun FStar.Pervasives.Native.__proj__Mktuple3__item___2@tok () Term)

; </end encoding FStar.Pervasives.Native.__proj__Mktuple3__item___2>


; <Skipped FStar.Pervasives.Native.__proj__Mktuple3__item___2/>


; <Start encoding FStar.Pervasives.Native.__proj__Mktuple3__item___3>

(declare-fun FStar.Pervasives.Native.__proj__Mktuple3__item___3 (Term Term Term Term) Term)
(declare-fun Tm_arrow_08246a62c9aeca08c44c602ad80e95a4 () Term)
(declare-fun FStar.Pervasives.Native.__proj__Mktuple3__item___3@tok () Term)

; </end encoding FStar.Pervasives.Native.__proj__Mktuple3__item___3>


; <Skipped FStar.Pervasives.Native.__proj__Mktuple3__item___3/>


; <Start encoding >

;;;;;;;;;;;;;;;;Constructor
(declare-fun FStar.Pervasives.Native.tuple4 (Term Term Term Term) Term)
;;;;;;;;;;;;;;;;Projector
(declare-fun FStar.Pervasives.Native.tuple4@x0 (Term) Term)
;;;;;;;;;;;;;;;;Projector
(declare-fun FStar.Pervasives.Native.tuple4@x1 (Term) Term)
;;;;;;;;;;;;;;;;Projector
(declare-fun FStar.Pervasives.Native.tuple4@x2 (Term) Term)
;;;;;;;;;;;;;;;;Projector
(declare-fun FStar.Pervasives.Native.tuple4@x3 (Term) Term)
;;;;;;;;;;;;;;;;token
(declare-fun FStar.Pervasives.Native.tuple4@tok () Term)
;;;;;;;;;;;;;;;;Constructor
(declare-fun FStar.Pervasives.Native.Mktuple4 (Term Term Term Term Term Term Term Term) Term)
;;;;;;;;;;;;;;;;Projector
(declare-fun FStar.Pervasives.Native.Mktuple4__a (Term) Term)
;;;;;;;;;;;;;;;;Projector
(declare-fun FStar.Pervasives.Native.Mktuple4__b (Term) Term)
;;;;;;;;;;;;;;;;Projector
(declare-fun FStar.Pervasives.Native.Mktuple4__c (Term) Term)
;;;;;;;;;;;;;;;;Projector
(declare-fun FStar.Pervasives.Native.Mktuple4__d (Term) Term)
;;;;;;;;;;;;;;;;Projector
(declare-fun FStar.Pervasives.Native.Mktuple4__1 (Term) Term)
;;;;;;;;;;;;;;;;Projector
(declare-fun FStar.Pervasives.Native.Mktuple4__2 (Term) Term)
;;;;;;;;;;;;;;;;Projector
(declare-fun FStar.Pervasives.Native.Mktuple4__3 (Term) Term)
;;;;;;;;;;;;;;;;Projector
(declare-fun FStar.Pervasives.Native.Mktuple4__4 (Term) Term)
;;;;;;;;;;;;;;;;data constructor proxy: Mktuple4
(declare-fun FStar.Pervasives.Native.Mktuple4@tok () Term)
(declare-fun Tm_arrow_cbe72a10167439fe1ecfaf4fec8fd23f () Term)

; <Start encoding FStar.Pervasives.Native.tuple4>


; <start constructor FStar.Pervasives.Native.tuple4>

;;;;;;;;;;;;;;;;Discriminator definition
(define-fun is-FStar.Pervasives.Native.tuple4 ((__@x0 Term)) Bool
 (and (= (Term_constr_id __@x0)
165)
(exists ((@x0 Term) (@x1 Term) (@x2 Term) (@x3 Term))
 (! (= __@x0
(FStar.Pervasives.Native.tuple4 @x0
@x1
@x2
@x3))
 
;;no pats
:qid is-FStar.Pervasives.Native.tuple4))))

; </end constructor FStar.Pervasives.Native.tuple4>


; </end encoding FStar.Pervasives.Native.tuple4>


; <Start encoding FStar.Pervasives.Native.Mktuple4>


; <start constructor FStar.Pervasives.Native.Mktuple4>

;;;;;;;;;;;;;;;;Discriminator definition
(define-fun is-FStar.Pervasives.Native.Mktuple4 ((__@x0 Term)) Bool
 (and (= (Term_constr_id __@x0)
172)
(= __@x0
(FStar.Pervasives.Native.Mktuple4 (FStar.Pervasives.Native.Mktuple4__a __@x0)
(FStar.Pervasives.Native.Mktuple4__b __@x0)
(FStar.Pervasives.Native.Mktuple4__c __@x0)
(FStar.Pervasives.Native.Mktuple4__d __@x0)
(FStar.Pervasives.Native.Mktuple4__1 __@x0)
(FStar.Pervasives.Native.Mktuple4__2 __@x0)
(FStar.Pervasives.Native.Mktuple4__3 __@x0)
(FStar.Pervasives.Native.Mktuple4__4 __@x0)))))

; </end constructor FStar.Pervasives.Native.Mktuple4>


; </end encoding FStar.Pervasives.Native.Mktuple4>


; </end encoding >


; <Start encoding FStar.Pervasives.Native.tuple4__uu___haseq>


; </end encoding FStar.Pervasives.Native.tuple4__uu___haseq>


; <Start encoding FStar.Pervasives.Native.uu___is_Mktuple4>

(declare-fun FStar.Pervasives.Native.uu___is_Mktuple4 (Term Term Term Term Term) Term)
(declare-fun Tm_arrow_4319694c225efa92ce9fad6e9d81f761 () Term)
(declare-fun FStar.Pervasives.Native.uu___is_Mktuple4@tok () Term)

; </end encoding FStar.Pervasives.Native.uu___is_Mktuple4>


; <Skipped FStar.Pervasives.Native.uu___is_Mktuple4/>


; <Start encoding FStar.Pervasives.Native.__proj__Mktuple4__item___1>

(declare-fun FStar.Pervasives.Native.__proj__Mktuple4__item___1 (Term Term Term Term Term) Term)
(declare-fun Tm_arrow_382d1e9129053162252ec57e86d46f82 () Term)
(declare-fun FStar.Pervasives.Native.__proj__Mktuple4__item___1@tok () Term)

; </end encoding FStar.Pervasives.Native.__proj__Mktuple4__item___1>


; <Skipped FStar.Pervasives.Native.__proj__Mktuple4__item___1/>


; <Start encoding FStar.Pervasives.Native.__proj__Mktuple4__item___2>

(declare-fun FStar.Pervasives.Native.__proj__Mktuple4__item___2 (Term Term Term Term Term) Term)
(declare-fun Tm_arrow_fffd25e5325d259efa0675ef649c6864 () Term)
(declare-fun FStar.Pervasives.Native.__proj__Mktuple4__item___2@tok () Term)

; </end encoding FStar.Pervasives.Native.__proj__Mktuple4__item___2>


; <Skipped FStar.Pervasives.Native.__proj__Mktuple4__item___2/>


; <Start encoding FStar.Pervasives.Native.__proj__Mktuple4__item___3>

(declare-fun FStar.Pervasives.Native.__proj__Mktuple4__item___3 (Term Term Term Term Term) Term)
(declare-fun Tm_arrow_57b4005e0833f7b396e349ed7cdd1bb2 () Term)
(declare-fun FStar.Pervasives.Native.__proj__Mktuple4__item___3@tok () Term)

; </end encoding FStar.Pervasives.Native.__proj__Mktuple4__item___3>


; <Skipped FStar.Pervasives.Native.__proj__Mktuple4__item___3/>


; <Start encoding FStar.Pervasives.Native.__proj__Mktuple4__item___4>

(declare-fun FStar.Pervasives.Native.__proj__Mktuple4__item___4 (Term Term Term Term Term) Term)
(declare-fun Tm_arrow_9e6c1a63d63f8735645b9898955a2dca () Term)
(declare-fun FStar.Pervasives.Native.__proj__Mktuple4__item___4@tok () Term)

; </end encoding FStar.Pervasives.Native.__proj__Mktuple4__item___4>


; <Skipped FStar.Pervasives.Native.__proj__Mktuple4__item___4/>


; <Start encoding >

;;;;;;;;;;;;;;;;Constructor
(declare-fun FStar.Pervasives.Native.tuple5 (Term Term Term Term Term) Term)
;;;;;;;;;;;;;;;;Projector
(declare-fun FStar.Pervasives.Native.tuple5@x0 (Term) Term)
;;;;;;;;;;;;;;;;Projector
(declare-fun FStar.Pervasives.Native.tuple5@x1 (Term) Term)
;;;;;;;;;;;;;;;;Projector
(declare-fun FStar.Pervasives.Native.tuple5@x2 (Term) Term)
;;;;;;;;;;;;;;;;Projector
(declare-fun FStar.Pervasives.Native.tuple5@x3 (Term) Term)
;;;;;;;;;;;;;;;;Projector
(declare-fun FStar.Pervasives.Native.tuple5@x4 (Term) Term)
;;;;;;;;;;;;;;;;token
(declare-fun FStar.Pervasives.Native.tuple5@tok () Term)
;;;;;;;;;;;;;;;;Constructor
(declare-fun FStar.Pervasives.Native.Mktuple5 (Term Term Term Term Term Term Term Term Term Term) Term)
;;;;;;;;;;;;;;;;Projector
(declare-fun FStar.Pervasives.Native.Mktuple5__a (Term) Term)
;;;;;;;;;;;;;;;;Projector
(declare-fun FStar.Pervasives.Native.Mktuple5__b (Term) Term)
;;;;;;;;;;;;;;;;Projector
(declare-fun FStar.Pervasives.Native.Mktuple5__c (Term) Term)
;;;;;;;;;;;;;;;;Projector
(declare-fun FStar.Pervasives.Native.Mktuple5__d (Term) Term)
;;;;;;;;;;;;;;;;Projector
(declare-fun FStar.Pervasives.Native.Mktuple5__e (Term) Term)
;;;;;;;;;;;;;;;;Projector
(declare-fun FStar.Pervasives.Native.Mktuple5__1 (Term) Term)
;;;;;;;;;;;;;;;;Projector
(declare-fun FStar.Pervasives.Native.Mktuple5__2 (Term) Term)
;;;;;;;;;;;;;;;;Projector
(declare-fun FStar.Pervasives.Native.Mktuple5__3 (Term) Term)
;;;;;;;;;;;;;;;;Projector
(declare-fun FStar.Pervasives.Native.Mktuple5__4 (Term) Term)
;;;;;;;;;;;;;;;;Projector
(declare-fun FStar.Pervasives.Native.Mktuple5__5 (Term) Term)
;;;;;;;;;;;;;;;;data constructor proxy: Mktuple5
(declare-fun FStar.Pervasives.Native.Mktuple5@tok () Term)
(declare-fun Tm_arrow_dd8a078a1b97a81b5089dc3637cc2887 () Term)

; <Start encoding FStar.Pervasives.Native.tuple5>


; <start constructor FStar.Pervasives.Native.tuple5>

;;;;;;;;;;;;;;;;Discriminator definition
(define-fun is-FStar.Pervasives.Native.tuple5 ((__@x0 Term)) Bool
 (and (= (Term_constr_id __@x0)
186)
(exists ((@x0 Term) (@x1 Term) (@x2 Term) (@x3 Term) (@x4 Term))
 (! (= __@x0
(FStar.Pervasives.Native.tuple5 @x0
@x1
@x2
@x3
@x4))
 
;;no pats
:qid is-FStar.Pervasives.Native.tuple5))))

; </end constructor FStar.Pervasives.Native.tuple5>


; </end encoding FStar.Pervasives.Native.tuple5>


; <Start encoding FStar.Pervasives.Native.Mktuple5>


; <start constructor FStar.Pervasives.Native.Mktuple5>

;;;;;;;;;;;;;;;;Discriminator definition
(define-fun is-FStar.Pervasives.Native.Mktuple5 ((__@x0 Term)) Bool
 (and (= (Term_constr_id __@x0)
193)
(= __@x0
(FStar.Pervasives.Native.Mktuple5 (FStar.Pervasives.Native.Mktuple5__a __@x0)
(FStar.Pervasives.Native.Mktuple5__b __@x0)
(FStar.Pervasives.Native.Mktuple5__c __@x0)
(FStar.Pervasives.Native.Mktuple5__d __@x0)
(FStar.Pervasives.Native.Mktuple5__e __@x0)
(FStar.Pervasives.Native.Mktuple5__1 __@x0)
(FStar.Pervasives.Native.Mktuple5__2 __@x0)
(FStar.Pervasives.Native.Mktuple5__3 __@x0)
(FStar.Pervasives.Native.Mktuple5__4 __@x0)
(FStar.Pervasives.Native.Mktuple5__5 __@x0)))))

; </end constructor FStar.Pervasives.Native.Mktuple5>


; </end encoding FStar.Pervasives.Native.Mktuple5>


; </end encoding >


; <Start encoding FStar.Pervasives.Native.tuple5__uu___haseq>


; </end encoding FStar.Pervasives.Native.tuple5__uu___haseq>


; <Start encoding FStar.Pervasives.Native.uu___is_Mktuple5>

(declare-fun FStar.Pervasives.Native.uu___is_Mktuple5 (Term Term Term Term Term Term) Term)
(declare-fun Tm_arrow_cfa2e2c8b8b41312889ff659c4faa5f9 () Term)
(declare-fun FStar.Pervasives.Native.uu___is_Mktuple5@tok () Term)

; </end encoding FStar.Pervasives.Native.uu___is_Mktuple5>


; <Skipped FStar.Pervasives.Native.uu___is_Mktuple5/>


; <Start encoding FStar.Pervasives.Native.__proj__Mktuple5__item___1>

(declare-fun FStar.Pervasives.Native.__proj__Mktuple5__item___1 (Term Term Term Term Term Term) Term)
(declare-fun Tm_arrow_7519f72fe101267af170e00c6ce694af () Term)
(declare-fun FStar.Pervasives.Native.__proj__Mktuple5__item___1@tok () Term)

; </end encoding FStar.Pervasives.Native.__proj__Mktuple5__item___1>


; <Skipped FStar.Pervasives.Native.__proj__Mktuple5__item___1/>


; <Start encoding FStar.Pervasives.Native.__proj__Mktuple5__item___2>

(declare-fun FStar.Pervasives.Native.__proj__Mktuple5__item___2 (Term Term Term Term Term Term) Term)
(declare-fun Tm_arrow_3e46329f224aa70981a337f98afbaa87 () Term)
(declare-fun FStar.Pervasives.Native.__proj__Mktuple5__item___2@tok () Term)

; </end encoding FStar.Pervasives.Native.__proj__Mktuple5__item___2>


; <Skipped FStar.Pervasives.Native.__proj__Mktuple5__item___2/>


; <Start encoding FStar.Pervasives.Native.__proj__Mktuple5__item___3>

(declare-fun FStar.Pervasives.Native.__proj__Mktuple5__item___3 (Term Term Term Term Term Term) Term)
(declare-fun Tm_arrow_55e6dc1b736536de45fedf844003f847 () Term)
(declare-fun FStar.Pervasives.Native.__proj__Mktuple5__item___3@tok () Term)

; </end encoding FStar.Pervasives.Native.__proj__Mktuple5__item___3>


; <Skipped FStar.Pervasives.Native.__proj__Mktuple5__item___3/>


; <Start encoding FStar.Pervasives.Native.__proj__Mktuple5__item___4>

(declare-fun FStar.Pervasives.Native.__proj__Mktuple5__item___4 (Term Term Term Term Term Term) Term)
(declare-fun Tm_arrow_3a4e86c6aee1a39b4811bdbc12405398 () Term)
(declare-fun FStar.Pervasives.Native.__proj__Mktuple5__item___4@tok () Term)

; </end encoding FStar.Pervasives.Native.__proj__Mktuple5__item___4>


; <Skipped FStar.Pervasives.Native.__proj__Mktuple5__item___4/>


; <Start encoding FStar.Pervasives.Native.__proj__Mktuple5__item___5>

(declare-fun FStar.Pervasives.Native.__proj__Mktuple5__item___5 (Term Term Term Term Term Term) Term)
(declare-fun Tm_arrow_1a78355922fdaba3f3848932dfc0a089 () Term)
(declare-fun FStar.Pervasives.Native.__proj__Mktuple5__item___5@tok () Term)

; </end encoding FStar.Pervasives.Native.__proj__Mktuple5__item___5>


; <Skipped FStar.Pervasives.Native.__proj__Mktuple5__item___5/>


; <Start encoding >

;;;;;;;;;;;;;;;;Constructor
(declare-fun FStar.Pervasives.Native.tuple6 (Term Term Term Term Term Term) Term)
;;;;;;;;;;;;;;;;Projector
(declare-fun FStar.Pervasives.Native.tuple6@x0 (Term) Term)
;;;;;;;;;;;;;;;;Projector
(declare-fun FStar.Pervasives.Native.tuple6@x1 (Term) Term)
;;;;;;;;;;;;;;;;Projector
(declare-fun FStar.Pervasives.Native.tuple6@x2 (Term) Term)
;;;;;;;;;;;;;;;;Projector
(declare-fun FStar.Pervasives.Native.tuple6@x3 (Term) Term)
;;;;;;;;;;;;;;;;Projector
(declare-fun FStar.Pervasives.Native.tuple6@x4 (Term) Term)
;;;;;;;;;;;;;;;;Projector
(declare-fun FStar.Pervasives.Native.tuple6@x5 (Term) Term)
;;;;;;;;;;;;;;;;token
(declare-fun FStar.Pervasives.Native.tuple6@tok () Term)
;;;;;;;;;;;;;;;;Constructor
(declare-fun FStar.Pervasives.Native.Mktuple6 (Term Term Term Term Term Term Term Term Term Term Term Term) Term)
;;;;;;;;;;;;;;;;Projector
(declare-fun FStar.Pervasives.Native.Mktuple6__a (Term) Term)
;;;;;;;;;;;;;;;;Projector
(declare-fun FStar.Pervasives.Native.Mktuple6__b (Term) Term)
;;;;;;;;;;;;;;;;Projector
(declare-fun FStar.Pervasives.Native.Mktuple6__c (Term) Term)
;;;;;;;;;;;;;;;;Projector
(declare-fun FStar.Pervasives.Native.Mktuple6__d (Term) Term)
;;;;;;;;;;;;;;;;Projector
(declare-fun FStar.Pervasives.Native.Mktuple6__e (Term) Term)
;;;;;;;;;;;;;;;;Projector
(declare-fun FStar.Pervasives.Native.Mktuple6__f (Term) Term)
;;;;;;;;;;;;;;;;Projector
(declare-fun FStar.Pervasives.Native.Mktuple6__1 (Term) Term)
;;;;;;;;;;;;;;;;Projector
(declare-fun FStar.Pervasives.Native.Mktuple6__2 (Term) Term)
;;;;;;;;;;;;;;;;Projector
(declare-fun FStar.Pervasives.Native.Mktuple6__3 (Term) Term)
;;;;;;;;;;;;;;;;Projector
(declare-fun FStar.Pervasives.Native.Mktuple6__4 (Term) Term)
;;;;;;;;;;;;;;;;Projector
(declare-fun FStar.Pervasives.Native.Mktuple6__5 (Term) Term)
;;;;;;;;;;;;;;;;Projector
(declare-fun FStar.Pervasives.Native.Mktuple6__6 (Term) Term)
;;;;;;;;;;;;;;;;data constructor proxy: Mktuple6
(declare-fun FStar.Pervasives.Native.Mktuple6@tok () Term)
(declare-fun Tm_arrow_f277ffaa7e891207f9c6bff5b88ffd67 () Term)

; <Start encoding FStar.Pervasives.Native.tuple6>


; <start constructor FStar.Pervasives.Native.tuple6>

;;;;;;;;;;;;;;;;Discriminator definition
(define-fun is-FStar.Pervasives.Native.tuple6 ((__@x0 Term)) Bool
 (and (= (Term_constr_id __@x0)
209)
(exists ((@x0 Term) (@x1 Term) (@x2 Term) (@x3 Term) (@x4 Term) (@x5 Term))
 (! (= __@x0
(FStar.Pervasives.Native.tuple6 @x0
@x1
@x2
@x3
@x4
@x5))
 
;;no pats
:qid is-FStar.Pervasives.Native.tuple6))))

; </end constructor FStar.Pervasives.Native.tuple6>


; </end encoding FStar.Pervasives.Native.tuple6>


; <Start encoding FStar.Pervasives.Native.Mktuple6>


; <start constructor FStar.Pervasives.Native.Mktuple6>

;;;;;;;;;;;;;;;;Discriminator definition
(define-fun is-FStar.Pervasives.Native.Mktuple6 ((__@x0 Term)) Bool
 (and (= (Term_constr_id __@x0)
216)
(= __@x0
(FStar.Pervasives.Native.Mktuple6 (FStar.Pervasives.Native.Mktuple6__a __@x0)
(FStar.Pervasives.Native.Mktuple6__b __@x0)
(FStar.Pervasives.Native.Mktuple6__c __@x0)
(FStar.Pervasives.Native.Mktuple6__d __@x0)
(FStar.Pervasives.Native.Mktuple6__e __@x0)
(FStar.Pervasives.Native.Mktuple6__f __@x0)
(FStar.Pervasives.Native.Mktuple6__1 __@x0)
(FStar.Pervasives.Native.Mktuple6__2 __@x0)
(FStar.Pervasives.Native.Mktuple6__3 __@x0)
(FStar.Pervasives.Native.Mktuple6__4 __@x0)
(FStar.Pervasives.Native.Mktuple6__5 __@x0)
(FStar.Pervasives.Native.Mktuple6__6 __@x0)))))

; </end constructor FStar.Pervasives.Native.Mktuple6>


; </end encoding FStar.Pervasives.Native.Mktuple6>


; </end encoding >


; <Start encoding FStar.Pervasives.Native.tuple6__uu___haseq>


; </end encoding FStar.Pervasives.Native.tuple6__uu___haseq>


; <Start encoding FStar.Pervasives.Native.uu___is_Mktuple6>

(declare-fun FStar.Pervasives.Native.uu___is_Mktuple6 (Term Term Term Term Term Term Term) Term)
(declare-fun Tm_arrow_286587a1b9d299ba75a076f54a6dad5f () Term)
(declare-fun FStar.Pervasives.Native.uu___is_Mktuple6@tok () Term)

; </end encoding FStar.Pervasives.Native.uu___is_Mktuple6>


; <Skipped FStar.Pervasives.Native.uu___is_Mktuple6/>


; <Start encoding FStar.Pervasives.Native.__proj__Mktuple6__item___1>

(declare-fun FStar.Pervasives.Native.__proj__Mktuple6__item___1 (Term Term Term Term Term Term Term) Term)
(declare-fun Tm_arrow_5b1e145eeceab869b8e427e6927dbd63 () Term)
(declare-fun FStar.Pervasives.Native.__proj__Mktuple6__item___1@tok () Term)

; </end encoding FStar.Pervasives.Native.__proj__Mktuple6__item___1>


; <Skipped FStar.Pervasives.Native.__proj__Mktuple6__item___1/>


; <Start encoding FStar.Pervasives.Native.__proj__Mktuple6__item___2>

(declare-fun FStar.Pervasives.Native.__proj__Mktuple6__item___2 (Term Term Term Term Term Term Term) Term)
(declare-fun Tm_arrow_3207475e225d584881d3e0a297482887 () Term)
(declare-fun FStar.Pervasives.Native.__proj__Mktuple6__item___2@tok () Term)

; </end encoding FStar.Pervasives.Native.__proj__Mktuple6__item___2>


; <Skipped FStar.Pervasives.Native.__proj__Mktuple6__item___2/>


; <Start encoding FStar.Pervasives.Native.__proj__Mktuple6__item___3>

(declare-fun FStar.Pervasives.Native.__proj__Mktuple6__item___3 (Term Term Term Term Term Term Term) Term)
(declare-fun Tm_arrow_43e491b3b537a523a4f10de18b1915f5 () Term)
(declare-fun FStar.Pervasives.Native.__proj__Mktuple6__item___3@tok () Term)

; </end encoding FStar.Pervasives.Native.__proj__Mktuple6__item___3>


; <Skipped FStar.Pervasives.Native.__proj__Mktuple6__item___3/>


; <Start encoding FStar.Pervasives.Native.__proj__Mktuple6__item___4>

(declare-fun FStar.Pervasives.Native.__proj__Mktuple6__item___4 (Term Term Term Term Term Term Term) Term)
(declare-fun Tm_arrow_f5747d5b721642d7ecb757b043f20880 () Term)
(declare-fun FStar.Pervasives.Native.__proj__Mktuple6__item___4@tok () Term)

; </end encoding FStar.Pervasives.Native.__proj__Mktuple6__item___4>


; <Skipped FStar.Pervasives.Native.__proj__Mktuple6__item___4/>


; <Start encoding FStar.Pervasives.Native.__proj__Mktuple6__item___5>

(declare-fun FStar.Pervasives.Native.__proj__Mktuple6__item___5 (Term Term Term Term Term Term Term) Term)
(declare-fun Tm_arrow_d6501381a0206e157ecc43950bb31fea () Term)
(declare-fun FStar.Pervasives.Native.__proj__Mktuple6__item___5@tok () Term)

; </end encoding FStar.Pervasives.Native.__proj__Mktuple6__item___5>


; <Skipped FStar.Pervasives.Native.__proj__Mktuple6__item___5/>


; <Start encoding FStar.Pervasives.Native.__proj__Mktuple6__item___6>

(declare-fun FStar.Pervasives.Native.__proj__Mktuple6__item___6 (Term Term Term Term Term Term Term) Term)
(declare-fun Tm_arrow_9c342f41120d0c7aea115b09b58cefb2 () Term)
(declare-fun FStar.Pervasives.Native.__proj__Mktuple6__item___6@tok () Term)

; </end encoding FStar.Pervasives.Native.__proj__Mktuple6__item___6>


; <Skipped FStar.Pervasives.Native.__proj__Mktuple6__item___6/>


; <Start encoding >

;;;;;;;;;;;;;;;;Constructor
(declare-fun FStar.Pervasives.Native.tuple7 (Term Term Term Term Term Term Term) Term)
;;;;;;;;;;;;;;;;Projector
(declare-fun FStar.Pervasives.Native.tuple7@x0 (Term) Term)
;;;;;;;;;;;;;;;;Projector
(declare-fun FStar.Pervasives.Native.tuple7@x1 (Term) Term)
;;;;;;;;;;;;;;;;Projector
(declare-fun FStar.Pervasives.Native.tuple7@x2 (Term) Term)
;;;;;;;;;;;;;;;;Projector
(declare-fun FStar.Pervasives.Native.tuple7@x3 (Term) Term)
;;;;;;;;;;;;;;;;Projector
(declare-fun FStar.Pervasives.Native.tuple7@x4 (Term) Term)
;;;;;;;;;;;;;;;;Projector
(declare-fun FStar.Pervasives.Native.tuple7@x5 (Term) Term)
;;;;;;;;;;;;;;;;Projector
(declare-fun FStar.Pervasives.Native.tuple7@x6 (Term) Term)
;;;;;;;;;;;;;;;;token
(declare-fun FStar.Pervasives.Native.tuple7@tok () Term)
;;;;;;;;;;;;;;;;Constructor
(declare-fun FStar.Pervasives.Native.Mktuple7 (Term Term Term Term Term Term Term Term Term Term Term Term Term Term) Term)
;;;;;;;;;;;;;;;;Projector
(declare-fun FStar.Pervasives.Native.Mktuple7__a (Term) Term)
;;;;;;;;;;;;;;;;Projector
(declare-fun FStar.Pervasives.Native.Mktuple7__b (Term) Term)
;;;;;;;;;;;;;;;;Projector
(declare-fun FStar.Pervasives.Native.Mktuple7__c (Term) Term)
;;;;;;;;;;;;;;;;Projector
(declare-fun FStar.Pervasives.Native.Mktuple7__d (Term) Term)
;;;;;;;;;;;;;;;;Projector
(declare-fun FStar.Pervasives.Native.Mktuple7__e (Term) Term)
;;;;;;;;;;;;;;;;Projector
(declare-fun FStar.Pervasives.Native.Mktuple7__f (Term) Term)
;;;;;;;;;;;;;;;;Projector
(declare-fun FStar.Pervasives.Native.Mktuple7__g (Term) Term)
;;;;;;;;;;;;;;;;Projector
(declare-fun FStar.Pervasives.Native.Mktuple7__1 (Term) Term)
;;;;;;;;;;;;;;;;Projector
(declare-fun FStar.Pervasives.Native.Mktuple7__2 (Term) Term)
;;;;;;;;;;;;;;;;Projector
(declare-fun FStar.Pervasives.Native.Mktuple7__3 (Term) Term)
;;;;;;;;;;;;;;;;Projector
(declare-fun FStar.Pervasives.Native.Mktuple7__4 (Term) Term)
;;;;;;;;;;;;;;;;Projector
(declare-fun FStar.Pervasives.Native.Mktuple7__5 (Term) Term)
;;;;;;;;;;;;;;;;Projector
(declare-fun FStar.Pervasives.Native.Mktuple7__6 (Term) Term)
;;;;;;;;;;;;;;;;Projector
(declare-fun FStar.Pervasives.Native.Mktuple7__7 (Term) Term)
;;;;;;;;;;;;;;;;data constructor proxy: Mktuple7
(declare-fun FStar.Pervasives.Native.Mktuple7@tok () Term)
(declare-fun Tm_arrow_37ee9ec407a0f7bb69bf1b308f74a230 () Term)

; <Start encoding FStar.Pervasives.Native.tuple7>


; <start constructor FStar.Pervasives.Native.tuple7>

;;;;;;;;;;;;;;;;Discriminator definition
(define-fun is-FStar.Pervasives.Native.tuple7 ((__@x0 Term)) Bool
 (and (= (Term_constr_id __@x0)
234)
(exists ((@x0 Term) (@x1 Term) (@x2 Term) (@x3 Term) (@x4 Term) (@x5 Term) (@x6 Term))
 (! (= __@x0
(FStar.Pervasives.Native.tuple7 @x0
@x1
@x2
@x3
@x4
@x5
@x6))
 
;;no pats
:qid is-FStar.Pervasives.Native.tuple7))))

; </end constructor FStar.Pervasives.Native.tuple7>


; </end encoding FStar.Pervasives.Native.tuple7>


; <Start encoding FStar.Pervasives.Native.Mktuple7>


; <start constructor FStar.Pervasives.Native.Mktuple7>

;;;;;;;;;;;;;;;;Discriminator definition
(define-fun is-FStar.Pervasives.Native.Mktuple7 ((__@x0 Term)) Bool
 (and (= (Term_constr_id __@x0)
241)
(= __@x0
(FStar.Pervasives.Native.Mktuple7 (FStar.Pervasives.Native.Mktuple7__a __@x0)
(FStar.Pervasives.Native.Mktuple7__b __@x0)
(FStar.Pervasives.Native.Mktuple7__c __@x0)
(FStar.Pervasives.Native.Mktuple7__d __@x0)
(FStar.Pervasives.Native.Mktuple7__e __@x0)
(FStar.Pervasives.Native.Mktuple7__f __@x0)
(FStar.Pervasives.Native.Mktuple7__g __@x0)
(FStar.Pervasives.Native.Mktuple7__1 __@x0)
(FStar.Pervasives.Native.Mktuple7__2 __@x0)
(FStar.Pervasives.Native.Mktuple7__3 __@x0)
(FStar.Pervasives.Native.Mktuple7__4 __@x0)
(FStar.Pervasives.Native.Mktuple7__5 __@x0)
(FStar.Pervasives.Native.Mktuple7__6 __@x0)
(FStar.Pervasives.Native.Mktuple7__7 __@x0)))))

; </end constructor FStar.Pervasives.Native.Mktuple7>


; </end encoding FStar.Pervasives.Native.Mktuple7>


; </end encoding >


; <Start encoding FStar.Pervasives.Native.tuple7__uu___haseq>


; </end encoding FStar.Pervasives.Native.tuple7__uu___haseq>


; <Start encoding FStar.Pervasives.Native.uu___is_Mktuple7>

(declare-fun FStar.Pervasives.Native.uu___is_Mktuple7 (Term Term Term Term Term Term Term Term) Term)
(declare-fun Tm_arrow_612dde2fedb1440c5d790ba7f5015319 () Term)
(declare-fun FStar.Pervasives.Native.uu___is_Mktuple7@tok () Term)

; </end encoding FStar.Pervasives.Native.uu___is_Mktuple7>


; <Skipped FStar.Pervasives.Native.uu___is_Mktuple7/>


; <Start encoding FStar.Pervasives.Native.__proj__Mktuple7__item___1>

(declare-fun FStar.Pervasives.Native.__proj__Mktuple7__item___1 (Term Term Term Term Term Term Term Term) Term)
(declare-fun Tm_arrow_01c4488a68699f466c59799f5c1173ff () Term)
(declare-fun FStar.Pervasives.Native.__proj__Mktuple7__item___1@tok () Term)

; </end encoding FStar.Pervasives.Native.__proj__Mktuple7__item___1>


; <Skipped FStar.Pervasives.Native.__proj__Mktuple7__item___1/>


; <Start encoding FStar.Pervasives.Native.__proj__Mktuple7__item___2>

(declare-fun FStar.Pervasives.Native.__proj__Mktuple7__item___2 (Term Term Term Term Term Term Term Term) Term)
(declare-fun Tm_arrow_f317591858699585c67fe4ba8664e34c () Term)
(declare-fun FStar.Pervasives.Native.__proj__Mktuple7__item___2@tok () Term)

; </end encoding FStar.Pervasives.Native.__proj__Mktuple7__item___2>


; <Skipped FStar.Pervasives.Native.__proj__Mktuple7__item___2/>


; <Start encoding FStar.Pervasives.Native.__proj__Mktuple7__item___3>

(declare-fun FStar.Pervasives.Native.__proj__Mktuple7__item___3 (Term Term Term Term Term Term Term Term) Term)
(declare-fun Tm_arrow_44afce9d86f095aacc82b3ea2e0e223c () Term)
(declare-fun FStar.Pervasives.Native.__proj__Mktuple7__item___3@tok () Term)

; </end encoding FStar.Pervasives.Native.__proj__Mktuple7__item___3>


; <Skipped FStar.Pervasives.Native.__proj__Mktuple7__item___3/>


; <Start encoding FStar.Pervasives.Native.__proj__Mktuple7__item___4>

(declare-fun FStar.Pervasives.Native.__proj__Mktuple7__item___4 (Term Term Term Term Term Term Term Term) Term)
(declare-fun Tm_arrow_e857539d4cc5be0510cbcfb97cb64b35 () Term)
(declare-fun FStar.Pervasives.Native.__proj__Mktuple7__item___4@tok () Term)

; </end encoding FStar.Pervasives.Native.__proj__Mktuple7__item___4>


; <Skipped FStar.Pervasives.Native.__proj__Mktuple7__item___4/>


; <Start encoding FStar.Pervasives.Native.__proj__Mktuple7__item___5>

(declare-fun FStar.Pervasives.Native.__proj__Mktuple7__item___5 (Term Term Term Term Term Term Term Term) Term)
(declare-fun Tm_arrow_a249d3d5ba06026b12d41e289bb88061 () Term)
(declare-fun FStar.Pervasives.Native.__proj__Mktuple7__item___5@tok () Term)

; </end encoding FStar.Pervasives.Native.__proj__Mktuple7__item___5>


; <Skipped FStar.Pervasives.Native.__proj__Mktuple7__item___5/>


; <Start encoding FStar.Pervasives.Native.__proj__Mktuple7__item___6>

(declare-fun FStar.Pervasives.Native.__proj__Mktuple7__item___6 (Term Term Term Term Term Term Term Term) Term)
(declare-fun Tm_arrow_bf614c740d11cac9b5f8eb20b24c7d00 () Term)
(declare-fun FStar.Pervasives.Native.__proj__Mktuple7__item___6@tok () Term)

; </end encoding FStar.Pervasives.Native.__proj__Mktuple7__item___6>


; <Skipped FStar.Pervasives.Native.__proj__Mktuple7__item___6/>


; <Start encoding FStar.Pervasives.Native.__proj__Mktuple7__item___7>

(declare-fun FStar.Pervasives.Native.__proj__Mktuple7__item___7 (Term Term Term Term Term Term Term Term) Term)
(declare-fun Tm_arrow_e775fbf03b08091e48143165286522f7 () Term)
(declare-fun FStar.Pervasives.Native.__proj__Mktuple7__item___7@tok () Term)

; </end encoding FStar.Pervasives.Native.__proj__Mktuple7__item___7>


; <Skipped FStar.Pervasives.Native.__proj__Mktuple7__item___7/>


; <Start encoding >

;;;;;;;;;;;;;;;;Constructor
(declare-fun FStar.Pervasives.Native.tuple8 (Term Term Term Term Term Term Term Term) Term)
;;;;;;;;;;;;;;;;Projector
(declare-fun FStar.Pervasives.Native.tuple8@x0 (Term) Term)
;;;;;;;;;;;;;;;;Projector
(declare-fun FStar.Pervasives.Native.tuple8@x1 (Term) Term)
;;;;;;;;;;;;;;;;Projector
(declare-fun FStar.Pervasives.Native.tuple8@x2 (Term) Term)
;;;;;;;;;;;;;;;;Projector
(declare-fun FStar.Pervasives.Native.tuple8@x3 (Term) Term)
;;;;;;;;;;;;;;;;Projector
(declare-fun FStar.Pervasives.Native.tuple8@x4 (Term) Term)
;;;;;;;;;;;;;;;;Projector
(declare-fun FStar.Pervasives.Native.tuple8@x5 (Term) Term)
;;;;;;;;;;;;;;;;Projector
(declare-fun FStar.Pervasives.Native.tuple8@x6 (Term) Term)
;;;;;;;;;;;;;;;;Projector
(declare-fun FStar.Pervasives.Native.tuple8@x7 (Term) Term)
;;;;;;;;;;;;;;;;token
(declare-fun FStar.Pervasives.Native.tuple8@tok () Term)
;;;;;;;;;;;;;;;;Constructor
(declare-fun FStar.Pervasives.Native.Mktuple8 (Term Term Term Term Term Term Term Term Term Term Term Term Term Term Term Term) Term)
;;;;;;;;;;;;;;;;Projector
(declare-fun FStar.Pervasives.Native.Mktuple8__a (Term) Term)
;;;;;;;;;;;;;;;;Projector
(declare-fun FStar.Pervasives.Native.Mktuple8__b (Term) Term)
;;;;;;;;;;;;;;;;Projector
(declare-fun FStar.Pervasives.Native.Mktuple8__c (Term) Term)
;;;;;;;;;;;;;;;;Projector
(declare-fun FStar.Pervasives.Native.Mktuple8__d (Term) Term)
;;;;;;;;;;;;;;;;Projector
(declare-fun FStar.Pervasives.Native.Mktuple8__e (Term) Term)
;;;;;;;;;;;;;;;;Projector
(declare-fun FStar.Pervasives.Native.Mktuple8__f (Term) Term)
;;;;;;;;;;;;;;;;Projector
(declare-fun FStar.Pervasives.Native.Mktuple8__g (Term) Term)
;;;;;;;;;;;;;;;;Projector
(declare-fun FStar.Pervasives.Native.Mktuple8__h (Term) Term)
;;;;;;;;;;;;;;;;Projector
(declare-fun FStar.Pervasives.Native.Mktuple8__1 (Term) Term)
;;;;;;;;;;;;;;;;Projector
(declare-fun FStar.Pervasives.Native.Mktuple8__2 (Term) Term)
;;;;;;;;;;;;;;;;Projector
(declare-fun FStar.Pervasives.Native.Mktuple8__3 (Term) Term)
;;;;;;;;;;;;;;;;Projector
(declare-fun FStar.Pervasives.Native.Mktuple8__4 (Term) Term)
;;;;;;;;;;;;;;;;Projector
(declare-fun FStar.Pervasives.Native.Mktuple8__5 (Term) Term)
;;;;;;;;;;;;;;;;Projector
(declare-fun FStar.Pervasives.Native.Mktuple8__6 (Term) Term)
;;;;;;;;;;;;;;;;Projector
(declare-fun FStar.Pervasives.Native.Mktuple8__7 (Term) Term)
;;;;;;;;;;;;;;;;Projector
(declare-fun FStar.Pervasives.Native.Mktuple8__8 (Term) Term)
;;;;;;;;;;;;;;;;data constructor proxy: Mktuple8
(declare-fun FStar.Pervasives.Native.Mktuple8@tok () Term)
(declare-fun Tm_arrow_e922a339a0aa0f375ed7113049811583 () Term)

; <Start encoding FStar.Pervasives.Native.tuple8>


; <start constructor FStar.Pervasives.Native.tuple8>

;;;;;;;;;;;;;;;;Discriminator definition
(define-fun is-FStar.Pervasives.Native.tuple8 ((__@x0 Term)) Bool
 (and (= (Term_constr_id __@x0)
261)
(exists ((@x0 Term) (@x1 Term) (@x2 Term) (@x3 Term) (@x4 Term) (@x5 Term) (@x6 Term) (@x7 Term))
 (! (= __@x0
(FStar.Pervasives.Native.tuple8 @x0
@x1
@x2
@x3
@x4
@x5
@x6
@x7))
 
;;no pats
:qid is-FStar.Pervasives.Native.tuple8))))

; </end constructor FStar.Pervasives.Native.tuple8>


; </end encoding FStar.Pervasives.Native.tuple8>


; <Start encoding FStar.Pervasives.Native.Mktuple8>


; <start constructor FStar.Pervasives.Native.Mktuple8>

;;;;;;;;;;;;;;;;Discriminator definition
(define-fun is-FStar.Pervasives.Native.Mktuple8 ((__@x0 Term)) Bool
 (and (= (Term_constr_id __@x0)
268)
(= __@x0
(FStar.Pervasives.Native.Mktuple8 (FStar.Pervasives.Native.Mktuple8__a __@x0)
(FStar.Pervasives.Native.Mktuple8__b __@x0)
(FStar.Pervasives.Native.Mktuple8__c __@x0)
(FStar.Pervasives.Native.Mktuple8__d __@x0)
(FStar.Pervasives.Native.Mktuple8__e __@x0)
(FStar.Pervasives.Native.Mktuple8__f __@x0)
(FStar.Pervasives.Native.Mktuple8__g __@x0)
(FStar.Pervasives.Native.Mktuple8__h __@x0)
(FStar.Pervasives.Native.Mktuple8__1 __@x0)
(FStar.Pervasives.Native.Mktuple8__2 __@x0)
(FStar.Pervasives.Native.Mktuple8__3 __@x0)
(FStar.Pervasives.Native.Mktuple8__4 __@x0)
(FStar.Pervasives.Native.Mktuple8__5 __@x0)
(FStar.Pervasives.Native.Mktuple8__6 __@x0)
(FStar.Pervasives.Native.Mktuple8__7 __@x0)
(FStar.Pervasives.Native.Mktuple8__8 __@x0)))))

; </end constructor FStar.Pervasives.Native.Mktuple8>


; </end encoding FStar.Pervasives.Native.Mktuple8>


; </end encoding >


; <Start encoding FStar.Pervasives.Native.tuple8__uu___haseq>


; </end encoding FStar.Pervasives.Native.tuple8__uu___haseq>


; <Start encoding FStar.Pervasives.Native.uu___is_Mktuple8>

(declare-fun FStar.Pervasives.Native.uu___is_Mktuple8 (Term Term Term Term Term Term Term Term Term) Term)
(declare-fun Tm_arrow_ee31533e24c78558f4566668a6ec027c () Term)
(declare-fun FStar.Pervasives.Native.uu___is_Mktuple8@tok () Term)

; </end encoding FStar.Pervasives.Native.uu___is_Mktuple8>


; <Skipped FStar.Pervasives.Native.uu___is_Mktuple8/>


; <Start encoding FStar.Pervasives.Native.__proj__Mktuple8__item___1>

(declare-fun FStar.Pervasives.Native.__proj__Mktuple8__item___1 (Term Term Term Term Term Term Term Term Term) Term)
(declare-fun Tm_arrow_c971649e117e4941e7317eff508d5ea7 () Term)
(declare-fun FStar.Pervasives.Native.__proj__Mktuple8__item___1@tok () Term)

; </end encoding FStar.Pervasives.Native.__proj__Mktuple8__item___1>


; <Skipped FStar.Pervasives.Native.__proj__Mktuple8__item___1/>


; <Start encoding FStar.Pervasives.Native.__proj__Mktuple8__item___2>

(declare-fun FStar.Pervasives.Native.__proj__Mktuple8__item___2 (Term Term Term Term Term Term Term Term Term) Term)
(declare-fun Tm_arrow_97dd51e3888c1c543d8f6c73d1808548 () Term)
(declare-fun FStar.Pervasives.Native.__proj__Mktuple8__item___2@tok () Term)

; </end encoding FStar.Pervasives.Native.__proj__Mktuple8__item___2>


; <Skipped FStar.Pervasives.Native.__proj__Mktuple8__item___2/>


; <Start encoding FStar.Pervasives.Native.__proj__Mktuple8__item___3>

(declare-fun FStar.Pervasives.Native.__proj__Mktuple8__item___3 (Term Term Term Term Term Term Term Term Term) Term)
(declare-fun Tm_arrow_3931d1873633dc65fed4e022ee3df3ca () Term)
(declare-fun FStar.Pervasives.Native.__proj__Mktuple8__item___3@tok () Term)

; </end encoding FStar.Pervasives.Native.__proj__Mktuple8__item___3>


; <Skipped FStar.Pervasives.Native.__proj__Mktuple8__item___3/>


; <Start encoding FStar.Pervasives.Native.__proj__Mktuple8__item___4>

(declare-fun FStar.Pervasives.Native.__proj__Mktuple8__item___4 (Term Term Term Term Term Term Term Term Term) Term)
(declare-fun Tm_arrow_5c791e62f9472e4c351c2befb2b7a3d8 () Term)
(declare-fun FStar.Pervasives.Native.__proj__Mktuple8__item___4@tok () Term)

; </end encoding FStar.Pervasives.Native.__proj__Mktuple8__item___4>


; <Skipped FStar.Pervasives.Native.__proj__Mktuple8__item___4/>


; <Start encoding FStar.Pervasives.Native.__proj__Mktuple8__item___5>

(declare-fun FStar.Pervasives.Native.__proj__Mktuple8__item___5 (Term Term Term Term Term Term Term Term Term) Term)
(declare-fun Tm_arrow_7ef7cac898ca0ef25893959e91d8c6ce () Term)
(declare-fun FStar.Pervasives.Native.__proj__Mktuple8__item___5@tok () Term)

; </end encoding FStar.Pervasives.Native.__proj__Mktuple8__item___5>


; <Skipped FStar.Pervasives.Native.__proj__Mktuple8__item___5/>


; <Start encoding FStar.Pervasives.Native.__proj__Mktuple8__item___6>

(declare-fun FStar.Pervasives.Native.__proj__Mktuple8__item___6 (Term Term Term Term Term Term Term Term Term) Term)
(declare-fun Tm_arrow_b0ae5f58a7fa002e0313b58bf5fc74cb () Term)
(declare-fun FStar.Pervasives.Native.__proj__Mktuple8__item___6@tok () Term)

; </end encoding FStar.Pervasives.Native.__proj__Mktuple8__item___6>


; <Skipped FStar.Pervasives.Native.__proj__Mktuple8__item___6/>


; <Start encoding FStar.Pervasives.Native.__proj__Mktuple8__item___7>

(declare-fun FStar.Pervasives.Native.__proj__Mktuple8__item___7 (Term Term Term Term Term Term Term Term Term) Term)
(declare-fun Tm_arrow_7fcd94f7549ca8acfadc26bc5b82f590 () Term)
(declare-fun FStar.Pervasives.Native.__proj__Mktuple8__item___7@tok () Term)

; </end encoding FStar.Pervasives.Native.__proj__Mktuple8__item___7>


; <Skipped FStar.Pervasives.Native.__proj__Mktuple8__item___7/>


; <Start encoding FStar.Pervasives.Native.__proj__Mktuple8__item___8>

(declare-fun FStar.Pervasives.Native.__proj__Mktuple8__item___8 (Term Term Term Term Term Term Term Term Term) Term)
(declare-fun Tm_arrow_feaaf61fa62fef18c5ee7c39e9f86573 () Term)
(declare-fun FStar.Pervasives.Native.__proj__Mktuple8__item___8@tok () Term)

; </end encoding FStar.Pervasives.Native.__proj__Mktuple8__item___8>


; <Skipped FStar.Pervasives.Native.__proj__Mktuple8__item___8/>


; <Start encoding >

;;;;;;;;;;;;;;;;Constructor
(declare-fun FStar.Pervasives.Native.tuple9 (Term Term Term Term Term Term Term Term Term) Term)
;;;;;;;;;;;;;;;;Projector
(declare-fun FStar.Pervasives.Native.tuple9@x0 (Term) Term)
;;;;;;;;;;;;;;;;Projector
(declare-fun FStar.Pervasives.Native.tuple9@x1 (Term) Term)
;;;;;;;;;;;;;;;;Projector
(declare-fun FStar.Pervasives.Native.tuple9@x2 (Term) Term)
;;;;;;;;;;;;;;;;Projector
(declare-fun FStar.Pervasives.Native.tuple9@x3 (Term) Term)
;;;;;;;;;;;;;;;;Projector
(declare-fun FStar.Pervasives.Native.tuple9@x4 (Term) Term)
;;;;;;;;;;;;;;;;Projector
(declare-fun FStar.Pervasives.Native.tuple9@x5 (Term) Term)
;;;;;;;;;;;;;;;;Projector
(declare-fun FStar.Pervasives.Native.tuple9@x6 (Term) Term)
;;;;;;;;;;;;;;;;Projector
(declare-fun FStar.Pervasives.Native.tuple9@x7 (Term) Term)
;;;;;;;;;;;;;;;;Projector
(declare-fun FStar.Pervasives.Native.tuple9@x8 (Term) Term)
;;;;;;;;;;;;;;;;token
(declare-fun FStar.Pervasives.Native.tuple9@tok () Term)
;;;;;;;;;;;;;;;;Constructor
(declare-fun FStar.Pervasives.Native.Mktuple9 (Term Term Term Term Term Term Term Term Term Term Term Term Term Term Term Term Term Term) Term)
;;;;;;;;;;;;;;;;Projector
(declare-fun FStar.Pervasives.Native.Mktuple9__a (Term) Term)
;;;;;;;;;;;;;;;;Projector
(declare-fun FStar.Pervasives.Native.Mktuple9__b (Term) Term)
;;;;;;;;;;;;;;;;Projector
(declare-fun FStar.Pervasives.Native.Mktuple9__c (Term) Term)
;;;;;;;;;;;;;;;;Projector
(declare-fun FStar.Pervasives.Native.Mktuple9__d (Term) Term)
;;;;;;;;;;;;;;;;Projector
(declare-fun FStar.Pervasives.Native.Mktuple9__e (Term) Term)
;;;;;;;;;;;;;;;;Projector
(declare-fun FStar.Pervasives.Native.Mktuple9__f (Term) Term)
;;;;;;;;;;;;;;;;Projector
(declare-fun FStar.Pervasives.Native.Mktuple9__g (Term) Term)
;;;;;;;;;;;;;;;;Projector
(declare-fun FStar.Pervasives.Native.Mktuple9__h (Term) Term)
;;;;;;;;;;;;;;;;Projector
(declare-fun FStar.Pervasives.Native.Mktuple9__i (Term) Term)
;;;;;;;;;;;;;;;;Projector
(declare-fun FStar.Pervasives.Native.Mktuple9__1 (Term) Term)
;;;;;;;;;;;;;;;;Projector
(declare-fun FStar.Pervasives.Native.Mktuple9__2 (Term) Term)
;;;;;;;;;;;;;;;;Projector
(declare-fun FStar.Pervasives.Native.Mktuple9__3 (Term) Term)
;;;;;;;;;;;;;;;;Projector
(declare-fun FStar.Pervasives.Native.Mktuple9__4 (Term) Term)
;;;;;;;;;;;;;;;;Projector
(declare-fun FStar.Pervasives.Native.Mktuple9__5 (Term) Term)
;;;;;;;;;;;;;;;;Projector
(declare-fun FStar.Pervasives.Native.Mktuple9__6 (Term) Term)
;;;;;;;;;;;;;;;;Projector
(declare-fun FStar.Pervasives.Native.Mktuple9__7 (Term) Term)
;;;;;;;;;;;;;;;;Projector
(declare-fun FStar.Pervasives.Native.Mktuple9__8 (Term) Term)
;;;;;;;;;;;;;;;;Projector
(declare-fun FStar.Pervasives.Native.Mktuple9__9 (Term) Term)
;;;;;;;;;;;;;;;;data constructor proxy: Mktuple9
(declare-fun FStar.Pervasives.Native.Mktuple9@tok () Term)
(declare-fun Tm_arrow_0c6bc368a301d7de6e1939ebea91ee60 () Term)

; <Start encoding FStar.Pervasives.Native.tuple9>


; <start constructor FStar.Pervasives.Native.tuple9>

;;;;;;;;;;;;;;;;Discriminator definition
(define-fun is-FStar.Pervasives.Native.tuple9 ((__@x0 Term)) Bool
 (and (= (Term_constr_id __@x0)
290)
(exists ((@x0 Term) (@x1 Term) (@x2 Term) (@x3 Term) (@x4 Term) (@x5 Term) (@x6 Term) (@x7 Term) (@x8 Term))
 (! (= __@x0
(FStar.Pervasives.Native.tuple9 @x0
@x1
@x2
@x3
@x4
@x5
@x6
@x7
@x8))
 
;;no pats
:qid is-FStar.Pervasives.Native.tuple9))))

; </end constructor FStar.Pervasives.Native.tuple9>


; </end encoding FStar.Pervasives.Native.tuple9>


; <Start encoding FStar.Pervasives.Native.Mktuple9>


; <start constructor FStar.Pervasives.Native.Mktuple9>

;;;;;;;;;;;;;;;;Discriminator definition
(define-fun is-FStar.Pervasives.Native.Mktuple9 ((__@x0 Term)) Bool
 (and (= (Term_constr_id __@x0)
297)
(= __@x0
(FStar.Pervasives.Native.Mktuple9 (FStar.Pervasives.Native.Mktuple9__a __@x0)
(FStar.Pervasives.Native.Mktuple9__b __@x0)
(FStar.Pervasives.Native.Mktuple9__c __@x0)
(FStar.Pervasives.Native.Mktuple9__d __@x0)
(FStar.Pervasives.Native.Mktuple9__e __@x0)
(FStar.Pervasives.Native.Mktuple9__f __@x0)
(FStar.Pervasives.Native.Mktuple9__g __@x0)
(FStar.Pervasives.Native.Mktuple9__h __@x0)
(FStar.Pervasives.Native.Mktuple9__i __@x0)
(FStar.Pervasives.Native.Mktuple9__1 __@x0)
(FStar.Pervasives.Native.Mktuple9__2 __@x0)
(FStar.Pervasives.Native.Mktuple9__3 __@x0)
(FStar.Pervasives.Native.Mktuple9__4 __@x0)
(FStar.Pervasives.Native.Mktuple9__5 __@x0)
(FStar.Pervasives.Native.Mktuple9__6 __@x0)
(FStar.Pervasives.Native.Mktuple9__7 __@x0)
(FStar.Pervasives.Native.Mktuple9__8 __@x0)
(FStar.Pervasives.Native.Mktuple9__9 __@x0)))))

; </end constructor FStar.Pervasives.Native.Mktuple9>


; </end encoding FStar.Pervasives.Native.Mktuple9>


; </end encoding >


; <Start encoding FStar.Pervasives.Native.tuple9__uu___haseq>


; </end encoding FStar.Pervasives.Native.tuple9__uu___haseq>


; <Start encoding FStar.Pervasives.Native.uu___is_Mktuple9>

(declare-fun FStar.Pervasives.Native.uu___is_Mktuple9 (Term Term Term Term Term Term Term Term Term Term) Term)
(declare-fun Tm_arrow_9ac8f39c7b1df1e87db7c9bf5bc37a38 () Term)
(declare-fun FStar.Pervasives.Native.uu___is_Mktuple9@tok () Term)

; </end encoding FStar.Pervasives.Native.uu___is_Mktuple9>


; <Skipped FStar.Pervasives.Native.uu___is_Mktuple9/>


; <Start encoding FStar.Pervasives.Native.__proj__Mktuple9__item___1>

(declare-fun FStar.Pervasives.Native.__proj__Mktuple9__item___1 (Term Term Term Term Term Term Term Term Term Term) Term)
(declare-fun Tm_arrow_270119cc1f13c9afeb25322d78efc328 () Term)
(declare-fun FStar.Pervasives.Native.__proj__Mktuple9__item___1@tok () Term)

; </end encoding FStar.Pervasives.Native.__proj__Mktuple9__item___1>


; <Skipped FStar.Pervasives.Native.__proj__Mktuple9__item___1/>


; <Start encoding FStar.Pervasives.Native.__proj__Mktuple9__item___2>

(declare-fun FStar.Pervasives.Native.__proj__Mktuple9__item___2 (Term Term Term Term Term Term Term Term Term Term) Term)
(declare-fun Tm_arrow_3c368dee2c86a1af7bd7ea91baab7613 () Term)
(declare-fun FStar.Pervasives.Native.__proj__Mktuple9__item___2@tok () Term)

; </end encoding FStar.Pervasives.Native.__proj__Mktuple9__item___2>


; <Skipped FStar.Pervasives.Native.__proj__Mktuple9__item___2/>


; <Start encoding FStar.Pervasives.Native.__proj__Mktuple9__item___3>

(declare-fun FStar.Pervasives.Native.__proj__Mktuple9__item___3 (Term Term Term Term Term Term Term Term Term Term) Term)
(declare-fun Tm_arrow_e9c745e2da3dec50930b0a7e01a11cc3 () Term)
(declare-fun FStar.Pervasives.Native.__proj__Mktuple9__item___3@tok () Term)

; </end encoding FStar.Pervasives.Native.__proj__Mktuple9__item___3>


; <Skipped FStar.Pervasives.Native.__proj__Mktuple9__item___3/>


; <Start encoding FStar.Pervasives.Native.__proj__Mktuple9__item___4>

(declare-fun FStar.Pervasives.Native.__proj__Mktuple9__item___4 (Term Term Term Term Term Term Term Term Term Term) Term)
(declare-fun Tm_arrow_a82ff41c5c66cd37481c83584c94a54d () Term)
(declare-fun FStar.Pervasives.Native.__proj__Mktuple9__item___4@tok () Term)

; </end encoding FStar.Pervasives.Native.__proj__Mktuple9__item___4>


; <Skipped FStar.Pervasives.Native.__proj__Mktuple9__item___4/>


; <Start encoding FStar.Pervasives.Native.__proj__Mktuple9__item___5>

(declare-fun FStar.Pervasives.Native.__proj__Mktuple9__item___5 (Term Term Term Term Term Term Term Term Term Term) Term)
(declare-fun Tm_arrow_1b3b4c5e68fdf7277f64bde93e6534de () Term)
(declare-fun FStar.Pervasives.Native.__proj__Mktuple9__item___5@tok () Term)

; </end encoding FStar.Pervasives.Native.__proj__Mktuple9__item___5>


; <Skipped FStar.Pervasives.Native.__proj__Mktuple9__item___5/>


; <Start encoding FStar.Pervasives.Native.__proj__Mktuple9__item___6>

(declare-fun FStar.Pervasives.Native.__proj__Mktuple9__item___6 (Term Term Term Term Term Term Term Term Term Term) Term)
(declare-fun Tm_arrow_837f1324f6fa51bb8a0e45ee48e4e058 () Term)
(declare-fun FStar.Pervasives.Native.__proj__Mktuple9__item___6@tok () Term)

; </end encoding FStar.Pervasives.Native.__proj__Mktuple9__item___6>


; <Skipped FStar.Pervasives.Native.__proj__Mktuple9__item___6/>


; <Start encoding FStar.Pervasives.Native.__proj__Mktuple9__item___7>

(declare-fun FStar.Pervasives.Native.__proj__Mktuple9__item___7 (Term Term Term Term Term Term Term Term Term Term) Term)
(declare-fun Tm_arrow_a7562220963e3431d35de76c3c9c87b9 () Term)
(declare-fun FStar.Pervasives.Native.__proj__Mktuple9__item___7@tok () Term)

; </end encoding FStar.Pervasives.Native.__proj__Mktuple9__item___7>


; <Skipped FStar.Pervasives.Native.__proj__Mktuple9__item___7/>


; <Start encoding FStar.Pervasives.Native.__proj__Mktuple9__item___8>

(declare-fun FStar.Pervasives.Native.__proj__Mktuple9__item___8 (Term Term Term Term Term Term Term Term Term Term) Term)
(declare-fun Tm_arrow_861b810bc1c20bbd221cecbce824b695 () Term)
(declare-fun FStar.Pervasives.Native.__proj__Mktuple9__item___8@tok () Term)

; </end encoding FStar.Pervasives.Native.__proj__Mktuple9__item___8>


; <Skipped FStar.Pervasives.Native.__proj__Mktuple9__item___8/>


; <Start encoding FStar.Pervasives.Native.__proj__Mktuple9__item___9>

(declare-fun FStar.Pervasives.Native.__proj__Mktuple9__item___9 (Term Term Term Term Term Term Term Term Term Term) Term)
(declare-fun Tm_arrow_9a54b18d8e08fdf0e20244b3f960c9dc () Term)
(declare-fun FStar.Pervasives.Native.__proj__Mktuple9__item___9@tok () Term)

; </end encoding FStar.Pervasives.Native.__proj__Mktuple9__item___9>


; <Skipped FStar.Pervasives.Native.__proj__Mktuple9__item___9/>


; <Start encoding >

;;;;;;;;;;;;;;;;Constructor
(declare-fun FStar.Pervasives.Native.tuple10 (Term Term Term Term Term Term Term Term Term Term) Term)
;;;;;;;;;;;;;;;;Projector
(declare-fun FStar.Pervasives.Native.tuple10@x0 (Term) Term)
;;;;;;;;;;;;;;;;Projector
(declare-fun FStar.Pervasives.Native.tuple10@x1 (Term) Term)
;;;;;;;;;;;;;;;;Projector
(declare-fun FStar.Pervasives.Native.tuple10@x2 (Term) Term)
;;;;;;;;;;;;;;;;Projector
(declare-fun FStar.Pervasives.Native.tuple10@x3 (Term) Term)
;;;;;;;;;;;;;;;;Projector
(declare-fun FStar.Pervasives.Native.tuple10@x4 (Term) Term)
;;;;;;;;;;;;;;;;Projector
(declare-fun FStar.Pervasives.Native.tuple10@x5 (Term) Term)
;;;;;;;;;;;;;;;;Projector
(declare-fun FStar.Pervasives.Native.tuple10@x6 (Term) Term)
;;;;;;;;;;;;;;;;Projector
(declare-fun FStar.Pervasives.Native.tuple10@x7 (Term) Term)
;;;;;;;;;;;;;;;;Projector
(declare-fun FStar.Pervasives.Native.tuple10@x8 (Term) Term)
;;;;;;;;;;;;;;;;Projector
(declare-fun FStar.Pervasives.Native.tuple10@x9 (Term) Term)
;;;;;;;;;;;;;;;;token
(declare-fun FStar.Pervasives.Native.tuple10@tok () Term)
;;;;;;;;;;;;;;;;Constructor
(declare-fun FStar.Pervasives.Native.Mktuple10 (Term Term Term Term Term Term Term Term Term Term Term Term Term Term Term Term Term Term Term Term) Term)
;;;;;;;;;;;;;;;;Projector
(declare-fun FStar.Pervasives.Native.Mktuple10__a (Term) Term)
;;;;;;;;;;;;;;;;Projector
(declare-fun FStar.Pervasives.Native.Mktuple10__b (Term) Term)
;;;;;;;;;;;;;;;;Projector
(declare-fun FStar.Pervasives.Native.Mktuple10__c (Term) Term)
;;;;;;;;;;;;;;;;Projector
(declare-fun FStar.Pervasives.Native.Mktuple10__d (Term) Term)
;;;;;;;;;;;;;;;;Projector
(declare-fun FStar.Pervasives.Native.Mktuple10__e (Term) Term)
;;;;;;;;;;;;;;;;Projector
(declare-fun FStar.Pervasives.Native.Mktuple10__f (Term) Term)
;;;;;;;;;;;;;;;;Projector
(declare-fun FStar.Pervasives.Native.Mktuple10__g (Term) Term)
;;;;;;;;;;;;;;;;Projector
(declare-fun FStar.Pervasives.Native.Mktuple10__h (Term) Term)
;;;;;;;;;;;;;;;;Projector
(declare-fun FStar.Pervasives.Native.Mktuple10__i (Term) Term)
;;;;;;;;;;;;;;;;Projector
(declare-fun FStar.Pervasives.Native.Mktuple10__j (Term) Term)
;;;;;;;;;;;;;;;;Projector
(declare-fun FStar.Pervasives.Native.Mktuple10__1 (Term) Term)
;;;;;;;;;;;;;;;;Projector
(declare-fun FStar.Pervasives.Native.Mktuple10__2 (Term) Term)
;;;;;;;;;;;;;;;;Projector
(declare-fun FStar.Pervasives.Native.Mktuple10__3 (Term) Term)
;;;;;;;;;;;;;;;;Projector
(declare-fun FStar.Pervasives.Native.Mktuple10__4 (Term) Term)
;;;;;;;;;;;;;;;;Projector
(declare-fun FStar.Pervasives.Native.Mktuple10__5 (Term) Term)
;;;;;;;;;;;;;;;;Projector
(declare-fun FStar.Pervasives.Native.Mktuple10__6 (Term) Term)
;;;;;;;;;;;;;;;;Projector
(declare-fun FStar.Pervasives.Native.Mktuple10__7 (Term) Term)
;;;;;;;;;;;;;;;;Projector
(declare-fun FStar.Pervasives.Native.Mktuple10__8 (Term) Term)
;;;;;;;;;;;;;;;;Projector
(declare-fun FStar.Pervasives.Native.Mktuple10__9 (Term) Term)
;;;;;;;;;;;;;;;;Projector
(declare-fun FStar.Pervasives.Native.Mktuple10__10 (Term) Term)
;;;;;;;;;;;;;;;;data constructor proxy: Mktuple10
(declare-fun FStar.Pervasives.Native.Mktuple10@tok () Term)
(declare-fun Tm_arrow_61d31241317018093b2245d256adbcb5 () Term)

; <Start encoding FStar.Pervasives.Native.tuple10>


; <start constructor FStar.Pervasives.Native.tuple10>

;;;;;;;;;;;;;;;;Discriminator definition
(define-fun is-FStar.Pervasives.Native.tuple10 ((__@x0 Term)) Bool
 (and (= (Term_constr_id __@x0)
321)
(exists ((@x0 Term) (@x1 Term) (@x2 Term) (@x3 Term) (@x4 Term) (@x5 Term) (@x6 Term) (@x7 Term) (@x8 Term) (@x9 Term))
 (! (= __@x0
(FStar.Pervasives.Native.tuple10 @x0
@x1
@x2
@x3
@x4
@x5
@x6
@x7
@x8
@x9))
 
;;no pats
:qid is-FStar.Pervasives.Native.tuple10))))

; </end constructor FStar.Pervasives.Native.tuple10>


; </end encoding FStar.Pervasives.Native.tuple10>


; <Start encoding FStar.Pervasives.Native.Mktuple10>


; <start constructor FStar.Pervasives.Native.Mktuple10>

;;;;;;;;;;;;;;;;Discriminator definition
(define-fun is-FStar.Pervasives.Native.Mktuple10 ((__@x0 Term)) Bool
 (and (= (Term_constr_id __@x0)
328)
(= __@x0
(FStar.Pervasives.Native.Mktuple10 (FStar.Pervasives.Native.Mktuple10__a __@x0)
(FStar.Pervasives.Native.Mktuple10__b __@x0)
(FStar.Pervasives.Native.Mktuple10__c __@x0)
(FStar.Pervasives.Native.Mktuple10__d __@x0)
(FStar.Pervasives.Native.Mktuple10__e __@x0)
(FStar.Pervasives.Native.Mktuple10__f __@x0)
(FStar.Pervasives.Native.Mktuple10__g __@x0)
(FStar.Pervasives.Native.Mktuple10__h __@x0)
(FStar.Pervasives.Native.Mktuple10__i __@x0)
(FStar.Pervasives.Native.Mktuple10__j __@x0)
(FStar.Pervasives.Native.Mktuple10__1 __@x0)
(FStar.Pervasives.Native.Mktuple10__2 __@x0)
(FStar.Pervasives.Native.Mktuple10__3 __@x0)
(FStar.Pervasives.Native.Mktuple10__4 __@x0)
(FStar.Pervasives.Native.Mktuple10__5 __@x0)
(FStar.Pervasives.Native.Mktuple10__6 __@x0)
(FStar.Pervasives.Native.Mktuple10__7 __@x0)
(FStar.Pervasives.Native.Mktuple10__8 __@x0)
(FStar.Pervasives.Native.Mktuple10__9 __@x0)
(FStar.Pervasives.Native.Mktuple10__10 __@x0)))))

; </end constructor FStar.Pervasives.Native.Mktuple10>


; </end encoding FStar.Pervasives.Native.Mktuple10>


; </end encoding >


; <Start encoding FStar.Pervasives.Native.tuple10__uu___haseq>


; </end encoding FStar.Pervasives.Native.tuple10__uu___haseq>


; <Start encoding FStar.Pervasives.Native.uu___is_Mktuple10>

(declare-fun FStar.Pervasives.Native.uu___is_Mktuple10 (Term Term Term Term Term Term Term Term Term Term Term) Term)
(declare-fun Tm_arrow_f27282a056f525d8710bf32204d252ec () Term)
(declare-fun FStar.Pervasives.Native.uu___is_Mktuple10@tok () Term)

; </end encoding FStar.Pervasives.Native.uu___is_Mktuple10>


; <Skipped FStar.Pervasives.Native.uu___is_Mktuple10/>


; <Start encoding FStar.Pervasives.Native.__proj__Mktuple10__item___1>

(declare-fun FStar.Pervasives.Native.__proj__Mktuple10__item___1 (Term Term Term Term Term Term Term Term Term Term Term) Term)
(declare-fun Tm_arrow_c581e9177cd071a1b6e057fca49ea75b () Term)
(declare-fun FStar.Pervasives.Native.__proj__Mktuple10__item___1@tok () Term)

; </end encoding FStar.Pervasives.Native.__proj__Mktuple10__item___1>


; <Skipped FStar.Pervasives.Native.__proj__Mktuple10__item___1/>


; <Start encoding FStar.Pervasives.Native.__proj__Mktuple10__item___2>

(declare-fun FStar.Pervasives.Native.__proj__Mktuple10__item___2 (Term Term Term Term Term Term Term Term Term Term Term) Term)
(declare-fun Tm_arrow_ae4b2db87d7c69a8380f4d5ae20f2149 () Term)
(declare-fun FStar.Pervasives.Native.__proj__Mktuple10__item___2@tok () Term)

; </end encoding FStar.Pervasives.Native.__proj__Mktuple10__item___2>


; <Skipped FStar.Pervasives.Native.__proj__Mktuple10__item___2/>


; <Start encoding FStar.Pervasives.Native.__proj__Mktuple10__item___3>

(declare-fun FStar.Pervasives.Native.__proj__Mktuple10__item___3 (Term Term Term Term Term Term Term Term Term Term Term) Term)
(declare-fun Tm_arrow_a21274cb112dc6619b2bde244e6a0f9a () Term)
(declare-fun FStar.Pervasives.Native.__proj__Mktuple10__item___3@tok () Term)

; </end encoding FStar.Pervasives.Native.__proj__Mktuple10__item___3>


; <Skipped FStar.Pervasives.Native.__proj__Mktuple10__item___3/>


; <Start encoding FStar.Pervasives.Native.__proj__Mktuple10__item___4>

(declare-fun FStar.Pervasives.Native.__proj__Mktuple10__item___4 (Term Term Term Term Term Term Term Term Term Term Term) Term)
(declare-fun Tm_arrow_9a051d5cacf4367d170d590ba8bb720d () Term)
(declare-fun FStar.Pervasives.Native.__proj__Mktuple10__item___4@tok () Term)

; </end encoding FStar.Pervasives.Native.__proj__Mktuple10__item___4>


; <Skipped FStar.Pervasives.Native.__proj__Mktuple10__item___4/>


; <Start encoding FStar.Pervasives.Native.__proj__Mktuple10__item___5>

(declare-fun FStar.Pervasives.Native.__proj__Mktuple10__item___5 (Term Term Term Term Term Term Term Term Term Term Term) Term)
(declare-fun Tm_arrow_bbd73769b626202d4de52d4d60cd3b75 () Term)
(declare-fun FStar.Pervasives.Native.__proj__Mktuple10__item___5@tok () Term)

; </end encoding FStar.Pervasives.Native.__proj__Mktuple10__item___5>


; <Skipped FStar.Pervasives.Native.__proj__Mktuple10__item___5/>


; <Start encoding FStar.Pervasives.Native.__proj__Mktuple10__item___6>

(declare-fun FStar.Pervasives.Native.__proj__Mktuple10__item___6 (Term Term Term Term Term Term Term Term Term Term Term) Term)
(declare-fun Tm_arrow_7ceeded5a3852448c1a5406becbd990e () Term)
(declare-fun FStar.Pervasives.Native.__proj__Mktuple10__item___6@tok () Term)

; </end encoding FStar.Pervasives.Native.__proj__Mktuple10__item___6>


; <Skipped FStar.Pervasives.Native.__proj__Mktuple10__item___6/>


; <Start encoding FStar.Pervasives.Native.__proj__Mktuple10__item___7>

(declare-fun FStar.Pervasives.Native.__proj__Mktuple10__item___7 (Term Term Term Term Term Term Term Term Term Term Term) Term)
(declare-fun Tm_arrow_c68947c71d484ad43cd50646c4e1daf4 () Term)
(declare-fun FStar.Pervasives.Native.__proj__Mktuple10__item___7@tok () Term)

; </end encoding FStar.Pervasives.Native.__proj__Mktuple10__item___7>


; <Skipped FStar.Pervasives.Native.__proj__Mktuple10__item___7/>


; <Start encoding FStar.Pervasives.Native.__proj__Mktuple10__item___8>

(declare-fun FStar.Pervasives.Native.__proj__Mktuple10__item___8 (Term Term Term Term Term Term Term Term Term Term Term) Term)
(declare-fun Tm_arrow_e7b9ff90289491020fe84c6ab3bc60c6 () Term)
(declare-fun FStar.Pervasives.Native.__proj__Mktuple10__item___8@tok () Term)

; </end encoding FStar.Pervasives.Native.__proj__Mktuple10__item___8>


; <Skipped FStar.Pervasives.Native.__proj__Mktuple10__item___8/>


; <Start encoding FStar.Pervasives.Native.__proj__Mktuple10__item___9>

(declare-fun FStar.Pervasives.Native.__proj__Mktuple10__item___9 (Term Term Term Term Term Term Term Term Term Term Term) Term)
(declare-fun Tm_arrow_6dbb3170f112f78092d1caee0b341678 () Term)
(declare-fun FStar.Pervasives.Native.__proj__Mktuple10__item___9@tok () Term)

; </end encoding FStar.Pervasives.Native.__proj__Mktuple10__item___9>


; <Skipped FStar.Pervasives.Native.__proj__Mktuple10__item___9/>


; <Start encoding FStar.Pervasives.Native.__proj__Mktuple10__item___10>

(declare-fun FStar.Pervasives.Native.__proj__Mktuple10__item___10 (Term Term Term Term Term Term Term Term Term Term Term) Term)
(declare-fun Tm_arrow_45598a99c0a7fcc1bf2258b9ad4256cf () Term)
(declare-fun FStar.Pervasives.Native.__proj__Mktuple10__item___10@tok () Term)

; </end encoding FStar.Pervasives.Native.__proj__Mktuple10__item___10>


; <Skipped FStar.Pervasives.Native.__proj__Mktuple10__item___10/>


; <Start encoding >

;;;;;;;;;;;;;;;;Constructor
(declare-fun FStar.Pervasives.Native.tuple11 (Term Term Term Term Term Term Term Term Term Term Term) Term)
;;;;;;;;;;;;;;;;Projector
(declare-fun FStar.Pervasives.Native.tuple11@x0 (Term) Term)
;;;;;;;;;;;;;;;;Projector
(declare-fun FStar.Pervasives.Native.tuple11@x1 (Term) Term)
;;;;;;;;;;;;;;;;Projector
(declare-fun FStar.Pervasives.Native.tuple11@x2 (Term) Term)
;;;;;;;;;;;;;;;;Projector
(declare-fun FStar.Pervasives.Native.tuple11@x3 (Term) Term)
;;;;;;;;;;;;;;;;Projector
(declare-fun FStar.Pervasives.Native.tuple11@x4 (Term) Term)
;;;;;;;;;;;;;;;;Projector
(declare-fun FStar.Pervasives.Native.tuple11@x5 (Term) Term)
;;;;;;;;;;;;;;;;Projector
(declare-fun FStar.Pervasives.Native.tuple11@x6 (Term) Term)
;;;;;;;;;;;;;;;;Projector
(declare-fun FStar.Pervasives.Native.tuple11@x7 (Term) Term)
;;;;;;;;;;;;;;;;Projector
(declare-fun FStar.Pervasives.Native.tuple11@x8 (Term) Term)
;;;;;;;;;;;;;;;;Projector
(declare-fun FStar.Pervasives.Native.tuple11@x9 (Term) Term)
;;;;;;;;;;;;;;;;Projector
(declare-fun FStar.Pervasives.Native.tuple11@x10 (Term) Term)
;;;;;;;;;;;;;;;;token
(declare-fun FStar.Pervasives.Native.tuple11@tok () Term)
;;;;;;;;;;;;;;;;Constructor
(declare-fun FStar.Pervasives.Native.Mktuple11 (Term Term Term Term Term Term Term Term Term Term Term Term Term Term Term Term Term Term Term Term Term Term) Term)
;;;;;;;;;;;;;;;;Projector
(declare-fun FStar.Pervasives.Native.Mktuple11__a (Term) Term)
;;;;;;;;;;;;;;;;Projector
(declare-fun FStar.Pervasives.Native.Mktuple11__b (Term) Term)
;;;;;;;;;;;;;;;;Projector
(declare-fun FStar.Pervasives.Native.Mktuple11__c (Term) Term)
;;;;;;;;;;;;;;;;Projector
(declare-fun FStar.Pervasives.Native.Mktuple11__d (Term) Term)
;;;;;;;;;;;;;;;;Projector
(declare-fun FStar.Pervasives.Native.Mktuple11__e (Term) Term)
;;;;;;;;;;;;;;;;Projector
(declare-fun FStar.Pervasives.Native.Mktuple11__f (Term) Term)
;;;;;;;;;;;;;;;;Projector
(declare-fun FStar.Pervasives.Native.Mktuple11__g (Term) Term)
;;;;;;;;;;;;;;;;Projector
(declare-fun FStar.Pervasives.Native.Mktuple11__h (Term) Term)
;;;;;;;;;;;;;;;;Projector
(declare-fun FStar.Pervasives.Native.Mktuple11__i (Term) Term)
;;;;;;;;;;;;;;;;Projector
(declare-fun FStar.Pervasives.Native.Mktuple11__j (Term) Term)
;;;;;;;;;;;;;;;;Projector
(declare-fun FStar.Pervasives.Native.Mktuple11__k (Term) Term)
;;;;;;;;;;;;;;;;Projector
(declare-fun FStar.Pervasives.Native.Mktuple11__1 (Term) Term)
;;;;;;;;;;;;;;;;Projector
(declare-fun FStar.Pervasives.Native.Mktuple11__2 (Term) Term)
;;;;;;;;;;;;;;;;Projector
(declare-fun FStar.Pervasives.Native.Mktuple11__3 (Term) Term)
;;;;;;;;;;;;;;;;Projector
(declare-fun FStar.Pervasives.Native.Mktuple11__4 (Term) Term)
;;;;;;;;;;;;;;;;Projector
(declare-fun FStar.Pervasives.Native.Mktuple11__5 (Term) Term)
;;;;;;;;;;;;;;;;Projector
(declare-fun FStar.Pervasives.Native.Mktuple11__6 (Term) Term)
;;;;;;;;;;;;;;;;Projector
(declare-fun FStar.Pervasives.Native.Mktuple11__7 (Term) Term)
;;;;;;;;;;;;;;;;Projector
(declare-fun FStar.Pervasives.Native.Mktuple11__8 (Term) Term)
;;;;;;;;;;;;;;;;Projector
(declare-fun FStar.Pervasives.Native.Mktuple11__9 (Term) Term)
;;;;;;;;;;;;;;;;Projector
(declare-fun FStar.Pervasives.Native.Mktuple11__10 (Term) Term)
;;;;;;;;;;;;;;;;Projector
(declare-fun FStar.Pervasives.Native.Mktuple11__11 (Term) Term)
;;;;;;;;;;;;;;;;data constructor proxy: Mktuple11
(declare-fun FStar.Pervasives.Native.Mktuple11@tok () Term)
(declare-fun Tm_arrow_bf9783a1a3bf19ab918f42acff1daa32 () Term)

; <Start encoding FStar.Pervasives.Native.tuple11>


; <start constructor FStar.Pervasives.Native.tuple11>

;;;;;;;;;;;;;;;;Discriminator definition
(define-fun is-FStar.Pervasives.Native.tuple11 ((__@x0 Term)) Bool
 (and (= (Term_constr_id __@x0)
354)
(exists ((@x0 Term) (@x1 Term) (@x2 Term) (@x3 Term) (@x4 Term) (@x5 Term) (@x6 Term) (@x7 Term) (@x8 Term) (@x9 Term) (@x10 Term))
 (! (= __@x0
(FStar.Pervasives.Native.tuple11 @x0
@x1
@x2
@x3
@x4
@x5
@x6
@x7
@x8
@x9
@x10))
 
;;no pats
:qid is-FStar.Pervasives.Native.tuple11))))

; </end constructor FStar.Pervasives.Native.tuple11>


; </end encoding FStar.Pervasives.Native.tuple11>


; <Start encoding FStar.Pervasives.Native.Mktuple11>


; <start constructor FStar.Pervasives.Native.Mktuple11>

;;;;;;;;;;;;;;;;Discriminator definition
(define-fun is-FStar.Pervasives.Native.Mktuple11 ((__@x0 Term)) Bool
 (and (= (Term_constr_id __@x0)
361)
(= __@x0
(FStar.Pervasives.Native.Mktuple11 (FStar.Pervasives.Native.Mktuple11__a __@x0)
(FStar.Pervasives.Native.Mktuple11__b __@x0)
(FStar.Pervasives.Native.Mktuple11__c __@x0)
(FStar.Pervasives.Native.Mktuple11__d __@x0)
(FStar.Pervasives.Native.Mktuple11__e __@x0)
(FStar.Pervasives.Native.Mktuple11__f __@x0)
(FStar.Pervasives.Native.Mktuple11__g __@x0)
(FStar.Pervasives.Native.Mktuple11__h __@x0)
(FStar.Pervasives.Native.Mktuple11__i __@x0)
(FStar.Pervasives.Native.Mktuple11__j __@x0)
(FStar.Pervasives.Native.Mktuple11__k __@x0)
(FStar.Pervasives.Native.Mktuple11__1 __@x0)
(FStar.Pervasives.Native.Mktuple11__2 __@x0)
(FStar.Pervasives.Native.Mktuple11__3 __@x0)
(FStar.Pervasives.Native.Mktuple11__4 __@x0)
(FStar.Pervasives.Native.Mktuple11__5 __@x0)
(FStar.Pervasives.Native.Mktuple11__6 __@x0)
(FStar.Pervasives.Native.Mktuple11__7 __@x0)
(FStar.Pervasives.Native.Mktuple11__8 __@x0)
(FStar.Pervasives.Native.Mktuple11__9 __@x0)
(FStar.Pervasives.Native.Mktuple11__10 __@x0)
(FStar.Pervasives.Native.Mktuple11__11 __@x0)))))

; </end constructor FStar.Pervasives.Native.Mktuple11>


; </end encoding FStar.Pervasives.Native.Mktuple11>


; </end encoding >


; <Start encoding FStar.Pervasives.Native.tuple11__uu___haseq>


; </end encoding FStar.Pervasives.Native.tuple11__uu___haseq>


; <Start encoding FStar.Pervasives.Native.uu___is_Mktuple11>

(declare-fun FStar.Pervasives.Native.uu___is_Mktuple11 (Term Term Term Term Term Term Term Term Term Term Term Term) Term)
(declare-fun Tm_arrow_005819ee7a23a5c47189bae72b85d85c () Term)
(declare-fun FStar.Pervasives.Native.uu___is_Mktuple11@tok () Term)

; </end encoding FStar.Pervasives.Native.uu___is_Mktuple11>


; <Skipped FStar.Pervasives.Native.uu___is_Mktuple11/>


; <Start encoding FStar.Pervasives.Native.__proj__Mktuple11__item___1>

(declare-fun FStar.Pervasives.Native.__proj__Mktuple11__item___1 (Term Term Term Term Term Term Term Term Term Term Term Term) Term)
(declare-fun Tm_arrow_31968e334e9582d95281307f534992a9 () Term)
(declare-fun FStar.Pervasives.Native.__proj__Mktuple11__item___1@tok () Term)

; </end encoding FStar.Pervasives.Native.__proj__Mktuple11__item___1>


; <Skipped FStar.Pervasives.Native.__proj__Mktuple11__item___1/>


; <Start encoding FStar.Pervasives.Native.__proj__Mktuple11__item___2>

(declare-fun FStar.Pervasives.Native.__proj__Mktuple11__item___2 (Term Term Term Term Term Term Term Term Term Term Term Term) Term)
(declare-fun Tm_arrow_6252dd9f4473dc54a3482810e8556404 () Term)
(declare-fun FStar.Pervasives.Native.__proj__Mktuple11__item___2@tok () Term)

; </end encoding FStar.Pervasives.Native.__proj__Mktuple11__item___2>


; <Skipped FStar.Pervasives.Native.__proj__Mktuple11__item___2/>


; <Start encoding FStar.Pervasives.Native.__proj__Mktuple11__item___3>

(declare-fun FStar.Pervasives.Native.__proj__Mktuple11__item___3 (Term Term Term Term Term Term Term Term Term Term Term Term) Term)
(declare-fun Tm_arrow_ec3ce6b7406c091cd7d0961922bb5a02 () Term)
(declare-fun FStar.Pervasives.Native.__proj__Mktuple11__item___3@tok () Term)

; </end encoding FStar.Pervasives.Native.__proj__Mktuple11__item___3>


; <Skipped FStar.Pervasives.Native.__proj__Mktuple11__item___3/>


; <Start encoding FStar.Pervasives.Native.__proj__Mktuple11__item___4>

(declare-fun FStar.Pervasives.Native.__proj__Mktuple11__item___4 (Term Term Term Term Term Term Term Term Term Term Term Term) Term)
(declare-fun Tm_arrow_be7571e73b0e7fc24d03efe0e003c054 () Term)
(declare-fun FStar.Pervasives.Native.__proj__Mktuple11__item___4@tok () Term)

; </end encoding FStar.Pervasives.Native.__proj__Mktuple11__item___4>


; <Skipped FStar.Pervasives.Native.__proj__Mktuple11__item___4/>


; <Start encoding FStar.Pervasives.Native.__proj__Mktuple11__item___5>

(declare-fun FStar.Pervasives.Native.__proj__Mktuple11__item___5 (Term Term Term Term Term Term Term Term Term Term Term Term) Term)
(declare-fun Tm_arrow_97ae7d913e508c46c48c3b51553d4459 () Term)
(declare-fun FStar.Pervasives.Native.__proj__Mktuple11__item___5@tok () Term)

; </end encoding FStar.Pervasives.Native.__proj__Mktuple11__item___5>


; <Skipped FStar.Pervasives.Native.__proj__Mktuple11__item___5/>


; <Start encoding FStar.Pervasives.Native.__proj__Mktuple11__item___6>

(declare-fun FStar.Pervasives.Native.__proj__Mktuple11__item___6 (Term Term Term Term Term Term Term Term Term Term Term Term) Term)
(declare-fun Tm_arrow_1dca311798936510e0ead61e14cf32a6 () Term)
(declare-fun FStar.Pervasives.Native.__proj__Mktuple11__item___6@tok () Term)

; </end encoding FStar.Pervasives.Native.__proj__Mktuple11__item___6>


; <Skipped FStar.Pervasives.Native.__proj__Mktuple11__item___6/>


; <Start encoding FStar.Pervasives.Native.__proj__Mktuple11__item___7>

(declare-fun FStar.Pervasives.Native.__proj__Mktuple11__item___7 (Term Term Term Term Term Term Term Term Term Term Term Term) Term)
(declare-fun Tm_arrow_eec431ea31093a646681ef2ceb2e2986 () Term)
(declare-fun FStar.Pervasives.Native.__proj__Mktuple11__item___7@tok () Term)

; </end encoding FStar.Pervasives.Native.__proj__Mktuple11__item___7>


; <Skipped FStar.Pervasives.Native.__proj__Mktuple11__item___7/>


; <Start encoding FStar.Pervasives.Native.__proj__Mktuple11__item___8>

(declare-fun FStar.Pervasives.Native.__proj__Mktuple11__item___8 (Term Term Term Term Term Term Term Term Term Term Term Term) Term)
(declare-fun Tm_arrow_689b2f06e9fd83f7a84ce80a13d338c6 () Term)
(declare-fun FStar.Pervasives.Native.__proj__Mktuple11__item___8@tok () Term)

; </end encoding FStar.Pervasives.Native.__proj__Mktuple11__item___8>


; <Skipped FStar.Pervasives.Native.__proj__Mktuple11__item___8/>


; <Start encoding FStar.Pervasives.Native.__proj__Mktuple11__item___9>

(declare-fun FStar.Pervasives.Native.__proj__Mktuple11__item___9 (Term Term Term Term Term Term Term Term Term Term Term Term) Term)
(declare-fun Tm_arrow_20210a3d9498f929cb7aa68d9e8b5ebf () Term)
(declare-fun FStar.Pervasives.Native.__proj__Mktuple11__item___9@tok () Term)

; </end encoding FStar.Pervasives.Native.__proj__Mktuple11__item___9>


; <Skipped FStar.Pervasives.Native.__proj__Mktuple11__item___9/>


; <Start encoding FStar.Pervasives.Native.__proj__Mktuple11__item___10>

(declare-fun FStar.Pervasives.Native.__proj__Mktuple11__item___10 (Term Term Term Term Term Term Term Term Term Term Term Term) Term)
(declare-fun Tm_arrow_96812f2124d88760b2002bbe1502c3c9 () Term)
(declare-fun FStar.Pervasives.Native.__proj__Mktuple11__item___10@tok () Term)

; </end encoding FStar.Pervasives.Native.__proj__Mktuple11__item___10>


; <Skipped FStar.Pervasives.Native.__proj__Mktuple11__item___10/>


; <Start encoding FStar.Pervasives.Native.__proj__Mktuple11__item___11>

(declare-fun FStar.Pervasives.Native.__proj__Mktuple11__item___11 (Term Term Term Term Term Term Term Term Term Term Term Term) Term)
(declare-fun Tm_arrow_abcfa2582f68905d460c5ef4a7642f2d () Term)
(declare-fun FStar.Pervasives.Native.__proj__Mktuple11__item___11@tok () Term)

; </end encoding FStar.Pervasives.Native.__proj__Mktuple11__item___11>


; <Skipped FStar.Pervasives.Native.__proj__Mktuple11__item___11/>


; <Start encoding >

;;;;;;;;;;;;;;;;Constructor
(declare-fun FStar.Pervasives.Native.tuple12 (Term Term Term Term Term Term Term Term Term Term Term Term) Term)
;;;;;;;;;;;;;;;;Projector
(declare-fun FStar.Pervasives.Native.tuple12@x0 (Term) Term)
;;;;;;;;;;;;;;;;Projector
(declare-fun FStar.Pervasives.Native.tuple12@x1 (Term) Term)
;;;;;;;;;;;;;;;;Projector
(declare-fun FStar.Pervasives.Native.tuple12@x2 (Term) Term)
;;;;;;;;;;;;;;;;Projector
(declare-fun FStar.Pervasives.Native.tuple12@x3 (Term) Term)
;;;;;;;;;;;;;;;;Projector
(declare-fun FStar.Pervasives.Native.tuple12@x4 (Term) Term)
;;;;;;;;;;;;;;;;Projector
(declare-fun FStar.Pervasives.Native.tuple12@x5 (Term) Term)
;;;;;;;;;;;;;;;;Projector
(declare-fun FStar.Pervasives.Native.tuple12@x6 (Term) Term)
;;;;;;;;;;;;;;;;Projector
(declare-fun FStar.Pervasives.Native.tuple12@x7 (Term) Term)
;;;;;;;;;;;;;;;;Projector
(declare-fun FStar.Pervasives.Native.tuple12@x8 (Term) Term)
;;;;;;;;;;;;;;;;Projector
(declare-fun FStar.Pervasives.Native.tuple12@x9 (Term) Term)
;;;;;;;;;;;;;;;;Projector
(declare-fun FStar.Pervasives.Native.tuple12@x10 (Term) Term)
;;;;;;;;;;;;;;;;Projector
(declare-fun FStar.Pervasives.Native.tuple12@x11 (Term) Term)
;;;;;;;;;;;;;;;;token
(declare-fun FStar.Pervasives.Native.tuple12@tok () Term)
;;;;;;;;;;;;;;;;Constructor
(declare-fun FStar.Pervasives.Native.Mktuple12 (Term Term Term Term Term Term Term Term Term Term Term Term Term Term Term Term Term Term Term Term Term Term Term Term) Term)
;;;;;;;;;;;;;;;;Projector
(declare-fun FStar.Pervasives.Native.Mktuple12__a (Term) Term)
;;;;;;;;;;;;;;;;Projector
(declare-fun FStar.Pervasives.Native.Mktuple12__b (Term) Term)
;;;;;;;;;;;;;;;;Projector
(declare-fun FStar.Pervasives.Native.Mktuple12__c (Term) Term)
;;;;;;;;;;;;;;;;Projector
(declare-fun FStar.Pervasives.Native.Mktuple12__d (Term) Term)
;;;;;;;;;;;;;;;;Projector
(declare-fun FStar.Pervasives.Native.Mktuple12__e (Term) Term)
;;;;;;;;;;;;;;;;Projector
(declare-fun FStar.Pervasives.Native.Mktuple12__f (Term) Term)
;;;;;;;;;;;;;;;;Projector
(declare-fun FStar.Pervasives.Native.Mktuple12__g (Term) Term)
;;;;;;;;;;;;;;;;Projector
(declare-fun FStar.Pervasives.Native.Mktuple12__h (Term) Term)
;;;;;;;;;;;;;;;;Projector
(declare-fun FStar.Pervasives.Native.Mktuple12__i (Term) Term)
;;;;;;;;;;;;;;;;Projector
(declare-fun FStar.Pervasives.Native.Mktuple12__j (Term) Term)
;;;;;;;;;;;;;;;;Projector
(declare-fun FStar.Pervasives.Native.Mktuple12__k (Term) Term)
;;;;;;;;;;;;;;;;Projector
(declare-fun FStar.Pervasives.Native.Mktuple12__l (Term) Term)
;;;;;;;;;;;;;;;;Projector
(declare-fun FStar.Pervasives.Native.Mktuple12__1 (Term) Term)
;;;;;;;;;;;;;;;;Projector
(declare-fun FStar.Pervasives.Native.Mktuple12__2 (Term) Term)
;;;;;;;;;;;;;;;;Projector
(declare-fun FStar.Pervasives.Native.Mktuple12__3 (Term) Term)
;;;;;;;;;;;;;;;;Projector
(declare-fun FStar.Pervasives.Native.Mktuple12__4 (Term) Term)
;;;;;;;;;;;;;;;;Projector
(declare-fun FStar.Pervasives.Native.Mktuple12__5 (Term) Term)
;;;;;;;;;;;;;;;;Projector
(declare-fun FStar.Pervasives.Native.Mktuple12__6 (Term) Term)
;;;;;;;;;;;;;;;;Projector
(declare-fun FStar.Pervasives.Native.Mktuple12__7 (Term) Term)
;;;;;;;;;;;;;;;;Projector
(declare-fun FStar.Pervasives.Native.Mktuple12__8 (Term) Term)
;;;;;;;;;;;;;;;;Projector
(declare-fun FStar.Pervasives.Native.Mktuple12__9 (Term) Term)
;;;;;;;;;;;;;;;;Projector
(declare-fun FStar.Pervasives.Native.Mktuple12__10 (Term) Term)
;;;;;;;;;;;;;;;;Projector
(declare-fun FStar.Pervasives.Native.Mktuple12__11 (Term) Term)
;;;;;;;;;;;;;;;;Projector
(declare-fun FStar.Pervasives.Native.Mktuple12__12 (Term) Term)
;;;;;;;;;;;;;;;;data constructor proxy: Mktuple12
(declare-fun FStar.Pervasives.Native.Mktuple12@tok () Term)
(declare-fun Tm_arrow_4d5cd995d6f44a2ec39d0f193be0be65 () Term)

; <Start encoding FStar.Pervasives.Native.tuple12>


; <start constructor FStar.Pervasives.Native.tuple12>

;;;;;;;;;;;;;;;;Discriminator definition
(define-fun is-FStar.Pervasives.Native.tuple12 ((__@x0 Term)) Bool
 (and (= (Term_constr_id __@x0)
389)
(exists ((@x0 Term) (@x1 Term) (@x2 Term) (@x3 Term) (@x4 Term) (@x5 Term) (@x6 Term) (@x7 Term) (@x8 Term) (@x9 Term) (@x10 Term) (@x11 Term))
 (! (= __@x0
(FStar.Pervasives.Native.tuple12 @x0
@x1
@x2
@x3
@x4
@x5
@x6
@x7
@x8
@x9
@x10
@x11))
 
;;no pats
:qid is-FStar.Pervasives.Native.tuple12))))

; </end constructor FStar.Pervasives.Native.tuple12>


; </end encoding FStar.Pervasives.Native.tuple12>


; <Start encoding FStar.Pervasives.Native.Mktuple12>


; <start constructor FStar.Pervasives.Native.Mktuple12>

;;;;;;;;;;;;;;;;Discriminator definition
(define-fun is-FStar.Pervasives.Native.Mktuple12 ((__@x0 Term)) Bool
 (and (= (Term_constr_id __@x0)
396)
(= __@x0
(FStar.Pervasives.Native.Mktuple12 (FStar.Pervasives.Native.Mktuple12__a __@x0)
(FStar.Pervasives.Native.Mktuple12__b __@x0)
(FStar.Pervasives.Native.Mktuple12__c __@x0)
(FStar.Pervasives.Native.Mktuple12__d __@x0)
(FStar.Pervasives.Native.Mktuple12__e __@x0)
(FStar.Pervasives.Native.Mktuple12__f __@x0)
(FStar.Pervasives.Native.Mktuple12__g __@x0)
(FStar.Pervasives.Native.Mktuple12__h __@x0)
(FStar.Pervasives.Native.Mktuple12__i __@x0)
(FStar.Pervasives.Native.Mktuple12__j __@x0)
(FStar.Pervasives.Native.Mktuple12__k __@x0)
(FStar.Pervasives.Native.Mktuple12__l __@x0)
(FStar.Pervasives.Native.Mktuple12__1 __@x0)
(FStar.Pervasives.Native.Mktuple12__2 __@x0)
(FStar.Pervasives.Native.Mktuple12__3 __@x0)
(FStar.Pervasives.Native.Mktuple12__4 __@x0)
(FStar.Pervasives.Native.Mktuple12__5 __@x0)
(FStar.Pervasives.Native.Mktuple12__6 __@x0)
(FStar.Pervasives.Native.Mktuple12__7 __@x0)
(FStar.Pervasives.Native.Mktuple12__8 __@x0)
(FStar.Pervasives.Native.Mktuple12__9 __@x0)
(FStar.Pervasives.Native.Mktuple12__10 __@x0)
(FStar.Pervasives.Native.Mktuple12__11 __@x0)
(FStar.Pervasives.Native.Mktuple12__12 __@x0)))))

; </end constructor FStar.Pervasives.Native.Mktuple12>


; </end encoding FStar.Pervasives.Native.Mktuple12>


; </end encoding >


; <Start encoding FStar.Pervasives.Native.tuple12__uu___haseq>


; </end encoding FStar.Pervasives.Native.tuple12__uu___haseq>


; <Start encoding FStar.Pervasives.Native.uu___is_Mktuple12>

(declare-fun FStar.Pervasives.Native.uu___is_Mktuple12 (Term Term Term Term Term Term Term Term Term Term Term Term Term) Term)
(declare-fun Tm_arrow_5c9f47d9090f554c9826d2f65e388f20 () Term)
(declare-fun FStar.Pervasives.Native.uu___is_Mktuple12@tok () Term)

; </end encoding FStar.Pervasives.Native.uu___is_Mktuple12>


; <Skipped FStar.Pervasives.Native.uu___is_Mktuple12/>


; <Start encoding FStar.Pervasives.Native.__proj__Mktuple12__item___1>

(declare-fun FStar.Pervasives.Native.__proj__Mktuple12__item___1 (Term Term Term Term Term Term Term Term Term Term Term Term Term) Term)
(declare-fun Tm_arrow_618941d7cf5ddbaabe15df8579b4a387 () Term)
(declare-fun FStar.Pervasives.Native.__proj__Mktuple12__item___1@tok () Term)

; </end encoding FStar.Pervasives.Native.__proj__Mktuple12__item___1>


; <Skipped FStar.Pervasives.Native.__proj__Mktuple12__item___1/>


; <Start encoding FStar.Pervasives.Native.__proj__Mktuple12__item___2>

(declare-fun FStar.Pervasives.Native.__proj__Mktuple12__item___2 (Term Term Term Term Term Term Term Term Term Term Term Term Term) Term)
(declare-fun Tm_arrow_84e9e2280e9bcb3233e4f33f86d66ea6 () Term)
(declare-fun FStar.Pervasives.Native.__proj__Mktuple12__item___2@tok () Term)

; </end encoding FStar.Pervasives.Native.__proj__Mktuple12__item___2>


; <Skipped FStar.Pervasives.Native.__proj__Mktuple12__item___2/>


; <Start encoding FStar.Pervasives.Native.__proj__Mktuple12__item___3>

(declare-fun FStar.Pervasives.Native.__proj__Mktuple12__item___3 (Term Term Term Term Term Term Term Term Term Term Term Term Term) Term)
(declare-fun Tm_arrow_1fa79c5abf9f18607bd2e46a1a6967fa () Term)
(declare-fun FStar.Pervasives.Native.__proj__Mktuple12__item___3@tok () Term)

; </end encoding FStar.Pervasives.Native.__proj__Mktuple12__item___3>


; <Skipped FStar.Pervasives.Native.__proj__Mktuple12__item___3/>


; <Start encoding FStar.Pervasives.Native.__proj__Mktuple12__item___4>

(declare-fun FStar.Pervasives.Native.__proj__Mktuple12__item___4 (Term Term Term Term Term Term Term Term Term Term Term Term Term) Term)
(declare-fun Tm_arrow_0f49c582489d782b08195e81221181dc () Term)
(declare-fun FStar.Pervasives.Native.__proj__Mktuple12__item___4@tok () Term)

; </end encoding FStar.Pervasives.Native.__proj__Mktuple12__item___4>


; <Skipped FStar.Pervasives.Native.__proj__Mktuple12__item___4/>


; <Start encoding FStar.Pervasives.Native.__proj__Mktuple12__item___5>

(declare-fun FStar.Pervasives.Native.__proj__Mktuple12__item___5 (Term Term Term Term Term Term Term Term Term Term Term Term Term) Term)
(declare-fun Tm_arrow_29b7181ebb44f9e4a45f95c4f8478c6a () Term)
(declare-fun FStar.Pervasives.Native.__proj__Mktuple12__item___5@tok () Term)

; </end encoding FStar.Pervasives.Native.__proj__Mktuple12__item___5>


; <Skipped FStar.Pervasives.Native.__proj__Mktuple12__item___5/>


; <Start encoding FStar.Pervasives.Native.__proj__Mktuple12__item___6>

(declare-fun FStar.Pervasives.Native.__proj__Mktuple12__item___6 (Term Term Term Term Term Term Term Term Term Term Term Term Term) Term)
(declare-fun Tm_arrow_3cc2863a7d7f23e3916fa1e43483cb90 () Term)
(declare-fun FStar.Pervasives.Native.__proj__Mktuple12__item___6@tok () Term)

; </end encoding FStar.Pervasives.Native.__proj__Mktuple12__item___6>


; <Skipped FStar.Pervasives.Native.__proj__Mktuple12__item___6/>


; <Start encoding FStar.Pervasives.Native.__proj__Mktuple12__item___7>

(declare-fun FStar.Pervasives.Native.__proj__Mktuple12__item___7 (Term Term Term Term Term Term Term Term Term Term Term Term Term) Term)
(declare-fun Tm_arrow_c7deea49701ab64a73985bf522e46359 () Term)
(declare-fun FStar.Pervasives.Native.__proj__Mktuple12__item___7@tok () Term)

; </end encoding FStar.Pervasives.Native.__proj__Mktuple12__item___7>


; <Skipped FStar.Pervasives.Native.__proj__Mktuple12__item___7/>


; <Start encoding FStar.Pervasives.Native.__proj__Mktuple12__item___8>

(declare-fun FStar.Pervasives.Native.__proj__Mktuple12__item___8 (Term Term Term Term Term Term Term Term Term Term Term Term Term) Term)
(declare-fun Tm_arrow_380615e7761919086537a14273a02d22 () Term)
(declare-fun FStar.Pervasives.Native.__proj__Mktuple12__item___8@tok () Term)

; </end encoding FStar.Pervasives.Native.__proj__Mktuple12__item___8>


; <Skipped FStar.Pervasives.Native.__proj__Mktuple12__item___8/>


; <Start encoding FStar.Pervasives.Native.__proj__Mktuple12__item___9>

(declare-fun FStar.Pervasives.Native.__proj__Mktuple12__item___9 (Term Term Term Term Term Term Term Term Term Term Term Term Term) Term)
(declare-fun Tm_arrow_245250918a4432b31aea8152d056489a () Term)
(declare-fun FStar.Pervasives.Native.__proj__Mktuple12__item___9@tok () Term)

; </end encoding FStar.Pervasives.Native.__proj__Mktuple12__item___9>


; <Skipped FStar.Pervasives.Native.__proj__Mktuple12__item___9/>


; <Start encoding FStar.Pervasives.Native.__proj__Mktuple12__item___10>

(declare-fun FStar.Pervasives.Native.__proj__Mktuple12__item___10 (Term Term Term Term Term Term Term Term Term Term Term Term Term) Term)
(declare-fun Tm_arrow_2a967c8402c441e6d8a9336a7568e4de () Term)
(declare-fun FStar.Pervasives.Native.__proj__Mktuple12__item___10@tok () Term)

; </end encoding FStar.Pervasives.Native.__proj__Mktuple12__item___10>


; <Skipped FStar.Pervasives.Native.__proj__Mktuple12__item___10/>


; <Start encoding FStar.Pervasives.Native.__proj__Mktuple12__item___11>

(declare-fun FStar.Pervasives.Native.__proj__Mktuple12__item___11 (Term Term Term Term Term Term Term Term Term Term Term Term Term) Term)
(declare-fun Tm_arrow_543c3feac0cd9e04ecb6cfd74ced8964 () Term)
(declare-fun FStar.Pervasives.Native.__proj__Mktuple12__item___11@tok () Term)

; </end encoding FStar.Pervasives.Native.__proj__Mktuple12__item___11>


; <Skipped FStar.Pervasives.Native.__proj__Mktuple12__item___11/>


; <Start encoding FStar.Pervasives.Native.__proj__Mktuple12__item___12>

(declare-fun FStar.Pervasives.Native.__proj__Mktuple12__item___12 (Term Term Term Term Term Term Term Term Term Term Term Term Term) Term)
(declare-fun Tm_arrow_e91029e2320896c60e94f554727a0c41 () Term)
(declare-fun FStar.Pervasives.Native.__proj__Mktuple12__item___12@tok () Term)

; </end encoding FStar.Pervasives.Native.__proj__Mktuple12__item___12>


; <Skipped FStar.Pervasives.Native.__proj__Mktuple12__item___12/>


; <Start encoding >

;;;;;;;;;;;;;;;;Constructor
(declare-fun FStar.Pervasives.Native.tuple13 (Term Term Term Term Term Term Term Term Term Term Term Term Term) Term)
;;;;;;;;;;;;;;;;Projector
(declare-fun FStar.Pervasives.Native.tuple13@x0 (Term) Term)
;;;;;;;;;;;;;;;;Projector
(declare-fun FStar.Pervasives.Native.tuple13@x1 (Term) Term)
;;;;;;;;;;;;;;;;Projector
(declare-fun FStar.Pervasives.Native.tuple13@x2 (Term) Term)
;;;;;;;;;;;;;;;;Projector
(declare-fun FStar.Pervasives.Native.tuple13@x3 (Term) Term)
;;;;;;;;;;;;;;;;Projector
(declare-fun FStar.Pervasives.Native.tuple13@x4 (Term) Term)
;;;;;;;;;;;;;;;;Projector
(declare-fun FStar.Pervasives.Native.tuple13@x5 (Term) Term)
;;;;;;;;;;;;;;;;Projector
(declare-fun FStar.Pervasives.Native.tuple13@x6 (Term) Term)
;;;;;;;;;;;;;;;;Projector
(declare-fun FStar.Pervasives.Native.tuple13@x7 (Term) Term)
;;;;;;;;;;;;;;;;Projector
(declare-fun FStar.Pervasives.Native.tuple13@x8 (Term) Term)
;;;;;;;;;;;;;;;;Projector
(declare-fun FStar.Pervasives.Native.tuple13@x9 (Term) Term)
;;;;;;;;;;;;;;;;Projector
(declare-fun FStar.Pervasives.Native.tuple13@x10 (Term) Term)
;;;;;;;;;;;;;;;;Projector
(declare-fun FStar.Pervasives.Native.tuple13@x11 (Term) Term)
;;;;;;;;;;;;;;;;Projector
(declare-fun FStar.Pervasives.Native.tuple13@x12 (Term) Term)
;;;;;;;;;;;;;;;;token
(declare-fun FStar.Pervasives.Native.tuple13@tok () Term)
;;;;;;;;;;;;;;;;Constructor
(declare-fun FStar.Pervasives.Native.Mktuple13 (Term Term Term Term Term Term Term Term Term Term Term Term Term Term Term Term Term Term Term Term Term Term Term Term Term Term) Term)
;;;;;;;;;;;;;;;;Projector
(declare-fun FStar.Pervasives.Native.Mktuple13__a (Term) Term)
;;;;;;;;;;;;;;;;Projector
(declare-fun FStar.Pervasives.Native.Mktuple13__b (Term) Term)
;;;;;;;;;;;;;;;;Projector
(declare-fun FStar.Pervasives.Native.Mktuple13__c (Term) Term)
;;;;;;;;;;;;;;;;Projector
(declare-fun FStar.Pervasives.Native.Mktuple13__d (Term) Term)
;;;;;;;;;;;;;;;;Projector
(declare-fun FStar.Pervasives.Native.Mktuple13__e (Term) Term)
;;;;;;;;;;;;;;;;Projector
(declare-fun FStar.Pervasives.Native.Mktuple13__f (Term) Term)
;;;;;;;;;;;;;;;;Projector
(declare-fun FStar.Pervasives.Native.Mktuple13__g (Term) Term)
;;;;;;;;;;;;;;;;Projector
(declare-fun FStar.Pervasives.Native.Mktuple13__h (Term) Term)
;;;;;;;;;;;;;;;;Projector
(declare-fun FStar.Pervasives.Native.Mktuple13__i (Term) Term)
;;;;;;;;;;;;;;;;Projector
(declare-fun FStar.Pervasives.Native.Mktuple13__j (Term) Term)
;;;;;;;;;;;;;;;;Projector
(declare-fun FStar.Pervasives.Native.Mktuple13__k (Term) Term)
;;;;;;;;;;;;;;;;Projector
(declare-fun FStar.Pervasives.Native.Mktuple13__l (Term) Term)
;;;;;;;;;;;;;;;;Projector
(declare-fun FStar.Pervasives.Native.Mktuple13__m (Term) Term)
;;;;;;;;;;;;;;;;Projector
(declare-fun FStar.Pervasives.Native.Mktuple13__1 (Term) Term)
;;;;;;;;;;;;;;;;Projector
(declare-fun FStar.Pervasives.Native.Mktuple13__2 (Term) Term)
;;;;;;;;;;;;;;;;Projector
(declare-fun FStar.Pervasives.Native.Mktuple13__3 (Term) Term)
;;;;;;;;;;;;;;;;Projector
(declare-fun FStar.Pervasives.Native.Mktuple13__4 (Term) Term)
;;;;;;;;;;;;;;;;Projector
(declare-fun FStar.Pervasives.Native.Mktuple13__5 (Term) Term)
;;;;;;;;;;;;;;;;Projector
(declare-fun FStar.Pervasives.Native.Mktuple13__6 (Term) Term)
;;;;;;;;;;;;;;;;Projector
(declare-fun FStar.Pervasives.Native.Mktuple13__7 (Term) Term)
;;;;;;;;;;;;;;;;Projector
(declare-fun FStar.Pervasives.Native.Mktuple13__8 (Term) Term)
;;;;;;;;;;;;;;;;Projector
(declare-fun FStar.Pervasives.Native.Mktuple13__9 (Term) Term)
;;;;;;;;;;;;;;;;Projector
(declare-fun FStar.Pervasives.Native.Mktuple13__10 (Term) Term)
;;;;;;;;;;;;;;;;Projector
(declare-fun FStar.Pervasives.Native.Mktuple13__11 (Term) Term)
;;;;;;;;;;;;;;;;Projector
(declare-fun FStar.Pervasives.Native.Mktuple13__12 (Term) Term)
;;;;;;;;;;;;;;;;Projector
(declare-fun FStar.Pervasives.Native.Mktuple13__13 (Term) Term)
;;;;;;;;;;;;;;;;data constructor proxy: Mktuple13
(declare-fun FStar.Pervasives.Native.Mktuple13@tok () Term)
(declare-fun Tm_arrow_6462785e86ca440ee74ed32e1053eae3 () Term)

; <Start encoding FStar.Pervasives.Native.tuple13>


; <start constructor FStar.Pervasives.Native.tuple13>

;;;;;;;;;;;;;;;;Discriminator definition
(define-fun is-FStar.Pervasives.Native.tuple13 ((__@x0 Term)) Bool
 (and (= (Term_constr_id __@x0)
426)
(exists ((@x0 Term) (@x1 Term) (@x2 Term) (@x3 Term) (@x4 Term) (@x5 Term) (@x6 Term) (@x7 Term) (@x8 Term) (@x9 Term) (@x10 Term) (@x11 Term) (@x12 Term))
 (! (= __@x0
(FStar.Pervasives.Native.tuple13 @x0
@x1
@x2
@x3
@x4
@x5
@x6
@x7
@x8
@x9
@x10
@x11
@x12))
 
;;no pats
:qid is-FStar.Pervasives.Native.tuple13))))

; </end constructor FStar.Pervasives.Native.tuple13>


; </end encoding FStar.Pervasives.Native.tuple13>


; <Start encoding FStar.Pervasives.Native.Mktuple13>


; <start constructor FStar.Pervasives.Native.Mktuple13>

;;;;;;;;;;;;;;;;Discriminator definition
(define-fun is-FStar.Pervasives.Native.Mktuple13 ((__@x0 Term)) Bool
 (and (= (Term_constr_id __@x0)
433)
(= __@x0
(FStar.Pervasives.Native.Mktuple13 (FStar.Pervasives.Native.Mktuple13__a __@x0)
(FStar.Pervasives.Native.Mktuple13__b __@x0)
(FStar.Pervasives.Native.Mktuple13__c __@x0)
(FStar.Pervasives.Native.Mktuple13__d __@x0)
(FStar.Pervasives.Native.Mktuple13__e __@x0)
(FStar.Pervasives.Native.Mktuple13__f __@x0)
(FStar.Pervasives.Native.Mktuple13__g __@x0)
(FStar.Pervasives.Native.Mktuple13__h __@x0)
(FStar.Pervasives.Native.Mktuple13__i __@x0)
(FStar.Pervasives.Native.Mktuple13__j __@x0)
(FStar.Pervasives.Native.Mktuple13__k __@x0)
(FStar.Pervasives.Native.Mktuple13__l __@x0)
(FStar.Pervasives.Native.Mktuple13__m __@x0)
(FStar.Pervasives.Native.Mktuple13__1 __@x0)
(FStar.Pervasives.Native.Mktuple13__2 __@x0)
(FStar.Pervasives.Native.Mktuple13__3 __@x0)
(FStar.Pervasives.Native.Mktuple13__4 __@x0)
(FStar.Pervasives.Native.Mktuple13__5 __@x0)
(FStar.Pervasives.Native.Mktuple13__6 __@x0)
(FStar.Pervasives.Native.Mktuple13__7 __@x0)
(FStar.Pervasives.Native.Mktuple13__8 __@x0)
(FStar.Pervasives.Native.Mktuple13__9 __@x0)
(FStar.Pervasives.Native.Mktuple13__10 __@x0)
(FStar.Pervasives.Native.Mktuple13__11 __@x0)
(FStar.Pervasives.Native.Mktuple13__12 __@x0)
(FStar.Pervasives.Native.Mktuple13__13 __@x0)))))

; </end constructor FStar.Pervasives.Native.Mktuple13>


; </end encoding FStar.Pervasives.Native.Mktuple13>


; </end encoding >


; <Start encoding FStar.Pervasives.Native.tuple13__uu___haseq>


; </end encoding FStar.Pervasives.Native.tuple13__uu___haseq>


; <Start encoding FStar.Pervasives.Native.uu___is_Mktuple13>

(declare-fun FStar.Pervasives.Native.uu___is_Mktuple13 (Term Term Term Term Term Term Term Term Term Term Term Term Term Term) Term)
(declare-fun Tm_arrow_68c092e8b387730b412c4dcf592b12d3 () Term)
(declare-fun FStar.Pervasives.Native.uu___is_Mktuple13@tok () Term)

; </end encoding FStar.Pervasives.Native.uu___is_Mktuple13>


; <Skipped FStar.Pervasives.Native.uu___is_Mktuple13/>


; <Start encoding FStar.Pervasives.Native.__proj__Mktuple13__item___1>

(declare-fun FStar.Pervasives.Native.__proj__Mktuple13__item___1 (Term Term Term Term Term Term Term Term Term Term Term Term Term Term) Term)
(declare-fun Tm_arrow_82a3dc3a5dbad615d8d4a31db238e43f () Term)
(declare-fun FStar.Pervasives.Native.__proj__Mktuple13__item___1@tok () Term)

; </end encoding FStar.Pervasives.Native.__proj__Mktuple13__item___1>


; <Skipped FStar.Pervasives.Native.__proj__Mktuple13__item___1/>


; <Start encoding FStar.Pervasives.Native.__proj__Mktuple13__item___2>

(declare-fun FStar.Pervasives.Native.__proj__Mktuple13__item___2 (Term Term Term Term Term Term Term Term Term Term Term Term Term Term) Term)
(declare-fun Tm_arrow_1da976aaa65f1c6b8b256dfc45c41306 () Term)
(declare-fun FStar.Pervasives.Native.__proj__Mktuple13__item___2@tok () Term)

; </end encoding FStar.Pervasives.Native.__proj__Mktuple13__item___2>


; <Skipped FStar.Pervasives.Native.__proj__Mktuple13__item___2/>


; <Start encoding FStar.Pervasives.Native.__proj__Mktuple13__item___3>

(declare-fun FStar.Pervasives.Native.__proj__Mktuple13__item___3 (Term Term Term Term Term Term Term Term Term Term Term Term Term Term) Term)
(declare-fun Tm_arrow_ca5cf529c415deee29e0a34c0c5d1c9f () Term)
(declare-fun FStar.Pervasives.Native.__proj__Mktuple13__item___3@tok () Term)

; </end encoding FStar.Pervasives.Native.__proj__Mktuple13__item___3>


; <Skipped FStar.Pervasives.Native.__proj__Mktuple13__item___3/>


; <Start encoding FStar.Pervasives.Native.__proj__Mktuple13__item___4>

(declare-fun FStar.Pervasives.Native.__proj__Mktuple13__item___4 (Term Term Term Term Term Term Term Term Term Term Term Term Term Term) Term)
(declare-fun Tm_arrow_94f6c578541b6cb528ca9e7dd1dacc3b () Term)
(declare-fun FStar.Pervasives.Native.__proj__Mktuple13__item___4@tok () Term)

; </end encoding FStar.Pervasives.Native.__proj__Mktuple13__item___4>


; <Skipped FStar.Pervasives.Native.__proj__Mktuple13__item___4/>


; <Start encoding FStar.Pervasives.Native.__proj__Mktuple13__item___5>

(declare-fun FStar.Pervasives.Native.__proj__Mktuple13__item___5 (Term Term Term Term Term Term Term Term Term Term Term Term Term Term) Term)
(declare-fun Tm_arrow_211e172b7220adc186d8a02ff17e8780 () Term)
(declare-fun FStar.Pervasives.Native.__proj__Mktuple13__item___5@tok () Term)

; </end encoding FStar.Pervasives.Native.__proj__Mktuple13__item___5>


; <Skipped FStar.Pervasives.Native.__proj__Mktuple13__item___5/>


; <Start encoding FStar.Pervasives.Native.__proj__Mktuple13__item___6>

(declare-fun FStar.Pervasives.Native.__proj__Mktuple13__item___6 (Term Term Term Term Term Term Term Term Term Term Term Term Term Term) Term)
(declare-fun Tm_arrow_9276a4f669d8497205e8d59f12da53ba () Term)
(declare-fun FStar.Pervasives.Native.__proj__Mktuple13__item___6@tok () Term)

; </end encoding FStar.Pervasives.Native.__proj__Mktuple13__item___6>


; <Skipped FStar.Pervasives.Native.__proj__Mktuple13__item___6/>


; <Start encoding FStar.Pervasives.Native.__proj__Mktuple13__item___7>

(declare-fun FStar.Pervasives.Native.__proj__Mktuple13__item___7 (Term Term Term Term Term Term Term Term Term Term Term Term Term Term) Term)
(declare-fun Tm_arrow_8aa8f381a5ed57cbbae9dcd2405ce80f () Term)
(declare-fun FStar.Pervasives.Native.__proj__Mktuple13__item___7@tok () Term)

; </end encoding FStar.Pervasives.Native.__proj__Mktuple13__item___7>


; <Skipped FStar.Pervasives.Native.__proj__Mktuple13__item___7/>


; <Start encoding FStar.Pervasives.Native.__proj__Mktuple13__item___8>

(declare-fun FStar.Pervasives.Native.__proj__Mktuple13__item___8 (Term Term Term Term Term Term Term Term Term Term Term Term Term Term) Term)
(declare-fun Tm_arrow_51814106613688cf259d7cdba9c24d93 () Term)
(declare-fun FStar.Pervasives.Native.__proj__Mktuple13__item___8@tok () Term)

; </end encoding FStar.Pervasives.Native.__proj__Mktuple13__item___8>


; <Skipped FStar.Pervasives.Native.__proj__Mktuple13__item___8/>


; <Start encoding FStar.Pervasives.Native.__proj__Mktuple13__item___9>

(declare-fun FStar.Pervasives.Native.__proj__Mktuple13__item___9 (Term Term Term Term Term Term Term Term Term Term Term Term Term Term) Term)
(declare-fun Tm_arrow_05fec25e6f03f974bb2933a910642d7e () Term)
(declare-fun FStar.Pervasives.Native.__proj__Mktuple13__item___9@tok () Term)

; </end encoding FStar.Pervasives.Native.__proj__Mktuple13__item___9>


; <Skipped FStar.Pervasives.Native.__proj__Mktuple13__item___9/>


; <Start encoding FStar.Pervasives.Native.__proj__Mktuple13__item___10>

(declare-fun FStar.Pervasives.Native.__proj__Mktuple13__item___10 (Term Term Term Term Term Term Term Term Term Term Term Term Term Term) Term)
(declare-fun Tm_arrow_3280ee04611a7985c9d107bb1a8a330a () Term)
(declare-fun FStar.Pervasives.Native.__proj__Mktuple13__item___10@tok () Term)

; </end encoding FStar.Pervasives.Native.__proj__Mktuple13__item___10>


; <Skipped FStar.Pervasives.Native.__proj__Mktuple13__item___10/>


; <Start encoding FStar.Pervasives.Native.__proj__Mktuple13__item___11>

(declare-fun FStar.Pervasives.Native.__proj__Mktuple13__item___11 (Term Term Term Term Term Term Term Term Term Term Term Term Term Term) Term)
(declare-fun Tm_arrow_86c868d5d5058e8e5ec1f4d0285c7e90 () Term)
(declare-fun FStar.Pervasives.Native.__proj__Mktuple13__item___11@tok () Term)

; </end encoding FStar.Pervasives.Native.__proj__Mktuple13__item___11>


; <Skipped FStar.Pervasives.Native.__proj__Mktuple13__item___11/>


; <Start encoding FStar.Pervasives.Native.__proj__Mktuple13__item___12>

(declare-fun FStar.Pervasives.Native.__proj__Mktuple13__item___12 (Term Term Term Term Term Term Term Term Term Term Term Term Term Term) Term)
(declare-fun Tm_arrow_7263c1a3c4475bb4e4b41a1be4bf22da () Term)
(declare-fun FStar.Pervasives.Native.__proj__Mktuple13__item___12@tok () Term)

; </end encoding FStar.Pervasives.Native.__proj__Mktuple13__item___12>


; <Skipped FStar.Pervasives.Native.__proj__Mktuple13__item___12/>


; <Start encoding FStar.Pervasives.Native.__proj__Mktuple13__item___13>

(declare-fun FStar.Pervasives.Native.__proj__Mktuple13__item___13 (Term Term Term Term Term Term Term Term Term Term Term Term Term Term) Term)
(declare-fun Tm_arrow_338c65ae58844787891c6f47cf01c068 () Term)
(declare-fun FStar.Pervasives.Native.__proj__Mktuple13__item___13@tok () Term)

; </end encoding FStar.Pervasives.Native.__proj__Mktuple13__item___13>


; <Skipped FStar.Pervasives.Native.__proj__Mktuple13__item___13/>


; <Start encoding >

;;;;;;;;;;;;;;;;Constructor
(declare-fun FStar.Pervasives.Native.tuple14 (Term Term Term Term Term Term Term Term Term Term Term Term Term Term) Term)
;;;;;;;;;;;;;;;;Projector
(declare-fun FStar.Pervasives.Native.tuple14@x0 (Term) Term)
;;;;;;;;;;;;;;;;Projector
(declare-fun FStar.Pervasives.Native.tuple14@x1 (Term) Term)
;;;;;;;;;;;;;;;;Projector
(declare-fun FStar.Pervasives.Native.tuple14@x2 (Term) Term)
;;;;;;;;;;;;;;;;Projector
(declare-fun FStar.Pervasives.Native.tuple14@x3 (Term) Term)
;;;;;;;;;;;;;;;;Projector
(declare-fun FStar.Pervasives.Native.tuple14@x4 (Term) Term)
;;;;;;;;;;;;;;;;Projector
(declare-fun FStar.Pervasives.Native.tuple14@x5 (Term) Term)
;;;;;;;;;;;;;;;;Projector
(declare-fun FStar.Pervasives.Native.tuple14@x6 (Term) Term)
;;;;;;;;;;;;;;;;Projector
(declare-fun FStar.Pervasives.Native.tuple14@x7 (Term) Term)
;;;;;;;;;;;;;;;;Projector
(declare-fun FStar.Pervasives.Native.tuple14@x8 (Term) Term)
;;;;;;;;;;;;;;;;Projector
(declare-fun FStar.Pervasives.Native.tuple14@x9 (Term) Term)
;;;;;;;;;;;;;;;;Projector
(declare-fun FStar.Pervasives.Native.tuple14@x10 (Term) Term)
;;;;;;;;;;;;;;;;Projector
(declare-fun FStar.Pervasives.Native.tuple14@x11 (Term) Term)
;;;;;;;;;;;;;;;;Projector
(declare-fun FStar.Pervasives.Native.tuple14@x12 (Term) Term)
;;;;;;;;;;;;;;;;Projector
(declare-fun FStar.Pervasives.Native.tuple14@x13 (Term) Term)
;;;;;;;;;;;;;;;;token
(declare-fun FStar.Pervasives.Native.tuple14@tok () Term)
;;;;;;;;;;;;;;;;Constructor
(declare-fun FStar.Pervasives.Native.Mktuple14 (Term Term Term Term Term Term Term Term Term Term Term Term Term Term Term Term Term Term Term Term Term Term Term Term Term Term Term Term) Term)
;;;;;;;;;;;;;;;;Projector
(declare-fun FStar.Pervasives.Native.Mktuple14__a (Term) Term)
;;;;;;;;;;;;;;;;Projector
(declare-fun FStar.Pervasives.Native.Mktuple14__b (Term) Term)
;;;;;;;;;;;;;;;;Projector
(declare-fun FStar.Pervasives.Native.Mktuple14__c (Term) Term)
;;;;;;;;;;;;;;;;Projector
(declare-fun FStar.Pervasives.Native.Mktuple14__d (Term) Term)
;;;;;;;;;;;;;;;;Projector
(declare-fun FStar.Pervasives.Native.Mktuple14__e (Term) Term)
;;;;;;;;;;;;;;;;Projector
(declare-fun FStar.Pervasives.Native.Mktuple14__f (Term) Term)
;;;;;;;;;;;;;;;;Projector
(declare-fun FStar.Pervasives.Native.Mktuple14__g (Term) Term)
;;;;;;;;;;;;;;;;Projector
(declare-fun FStar.Pervasives.Native.Mktuple14__h (Term) Term)
;;;;;;;;;;;;;;;;Projector
(declare-fun FStar.Pervasives.Native.Mktuple14__i (Term) Term)
;;;;;;;;;;;;;;;;Projector
(declare-fun FStar.Pervasives.Native.Mktuple14__j (Term) Term)
;;;;;;;;;;;;;;;;Projector
(declare-fun FStar.Pervasives.Native.Mktuple14__k (Term) Term)
;;;;;;;;;;;;;;;;Projector
(declare-fun FStar.Pervasives.Native.Mktuple14__l (Term) Term)
;;;;;;;;;;;;;;;;Projector
(declare-fun FStar.Pervasives.Native.Mktuple14__m (Term) Term)
;;;;;;;;;;;;;;;;Projector
(declare-fun FStar.Pervasives.Native.Mktuple14__n (Term) Term)
;;;;;;;;;;;;;;;;Projector
(declare-fun FStar.Pervasives.Native.Mktuple14__1 (Term) Term)
;;;;;;;;;;;;;;;;Projector
(declare-fun FStar.Pervasives.Native.Mktuple14__2 (Term) Term)
;;;;;;;;;;;;;;;;Projector
(declare-fun FStar.Pervasives.Native.Mktuple14__3 (Term) Term)
;;;;;;;;;;;;;;;;Projector
(declare-fun FStar.Pervasives.Native.Mktuple14__4 (Term) Term)
;;;;;;;;;;;;;;;;Projector
(declare-fun FStar.Pervasives.Native.Mktuple14__5 (Term) Term)
;;;;;;;;;;;;;;;;Projector
(declare-fun FStar.Pervasives.Native.Mktuple14__6 (Term) Term)
;;;;;;;;;;;;;;;;Projector
(declare-fun FStar.Pervasives.Native.Mktuple14__7 (Term) Term)
;;;;;;;;;;;;;;;;Projector
(declare-fun FStar.Pervasives.Native.Mktuple14__8 (Term) Term)
;;;;;;;;;;;;;;;;Projector
(declare-fun FStar.Pervasives.Native.Mktuple14__9 (Term) Term)
;;;;;;;;;;;;;;;;Projector
(declare-fun FStar.Pervasives.Native.Mktuple14__10 (Term) Term)
;;;;;;;;;;;;;;;;Projector
(declare-fun FStar.Pervasives.Native.Mktuple14__11 (Term) Term)
;;;;;;;;;;;;;;;;Projector
(declare-fun FStar.Pervasives.Native.Mktuple14__12 (Term) Term)
;;;;;;;;;;;;;;;;Projector
(declare-fun FStar.Pervasives.Native.Mktuple14__13 (Term) Term)
;;;;;;;;;;;;;;;;Projector
(declare-fun FStar.Pervasives.Native.Mktuple14__14 (Term) Term)
;;;;;;;;;;;;;;;;data constructor proxy: Mktuple14
(declare-fun FStar.Pervasives.Native.Mktuple14@tok () Term)
(declare-fun Tm_arrow_484e3bf88a886900f7e695d7333615e9 () Term)

; <Start encoding FStar.Pervasives.Native.tuple14>


; <start constructor FStar.Pervasives.Native.tuple14>

;;;;;;;;;;;;;;;;Discriminator definition
(define-fun is-FStar.Pervasives.Native.tuple14 ((__@x0 Term)) Bool
 (and (= (Term_constr_id __@x0)
465)
(exists ((@x0 Term) (@x1 Term) (@x2 Term) (@x3 Term) (@x4 Term) (@x5 Term) (@x6 Term) (@x7 Term) (@x8 Term) (@x9 Term) (@x10 Term) (@x11 Term) (@x12 Term) (@x13 Term))
 (! (= __@x0
(FStar.Pervasives.Native.tuple14 @x0
@x1
@x2
@x3
@x4
@x5
@x6
@x7
@x8
@x9
@x10
@x11
@x12
@x13))
 
;;no pats
:qid is-FStar.Pervasives.Native.tuple14))))

; </end constructor FStar.Pervasives.Native.tuple14>


; </end encoding FStar.Pervasives.Native.tuple14>


; <Start encoding FStar.Pervasives.Native.Mktuple14>


; <start constructor FStar.Pervasives.Native.Mktuple14>

;;;;;;;;;;;;;;;;Discriminator definition
(define-fun is-FStar.Pervasives.Native.Mktuple14 ((__@x0 Term)) Bool
 (and (= (Term_constr_id __@x0)
472)
(= __@x0
(FStar.Pervasives.Native.Mktuple14 (FStar.Pervasives.Native.Mktuple14__a __@x0)
(FStar.Pervasives.Native.Mktuple14__b __@x0)
(FStar.Pervasives.Native.Mktuple14__c __@x0)
(FStar.Pervasives.Native.Mktuple14__d __@x0)
(FStar.Pervasives.Native.Mktuple14__e __@x0)
(FStar.Pervasives.Native.Mktuple14__f __@x0)
(FStar.Pervasives.Native.Mktuple14__g __@x0)
(FStar.Pervasives.Native.Mktuple14__h __@x0)
(FStar.Pervasives.Native.Mktuple14__i __@x0)
(FStar.Pervasives.Native.Mktuple14__j __@x0)
(FStar.Pervasives.Native.Mktuple14__k __@x0)
(FStar.Pervasives.Native.Mktuple14__l __@x0)
(FStar.Pervasives.Native.Mktuple14__m __@x0)
(FStar.Pervasives.Native.Mktuple14__n __@x0)
(FStar.Pervasives.Native.Mktuple14__1 __@x0)
(FStar.Pervasives.Native.Mktuple14__2 __@x0)
(FStar.Pervasives.Native.Mktuple14__3 __@x0)
(FStar.Pervasives.Native.Mktuple14__4 __@x0)
(FStar.Pervasives.Native.Mktuple14__5 __@x0)
(FStar.Pervasives.Native.Mktuple14__6 __@x0)
(FStar.Pervasives.Native.Mktuple14__7 __@x0)
(FStar.Pervasives.Native.Mktuple14__8 __@x0)
(FStar.Pervasives.Native.Mktuple14__9 __@x0)
(FStar.Pervasives.Native.Mktuple14__10 __@x0)
(FStar.Pervasives.Native.Mktuple14__11 __@x0)
(FStar.Pervasives.Native.Mktuple14__12 __@x0)
(FStar.Pervasives.Native.Mktuple14__13 __@x0)
(FStar.Pervasives.Native.Mktuple14__14 __@x0)))))

; </end constructor FStar.Pervasives.Native.Mktuple14>


; </end encoding FStar.Pervasives.Native.Mktuple14>


; </end encoding >


; <Start encoding FStar.Pervasives.Native.tuple14__uu___haseq>


; </end encoding FStar.Pervasives.Native.tuple14__uu___haseq>


; <Start encoding FStar.Pervasives.Native.uu___is_Mktuple14>

(declare-fun FStar.Pervasives.Native.uu___is_Mktuple14 (Term Term Term Term Term Term Term Term Term Term Term Term Term Term Term) Term)
(declare-fun Tm_arrow_2de133cfaca100fc23d8bf4b3421db9a () Term)
(declare-fun FStar.Pervasives.Native.uu___is_Mktuple14@tok () Term)

; </end encoding FStar.Pervasives.Native.uu___is_Mktuple14>


; <Skipped FStar.Pervasives.Native.uu___is_Mktuple14/>


; <Start encoding FStar.Pervasives.Native.__proj__Mktuple14__item___1>

(declare-fun FStar.Pervasives.Native.__proj__Mktuple14__item___1 (Term Term Term Term Term Term Term Term Term Term Term Term Term Term Term) Term)
(declare-fun Tm_arrow_2e3216cab266e138debd68d0a503c177 () Term)
(declare-fun FStar.Pervasives.Native.__proj__Mktuple14__item___1@tok () Term)

; </end encoding FStar.Pervasives.Native.__proj__Mktuple14__item___1>


; <Skipped FStar.Pervasives.Native.__proj__Mktuple14__item___1/>


; <Start encoding FStar.Pervasives.Native.__proj__Mktuple14__item___2>

(declare-fun FStar.Pervasives.Native.__proj__Mktuple14__item___2 (Term Term Term Term Term Term Term Term Term Term Term Term Term Term Term) Term)
(declare-fun Tm_arrow_958b0270e487d0bf5fe9191b9efaa127 () Term)
(declare-fun FStar.Pervasives.Native.__proj__Mktuple14__item___2@tok () Term)

; </end encoding FStar.Pervasives.Native.__proj__Mktuple14__item___2>


; <Skipped FStar.Pervasives.Native.__proj__Mktuple14__item___2/>


; <Start encoding FStar.Pervasives.Native.__proj__Mktuple14__item___3>

(declare-fun FStar.Pervasives.Native.__proj__Mktuple14__item___3 (Term Term Term Term Term Term Term Term Term Term Term Term Term Term Term) Term)
(declare-fun Tm_arrow_08349f596f8c0acf60d1587bebe8c91b () Term)
(declare-fun FStar.Pervasives.Native.__proj__Mktuple14__item___3@tok () Term)

; </end encoding FStar.Pervasives.Native.__proj__Mktuple14__item___3>


; <Skipped FStar.Pervasives.Native.__proj__Mktuple14__item___3/>


; <Start encoding FStar.Pervasives.Native.__proj__Mktuple14__item___4>

(declare-fun FStar.Pervasives.Native.__proj__Mktuple14__item___4 (Term Term Term Term Term Term Term Term Term Term Term Term Term Term Term) Term)
(declare-fun Tm_arrow_2b069168147ba0f67f117ad5b0ac078b () Term)
(declare-fun FStar.Pervasives.Native.__proj__Mktuple14__item___4@tok () Term)

; </end encoding FStar.Pervasives.Native.__proj__Mktuple14__item___4>


; <Skipped FStar.Pervasives.Native.__proj__Mktuple14__item___4/>


; <Start encoding FStar.Pervasives.Native.__proj__Mktuple14__item___5>

(declare-fun FStar.Pervasives.Native.__proj__Mktuple14__item___5 (Term Term Term Term Term Term Term Term Term Term Term Term Term Term Term) Term)
(declare-fun Tm_arrow_1e38bb16245a24a197c44a262fee7bf1 () Term)
(declare-fun FStar.Pervasives.Native.__proj__Mktuple14__item___5@tok () Term)

; </end encoding FStar.Pervasives.Native.__proj__Mktuple14__item___5>


; <Skipped FStar.Pervasives.Native.__proj__Mktuple14__item___5/>


; <Start encoding FStar.Pervasives.Native.__proj__Mktuple14__item___6>

(declare-fun FStar.Pervasives.Native.__proj__Mktuple14__item___6 (Term Term Term Term Term Term Term Term Term Term Term Term Term Term Term) Term)
(declare-fun Tm_arrow_7a148953a3884454d8a1dffddce086bb () Term)
(declare-fun FStar.Pervasives.Native.__proj__Mktuple14__item___6@tok () Term)

; </end encoding FStar.Pervasives.Native.__proj__Mktuple14__item___6>


; <Skipped FStar.Pervasives.Native.__proj__Mktuple14__item___6/>


; <Start encoding FStar.Pervasives.Native.__proj__Mktuple14__item___7>

(declare-fun FStar.Pervasives.Native.__proj__Mktuple14__item___7 (Term Term Term Term Term Term Term Term Term Term Term Term Term Term Term) Term)
(declare-fun Tm_arrow_812eeb3fdab56dfea8e419236740acb0 () Term)
(declare-fun FStar.Pervasives.Native.__proj__Mktuple14__item___7@tok () Term)

; </end encoding FStar.Pervasives.Native.__proj__Mktuple14__item___7>


; <Skipped FStar.Pervasives.Native.__proj__Mktuple14__item___7/>


; <Start encoding FStar.Pervasives.Native.__proj__Mktuple14__item___8>

(declare-fun FStar.Pervasives.Native.__proj__Mktuple14__item___8 (Term Term Term Term Term Term Term Term Term Term Term Term Term Term Term) Term)
(declare-fun Tm_arrow_9dc932ce7cdfd6fa57f6536787fcb65b () Term)
(declare-fun FStar.Pervasives.Native.__proj__Mktuple14__item___8@tok () Term)

; </end encoding FStar.Pervasives.Native.__proj__Mktuple14__item___8>


; <Skipped FStar.Pervasives.Native.__proj__Mktuple14__item___8/>


; <Start encoding FStar.Pervasives.Native.__proj__Mktuple14__item___9>

(declare-fun FStar.Pervasives.Native.__proj__Mktuple14__item___9 (Term Term Term Term Term Term Term Term Term Term Term Term Term Term Term) Term)
(declare-fun Tm_arrow_2600722933f06bc55e28bb3fc2ce4a6a () Term)
(declare-fun FStar.Pervasives.Native.__proj__Mktuple14__item___9@tok () Term)

; </end encoding FStar.Pervasives.Native.__proj__Mktuple14__item___9>


; <Skipped FStar.Pervasives.Native.__proj__Mktuple14__item___9/>


; <Start encoding FStar.Pervasives.Native.__proj__Mktuple14__item___10>

(declare-fun FStar.Pervasives.Native.__proj__Mktuple14__item___10 (Term Term Term Term Term Term Term Term Term Term Term Term Term Term Term) Term)
(declare-fun Tm_arrow_f51203e57fd66f9e9293b8962c57edfe () Term)
(declare-fun FStar.Pervasives.Native.__proj__Mktuple14__item___10@tok () Term)

; </end encoding FStar.Pervasives.Native.__proj__Mktuple14__item___10>


; <Skipped FStar.Pervasives.Native.__proj__Mktuple14__item___10/>


; <Start encoding FStar.Pervasives.Native.__proj__Mktuple14__item___11>

(declare-fun FStar.Pervasives.Native.__proj__Mktuple14__item___11 (Term Term Term Term Term Term Term Term Term Term Term Term Term Term Term) Term)
(declare-fun Tm_arrow_7c34e0c28edc5fc4ad24d0b749c0adb7 () Term)
(declare-fun FStar.Pervasives.Native.__proj__Mktuple14__item___11@tok () Term)

; </end encoding FStar.Pervasives.Native.__proj__Mktuple14__item___11>


; <Skipped FStar.Pervasives.Native.__proj__Mktuple14__item___11/>


; <Start encoding FStar.Pervasives.Native.__proj__Mktuple14__item___12>

(declare-fun FStar.Pervasives.Native.__proj__Mktuple14__item___12 (Term Term Term Term Term Term Term Term Term Term Term Term Term Term Term) Term)
(declare-fun Tm_arrow_8772cc50ea320af17b3f2371c273679a () Term)
(declare-fun FStar.Pervasives.Native.__proj__Mktuple14__item___12@tok () Term)

; </end encoding FStar.Pervasives.Native.__proj__Mktuple14__item___12>


; <Skipped FStar.Pervasives.Native.__proj__Mktuple14__item___12/>


; <Start encoding FStar.Pervasives.Native.__proj__Mktuple14__item___13>

(declare-fun FStar.Pervasives.Native.__proj__Mktuple14__item___13 (Term Term Term Term Term Term Term Term Term Term Term Term Term Term Term) Term)
(declare-fun Tm_arrow_039da0b9a8da1a651a1c570e55456614 () Term)
(declare-fun FStar.Pervasives.Native.__proj__Mktuple14__item___13@tok () Term)

; </end encoding FStar.Pervasives.Native.__proj__Mktuple14__item___13>


; <Skipped FStar.Pervasives.Native.__proj__Mktuple14__item___13/>


; <Start encoding FStar.Pervasives.Native.__proj__Mktuple14__item___14>

(declare-fun FStar.Pervasives.Native.__proj__Mktuple14__item___14 (Term Term Term Term Term Term Term Term Term Term Term Term Term Term Term) Term)
(declare-fun Tm_arrow_579ada2eb036c15c7306dac5b648153e () Term)
(declare-fun FStar.Pervasives.Native.__proj__Mktuple14__item___14@tok () Term)

; </end encoding FStar.Pervasives.Native.__proj__Mktuple14__item___14>


; <Skipped FStar.Pervasives.Native.__proj__Mktuple14__item___14/>


; UNSAT CORE: @MaxFuel_assumption, @MaxIFuel_assumption, @fuel_correspondence_Prims.pow2.fuel_instrumented, @query, constructor_distinct_Lib.IntTypes.S16, constructor_distinct_Lib.IntTypes.S32, constructor_distinct_Lib.IntTypes.SEC, equality_tok_Lib.IntTypes.S16@tok, equality_tok_Lib.IntTypes.S32@tok, equality_tok_Lib.IntTypes.SEC@tok, equation_Lib.IntTypes.bits, equation_Lib.IntTypes.range, equation_Lib.IntTypes.signed, equation_Lib.IntTypes.unsigned, equation_Lib.IntTypes.v, equation_Prims.nat, equation_Prims.pos, equation_Spec.Kyber2.Params.params_q, int_inversion, int_typing, lemma_FStar.UInt.pow2_values, primitive_Prims.op_Addition, primitive_Prims.op_Division, primitive_Prims.op_LessThanOrEqual, primitive_Prims.op_Minus, primitive_Prims.op_Multiply, primitive_Prims.op_Subtraction, projection_inverse_BoxBool_proj_0, projection_inverse_BoxInt_proj_0, refinement_interpretation_Tm_refine_2b320913041b873fce938dd17eebb3e2, refinement_interpretation_Tm_refine_542f9d4f129664613f2483a6c88bc7c2, refinement_interpretation_Tm_refine_774ba3f728d91ead8ef40be66c9802e5, refinement_interpretation_Tm_refine_83845a86f2550cdf941eeb1d9b59602b, refinement_interpretation_Tm_refine_9d3fd79fd314167f1a9c213a188da3ec, refinement_interpretation_Tm_refine_b2401a8cabe2f9a01538f32548fa9f6c, typing_Lib.IntTypes.mk_int, typing_Prims.pow2, typing_tok_Lib.IntTypes.S32@tok, typing_tok_Lib.IntTypes.SEC@tok

;;; End module FStar.Pervasives.Native (1323 decls; total size 119827)

;;; Start module FStar.Pervasives

; <Start encoding FStar.Pervasives.ambient>

(declare-fun FStar.Pervasives.ambient (Term Term) Term)
(declare-fun Tm_arrow_738454506bffd78401f680aeced784fe () Term)
(declare-fun FStar.Pervasives.ambient@tok () Term)

; </end encoding FStar.Pervasives.ambient>


; <Start encoding FStar.Pervasives.intro_ambient>

(declare-fun FStar.Pervasives.intro_ambient (Term Term) Term)
(declare-fun Tm_arrow_6fc6334d56387f3d408122a4bd045e7e () Term)
(declare-fun FStar.Pervasives.intro_ambient@tok () Term)

; </end encoding FStar.Pervasives.intro_ambient>


; <Start encoding FStar.Pervasives.id>

(declare-fun FStar.Pervasives.id (Term Term) Term)

(declare-fun FStar.Pervasives.id@tok () Term)

; </end encoding FStar.Pervasives.id>


; <Skipped FStar.Pervasives.DIV/>


; <Skipped />


; <Skipped FStar.Pervasives.Div/>


; <Skipped FStar.Pervasives.Dv/>


; <Skipped FStar.Pervasives.EXT/>


; <Start encoding FStar.Pervasives.st_pre_h>

(declare-fun FStar.Pervasives.st_pre_h (Term) Term)

(declare-fun FStar.Pervasives.st_pre_h@tok () Term)


; </end encoding FStar.Pervasives.st_pre_h>


; <Start encoding FStar.Pervasives.st_post_h'>

(declare-fun FStar.Pervasives.st_post_h_ (Term Term Term) Term)
(declare-fun Tm_arrow_659175ed40df3b798f91ffaee9e689bd () Term)
(declare-fun FStar.Pervasives.st_post_h_@tok () Term)

(declare-fun Tm_arrow_14435f7112db17792f8cd33f8f7ea859 (Term Term Term) Term)

; </end encoding FStar.Pervasives.st_post_h'>


; <Start encoding FStar.Pervasives.st_post_h>

(declare-fun FStar.Pervasives.st_post_h (Term Term) Term)

(declare-fun FStar.Pervasives.st_post_h@tok () Term)

; </end encoding FStar.Pervasives.st_post_h>


; <Start encoding FStar.Pervasives.st_wp_h>

(declare-fun FStar.Pervasives.st_wp_h (Term Term) Term)

(declare-fun FStar.Pervasives.st_wp_h@tok () Term)
(declare-fun Tm_arrow_c80b139653078194d2de90941effdc68 (Term Term) Term)

; </end encoding FStar.Pervasives.st_wp_h>


; <Start encoding FStar.Pervasives.st_return>

(declare-fun FStar.Pervasives.st_return (Term Term Term Term) Term)

(declare-fun Tm_arrow_6bfe4bf6faf1fb53a521d575cefc35ef () Term)
(declare-fun FStar.Pervasives.st_return@tok () Term)


; </end encoding FStar.Pervasives.st_return>


; <Start encoding FStar.Pervasives.st_bind_wp>

(declare-fun Tm_arrow_c6e0af8c2ccbdda79db5c09d07e87e35 (Term Term Term) Term)
(declare-fun FStar.Pervasives.st_bind_wp (Term Term Term Term Term Term Term Term) Term)

(declare-fun Tm_arrow_f06c598be842ca5b0249b52c3e190418 () Term)
(declare-fun FStar.Pervasives.st_bind_wp@tok () Term)

(declare-fun Tm_arrow_eb9b1a038524b37579c152a3f169145e (Term Term) Term)
(declare-fun Tm_abs_0f3b5ee9eaa8de8cacad7d3dcacb4558 (Term Term Term Term) Term)

; </end encoding FStar.Pervasives.st_bind_wp>


; <Start encoding FStar.Pervasives.st_if_then_else>

(declare-fun FStar.Pervasives.st_if_then_else (Term Term Term Term Term Term Term) Term)
(declare-fun Tm_arrow_6e48361e1a1c92df6ec1ff87e622ddad () Term)
(declare-fun FStar.Pervasives.st_if_then_else@tok () Term)

; </end encoding FStar.Pervasives.st_if_then_else>


; <Start encoding FStar.Pervasives.st_ite_wp>

(declare-fun FStar.Pervasives.st_ite_wp (Term Term Term Term Term) Term)
(declare-fun Tm_arrow_eaad896c6afdcb7ade2e80b5a6a930af () Term)
(declare-fun FStar.Pervasives.st_ite_wp@tok () Term)

; </end encoding FStar.Pervasives.st_ite_wp>


; <Start encoding FStar.Pervasives.st_stronger>

(declare-fun FStar.Pervasives.st_stronger (Term Term Term Term) Term)
(declare-fun Tm_arrow_ae4d7f489de84317e0022bf89d45dd95 () Term)
(declare-fun FStar.Pervasives.st_stronger@tok () Term)

; </end encoding FStar.Pervasives.st_stronger>


; <Start encoding FStar.Pervasives.st_close_wp>


(declare-fun FStar.Pervasives.st_close_wp (Term Term Term Term Term Term) Term)

(declare-fun Tm_arrow_de6d3045642382698e9e38d41acfd7cc () Term)
(declare-fun FStar.Pervasives.st_close_wp@tok () Term)


; </end encoding FStar.Pervasives.st_close_wp>


; <Start encoding FStar.Pervasives.st_assert_p>

(declare-fun FStar.Pervasives.st_assert_p (Term Term Term Term Term Term) Term)
(declare-fun Tm_arrow_69b748426aca76f96daf02179d99f50c () Term)
(declare-fun FStar.Pervasives.st_assert_p@tok () Term)

; </end encoding FStar.Pervasives.st_assert_p>


; <Start encoding FStar.Pervasives.st_assume_p>

(declare-fun FStar.Pervasives.st_assume_p (Term Term Term Term Term Term) Term)

(declare-fun FStar.Pervasives.st_assume_p@tok () Term)

; </end encoding FStar.Pervasives.st_assume_p>


; <Start encoding FStar.Pervasives.st_null_wp>

(declare-fun FStar.Pervasives.st_null_wp (Term Term Term Term) Term)
(declare-fun Tm_arrow_7d221e455210f4f11c5c9061856311bc () Term)
(declare-fun FStar.Pervasives.st_null_wp@tok () Term)

; </end encoding FStar.Pervasives.st_null_wp>


; <Start encoding FStar.Pervasives.st_trivial>

(declare-fun FStar.Pervasives.st_trivial (Term Term Term) Term)
(declare-fun Tm_arrow_f145e04ff3c7033bdfc718f7f5bb1df0 () Term)
(declare-fun FStar.Pervasives.st_trivial@tok () Term)

(declare-fun Tm_abs_89b21c42be5bc00d63e29f63ae20d4e2 (Term Term) Term)

; </end encoding FStar.Pervasives.st_trivial>


; <Skipped FStar.Pervasives.STATE_h/>


; <Start encoding >

;;;;;;;;;;;;;;;;Constructor
(declare-fun FStar.Pervasives.result (Term) Term)
;;;;;;;;;;;;;;;;Projector
(declare-fun FStar.Pervasives.result@x0 (Term) Term)
;;;;;;;;;;;;;;;;token
(declare-fun FStar.Pervasives.result@tok () Term)
;;;;;;;;;;;;;;;;Constructor
(declare-fun FStar.Pervasives.V (Term Term) Term)
;;;;;;;;;;;;;;;;Projector
(declare-fun FStar.Pervasives.V_a (Term) Term)
;;;;;;;;;;;;;;;;Projector
(declare-fun FStar.Pervasives.V_v (Term) Term)
;;;;;;;;;;;;;;;;data constructor proxy: V
(declare-fun FStar.Pervasives.V@tok () Term)
;;;;;;;;;;;;;;;;Constructor
(declare-fun FStar.Pervasives.E (Term Term) Term)
;;;;;;;;;;;;;;;;Projector
(declare-fun FStar.Pervasives.E_a (Term) Term)
;;;;;;;;;;;;;;;;Projector
(declare-fun FStar.Pervasives.E_e (Term) Term)
;;;;;;;;;;;;;;;;data constructor proxy: E
(declare-fun FStar.Pervasives.E@tok () Term)
;;;;;;;;;;;;;;;;Constructor
(declare-fun FStar.Pervasives.Err (Term Term) Term)
;;;;;;;;;;;;;;;;Projector
(declare-fun FStar.Pervasives.Err_a (Term) Term)
;;;;;;;;;;;;;;;;Projector
(declare-fun FStar.Pervasives.Err_msg (Term) Term)
;;;;;;;;;;;;;;;;data constructor proxy: Err
(declare-fun FStar.Pervasives.Err@tok () Term)
(declare-fun Tm_arrow_30908143640041985b9200e2fb38a259 () Term)
(declare-fun Tm_arrow_f8bb10130fea772e0f786d78a188c381 () Term)
(declare-fun Tm_arrow_93661c87034b0b64c4714dafbe2b02e6 () Term)

; <Start encoding FStar.Pervasives.result>


; <start constructor FStar.Pervasives.result>

;;;;;;;;;;;;;;;;Discriminator definition
(define-fun is-FStar.Pervasives.result ((__@x0 Term)) Bool
 (and (= (Term_constr_id __@x0)
162)
(exists ((@x0 Term))
 (! (= __@x0
(FStar.Pervasives.result @x0))
 
;;no pats
:qid is-FStar.Pervasives.result))))

; </end constructor FStar.Pervasives.result>


; </end encoding FStar.Pervasives.result>


; <Start encoding FStar.Pervasives.V>


; <start constructor FStar.Pervasives.V>

;;;;;;;;;;;;;;;;Discriminator definition
(define-fun is-FStar.Pervasives.V ((__@x0 Term)) Bool
 (and (= (Term_constr_id __@x0)
169)
(= __@x0
(FStar.Pervasives.V (FStar.Pervasives.V_a __@x0)
(FStar.Pervasives.V_v __@x0)))))

; </end constructor FStar.Pervasives.V>


; </end encoding FStar.Pervasives.V>


; <Start encoding FStar.Pervasives.E>


; <start constructor FStar.Pervasives.E>

;;;;;;;;;;;;;;;;Discriminator definition
(define-fun is-FStar.Pervasives.E ((__@x0 Term)) Bool
 (and (= (Term_constr_id __@x0)
174)
(= __@x0
(FStar.Pervasives.E (FStar.Pervasives.E_a __@x0)
(FStar.Pervasives.E_e __@x0)))))

; </end constructor FStar.Pervasives.E>


; </end encoding FStar.Pervasives.E>


; <Start encoding FStar.Pervasives.Err>


; <start constructor FStar.Pervasives.Err>

;;;;;;;;;;;;;;;;Discriminator definition
(define-fun is-FStar.Pervasives.Err ((__@x0 Term)) Bool
 (and (= (Term_constr_id __@x0)
179)
(= __@x0
(FStar.Pervasives.Err (FStar.Pervasives.Err_a __@x0)
(FStar.Pervasives.Err_msg __@x0)))))

; </end constructor FStar.Pervasives.Err>


; </end encoding FStar.Pervasives.Err>


; </end encoding >


; <Start encoding FStar.Pervasives.uu___is_V>

(declare-fun FStar.Pervasives.uu___is_V (Term Term) Term)
(declare-fun Tm_arrow_5cd1d0722a6a986faf6f8e557186fe24 () Term)
(declare-fun FStar.Pervasives.uu___is_V@tok () Term)

; </end encoding FStar.Pervasives.uu___is_V>


; <Skipped FStar.Pervasives.uu___is_V/>


; <Start encoding FStar.Pervasives.__proj__V__item__v>

(declare-fun Tm_refine_9db520b26a7f39c5a01493a3f375290d (Term) Term)
(declare-fun FStar.Pervasives.__proj__V__item__v (Term Term) Term)

(declare-fun Tm_arrow_1ea119bf213c016916a7095486e28467 () Term)
(declare-fun FStar.Pervasives.__proj__V__item__v@tok () Term)

; </end encoding FStar.Pervasives.__proj__V__item__v>


; <Skipped FStar.Pervasives.__proj__V__item__v/>


; <Start encoding FStar.Pervasives.uu___is_E>

(declare-fun FStar.Pervasives.uu___is_E (Term Term) Term)

(declare-fun FStar.Pervasives.uu___is_E@tok () Term)

; </end encoding FStar.Pervasives.uu___is_E>


; <Skipped FStar.Pervasives.uu___is_E/>


; <Start encoding FStar.Pervasives.__proj__E__item__e>

(declare-fun Tm_refine_95e1e2ee29104754cc3740f5575fc6e5 (Term) Term)
(declare-fun FStar.Pervasives.__proj__E__item__e (Term Term) Term)

(declare-fun Tm_arrow_19e73c373dbf3f9945c6fcfce8a07661 () Term)
(declare-fun FStar.Pervasives.__proj__E__item__e@tok () Term)

; </end encoding FStar.Pervasives.__proj__E__item__e>


; <Skipped FStar.Pervasives.__proj__E__item__e/>


; <Start encoding FStar.Pervasives.uu___is_Err>

(declare-fun FStar.Pervasives.uu___is_Err (Term Term) Term)

(declare-fun FStar.Pervasives.uu___is_Err@tok () Term)

; </end encoding FStar.Pervasives.uu___is_Err>


; <Skipped FStar.Pervasives.uu___is_Err/>


; <Start encoding FStar.Pervasives.__proj__Err__item__msg>

(declare-fun Tm_refine_22fb403854eba07427f92e79848f9d9f (Term) Term)
(declare-fun FStar.Pervasives.__proj__Err__item__msg (Term Term) Term)

(declare-fun Tm_arrow_f7e3debb858e412c9497460c5187d5cd () Term)
(declare-fun FStar.Pervasives.__proj__Err__item__msg@tok () Term)

; </end encoding FStar.Pervasives.__proj__Err__item__msg>


; <Skipped FStar.Pervasives.__proj__Err__item__msg/>


; <Start encoding FStar.Pervasives.ex_pre>

(declare-fun FStar.Pervasives.ex_pre () Term)

; </end encoding FStar.Pervasives.ex_pre>


; <Start encoding FStar.Pervasives.ex_post'>

(declare-fun FStar.Pervasives.ex_post_ (Term Term) Term)

(declare-fun FStar.Pervasives.ex_post_@tok () Term)
(declare-fun Tm_refine_a4dcdeeacbcb04d05a6720f786918fd6 (Term Term) Term)
(declare-fun Tm_arrow_68b66d987e8a7bdf825af8b370553e65 (Term Term) Term)

; </end encoding FStar.Pervasives.ex_post'>


; <Start encoding FStar.Pervasives.ex_post>

(declare-fun FStar.Pervasives.ex_post (Term) Term)

(declare-fun FStar.Pervasives.ex_post@tok () Term)

; </end encoding FStar.Pervasives.ex_post>


; <Start encoding FStar.Pervasives.ex_wp>

(declare-fun FStar.Pervasives.ex_wp (Term) Term)

(declare-fun FStar.Pervasives.ex_wp@tok () Term)
(declare-fun Tm_arrow_58168e52ae0908fefec42cac825ecc69 (Term) Term)

; </end encoding FStar.Pervasives.ex_wp>


; <Start encoding FStar.Pervasives.ex_return>

(declare-fun FStar.Pervasives.ex_return (Term Term Term) Term)
(declare-fun Tm_arrow_375264f6f19b4e37d33ffba9f6b1c7d2 () Term)
(declare-fun FStar.Pervasives.ex_return@tok () Term)

; </end encoding FStar.Pervasives.ex_return>


; <Start encoding FStar.Pervasives.ex_bind_wp>

(declare-fun Tm_arrow_3eb2992a529511f5b0ff2fef4e4594ad (Term Term) Term)
(declare-fun FStar.Pervasives.ex_bind_wp (Term Term Term Term Term Term) Term)

(declare-fun Tm_arrow_627f53cf48815f6216201f0583636724 () Term)
(declare-fun FStar.Pervasives.ex_bind_wp@tok () Term)

(declare-fun Tm_arrow_ca5db633696caf7e0cd44c11654eed8b (Term) Term)
(declare-fun Tm_abs_c1d9037a5cc10cc07ba9b6a7a58728db (Term Term Term Term) Term)

; </end encoding FStar.Pervasives.ex_bind_wp>


; <Start encoding FStar.Pervasives.ex_ite_wp>

(declare-fun FStar.Pervasives.ex_ite_wp (Term Term Term) Term)
(declare-fun Tm_arrow_c2a8c761b16a75376b24262cd8c50369 () Term)
(declare-fun FStar.Pervasives.ex_ite_wp@tok () Term)

; </end encoding FStar.Pervasives.ex_ite_wp>


; <Start encoding FStar.Pervasives.ex_if_then_else>

(declare-fun FStar.Pervasives.ex_if_then_else (Term Term Term Term Term) Term)
(declare-fun Tm_arrow_08bd7ce530cc6e8b4a3f8dadbd0806b0 () Term)
(declare-fun FStar.Pervasives.ex_if_then_else@tok () Term)

; </end encoding FStar.Pervasives.ex_if_then_else>


; <Start encoding FStar.Pervasives.ex_stronger>

(declare-fun FStar.Pervasives.ex_stronger (Term Term Term) Term)
(declare-fun Tm_arrow_1376d97b5d43e7d77d56729e2a3e04af () Term)
(declare-fun FStar.Pervasives.ex_stronger@tok () Term)

; </end encoding FStar.Pervasives.ex_stronger>


; <Start encoding FStar.Pervasives.ex_close_wp>


(declare-fun FStar.Pervasives.ex_close_wp (Term Term Term Term) Term)

(declare-fun Tm_arrow_814af0adff92aa08c5b8b0951bcb1959 () Term)
(declare-fun FStar.Pervasives.ex_close_wp@tok () Term)


; </end encoding FStar.Pervasives.ex_close_wp>


; <Start encoding FStar.Pervasives.ex_assert_p>

(declare-fun FStar.Pervasives.ex_assert_p (Term Term Term Term) Term)
(declare-fun Tm_arrow_4d1c92046405bea452a54e6fbbd0e897 () Term)
(declare-fun FStar.Pervasives.ex_assert_p@tok () Term)

; </end encoding FStar.Pervasives.ex_assert_p>


; <Start encoding FStar.Pervasives.ex_assume_p>

(declare-fun FStar.Pervasives.ex_assume_p (Term Term Term Term) Term)

(declare-fun FStar.Pervasives.ex_assume_p@tok () Term)

; </end encoding FStar.Pervasives.ex_assume_p>


; <Start encoding FStar.Pervasives.ex_null_wp>

(declare-fun FStar.Pervasives.ex_null_wp (Term Term) Term)
(declare-fun Tm_arrow_47cf1b178f571aeab56169fc4e5ebcd5 () Term)
(declare-fun FStar.Pervasives.ex_null_wp@tok () Term)

; </end encoding FStar.Pervasives.ex_null_wp>


; <Start encoding FStar.Pervasives.ex_trivial>

(declare-fun FStar.Pervasives.ex_trivial (Term Term) Term)
(declare-fun Tm_arrow_ee4a787765920b0cb4357a47a0d3ac5c () Term)
(declare-fun FStar.Pervasives.ex_trivial@tok () Term)

(declare-fun Tm_abs_5cc223716d095f4545f0dcc745acad5d (Term) Term)

; </end encoding FStar.Pervasives.ex_trivial>


; <Skipped FStar.Pervasives.EXN/>


; <Skipped FStar.Pervasives.Exn/>


; <Start encoding FStar.Pervasives.lift_div_exn>

(declare-fun FStar.Pervasives.lift_div_exn (Term Term Term) Term)
(declare-fun Tm_arrow_8196682216f286f6fe3a7dffb3de7d02 () Term)
(declare-fun FStar.Pervasives.lift_div_exn@tok () Term)

(declare-fun Tm_abs_c2b605ddd5d1991642baf5762d2b1dc5 (Term Term) Term)

; </end encoding FStar.Pervasives.lift_div_exn>


; <Skipped />


; <Skipped FStar.Pervasives.Ex/>


; <Start encoding FStar.Pervasives.all_pre_h>

(declare-fun FStar.Pervasives.all_pre_h (Term) Term)

(declare-fun FStar.Pervasives.all_pre_h@tok () Term)


; </end encoding FStar.Pervasives.all_pre_h>


; <Start encoding FStar.Pervasives.all_post_h'>

(declare-fun FStar.Pervasives.all_post_h_ (Term Term Term) Term)

(declare-fun FStar.Pervasives.all_post_h_@tok () Term)

(declare-fun Tm_arrow_fc269489cb2e24a10c7710a1f7f9d269 (Term Term Term) Term)

; </end encoding FStar.Pervasives.all_post_h'>


; <Start encoding FStar.Pervasives.all_post_h>

(declare-fun FStar.Pervasives.all_post_h (Term Term) Term)

(declare-fun FStar.Pervasives.all_post_h@tok () Term)

; </end encoding FStar.Pervasives.all_post_h>


; <Start encoding FStar.Pervasives.all_wp_h>

(declare-fun FStar.Pervasives.all_wp_h (Term Term) Term)

(declare-fun FStar.Pervasives.all_wp_h@tok () Term)
(declare-fun Tm_arrow_1cd90c71d90a216d9fb0ba0321a1d3b5 (Term Term) Term)

; </end encoding FStar.Pervasives.all_wp_h>


; <Start encoding FStar.Pervasives.all_ite_wp>

(declare-fun FStar.Pervasives.all_ite_wp (Term Term Term Term Term) Term)
(declare-fun Tm_arrow_20fdb4e6d0c32f949f55e39a059913a7 () Term)
(declare-fun FStar.Pervasives.all_ite_wp@tok () Term)

; </end encoding FStar.Pervasives.all_ite_wp>


; <Start encoding FStar.Pervasives.all_return>

(declare-fun FStar.Pervasives.all_return (Term Term Term Term) Term)

(declare-fun Tm_arrow_3f61557667800fb54cc62e48a5201f9d () Term)
(declare-fun FStar.Pervasives.all_return@tok () Term)


; </end encoding FStar.Pervasives.all_return>


; <Start encoding FStar.Pervasives.all_bind_wp>

(declare-fun Tm_arrow_b567b509414635f00096b9b1c3e30b57 (Term Term Term) Term)
(declare-fun FStar.Pervasives.all_bind_wp (Term Term Term Term Term Term Term Term) Term)

(declare-fun Tm_arrow_27354558e07d00e058824d7a847efedd () Term)
(declare-fun FStar.Pervasives.all_bind_wp@tok () Term)

(declare-fun Tm_arrow_59cac8a9b1ae3aa9511b8a867f8e934e (Term Term) Term)
(declare-fun Tm_abs_35ddc99cefc0079215f6f6ab3c58856d (Term Term Term Term Term) Term)

; </end encoding FStar.Pervasives.all_bind_wp>


; <Start encoding FStar.Pervasives.all_if_then_else>

(declare-fun FStar.Pervasives.all_if_then_else (Term Term Term Term Term Term Term) Term)
(declare-fun Tm_arrow_491eee2c8dc4eab4d420326a8285d2c4 () Term)
(declare-fun FStar.Pervasives.all_if_then_else@tok () Term)

; </end encoding FStar.Pervasives.all_if_then_else>


; <Start encoding FStar.Pervasives.all_stronger>

(declare-fun FStar.Pervasives.all_stronger (Term Term Term Term) Term)
(declare-fun Tm_arrow_073b21d0ec8edf2dda32907b45ec5f68 () Term)
(declare-fun FStar.Pervasives.all_stronger@tok () Term)

; </end encoding FStar.Pervasives.all_stronger>


; <Start encoding FStar.Pervasives.all_close_wp>


(declare-fun FStar.Pervasives.all_close_wp (Term Term Term Term Term Term) Term)

(declare-fun Tm_arrow_803d195802308e8beadf04438d3a6508 () Term)
(declare-fun FStar.Pervasives.all_close_wp@tok () Term)


; </end encoding FStar.Pervasives.all_close_wp>


; <Start encoding FStar.Pervasives.all_assert_p>

(declare-fun FStar.Pervasives.all_assert_p (Term Term Term Term Term Term) Term)
(declare-fun Tm_arrow_b09c8922c5b229f067ca33ea5a1ff149 () Term)
(declare-fun FStar.Pervasives.all_assert_p@tok () Term)

; </end encoding FStar.Pervasives.all_assert_p>


; <Start encoding FStar.Pervasives.all_assume_p>

(declare-fun FStar.Pervasives.all_assume_p (Term Term Term Term Term Term) Term)

(declare-fun FStar.Pervasives.all_assume_p@tok () Term)

; </end encoding FStar.Pervasives.all_assume_p>


; <Start encoding FStar.Pervasives.all_null_wp>

(declare-fun FStar.Pervasives.all_null_wp (Term Term Term Term) Term)
(declare-fun Tm_arrow_6df38fd0e348b5ae4311e5f1783de8f1 () Term)
(declare-fun FStar.Pervasives.all_null_wp@tok () Term)

; </end encoding FStar.Pervasives.all_null_wp>


; <Start encoding FStar.Pervasives.all_trivial>

(declare-fun FStar.Pervasives.all_trivial (Term Term Term) Term)
(declare-fun Tm_arrow_957927b0d25001784693eee8b2182308 () Term)
(declare-fun FStar.Pervasives.all_trivial@tok () Term)

(declare-fun Tm_abs_22e463dbd987016e31d6bc67025a7cd9 (Term Term) Term)

; </end encoding FStar.Pervasives.all_trivial>


; <Skipped FStar.Pervasives.ALL_h/>


; <Start encoding FStar.Pervasives.inversion>

(declare-fun FStar.Pervasives.inversion (Term) Term)
(declare-fun Tm_arrow_a9f9f8601414c575834fd3a493930aa6 () Term)
(declare-fun FStar.Pervasives.inversion@tok () Term)

; </end encoding FStar.Pervasives.inversion>


; <Start encoding FStar.Pervasives.allow_inversion>

(declare-fun FStar.Pervasives.allow_inversion (Term) Term)
(declare-fun Tm_refine_363615bee79fae5066b7c8bd06c286d0 (Term) Term)
(declare-fun Tm_arrow_bcab9cce464ec0f76562bc48c17ba410 () Term)
(declare-fun FStar.Pervasives.allow_inversion@tok () Term)


; </end encoding FStar.Pervasives.allow_inversion>


; <Start encoding FStar.Pervasives.invertOption>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.Pervasives.invertOption (Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.Pervasives.invertOption@tok () Term)

; </end encoding FStar.Pervasives.invertOption>


; <Start encoding >

;;;;;;;;;;;;;;;;Constructor
(declare-fun FStar.Pervasives.either (Term Term) Term)
;;;;;;;;;;;;;;;;Projector
(declare-fun FStar.Pervasives.either@x0 (Term) Term)
;;;;;;;;;;;;;;;;Projector
(declare-fun FStar.Pervasives.either@x1 (Term) Term)
;;;;;;;;;;;;;;;;token
(declare-fun FStar.Pervasives.either@tok () Term)
;;;;;;;;;;;;;;;;Constructor
(declare-fun FStar.Pervasives.Inl (Term Term Term) Term)
;;;;;;;;;;;;;;;;Projector
(declare-fun FStar.Pervasives.Inl__a (Term) Term)
;;;;;;;;;;;;;;;;Projector
(declare-fun FStar.Pervasives.Inl__b (Term) Term)
;;;;;;;;;;;;;;;;Projector
(declare-fun FStar.Pervasives.Inl_v (Term) Term)
;;;;;;;;;;;;;;;;data constructor proxy: Inl
(declare-fun FStar.Pervasives.Inl@tok () Term)
;;;;;;;;;;;;;;;;Constructor
(declare-fun FStar.Pervasives.Inr (Term Term Term) Term)
;;;;;;;;;;;;;;;;Projector
(declare-fun FStar.Pervasives.Inr__a (Term) Term)
;;;;;;;;;;;;;;;;Projector
(declare-fun FStar.Pervasives.Inr__b (Term) Term)
;;;;;;;;;;;;;;;;Projector
(declare-fun FStar.Pervasives.Inr_v (Term) Term)
;;;;;;;;;;;;;;;;data constructor proxy: Inr
(declare-fun FStar.Pervasives.Inr@tok () Term)
(declare-fun Tm_arrow_065da0adeba0c4ae0da1476ececee84c () Term)
(declare-fun Tm_arrow_c883938642e6d97d79c975d8d94b4aac () Term)

; <Start encoding FStar.Pervasives.either>


; <start constructor FStar.Pervasives.either>

;;;;;;;;;;;;;;;;Discriminator definition
(define-fun is-FStar.Pervasives.either ((__@x0 Term)) Bool
 (and (= (Term_constr_id __@x0)
313)
(exists ((@x0 Term) (@x1 Term))
 (! (= __@x0
(FStar.Pervasives.either @x0
@x1))
 
;;no pats
:qid is-FStar.Pervasives.either))))

; </end constructor FStar.Pervasives.either>


; </end encoding FStar.Pervasives.either>


; <Start encoding FStar.Pervasives.Inl>


; <start constructor FStar.Pervasives.Inl>

;;;;;;;;;;;;;;;;Discriminator definition
(define-fun is-FStar.Pervasives.Inl ((__@x0 Term)) Bool
 (and (= (Term_constr_id __@x0)
320)
(= __@x0
(FStar.Pervasives.Inl (FStar.Pervasives.Inl__a __@x0)
(FStar.Pervasives.Inl__b __@x0)
(FStar.Pervasives.Inl_v __@x0)))))

; </end constructor FStar.Pervasives.Inl>


; </end encoding FStar.Pervasives.Inl>


; <Start encoding FStar.Pervasives.Inr>


; <start constructor FStar.Pervasives.Inr>

;;;;;;;;;;;;;;;;Discriminator definition
(define-fun is-FStar.Pervasives.Inr ((__@x0 Term)) Bool
 (and (= (Term_constr_id __@x0)
325)
(= __@x0
(FStar.Pervasives.Inr (FStar.Pervasives.Inr__a __@x0)
(FStar.Pervasives.Inr__b __@x0)
(FStar.Pervasives.Inr_v __@x0)))))

; </end constructor FStar.Pervasives.Inr>


; </end encoding FStar.Pervasives.Inr>


; </end encoding >


; <Start encoding FStar.Pervasives.either__uu___haseq>


; </end encoding FStar.Pervasives.either__uu___haseq>


; <Start encoding FStar.Pervasives.uu___is_Inl>

(declare-fun FStar.Pervasives.uu___is_Inl (Term Term Term) Term)
(declare-fun Tm_arrow_af0c68f1e39d4d6020c0873b16730c7d () Term)
(declare-fun FStar.Pervasives.uu___is_Inl@tok () Term)

; </end encoding FStar.Pervasives.uu___is_Inl>


; <Skipped FStar.Pervasives.uu___is_Inl/>


; <Start encoding FStar.Pervasives.__proj__Inl__item__v>

(declare-fun Tm_refine_85e0cc884f8457202f90cd77f23733ba (Term Term) Term)
(declare-fun FStar.Pervasives.__proj__Inl__item__v (Term Term Term) Term)

(declare-fun Tm_arrow_a80e0750277867ba1a434ad3bba8702d () Term)
(declare-fun FStar.Pervasives.__proj__Inl__item__v@tok () Term)

; </end encoding FStar.Pervasives.__proj__Inl__item__v>


; <Skipped FStar.Pervasives.__proj__Inl__item__v/>


; <Start encoding FStar.Pervasives.uu___is_Inr>

(declare-fun FStar.Pervasives.uu___is_Inr (Term Term Term) Term)

(declare-fun FStar.Pervasives.uu___is_Inr@tok () Term)

; </end encoding FStar.Pervasives.uu___is_Inr>


; <Skipped FStar.Pervasives.uu___is_Inr/>


; <Start encoding FStar.Pervasives.__proj__Inr__item__v>

(declare-fun Tm_refine_8f1f5f564dae90240db429de2eb41517 (Term Term) Term)
(declare-fun FStar.Pervasives.__proj__Inr__item__v (Term Term Term) Term)

(declare-fun Tm_arrow_df618db6b42762940f198036c8a56200 () Term)
(declare-fun FStar.Pervasives.__proj__Inr__item__v@tok () Term)

; </end encoding FStar.Pervasives.__proj__Inr__item__v>


; <Skipped FStar.Pervasives.__proj__Inr__item__v/>


; <Start encoding FStar.Pervasives.dfst>


(declare-fun FStar.Pervasives.dfst (Term Term Term) Term)


(declare-fun FStar.Pervasives.dfst@tok () Term)


; </end encoding FStar.Pervasives.dfst>


; <Start encoding FStar.Pervasives.dsnd>


(declare-fun FStar.Pervasives.dsnd (Term Term Term) Term)


(declare-fun FStar.Pervasives.dsnd@tok () Term)


; </end encoding FStar.Pervasives.dsnd>


; <Start encoding >

;;;;;;;;;;;;;;;;Constructor
(declare-fun FStar.Pervasives.dtuple3 (Term Term Term) Term)
;;;;;;;;;;;;;;;;Projector
(declare-fun FStar.Pervasives.dtuple3@x0 (Term) Term)
;;;;;;;;;;;;;;;;Projector
(declare-fun FStar.Pervasives.dtuple3@x1 (Term) Term)
;;;;;;;;;;;;;;;;Projector
(declare-fun FStar.Pervasives.dtuple3@x2 (Term) Term)
;;;;;;;;;;;;;;;;token
(declare-fun FStar.Pervasives.dtuple3@tok () Term)
;;;;;;;;;;;;;;;;Constructor
(declare-fun FStar.Pervasives.Mkdtuple3 (Term Term Term Term Term Term) Term)
;;;;;;;;;;;;;;;;Projector
(declare-fun FStar.Pervasives.Mkdtuple3_a (Term) Term)
;;;;;;;;;;;;;;;;Projector
(declare-fun FStar.Pervasives.Mkdtuple3_b (Term) Term)
;;;;;;;;;;;;;;;;Projector
(declare-fun FStar.Pervasives.Mkdtuple3_c (Term) Term)
;;;;;;;;;;;;;;;;Projector
(declare-fun FStar.Pervasives.Mkdtuple3__1 (Term) Term)
;;;;;;;;;;;;;;;;Projector
(declare-fun FStar.Pervasives.Mkdtuple3__2 (Term) Term)
;;;;;;;;;;;;;;;;Projector
(declare-fun FStar.Pervasives.Mkdtuple3__3 (Term) Term)
;;;;;;;;;;;;;;;;data constructor proxy: Mkdtuple3
(declare-fun FStar.Pervasives.Mkdtuple3@tok () Term)

(declare-fun Tm_arrow_0b6559e6ff3addf84b0c2880affbb335 (Term Term) Term)




(declare-fun Tm_arrow_8423f67df62f9e824c55756f9e26058d () Term)



; <Start encoding FStar.Pervasives.dtuple3>


; <start constructor FStar.Pervasives.dtuple3>

;;;;;;;;;;;;;;;;Discriminator definition
(define-fun is-FStar.Pervasives.dtuple3 ((__@x0 Term)) Bool
 (and (= (Term_constr_id __@x0)
361)
(exists ((@x0 Term) (@x1 Term) (@x2 Term))
 (! (= __@x0
(FStar.Pervasives.dtuple3 @x0
@x1
@x2))
 
;;no pats
:qid is-FStar.Pervasives.dtuple3))))

; </end constructor FStar.Pervasives.dtuple3>


; </end encoding FStar.Pervasives.dtuple3>


; <Start encoding FStar.Pervasives.Mkdtuple3>


; <start constructor FStar.Pervasives.Mkdtuple3>

;;;;;;;;;;;;;;;;Discriminator definition
(define-fun is-FStar.Pervasives.Mkdtuple3 ((__@x0 Term)) Bool
 (and (= (Term_constr_id __@x0)
372)
(= __@x0
(FStar.Pervasives.Mkdtuple3 (FStar.Pervasives.Mkdtuple3_a __@x0)
(FStar.Pervasives.Mkdtuple3_b __@x0)
(FStar.Pervasives.Mkdtuple3_c __@x0)
(FStar.Pervasives.Mkdtuple3__1 __@x0)
(FStar.Pervasives.Mkdtuple3__2 __@x0)
(FStar.Pervasives.Mkdtuple3__3 __@x0)))))

; </end constructor FStar.Pervasives.Mkdtuple3>


; </end encoding FStar.Pervasives.Mkdtuple3>


; </end encoding >


; <Start encoding FStar.Pervasives.dtuple3__uu___haseq>




; </end encoding FStar.Pervasives.dtuple3__uu___haseq>


; <Start encoding FStar.Pervasives.uu___is_Mkdtuple3>



(declare-fun FStar.Pervasives.uu___is_Mkdtuple3 (Term Term Term Term) Term)


(declare-fun Tm_arrow_70452cb82cd0a282ca9a2dbeb54c1b04 () Term)
(declare-fun FStar.Pervasives.uu___is_Mkdtuple3@tok () Term)

; </end encoding FStar.Pervasives.uu___is_Mkdtuple3>


; <Skipped FStar.Pervasives.uu___is_Mkdtuple3/>


; <Start encoding FStar.Pervasives.__proj__Mkdtuple3__item___1>



(declare-fun FStar.Pervasives.__proj__Mkdtuple3__item___1 (Term Term Term Term) Term)


(declare-fun Tm_arrow_255f0cfe499b1d2e9836e157bce1dba3 () Term)
(declare-fun FStar.Pervasives.__proj__Mkdtuple3__item___1@tok () Term)

; </end encoding FStar.Pervasives.__proj__Mkdtuple3__item___1>


; <Skipped FStar.Pervasives.__proj__Mkdtuple3__item___1/>


; <Start encoding FStar.Pervasives.__proj__Mkdtuple3__item___2>



(declare-fun FStar.Pervasives.__proj__Mkdtuple3__item___2 (Term Term Term Term) Term)


(declare-fun Tm_arrow_ea1ded11f7d194a26e812f407333a011 () Term)
(declare-fun FStar.Pervasives.__proj__Mkdtuple3__item___2@tok () Term)

; </end encoding FStar.Pervasives.__proj__Mkdtuple3__item___2>


; <Skipped FStar.Pervasives.__proj__Mkdtuple3__item___2/>


; <Start encoding FStar.Pervasives.__proj__Mkdtuple3__item___3>



(declare-fun FStar.Pervasives.__proj__Mkdtuple3__item___3 (Term Term Term Term) Term)


(declare-fun Tm_arrow_1d7ad5cfa0fff643640e3f74466d283e () Term)
(declare-fun FStar.Pervasives.__proj__Mkdtuple3__item___3@tok () Term)

; </end encoding FStar.Pervasives.__proj__Mkdtuple3__item___3>


; <Skipped FStar.Pervasives.__proj__Mkdtuple3__item___3/>


; <Start encoding >

;;;;;;;;;;;;;;;;Constructor
(declare-fun FStar.Pervasives.dtuple4 (Term Term Term Term) Term)
;;;;;;;;;;;;;;;;Projector
(declare-fun FStar.Pervasives.dtuple4@x0 (Term) Term)
;;;;;;;;;;;;;;;;Projector
(declare-fun FStar.Pervasives.dtuple4@x1 (Term) Term)
;;;;;;;;;;;;;;;;Projector
(declare-fun FStar.Pervasives.dtuple4@x2 (Term) Term)
;;;;;;;;;;;;;;;;Projector
(declare-fun FStar.Pervasives.dtuple4@x3 (Term) Term)
;;;;;;;;;;;;;;;;token
(declare-fun FStar.Pervasives.dtuple4@tok () Term)
;;;;;;;;;;;;;;;;Constructor
(declare-fun FStar.Pervasives.Mkdtuple4 (Term Term Term Term Term Term Term Term) Term)
;;;;;;;;;;;;;;;;Projector
(declare-fun FStar.Pervasives.Mkdtuple4_a (Term) Term)
;;;;;;;;;;;;;;;;Projector
(declare-fun FStar.Pervasives.Mkdtuple4_b (Term) Term)
;;;;;;;;;;;;;;;;Projector
(declare-fun FStar.Pervasives.Mkdtuple4_c (Term) Term)
;;;;;;;;;;;;;;;;Projector
(declare-fun FStar.Pervasives.Mkdtuple4_d (Term) Term)
;;;;;;;;;;;;;;;;Projector
(declare-fun FStar.Pervasives.Mkdtuple4__1 (Term) Term)
;;;;;;;;;;;;;;;;Projector
(declare-fun FStar.Pervasives.Mkdtuple4__2 (Term) Term)
;;;;;;;;;;;;;;;;Projector
(declare-fun FStar.Pervasives.Mkdtuple4__3 (Term) Term)
;;;;;;;;;;;;;;;;Projector
(declare-fun FStar.Pervasives.Mkdtuple4__4 (Term) Term)
;;;;;;;;;;;;;;;;data constructor proxy: Mkdtuple4
(declare-fun FStar.Pervasives.Mkdtuple4@tok () Term)


(declare-fun Tm_arrow_af8eda99ba3685403be22a88669dcb35 (Term Term Term) Term)






(declare-fun Tm_arrow_cef44a6056754f192c2446237c4c1408 () Term)




; <Start encoding FStar.Pervasives.dtuple4>


; <start constructor FStar.Pervasives.dtuple4>

;;;;;;;;;;;;;;;;Discriminator definition
(define-fun is-FStar.Pervasives.dtuple4 ((__@x0 Term)) Bool
 (and (= (Term_constr_id __@x0)
434)
(exists ((@x0 Term) (@x1 Term) (@x2 Term) (@x3 Term))
 (! (= __@x0
(FStar.Pervasives.dtuple4 @x0
@x1
@x2
@x3))
 
;;no pats
:qid is-FStar.Pervasives.dtuple4))))

; </end constructor FStar.Pervasives.dtuple4>


; </end encoding FStar.Pervasives.dtuple4>


; <Start encoding FStar.Pervasives.Mkdtuple4>


; <start constructor FStar.Pervasives.Mkdtuple4>

;;;;;;;;;;;;;;;;Discriminator definition
(define-fun is-FStar.Pervasives.Mkdtuple4 ((__@x0 Term)) Bool
 (and (= (Term_constr_id __@x0)
447)
(= __@x0
(FStar.Pervasives.Mkdtuple4 (FStar.Pervasives.Mkdtuple4_a __@x0)
(FStar.Pervasives.Mkdtuple4_b __@x0)
(FStar.Pervasives.Mkdtuple4_c __@x0)
(FStar.Pervasives.Mkdtuple4_d __@x0)
(FStar.Pervasives.Mkdtuple4__1 __@x0)
(FStar.Pervasives.Mkdtuple4__2 __@x0)
(FStar.Pervasives.Mkdtuple4__3 __@x0)
(FStar.Pervasives.Mkdtuple4__4 __@x0)))))

; </end constructor FStar.Pervasives.Mkdtuple4>


; </end encoding FStar.Pervasives.Mkdtuple4>


; </end encoding >


; <Start encoding FStar.Pervasives.dtuple4__uu___haseq>





; </end encoding FStar.Pervasives.dtuple4__uu___haseq>


; <Start encoding FStar.Pervasives.uu___is_Mkdtuple4>




(declare-fun FStar.Pervasives.uu___is_Mkdtuple4 (Term Term Term Term Term) Term)



(declare-fun Tm_arrow_76a226dc2cea2ddd4e4258637fc95e5b () Term)
(declare-fun FStar.Pervasives.uu___is_Mkdtuple4@tok () Term)

; </end encoding FStar.Pervasives.uu___is_Mkdtuple4>


; <Skipped FStar.Pervasives.uu___is_Mkdtuple4/>


; <Start encoding FStar.Pervasives.__proj__Mkdtuple4__item___1>




(declare-fun FStar.Pervasives.__proj__Mkdtuple4__item___1 (Term Term Term Term Term) Term)



(declare-fun Tm_arrow_1da4d60ab69f411b912e76cc25e77965 () Term)
(declare-fun FStar.Pervasives.__proj__Mkdtuple4__item___1@tok () Term)

; </end encoding FStar.Pervasives.__proj__Mkdtuple4__item___1>


; <Skipped FStar.Pervasives.__proj__Mkdtuple4__item___1/>


; <Start encoding FStar.Pervasives.__proj__Mkdtuple4__item___2>




(declare-fun FStar.Pervasives.__proj__Mkdtuple4__item___2 (Term Term Term Term Term) Term)



(declare-fun Tm_arrow_a86867091548f3d7d3ca1cb8b0458b9f () Term)
(declare-fun FStar.Pervasives.__proj__Mkdtuple4__item___2@tok () Term)

; </end encoding FStar.Pervasives.__proj__Mkdtuple4__item___2>


; <Skipped FStar.Pervasives.__proj__Mkdtuple4__item___2/>


; <Start encoding FStar.Pervasives.__proj__Mkdtuple4__item___3>




(declare-fun FStar.Pervasives.__proj__Mkdtuple4__item___3 (Term Term Term Term Term) Term)



(declare-fun Tm_arrow_ee72552fcc293405aa0e854ba26f27ac () Term)
(declare-fun FStar.Pervasives.__proj__Mkdtuple4__item___3@tok () Term)

; </end encoding FStar.Pervasives.__proj__Mkdtuple4__item___3>


; <Skipped FStar.Pervasives.__proj__Mkdtuple4__item___3/>


; <Start encoding FStar.Pervasives.__proj__Mkdtuple4__item___4>




(declare-fun FStar.Pervasives.__proj__Mkdtuple4__item___4 (Term Term Term Term Term) Term)



(declare-fun Tm_arrow_6c79def96aa5d5d9eb9555c48dd9ebb6 () Term)
(declare-fun FStar.Pervasives.__proj__Mkdtuple4__item___4@tok () Term)

; </end encoding FStar.Pervasives.__proj__Mkdtuple4__item___4>


; <Skipped FStar.Pervasives.__proj__Mkdtuple4__item___4/>


; <Start encoding FStar.Pervasives.ignore>

(declare-fun FStar.Pervasives.ignore (Term Term) Term)
(declare-fun Tm_arrow_962476a7eea46a6ffc9b658c6d8fbc71 () Term)
(declare-fun FStar.Pervasives.ignore@tok () Term)

; </end encoding FStar.Pervasives.ignore>


; <Start encoding FStar.Pervasives.false_elim>

(declare-fun Tm_refine_f1ecc6ab6882a651504f328937700647 () Term)
(declare-fun FStar.Pervasives.false_elim (Term Term) Term)

(declare-fun Tm_arrow_7636fbfab5cd88ba06f60c10ea8caef2 () Term)
(declare-fun FStar.Pervasives.false_elim@tok () Term)

; </end encoding FStar.Pervasives.false_elim>


; <Start encoding >

;;;;;;;;;;;;;;;;Constructor
(declare-fun FStar.Pervasives.__internal_ocaml_attributes () Term)
;;;;;;;;;;;;;;;;Constructor
(declare-fun FStar.Pervasives.PpxDerivingShow () Term)
;;;;;;;;;;;;;;;;data constructor proxy: PpxDerivingShow
(declare-fun FStar.Pervasives.PpxDerivingShow@tok () Term)
;;;;;;;;;;;;;;;;Constructor
(declare-fun FStar.Pervasives.PpxDerivingShowConstant (Term) Term)
;;;;;;;;;;;;;;;;Projector
(declare-fun FStar.Pervasives.PpxDerivingShowConstant__0 (Term) Term)
;;;;;;;;;;;;;;;;data constructor proxy: PpxDerivingShowConstant
(declare-fun FStar.Pervasives.PpxDerivingShowConstant@tok () Term)
;;;;;;;;;;;;;;;;Constructor
(declare-fun FStar.Pervasives.PpxDerivingYoJson () Term)
;;;;;;;;;;;;;;;;data constructor proxy: PpxDerivingYoJson
(declare-fun FStar.Pervasives.PpxDerivingYoJson@tok () Term)
;;;;;;;;;;;;;;;;Constructor
(declare-fun FStar.Pervasives.CInline () Term)
;;;;;;;;;;;;;;;;data constructor proxy: CInline
(declare-fun FStar.Pervasives.CInline@tok () Term)
;;;;;;;;;;;;;;;;Constructor
(declare-fun FStar.Pervasives.Substitute () Term)
;;;;;;;;;;;;;;;;data constructor proxy: Substitute
(declare-fun FStar.Pervasives.Substitute@tok () Term)
;;;;;;;;;;;;;;;;Constructor
(declare-fun FStar.Pervasives.Gc () Term)
;;;;;;;;;;;;;;;;data constructor proxy: Gc
(declare-fun FStar.Pervasives.Gc@tok () Term)
;;;;;;;;;;;;;;;;Constructor
(declare-fun FStar.Pervasives.Comment (Term) Term)
;;;;;;;;;;;;;;;;Projector
(declare-fun FStar.Pervasives.Comment__0 (Term) Term)
;;;;;;;;;;;;;;;;data constructor proxy: Comment
(declare-fun FStar.Pervasives.Comment@tok () Term)
;;;;;;;;;;;;;;;;Constructor
(declare-fun FStar.Pervasives.CPrologue (Term) Term)
;;;;;;;;;;;;;;;;Projector
(declare-fun FStar.Pervasives.CPrologue__0 (Term) Term)
;;;;;;;;;;;;;;;;data constructor proxy: CPrologue
(declare-fun FStar.Pervasives.CPrologue@tok () Term)
;;;;;;;;;;;;;;;;Constructor
(declare-fun FStar.Pervasives.CEpilogue (Term) Term)
;;;;;;;;;;;;;;;;Projector
(declare-fun FStar.Pervasives.CEpilogue__0 (Term) Term)
;;;;;;;;;;;;;;;;data constructor proxy: CEpilogue
(declare-fun FStar.Pervasives.CEpilogue@tok () Term)
;;;;;;;;;;;;;;;;Constructor
(declare-fun FStar.Pervasives.CConst (Term) Term)
;;;;;;;;;;;;;;;;Projector
(declare-fun FStar.Pervasives.CConst__0 (Term) Term)
;;;;;;;;;;;;;;;;data constructor proxy: CConst
(declare-fun FStar.Pervasives.CConst@tok () Term)
;;;;;;;;;;;;;;;;Constructor
(declare-fun FStar.Pervasives.CCConv (Term) Term)
;;;;;;;;;;;;;;;;Projector
(declare-fun FStar.Pervasives.CCConv__0 (Term) Term)
;;;;;;;;;;;;;;;;data constructor proxy: CCConv
(declare-fun FStar.Pervasives.CCConv@tok () Term)
;;;;;;;;;;;;;;;;Constructor
(declare-fun FStar.Pervasives.CAbstractStruct () Term)
;;;;;;;;;;;;;;;;data constructor proxy: CAbstractStruct
(declare-fun FStar.Pervasives.CAbstractStruct@tok () Term)
;;;;;;;;;;;;;;;;Constructor
(declare-fun FStar.Pervasives.CIfDef () Term)
;;;;;;;;;;;;;;;;data constructor proxy: CIfDef
(declare-fun FStar.Pervasives.CIfDef@tok () Term)
;;;;;;;;;;;;;;;;Constructor
(declare-fun FStar.Pervasives.CMacro () Term)
;;;;;;;;;;;;;;;;data constructor proxy: CMacro
(declare-fun FStar.Pervasives.CMacro@tok () Term)
(declare-fun Tm_arrow_a25c6dbdd7c43412e925069991c0ef48 () Term)






; <Start encoding FStar.Pervasives.__internal_ocaml_attributes>


; <start constructor FStar.Pervasives.__internal_ocaml_attributes>

;;;;;;;;;;;;;;;;Discriminator definition
(define-fun is-FStar.Pervasives.__internal_ocaml_attributes ((__@x0 Term)) Bool
 (and (= (Term_constr_id __@x0)
545)
(= __@x0
FStar.Pervasives.__internal_ocaml_attributes)))

; </end constructor FStar.Pervasives.__internal_ocaml_attributes>


; </end encoding FStar.Pervasives.__internal_ocaml_attributes>


; <Start encoding FStar.Pervasives.PpxDerivingShow>


; <start constructor FStar.Pervasives.PpxDerivingShow>

;;;;;;;;;;;;;;;;Discriminator definition
(define-fun is-FStar.Pervasives.PpxDerivingShow ((__@x0 Term)) Bool
 (and (= (Term_constr_id __@x0)
551)
(= __@x0
FStar.Pervasives.PpxDerivingShow)))

; </end constructor FStar.Pervasives.PpxDerivingShow>


; </end encoding FStar.Pervasives.PpxDerivingShow>


; <Start encoding FStar.Pervasives.PpxDerivingShowConstant>


; <start constructor FStar.Pervasives.PpxDerivingShowConstant>

;;;;;;;;;;;;;;;;Discriminator definition
(define-fun is-FStar.Pervasives.PpxDerivingShowConstant ((__@x0 Term)) Bool
 (and (= (Term_constr_id __@x0)
553)
(= __@x0
(FStar.Pervasives.PpxDerivingShowConstant (FStar.Pervasives.PpxDerivingShowConstant__0 __@x0)))))

; </end constructor FStar.Pervasives.PpxDerivingShowConstant>


; </end encoding FStar.Pervasives.PpxDerivingShowConstant>


; <Start encoding FStar.Pervasives.PpxDerivingYoJson>


; <start constructor FStar.Pervasives.PpxDerivingYoJson>

;;;;;;;;;;;;;;;;Discriminator definition
(define-fun is-FStar.Pervasives.PpxDerivingYoJson ((__@x0 Term)) Bool
 (and (= (Term_constr_id __@x0)
558)
(= __@x0
FStar.Pervasives.PpxDerivingYoJson)))

; </end constructor FStar.Pervasives.PpxDerivingYoJson>


; </end encoding FStar.Pervasives.PpxDerivingYoJson>


; <Start encoding FStar.Pervasives.CInline>


; <start constructor FStar.Pervasives.CInline>

;;;;;;;;;;;;;;;;Discriminator definition
(define-fun is-FStar.Pervasives.CInline ((__@x0 Term)) Bool
 (and (= (Term_constr_id __@x0)
560)
(= __@x0
FStar.Pervasives.CInline)))

; </end constructor FStar.Pervasives.CInline>


; </end encoding FStar.Pervasives.CInline>


; <Start encoding FStar.Pervasives.Substitute>


; <start constructor FStar.Pervasives.Substitute>

;;;;;;;;;;;;;;;;Discriminator definition
(define-fun is-FStar.Pervasives.Substitute ((__@x0 Term)) Bool
 (and (= (Term_constr_id __@x0)
562)
(= __@x0
FStar.Pervasives.Substitute)))

; </end constructor FStar.Pervasives.Substitute>


; </end encoding FStar.Pervasives.Substitute>


; <Start encoding FStar.Pervasives.Gc>


; <start constructor FStar.Pervasives.Gc>

;;;;;;;;;;;;;;;;Discriminator definition
(define-fun is-FStar.Pervasives.Gc ((__@x0 Term)) Bool
 (and (= (Term_constr_id __@x0)
564)
(= __@x0
FStar.Pervasives.Gc)))

; </end constructor FStar.Pervasives.Gc>


; </end encoding FStar.Pervasives.Gc>


; <Start encoding FStar.Pervasives.Comment>


; <start constructor FStar.Pervasives.Comment>

;;;;;;;;;;;;;;;;Discriminator definition
(define-fun is-FStar.Pervasives.Comment ((__@x0 Term)) Bool
 (and (= (Term_constr_id __@x0)
566)
(= __@x0
(FStar.Pervasives.Comment (FStar.Pervasives.Comment__0 __@x0)))))

; </end constructor FStar.Pervasives.Comment>


; </end encoding FStar.Pervasives.Comment>


; <Start encoding FStar.Pervasives.CPrologue>


; <start constructor FStar.Pervasives.CPrologue>

;;;;;;;;;;;;;;;;Discriminator definition
(define-fun is-FStar.Pervasives.CPrologue ((__@x0 Term)) Bool
 (and (= (Term_constr_id __@x0)
571)
(= __@x0
(FStar.Pervasives.CPrologue (FStar.Pervasives.CPrologue__0 __@x0)))))

; </end constructor FStar.Pervasives.CPrologue>


; </end encoding FStar.Pervasives.CPrologue>


; <Start encoding FStar.Pervasives.CEpilogue>


; <start constructor FStar.Pervasives.CEpilogue>

;;;;;;;;;;;;;;;;Discriminator definition
(define-fun is-FStar.Pervasives.CEpilogue ((__@x0 Term)) Bool
 (and (= (Term_constr_id __@x0)
576)
(= __@x0
(FStar.Pervasives.CEpilogue (FStar.Pervasives.CEpilogue__0 __@x0)))))

; </end constructor FStar.Pervasives.CEpilogue>


; </end encoding FStar.Pervasives.CEpilogue>


; <Start encoding FStar.Pervasives.CConst>


; <start constructor FStar.Pervasives.CConst>

;;;;;;;;;;;;;;;;Discriminator definition
(define-fun is-FStar.Pervasives.CConst ((__@x0 Term)) Bool
 (and (= (Term_constr_id __@x0)
581)
(= __@x0
(FStar.Pervasives.CConst (FStar.Pervasives.CConst__0 __@x0)))))

; </end constructor FStar.Pervasives.CConst>


; </end encoding FStar.Pervasives.CConst>


; <Start encoding FStar.Pervasives.CCConv>


; <start constructor FStar.Pervasives.CCConv>

;;;;;;;;;;;;;;;;Discriminator definition
(define-fun is-FStar.Pervasives.CCConv ((__@x0 Term)) Bool
 (and (= (Term_constr_id __@x0)
586)
(= __@x0
(FStar.Pervasives.CCConv (FStar.Pervasives.CCConv__0 __@x0)))))

; </end constructor FStar.Pervasives.CCConv>


; </end encoding FStar.Pervasives.CCConv>


; <Start encoding FStar.Pervasives.CAbstractStruct>


; <start constructor FStar.Pervasives.CAbstractStruct>

;;;;;;;;;;;;;;;;Discriminator definition
(define-fun is-FStar.Pervasives.CAbstractStruct ((__@x0 Term)) Bool
 (and (= (Term_constr_id __@x0)
591)
(= __@x0
FStar.Pervasives.CAbstractStruct)))

; </end constructor FStar.Pervasives.CAbstractStruct>


; </end encoding FStar.Pervasives.CAbstractStruct>


; <Start encoding FStar.Pervasives.CIfDef>


; <start constructor FStar.Pervasives.CIfDef>

;;;;;;;;;;;;;;;;Discriminator definition
(define-fun is-FStar.Pervasives.CIfDef ((__@x0 Term)) Bool
 (and (= (Term_constr_id __@x0)
593)
(= __@x0
FStar.Pervasives.CIfDef)))

; </end constructor FStar.Pervasives.CIfDef>


; </end encoding FStar.Pervasives.CIfDef>


; <Start encoding FStar.Pervasives.CMacro>


; <start constructor FStar.Pervasives.CMacro>

;;;;;;;;;;;;;;;;Discriminator definition
(define-fun is-FStar.Pervasives.CMacro ((__@x0 Term)) Bool
 (and (= (Term_constr_id __@x0)
595)
(= __@x0
FStar.Pervasives.CMacro)))

; </end constructor FStar.Pervasives.CMacro>


; </end encoding FStar.Pervasives.CMacro>


; </end encoding >


; <Start encoding FStar.Pervasives.__internal_ocaml_attributes__uu___haseq>


; </end encoding FStar.Pervasives.__internal_ocaml_attributes__uu___haseq>


; <Start encoding FStar.Pervasives.uu___is_PpxDerivingShow>

(declare-fun FStar.Pervasives.uu___is_PpxDerivingShow (Term) Term)
(declare-fun Tm_arrow_89dc0c243f5e74d4fefc48cfe123db41 () Term)
(declare-fun FStar.Pervasives.uu___is_PpxDerivingShow@tok () Term)

; </end encoding FStar.Pervasives.uu___is_PpxDerivingShow>


; <Skipped FStar.Pervasives.uu___is_PpxDerivingShow/>


; <Start encoding FStar.Pervasives.uu___is_PpxDerivingShowConstant>

(declare-fun FStar.Pervasives.uu___is_PpxDerivingShowConstant (Term) Term)

(declare-fun FStar.Pervasives.uu___is_PpxDerivingShowConstant@tok () Term)

; </end encoding FStar.Pervasives.uu___is_PpxDerivingShowConstant>


; <Skipped FStar.Pervasives.uu___is_PpxDerivingShowConstant/>


; <Start encoding FStar.Pervasives.__proj__PpxDerivingShowConstant__item___0>

(declare-fun Tm_refine_564db2f0aa0878b4d96c60508be3dd36 () Term)
(declare-fun FStar.Pervasives.__proj__PpxDerivingShowConstant__item___0 (Term) Term)

(declare-fun Tm_arrow_dbb84ef8131159481071b6d6a41b7f31 () Term)
(declare-fun FStar.Pervasives.__proj__PpxDerivingShowConstant__item___0@tok () Term)

; </end encoding FStar.Pervasives.__proj__PpxDerivingShowConstant__item___0>


; <Skipped FStar.Pervasives.__proj__PpxDerivingShowConstant__item___0/>


; <Start encoding FStar.Pervasives.uu___is_PpxDerivingYoJson>

(declare-fun FStar.Pervasives.uu___is_PpxDerivingYoJson (Term) Term)

(declare-fun FStar.Pervasives.uu___is_PpxDerivingYoJson@tok () Term)

; </end encoding FStar.Pervasives.uu___is_PpxDerivingYoJson>


; <Skipped FStar.Pervasives.uu___is_PpxDerivingYoJson/>


; <Start encoding FStar.Pervasives.uu___is_CInline>

(declare-fun FStar.Pervasives.uu___is_CInline (Term) Term)

(declare-fun FStar.Pervasives.uu___is_CInline@tok () Term)

; </end encoding FStar.Pervasives.uu___is_CInline>


; <Skipped FStar.Pervasives.uu___is_CInline/>


; <Start encoding FStar.Pervasives.uu___is_Substitute>

(declare-fun FStar.Pervasives.uu___is_Substitute (Term) Term)

(declare-fun FStar.Pervasives.uu___is_Substitute@tok () Term)

; </end encoding FStar.Pervasives.uu___is_Substitute>


; <Skipped FStar.Pervasives.uu___is_Substitute/>


; <Start encoding FStar.Pervasives.uu___is_Gc>

(declare-fun FStar.Pervasives.uu___is_Gc (Term) Term)

(declare-fun FStar.Pervasives.uu___is_Gc@tok () Term)

; </end encoding FStar.Pervasives.uu___is_Gc>


; <Skipped FStar.Pervasives.uu___is_Gc/>


; <Start encoding FStar.Pervasives.uu___is_Comment>

(declare-fun FStar.Pervasives.uu___is_Comment (Term) Term)

(declare-fun FStar.Pervasives.uu___is_Comment@tok () Term)

; </end encoding FStar.Pervasives.uu___is_Comment>


; <Skipped FStar.Pervasives.uu___is_Comment/>


; <Start encoding FStar.Pervasives.__proj__Comment__item___0>

(declare-fun Tm_refine_c53089e2d20d1b0f5a267296ac8e45f0 () Term)
(declare-fun FStar.Pervasives.__proj__Comment__item___0 (Term) Term)

(declare-fun Tm_arrow_d4c2bbf4fb852b3f4b9961c7cbc2f3a2 () Term)
(declare-fun FStar.Pervasives.__proj__Comment__item___0@tok () Term)

; </end encoding FStar.Pervasives.__proj__Comment__item___0>


; <Skipped FStar.Pervasives.__proj__Comment__item___0/>


; <Start encoding FStar.Pervasives.uu___is_CPrologue>

(declare-fun FStar.Pervasives.uu___is_CPrologue (Term) Term)

(declare-fun FStar.Pervasives.uu___is_CPrologue@tok () Term)

; </end encoding FStar.Pervasives.uu___is_CPrologue>


; <Skipped FStar.Pervasives.uu___is_CPrologue/>


; <Start encoding FStar.Pervasives.__proj__CPrologue__item___0>

(declare-fun Tm_refine_ac46c1a2a06ce46a180e0eda48004c47 () Term)
(declare-fun FStar.Pervasives.__proj__CPrologue__item___0 (Term) Term)

(declare-fun Tm_arrow_929b9daa0a2a2e99e3571b146c52feaf () Term)
(declare-fun FStar.Pervasives.__proj__CPrologue__item___0@tok () Term)

; </end encoding FStar.Pervasives.__proj__CPrologue__item___0>


; <Skipped FStar.Pervasives.__proj__CPrologue__item___0/>


; <Start encoding FStar.Pervasives.uu___is_CEpilogue>

(declare-fun FStar.Pervasives.uu___is_CEpilogue (Term) Term)

(declare-fun FStar.Pervasives.uu___is_CEpilogue@tok () Term)

; </end encoding FStar.Pervasives.uu___is_CEpilogue>


; <Skipped FStar.Pervasives.uu___is_CEpilogue/>


; <Start encoding FStar.Pervasives.__proj__CEpilogue__item___0>

(declare-fun Tm_refine_47384bef739d1f0729fd782d351dc9a5 () Term)
(declare-fun FStar.Pervasives.__proj__CEpilogue__item___0 (Term) Term)

(declare-fun Tm_arrow_e37361b66babb46a30183ad1ff072689 () Term)
(declare-fun FStar.Pervasives.__proj__CEpilogue__item___0@tok () Term)

; </end encoding FStar.Pervasives.__proj__CEpilogue__item___0>


; <Skipped FStar.Pervasives.__proj__CEpilogue__item___0/>


; <Start encoding FStar.Pervasives.uu___is_CConst>

(declare-fun FStar.Pervasives.uu___is_CConst (Term) Term)

(declare-fun FStar.Pervasives.uu___is_CConst@tok () Term)

; </end encoding FStar.Pervasives.uu___is_CConst>


; <Skipped FStar.Pervasives.uu___is_CConst/>


; <Start encoding FStar.Pervasives.__proj__CConst__item___0>

(declare-fun Tm_refine_5036c6b2983454bc3afeffcba3f00f50 () Term)
(declare-fun FStar.Pervasives.__proj__CConst__item___0 (Term) Term)

(declare-fun Tm_arrow_2d0b7639551b88b0df758d7b36c8f77a () Term)
(declare-fun FStar.Pervasives.__proj__CConst__item___0@tok () Term)

; </end encoding FStar.Pervasives.__proj__CConst__item___0>


; <Skipped FStar.Pervasives.__proj__CConst__item___0/>


; <Start encoding FStar.Pervasives.uu___is_CCConv>

(declare-fun FStar.Pervasives.uu___is_CCConv (Term) Term)

(declare-fun FStar.Pervasives.uu___is_CCConv@tok () Term)

; </end encoding FStar.Pervasives.uu___is_CCConv>


; <Skipped FStar.Pervasives.uu___is_CCConv/>


; <Start encoding FStar.Pervasives.__proj__CCConv__item___0>

(declare-fun Tm_refine_2c4510f48649a66c3dca1fc9e3a2d320 () Term)
(declare-fun FStar.Pervasives.__proj__CCConv__item___0 (Term) Term)

(declare-fun Tm_arrow_b7e884ec94708f2b05c42d4d8834eac6 () Term)
(declare-fun FStar.Pervasives.__proj__CCConv__item___0@tok () Term)

; </end encoding FStar.Pervasives.__proj__CCConv__item___0>


; <Skipped FStar.Pervasives.__proj__CCConv__item___0/>


; <Start encoding FStar.Pervasives.uu___is_CAbstractStruct>

(declare-fun FStar.Pervasives.uu___is_CAbstractStruct (Term) Term)

(declare-fun FStar.Pervasives.uu___is_CAbstractStruct@tok () Term)

; </end encoding FStar.Pervasives.uu___is_CAbstractStruct>


; <Skipped FStar.Pervasives.uu___is_CAbstractStruct/>


; <Start encoding FStar.Pervasives.uu___is_CIfDef>

(declare-fun FStar.Pervasives.uu___is_CIfDef (Term) Term)

(declare-fun FStar.Pervasives.uu___is_CIfDef@tok () Term)

; </end encoding FStar.Pervasives.uu___is_CIfDef>


; <Skipped FStar.Pervasives.uu___is_CIfDef/>


; <Start encoding FStar.Pervasives.uu___is_CMacro>

(declare-fun FStar.Pervasives.uu___is_CMacro (Term) Term)

(declare-fun FStar.Pervasives.uu___is_CMacro@tok () Term)

; </end encoding FStar.Pervasives.uu___is_CMacro>


; <Skipped FStar.Pervasives.uu___is_CMacro/>


; <Start encoding FStar.Pervasives.inline_let>

(declare-fun FStar.Pervasives.inline_let (Dummy_sort) Term)

; </end encoding FStar.Pervasives.inline_let>


; <Start encoding FStar.Pervasives.plugin>

(declare-fun FStar.Pervasives.plugin (Term) Term)
(declare-fun Tm_arrow_f12575a0ee171a8be16a63e3359708f8 () Term)
(declare-fun FStar.Pervasives.plugin@tok () Term)

; </end encoding FStar.Pervasives.plugin>


; <Start encoding FStar.Pervasives.tcnorm>

(declare-fun FStar.Pervasives.tcnorm (Dummy_sort) Term)

; </end encoding FStar.Pervasives.tcnorm>


; <Start encoding FStar.Pervasives.must_erase_for_extraction>

(declare-fun FStar.Pervasives.must_erase_for_extraction (Dummy_sort) Term)

; </end encoding FStar.Pervasives.must_erase_for_extraction>


; <Start encoding FStar.Pervasives.dm4f_bind_range>

(declare-fun FStar.Pervasives.dm4f_bind_range (Dummy_sort) Term)

; </end encoding FStar.Pervasives.dm4f_bind_range>


; <Start encoding FStar.Pervasives.expect_failure>

(declare-fun FStar.Pervasives.expect_failure (Term) Term)
(declare-fun Tm_arrow_555d62757eeaf90340982fcdf25f6704 () Term)
(declare-fun FStar.Pervasives.expect_failure@tok () Term)

; </end encoding FStar.Pervasives.expect_failure>


; <Start encoding FStar.Pervasives.expect_lax_failure>

(declare-fun FStar.Pervasives.expect_lax_failure (Term) Term)

(declare-fun FStar.Pervasives.expect_lax_failure@tok () Term)

; </end encoding FStar.Pervasives.expect_lax_failure>


; <Start encoding FStar.Pervasives.tcdecltime>

(declare-fun FStar.Pervasives.tcdecltime (Dummy_sort) Term)

; </end encoding FStar.Pervasives.tcdecltime>


; <Start encoding FStar.Pervasives.assume_strictly_positive>

(declare-fun FStar.Pervasives.assume_strictly_positive (Dummy_sort) Term)

; </end encoding FStar.Pervasives.assume_strictly_positive>


; <Start encoding FStar.Pervasives.unifier_hint_injective>

(declare-fun FStar.Pervasives.unifier_hint_injective (Dummy_sort) Term)

; </end encoding FStar.Pervasives.unifier_hint_injective>


; <Start encoding FStar.Pervasives.normalize_term>

(declare-fun FStar.Pervasives.normalize_term (Term Term) Term)

(declare-fun FStar.Pervasives.normalize_term@tok () Term)

; </end encoding FStar.Pervasives.normalize_term>


; <Start encoding FStar.Pervasives.normalize>

(declare-fun FStar.Pervasives.normalize (Term) Term)

(declare-fun FStar.Pervasives.normalize@tok () Term)

; </end encoding FStar.Pervasives.normalize>


; <Start encoding FStar.Pervasives.norm_step>

(declare-fun FStar.Pervasives.norm_step () Term)

; </end encoding FStar.Pervasives.norm_step>


; <Start encoding FStar.Pervasives.simplify>

(declare-fun FStar.Pervasives.simplify (Dummy_sort) Term)

; </end encoding FStar.Pervasives.simplify>


; <Start encoding FStar.Pervasives.weak>

(declare-fun FStar.Pervasives.weak (Dummy_sort) Term)

; </end encoding FStar.Pervasives.weak>


; <Start encoding FStar.Pervasives.hnf>

(declare-fun FStar.Pervasives.hnf (Dummy_sort) Term)

; </end encoding FStar.Pervasives.hnf>


; <Start encoding FStar.Pervasives.primops>

(declare-fun FStar.Pervasives.primops (Dummy_sort) Term)

; </end encoding FStar.Pervasives.primops>


; <Start encoding FStar.Pervasives.delta>

(declare-fun FStar.Pervasives.delta (Dummy_sort) Term)

; </end encoding FStar.Pervasives.delta>


; <Start encoding FStar.Pervasives.zeta>

(declare-fun FStar.Pervasives.zeta (Dummy_sort) Term)

; </end encoding FStar.Pervasives.zeta>


; <Start encoding FStar.Pervasives.iota>

(declare-fun FStar.Pervasives.iota (Dummy_sort) Term)

; </end encoding FStar.Pervasives.iota>


; <Start encoding FStar.Pervasives.nbe>

(declare-fun FStar.Pervasives.nbe (Dummy_sort) Term)

; </end encoding FStar.Pervasives.nbe>


; <Start encoding FStar.Pervasives.reify_>

(declare-fun FStar.Pervasives.reify_ (Dummy_sort) Term)

; </end encoding FStar.Pervasives.reify_>


; <Start encoding FStar.Pervasives.delta_only>

(declare-fun FStar.Pervasives.delta_only (Term) Term)
(declare-fun Tm_arrow_f14a20345cd55ddda96b6c4cc49e05f1 () Term)
(declare-fun FStar.Pervasives.delta_only@tok () Term)

; </end encoding FStar.Pervasives.delta_only>


; <Start encoding FStar.Pervasives.delta_fully>

(declare-fun FStar.Pervasives.delta_fully (Term) Term)

(declare-fun FStar.Pervasives.delta_fully@tok () Term)

; </end encoding FStar.Pervasives.delta_fully>


; <Start encoding FStar.Pervasives.delta_attr>

(declare-fun FStar.Pervasives.delta_attr (Term) Term)

(declare-fun FStar.Pervasives.delta_attr@tok () Term)

; </end encoding FStar.Pervasives.delta_attr>


; <Start encoding FStar.Pervasives.norm>

(declare-fun FStar.Pervasives.norm (Term Term Term) Term)
(declare-fun Tm_arrow_7d92e7a4aa7eee4098b10c5f1b3d77ea () Term)
(declare-fun FStar.Pervasives.norm@tok () Term)

; </end encoding FStar.Pervasives.norm>


; <Start encoding FStar.Pervasives.assert_norm>

(declare-fun FStar.Pervasives.assert_norm (Term) Term)

(declare-fun Tm_arrow_ee24fcf624d074d3c637ee61e4a867fb () Term)
(declare-fun FStar.Pervasives.assert_norm@tok () Term)


; </end encoding FStar.Pervasives.assert_norm>


; <Start encoding FStar.Pervasives.normalize_term_spec>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.Pervasives.normalize_term_spec (Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.Pervasives.normalize_term_spec@tok () Term)

; </end encoding FStar.Pervasives.normalize_term_spec>


; <Start encoding FStar.Pervasives.normalize_spec>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.Pervasives.normalize_spec (Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.Pervasives.normalize_spec@tok () Term)

; </end encoding FStar.Pervasives.normalize_spec>


; <Start encoding FStar.Pervasives.norm_spec>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.Pervasives.norm_spec (Term Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.Pervasives.norm_spec@tok () Term)

; </end encoding FStar.Pervasives.norm_spec>


; <Start encoding FStar.Pervasives.reveal_opaque>

(declare-fun FStar.Pervasives.reveal_opaque (Term Term) Term)
(declare-fun Tm_refine_9cce35912d99bf51042f02fff62b6cf5 (Term Term Term) Term)
(declare-fun Tm_arrow_90324bd6d0db52152d012eefdf7852a1 (Term Term) Term)
(declare-fun Tm_arrow_d3acaf108460ddc930424dea55f7d40f () Term)
(declare-fun FStar.Pervasives.reveal_opaque@tok () Term)


;;;;;;;;;;;;;;;;kick_partial_app
;;; Fact-ids: Name FStar.Pervasives.reveal_opaque; Namespace FStar.Pervasives
(assert (! (Valid (ApplyTT __uu__PartialApp
FStar.Pervasives.norm_spec@tok))
:named @kick_partial_app_e5c933a9bc2cb06571c2abdcc101b877))

; </end encoding FStar.Pervasives.reveal_opaque>


; <Start encoding FStar.Pervasives.singleton>

(declare-fun FStar.Pervasives.singleton (Term Term) Term)
(declare-fun Tm_refine_2fbd657fe85bcb2423f9c7e5f9b3bcb5 (Term Term) Term)
(declare-fun Tm_arrow_9cdb4ebd85da757e86217b6fb07ef9fc () Term)
(declare-fun FStar.Pervasives.singleton@tok () Term)


; </end encoding FStar.Pervasives.singleton>


; <Start encoding FStar.Pervasives.with_type>

(declare-fun FStar.Pervasives.with_type (Term Term) Term)

(declare-fun FStar.Pervasives.with_type@tok () Term)
;;;;;;;;;;;;;;;;with_type primitive axiom
;;; Fact-ids: Name FStar.Pervasives.with_type; Namespace FStar.Pervasives
(assert (! (forall ((@x0 Term) (@x1 Term))
 (! (and (= (FStar.Pervasives.with_type @x0
@x1)
@x1)
(HasType (FStar.Pervasives.with_type @x0
@x1)
@x0))
 :weight 0


:pattern ((FStar.Pervasives.with_type @x0
@x1))
:qid @with_type_primitive_axiom))
:named @with_type_primitive_axiom))

; </end encoding FStar.Pervasives.with_type>


; UNSAT CORE: @MaxFuel_assumption, @MaxIFuel_assumption, @fuel_correspondence_Prims.pow2.fuel_instrumented, @query, constructor_distinct_Lib.IntTypes.S16, constructor_distinct_Lib.IntTypes.S32, constructor_distinct_Lib.IntTypes.SEC, equality_tok_Lib.IntTypes.S16@tok, equality_tok_Lib.IntTypes.S32@tok, equality_tok_Lib.IntTypes.SEC@tok, equation_Lib.IntTypes.bits, equation_Lib.IntTypes.range, equation_Lib.IntTypes.signed, equation_Lib.IntTypes.unsigned, equation_Lib.IntTypes.v, equation_Prims.nat, equation_Prims.pos, equation_Spec.Kyber2.Params.params_q, int_inversion, int_typing, lemma_FStar.UInt.pow2_values, primitive_Prims.op_Addition, primitive_Prims.op_Division, primitive_Prims.op_LessThanOrEqual, primitive_Prims.op_Minus, primitive_Prims.op_Multiply, primitive_Prims.op_Subtraction, projection_inverse_BoxBool_proj_0, projection_inverse_BoxInt_proj_0, refinement_interpretation_Tm_refine_2b320913041b873fce938dd17eebb3e2, refinement_interpretation_Tm_refine_542f9d4f129664613f2483a6c88bc7c2, refinement_interpretation_Tm_refine_774ba3f728d91ead8ef40be66c9802e5, refinement_interpretation_Tm_refine_83845a86f2550cdf941eeb1d9b59602b, refinement_interpretation_Tm_refine_9d3fd79fd314167f1a9c213a188da3ec, refinement_interpretation_Tm_refine_b2401a8cabe2f9a01538f32548fa9f6c, typing_Lib.IntTypes.mk_int, typing_Prims.pow2, typing_tok_Lib.IntTypes.S32@tok, typing_tok_Lib.IntTypes.SEC@tok

;;; End module FStar.Pervasives (1050 decls; total size 59718)

;;; Start module FStar.Mul

; <Start encoding FStar.Mul.op_Star>

(declare-fun FStar.Mul.op_Star (Term Term) Term)

(declare-fun FStar.Mul.op_Star@tok () Term)

; </end encoding FStar.Mul.op_Star>


; UNSAT CORE: @MaxFuel_assumption, @MaxIFuel_assumption, @fuel_correspondence_Prims.pow2.fuel_instrumented, @query, constructor_distinct_Lib.IntTypes.S16, constructor_distinct_Lib.IntTypes.S32, constructor_distinct_Lib.IntTypes.SEC, equality_tok_Lib.IntTypes.S16@tok, equality_tok_Lib.IntTypes.S32@tok, equality_tok_Lib.IntTypes.SEC@tok, equation_Lib.IntTypes.bits, equation_Lib.IntTypes.range, equation_Lib.IntTypes.signed, equation_Lib.IntTypes.unsigned, equation_Lib.IntTypes.v, equation_Prims.nat, equation_Prims.pos, equation_Spec.Kyber2.Params.params_q, int_inversion, int_typing, lemma_FStar.UInt.pow2_values, primitive_Prims.op_Addition, primitive_Prims.op_Division, primitive_Prims.op_LessThanOrEqual, primitive_Prims.op_Minus, primitive_Prims.op_Multiply, primitive_Prims.op_Subtraction, projection_inverse_BoxBool_proj_0, projection_inverse_BoxInt_proj_0, refinement_interpretation_Tm_refine_2b320913041b873fce938dd17eebb3e2, refinement_interpretation_Tm_refine_542f9d4f129664613f2483a6c88bc7c2, refinement_interpretation_Tm_refine_774ba3f728d91ead8ef40be66c9802e5, refinement_interpretation_Tm_refine_83845a86f2550cdf941eeb1d9b59602b, refinement_interpretation_Tm_refine_9d3fd79fd314167f1a9c213a188da3ec, refinement_interpretation_Tm_refine_b2401a8cabe2f9a01538f32548fa9f6c, typing_Lib.IntTypes.mk_int, typing_Prims.pow2, typing_tok_Lib.IntTypes.S32@tok, typing_tok_Lib.IntTypes.SEC@tok

;;; End module FStar.Mul (6 decls; total size 1571)

;;; Start module FStar.Preorder

; <Start encoding FStar.Preorder.relation>

(declare-fun FStar.Preorder.relation (Term) Term)

(declare-fun FStar.Preorder.relation@tok () Term)
(declare-fun Tm_arrow_a19f9d49348d4e0038f0ded87d87802f (Term) Term)

; </end encoding FStar.Preorder.relation>


; <Start encoding FStar.Preorder.predicate>

(declare-fun FStar.Preorder.predicate (Term) Term)

(declare-fun FStar.Preorder.predicate@tok () Term)


; </end encoding FStar.Preorder.predicate>


; <Start encoding FStar.Preorder.reflexive>

(declare-fun FStar.Preorder.reflexive (Term Term) Term)
(declare-fun Tm_arrow_8e677a33afbeb812aa3779b7bdd0131c () Term)
(declare-fun FStar.Preorder.reflexive@tok () Term)

; </end encoding FStar.Preorder.reflexive>


; <Start encoding FStar.Preorder.transitive>

(declare-fun FStar.Preorder.transitive (Term Term) Term)

(declare-fun FStar.Preorder.transitive@tok () Term)

; </end encoding FStar.Preorder.transitive>


; <Start encoding FStar.Preorder.preorder_rel>

(declare-fun FStar.Preorder.preorder_rel (Term Term) Term)

(declare-fun FStar.Preorder.preorder_rel@tok () Term)

; </end encoding FStar.Preorder.preorder_rel>


; <Start encoding FStar.Preorder.preorder>

(declare-fun FStar.Preorder.preorder (Term) Term)

(declare-fun FStar.Preorder.preorder@tok () Term)
(declare-fun Tm_refine_bd10f09297e0e7dc08314f7d9211801c (Term) Term)

; </end encoding FStar.Preorder.preorder>


; <Start encoding FStar.Preorder.stable>


(declare-fun FStar.Preorder.stable (Term Term Term) Term)

(declare-fun Tm_arrow_88036d0811eee3361efd6229bae2556d () Term)
(declare-fun FStar.Preorder.stable@tok () Term)


; </end encoding FStar.Preorder.stable>


; UNSAT CORE: @MaxFuel_assumption, @MaxIFuel_assumption, @fuel_correspondence_Prims.pow2.fuel_instrumented, @query, constructor_distinct_Lib.IntTypes.S16, constructor_distinct_Lib.IntTypes.S32, constructor_distinct_Lib.IntTypes.SEC, equality_tok_Lib.IntTypes.S16@tok, equality_tok_Lib.IntTypes.S32@tok, equality_tok_Lib.IntTypes.SEC@tok, equation_Lib.IntTypes.bits, equation_Lib.IntTypes.range, equation_Lib.IntTypes.signed, equation_Lib.IntTypes.unsigned, equation_Lib.IntTypes.v, equation_Prims.nat, equation_Prims.pos, equation_Spec.Kyber2.Params.params_q, int_inversion, int_typing, lemma_FStar.UInt.pow2_values, primitive_Prims.op_Addition, primitive_Prims.op_Division, primitive_Prims.op_LessThanOrEqual, primitive_Prims.op_Minus, primitive_Prims.op_Multiply, primitive_Prims.op_Subtraction, projection_inverse_BoxBool_proj_0, projection_inverse_BoxInt_proj_0, refinement_interpretation_Tm_refine_2b320913041b873fce938dd17eebb3e2, refinement_interpretation_Tm_refine_542f9d4f129664613f2483a6c88bc7c2, refinement_interpretation_Tm_refine_774ba3f728d91ead8ef40be66c9802e5, refinement_interpretation_Tm_refine_83845a86f2550cdf941eeb1d9b59602b, refinement_interpretation_Tm_refine_9d3fd79fd314167f1a9c213a188da3ec, refinement_interpretation_Tm_refine_b2401a8cabe2f9a01538f32548fa9f6c, typing_Lib.IntTypes.mk_int, typing_Prims.pow2, typing_tok_Lib.IntTypes.S32@tok, typing_tok_Lib.IntTypes.SEC@tok

;;; End module FStar.Preorder (42 decls; total size 3046)

;;; Start module FStar.Calc

; <Start encoding >

;;;;;;;;;;;;;;;;Constructor
(declare-fun FStar.Calc.calc_proof (Term Term Term Term) Term)
;;;;;;;;;;;;;;;;Projector
(declare-fun FStar.Calc.calc_proof@x0 (Term) Term)
;;;;;;;;;;;;;;;;Projector
(declare-fun FStar.Calc.calc_proof@x1 (Term) Term)
;;;;;;;;;;;;;;;;Projector
(declare-fun FStar.Calc.calc_proof@x2 (Term) Term)
;;;;;;;;;;;;;;;;Projector
(declare-fun FStar.Calc.calc_proof@x3 (Term) Term)
;;;;;;;;;;;;;;;;token
(declare-fun FStar.Calc.calc_proof@tok () Term)
;;;;;;;;;;;;;;;;Constructor
(declare-fun FStar.Calc.CalcRefl (Term Term) Term)
;;;;;;;;;;;;;;;;Projector
(declare-fun FStar.Calc.CalcRefl_t (Term) Term)
;;;;;;;;;;;;;;;;Projector
(declare-fun FStar.Calc.CalcRefl_x (Term) Term)
;;;;;;;;;;;;;;;;data constructor proxy: CalcRefl
(declare-fun FStar.Calc.CalcRefl@tok () Term)
;;;;;;;;;;;;;;;;Constructor
(declare-fun FStar.Calc.CalcStep (Term Term Term Term Term Term Term Term) Term)
;;;;;;;;;;;;;;;;Projector
(declare-fun FStar.Calc.CalcStep_t (Term) Term)
;;;;;;;;;;;;;;;;Projector
(declare-fun FStar.Calc.CalcStep_rs (Term) Term)
;;;;;;;;;;;;;;;;Projector
(declare-fun FStar.Calc.CalcStep_p (Term) Term)
;;;;;;;;;;;;;;;;Projector
(declare-fun FStar.Calc.CalcStep_x (Term) Term)
;;;;;;;;;;;;;;;;Projector
(declare-fun FStar.Calc.CalcStep_y (Term) Term)
;;;;;;;;;;;;;;;;Projector
(declare-fun FStar.Calc.CalcStep_z (Term) Term)
;;;;;;;;;;;;;;;;Projector
(declare-fun FStar.Calc.CalcStep__5 (Term) Term)
;;;;;;;;;;;;;;;;Projector
(declare-fun FStar.Calc.CalcStep__6 (Term) Term)
;;;;;;;;;;;;;;;;data constructor proxy: CalcStep
(declare-fun FStar.Calc.CalcStep@tok () Term)
(declare-fun Tm_arrow_e85dbe2d578edd2a2a61107bad64844c () Term)
(declare-fun Tm_arrow_b340ecb8383074bc46375a46145a7603 () Term)

; <Start encoding FStar.Calc.calc_proof>


; <start constructor FStar.Calc.calc_proof>

;;;;;;;;;;;;;;;;Discriminator definition
(define-fun is-FStar.Calc.calc_proof ((__@x0 Term)) Bool
 (and (= (Term_constr_id __@x0)
101)
(exists ((@x0 Term) (@x1 Term) (@x2 Term) (@x3 Term))
 (! (= __@x0
(FStar.Calc.calc_proof @x0
@x1
@x2
@x3))
 
;;no pats
:qid is-FStar.Calc.calc_proof))))

; </end constructor FStar.Calc.calc_proof>


; </end encoding FStar.Calc.calc_proof>


; <Start encoding FStar.Calc.CalcRefl>


; <start constructor FStar.Calc.CalcRefl>

;;;;;;;;;;;;;;;;Discriminator definition
(define-fun is-FStar.Calc.CalcRefl ((__@x0 Term)) Bool
 (and (= (Term_constr_id __@x0)
108)
(= __@x0
(FStar.Calc.CalcRefl (FStar.Calc.CalcRefl_t __@x0)
(FStar.Calc.CalcRefl_x __@x0)))))

; </end constructor FStar.Calc.CalcRefl>


; </end encoding FStar.Calc.CalcRefl>


; <Start encoding FStar.Calc.CalcStep>


; <start constructor FStar.Calc.CalcStep>

;;;;;;;;;;;;;;;;Discriminator definition
(define-fun is-FStar.Calc.CalcStep ((__@x0 Term)) Bool
 (and (= (Term_constr_id __@x0)
113)
(= __@x0
(FStar.Calc.CalcStep (FStar.Calc.CalcStep_t __@x0)
(FStar.Calc.CalcStep_rs __@x0)
(FStar.Calc.CalcStep_p __@x0)
(FStar.Calc.CalcStep_x __@x0)
(FStar.Calc.CalcStep_y __@x0)
(FStar.Calc.CalcStep_z __@x0)
(FStar.Calc.CalcStep__5 __@x0)
(FStar.Calc.CalcStep__6 __@x0)))))

; </end constructor FStar.Calc.CalcStep>


; </end encoding FStar.Calc.CalcStep>


; </end encoding >


; <Start encoding FStar.Calc.uu___is_CalcRefl>

(declare-fun FStar.Calc.uu___is_CalcRefl (Term Term Term Term Term) Term)
(declare-fun Tm_arrow_4137fd252e343de6e82922409404f02e () Term)
(declare-fun FStar.Calc.uu___is_CalcRefl@tok () Term)

; </end encoding FStar.Calc.uu___is_CalcRefl>


; <Skipped FStar.Calc.uu___is_CalcRefl/>


; <Start encoding FStar.Calc.__proj__CalcRefl__item__x>

(declare-fun Tm_refine_3b368c069648e8b27d83e18e9c122613 (Term Term Term Term) Term)
(declare-fun FStar.Calc.__proj__CalcRefl__item__x (Term Term Term Term Term) Term)

(declare-fun Tm_arrow_2cd208e10700fce02c13ab45b8ec22d1 () Term)
(declare-fun FStar.Calc.__proj__CalcRefl__item__x@tok () Term)

; </end encoding FStar.Calc.__proj__CalcRefl__item__x>


; <Skipped FStar.Calc.__proj__CalcRefl__item__x/>


; <Start encoding FStar.Calc.uu___is_CalcStep>

(declare-fun FStar.Calc.uu___is_CalcStep (Term Term Term Term Term) Term)

(declare-fun FStar.Calc.uu___is_CalcStep@tok () Term)

; </end encoding FStar.Calc.uu___is_CalcStep>


; <Skipped FStar.Calc.uu___is_CalcStep/>


; <Start encoding FStar.Calc.__proj__CalcStep__item__rs>

(declare-fun Tm_refine_4d2c352ec2a69453fd30fa2907779c8a (Term Term Term Term) Term)
(declare-fun FStar.Calc.__proj__CalcStep__item__rs (Term Term Term Term Term) Term)

(declare-fun Tm_arrow_4cf1c767ce599aeb9039370e57e3788e () Term)
(declare-fun FStar.Calc.__proj__CalcStep__item__rs@tok () Term)

; </end encoding FStar.Calc.__proj__CalcStep__item__rs>


; <Skipped FStar.Calc.__proj__CalcStep__item__rs/>


; <Start encoding FStar.Calc.__proj__CalcStep__item__p>


(declare-fun FStar.Calc.__proj__CalcStep__item__p (Term Term Term Term Term) Term)

(declare-fun Tm_arrow_b1e217e71bf6b687ca1506b780d4a748 () Term)
(declare-fun FStar.Calc.__proj__CalcStep__item__p@tok () Term)

; </end encoding FStar.Calc.__proj__CalcStep__item__p>


; <Skipped FStar.Calc.__proj__CalcStep__item__p/>


; <Start encoding FStar.Calc.__proj__CalcStep__item__x>


(declare-fun FStar.Calc.__proj__CalcStep__item__x (Term Term Term Term Term) Term)

(declare-fun Tm_arrow_6422593e91fed2dd4662ca0ddd49333f () Term)
(declare-fun FStar.Calc.__proj__CalcStep__item__x@tok () Term)

; </end encoding FStar.Calc.__proj__CalcStep__item__x>


; <Skipped FStar.Calc.__proj__CalcStep__item__x/>


; <Start encoding FStar.Calc.__proj__CalcStep__item__y>


(declare-fun FStar.Calc.__proj__CalcStep__item__y (Term Term Term Term Term) Term)


(declare-fun FStar.Calc.__proj__CalcStep__item__y@tok () Term)

; </end encoding FStar.Calc.__proj__CalcStep__item__y>


; <Skipped FStar.Calc.__proj__CalcStep__item__y/>


; <Start encoding FStar.Calc.__proj__CalcStep__item__z>


(declare-fun FStar.Calc.__proj__CalcStep__item__z (Term Term Term Term Term) Term)


(declare-fun FStar.Calc.__proj__CalcStep__item__z@tok () Term)

; </end encoding FStar.Calc.__proj__CalcStep__item__z>


; <Skipped FStar.Calc.__proj__CalcStep__item__z/>


; <Start encoding FStar.Calc.__proj__CalcStep__item___5>


(declare-fun FStar.Calc.__proj__CalcStep__item___5 (Term Term Term Term Term) Term)

(declare-fun Tm_arrow_d7049dfa77ce1d01d6c309530bcb86bd () Term)
(declare-fun FStar.Calc.__proj__CalcStep__item___5@tok () Term)

; </end encoding FStar.Calc.__proj__CalcStep__item___5>


; <Skipped FStar.Calc.__proj__CalcStep__item___5/>


; <Start encoding FStar.Calc.__proj__CalcStep__item___6>


(declare-fun FStar.Calc.__proj__CalcStep__item___6 (Term Term Term Term Term) Term)

;;;;;;;;;;;;;;;;kick_partial_app
;;; Fact-ids: Name FStar.Calc.__proj__CalcStep__item___6; Namespace FStar.Calc
(assert (! (Valid (ApplyTT __uu__PartialApp
FStar.Calc.__proj__CalcStep__item__p@tok))
:named @kick_partial_app_7e770844f3d19b99fd09de14d699dd47))
(declare-fun Tm_arrow_fc94a5c321c3df1500a9e8101a4f81de () Term)
(declare-fun FStar.Calc.__proj__CalcStep__item___6@tok () Term)


; </end encoding FStar.Calc.__proj__CalcStep__item___6>


; <Skipped FStar.Calc.__proj__CalcStep__item___6/>


; <Start encoding >

;;;;;;;;;;;;;;;;Constructor
(declare-fun FStar.Calc.calc_pack (Term Term Term) Term)
;;;;;;;;;;;;;;;;Projector
(declare-fun FStar.Calc.calc_pack@x0 (Term) Term)
;;;;;;;;;;;;;;;;Projector
(declare-fun FStar.Calc.calc_pack@x1 (Term) Term)
;;;;;;;;;;;;;;;;Projector
(declare-fun FStar.Calc.calc_pack@x2 (Term) Term)
;;;;;;;;;;;;;;;;token
(declare-fun FStar.Calc.calc_pack@tok () Term)
;;;;;;;;;;;;;;;;Constructor
(declare-fun FStar.Calc.Mkcalc_pack (Term Term Term Term Term) Term)
;;;;;;;;;;;;;;;;Projector
(declare-fun FStar.Calc.Mkcalc_pack_t (Term) Term)
;;;;;;;;;;;;;;;;Projector
(declare-fun FStar.Calc.Mkcalc_pack_x (Term) Term)
;;;;;;;;;;;;;;;;Projector
(declare-fun FStar.Calc.Mkcalc_pack_y (Term) Term)
;;;;;;;;;;;;;;;;Projector
(declare-fun FStar.Calc.Mkcalc_pack_rels (Term) Term)
;;;;;;;;;;;;;;;;Projector
(declare-fun FStar.Calc.Mkcalc_pack_proof (Term) Term)
;;;;;;;;;;;;;;;;data constructor proxy: Mkcalc_pack
(declare-fun FStar.Calc.Mkcalc_pack@tok () Term)
(declare-fun Tm_arrow_08dbb649c69d20f068597726626c6790 () Term)

; <Start encoding FStar.Calc.calc_pack>


; <start constructor FStar.Calc.calc_pack>

;;;;;;;;;;;;;;;;Discriminator definition
(define-fun is-FStar.Calc.calc_pack ((__@x0 Term)) Bool
 (and (= (Term_constr_id __@x0)
153)
(exists ((@x0 Term) (@x1 Term) (@x2 Term))
 (! (= __@x0
(FStar.Calc.calc_pack @x0
@x1
@x2))
 
;;no pats
:qid is-FStar.Calc.calc_pack))))

; </end constructor FStar.Calc.calc_pack>


; </end encoding FStar.Calc.calc_pack>


; <Start encoding FStar.Calc.Mkcalc_pack>


; <start constructor FStar.Calc.Mkcalc_pack>

;;;;;;;;;;;;;;;;Discriminator definition
(define-fun is-FStar.Calc.Mkcalc_pack ((__@x0 Term)) Bool
 (and (= (Term_constr_id __@x0)
160)
(= __@x0
(FStar.Calc.Mkcalc_pack (FStar.Calc.Mkcalc_pack_t __@x0)
(FStar.Calc.Mkcalc_pack_x __@x0)
(FStar.Calc.Mkcalc_pack_y __@x0)
(FStar.Calc.Mkcalc_pack_rels __@x0)
(FStar.Calc.Mkcalc_pack_proof __@x0)))))

; </end constructor FStar.Calc.Mkcalc_pack>


; </end encoding FStar.Calc.Mkcalc_pack>


; </end encoding >


; <Start encoding FStar.Calc.__proj__Mkcalc_pack__item__rels>

(declare-fun FStar.Calc.__proj__Mkcalc_pack__item__rels (Term Term Term Term) Term)
(declare-fun Tm_arrow_5b177b9d78b0cb599bb4b2c2ce18d878 () Term)
(declare-fun FStar.Calc.__proj__Mkcalc_pack__item__rels@tok () Term)

; </end encoding FStar.Calc.__proj__Mkcalc_pack__item__rels>


; <Skipped FStar.Calc.__proj__Mkcalc_pack__item__rels/>


; <Start encoding FStar.Calc.__proj__Mkcalc_pack__item__proof>

(declare-fun FStar.Calc.__proj__Mkcalc_pack__item__proof (Term Term Term Term) Term)
(declare-fun Tm_arrow_b6aae2dbdc7a690f7b3896c459e1cdc8 () Term)
(declare-fun FStar.Calc.__proj__Mkcalc_pack__item__proof@tok () Term)

; </end encoding FStar.Calc.__proj__Mkcalc_pack__item__proof>


; <Skipped FStar.Calc.__proj__Mkcalc_pack__item__proof/>


; <Start encoding FStar.Calc.pk_rels>

(declare-fun FStar.Calc.pk_rels (Term Term Term Term) Term)

(declare-fun FStar.Calc.pk_rels@tok () Term)

; </end encoding FStar.Calc.pk_rels>


; <Start encoding FStar.Calc.calc_chain_related>

;;;;;;;;;;;;;;;;Fuel-instrumented function name
(declare-fun FStar.Calc.calc_chain_related.fuel_instrumented (Fuel Term Term Term Term) Term)
;;;;;;;;;;;;;;;;Token for fuel-instrumented partial applications
(declare-fun FStar.Calc.calc_chain_related.fuel_instrumented_token () Term)
(declare-fun FStar.Calc.calc_chain_related (Term Term Term Term) Term)
(declare-fun FStar.Calc.calc_chain_related@tok () Term)

(declare-fun Tm_abs_7586508c09a323b289f361c85bf3dee3 (Fuel Term Term Term Term) Term)
(declare-fun Tm_arrow_10ae2c328e1918eb5ddde4274ac6d32a () Term)
;;;;;;;;;;;;;;;;Fuel irrelevance
;;; Fact-ids: Name FStar.Calc.calc_chain_related; Namespace FStar.Calc
(assert (! 
;; def=FStar.Calc.fst(20,8-20,26); use=FStar.Calc.fst(20,8-20,26)
(forall ((@u0 Fuel) (@x1 Term) (@x2 Term) (@x3 Term) (@x4 Term))
 (! (= (FStar.Calc.calc_chain_related.fuel_instrumented (SFuel @u0)
@x1
@x2
@x3
@x4)
(FStar.Calc.calc_chain_related.fuel_instrumented ZFuel
@x1
@x2
@x3
@x4))
 

:pattern ((FStar.Calc.calc_chain_related.fuel_instrumented (SFuel @u0)
@x1
@x2
@x3
@x4))
:qid @fuel_irrelevance_FStar.Calc.calc_chain_related.fuel_instrumented))

:named @fuel_irrelevance_FStar.Calc.calc_chain_related.fuel_instrumented))
;;;;;;;;;;;;;;;;Correspondence of recursive function to instrumented version
;;; Fact-ids: Name FStar.Calc.calc_chain_related; Namespace FStar.Calc
(assert (! 
;; def=FStar.Calc.fst(20,8-20,26); use=FStar.Calc.fst(20,8-20,26)
(forall ((@x0 Term) (@x1 Term) (@x2 Term) (@x3 Term))
 (! (= (FStar.Calc.calc_chain_related @x0
@x1
@x2
@x3)
(FStar.Calc.calc_chain_related.fuel_instrumented MaxFuel
@x0
@x1
@x2
@x3))
 

:pattern ((FStar.Calc.calc_chain_related @x0
@x1
@x2
@x3))
:qid @fuel_correspondence_FStar.Calc.calc_chain_related.fuel_instrumented))

:named @fuel_correspondence_FStar.Calc.calc_chain_related.fuel_instrumented))

; </end encoding FStar.Calc.calc_chain_related>


; <Start encoding FStar.Calc.calc_chain_compatible>

(declare-fun FStar.Calc.calc_chain_compatible (Term Term Term) Term)
(declare-fun Tm_arrow_5d25af94b872513cc464e94bbc6a8348 () Term)
(declare-fun FStar.Calc.calc_chain_compatible@tok () Term)

; </end encoding FStar.Calc.calc_chain_compatible>


; <Start encoding FStar.Calc.elim_calc_proof>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.Calc.elim_calc_proof (Term Term Term Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.Calc.elim_calc_proof@tok () Term)

; </end encoding FStar.Calc.elim_calc_proof>


; <Start encoding FStar.Calc._calc_init>

(declare-fun FStar.Calc._calc_init (Term Term) Term)

(declare-fun FStar.Calc._calc_init@tok () Term)

; </end encoding FStar.Calc._calc_init>


; <Start encoding FStar.Calc.calc_init>

(declare-fun FStar.Calc.calc_init (Term Term) Term)
(declare-fun Tm_arrow_d5eb09a3cb5614e873db952aa4f080f8 () Term)
(declare-fun FStar.Calc.calc_init@tok () Term)

; </end encoding FStar.Calc.calc_init>


; <Start encoding FStar.Calc._calc_step>

(declare-fun Tm_ghost_arrow_43913ea96b2971b9b206329e4c86f5cd (Term Term Term Term) Term)
(declare-fun Tm_arrow_924fe8a596e8d1052263cdb50ea0b3f9 (Term Term Term) Term)
(declare-fun FStar.Calc._calc_step (Term Term Term Term Term Term Term Term) Term)


(declare-fun Tm_ghost_arrow_4628eb98823ce323ac10495fcebb4286 () Term)
(declare-fun FStar.Calc._calc_step@tok () Term)

; </end encoding FStar.Calc._calc_step>


; <Start encoding FStar.Calc.calc_step>

(declare-fun Tm_ghost_arrow_7b3b97c1ad4e8c34eea5d3c0f4f9fe1a (Term Term Term) Term)

(declare-fun FStar.Calc.calc_step (Term Term Term Term Term Term Term) Term)


(declare-fun Tm_ghost_arrow_9937c4de8dd72b95461da0c35d6c3aef () Term)
(declare-fun FStar.Calc.calc_step@tok () Term)

; </end encoding FStar.Calc.calc_step>


; <Start encoding FStar.Calc.calc_finish>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.Calc.calc_finish (Term Term Term Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.Calc.calc_finish@tok () Term)

; </end encoding FStar.Calc.calc_finish>


; UNSAT CORE: @MaxFuel_assumption, @MaxIFuel_assumption, @fuel_correspondence_Prims.pow2.fuel_instrumented, @query, constructor_distinct_Lib.IntTypes.S16, constructor_distinct_Lib.IntTypes.S32, constructor_distinct_Lib.IntTypes.SEC, equality_tok_Lib.IntTypes.S16@tok, equality_tok_Lib.IntTypes.S32@tok, equality_tok_Lib.IntTypes.SEC@tok, equation_Lib.IntTypes.bits, equation_Lib.IntTypes.range, equation_Lib.IntTypes.signed, equation_Lib.IntTypes.unsigned, equation_Lib.IntTypes.v, equation_Prims.nat, equation_Prims.pos, equation_Spec.Kyber2.Params.params_q, int_inversion, int_typing, lemma_FStar.UInt.pow2_values, primitive_Prims.op_Addition, primitive_Prims.op_Division, primitive_Prims.op_LessThanOrEqual, primitive_Prims.op_Minus, primitive_Prims.op_Multiply, primitive_Prims.op_Subtraction, projection_inverse_BoxBool_proj_0, projection_inverse_BoxInt_proj_0, refinement_interpretation_Tm_refine_2b320913041b873fce938dd17eebb3e2, refinement_interpretation_Tm_refine_542f9d4f129664613f2483a6c88bc7c2, refinement_interpretation_Tm_refine_774ba3f728d91ead8ef40be66c9802e5, refinement_interpretation_Tm_refine_83845a86f2550cdf941eeb1d9b59602b, refinement_interpretation_Tm_refine_9d3fd79fd314167f1a9c213a188da3ec, refinement_interpretation_Tm_refine_b2401a8cabe2f9a01538f32548fa9f6c, typing_Lib.IntTypes.mk_int, typing_Prims.pow2, typing_tok_Lib.IntTypes.S32@tok, typing_tok_Lib.IntTypes.SEC@tok

;;; End module FStar.Calc (212 decls; total size 15742)

;;; Start module FStar.Classical

; <Start encoding FStar.Classical.give_witness>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.Classical.give_witness (Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.Classical.give_witness@tok () Term)

; </end encoding FStar.Classical.give_witness>


; <Start encoding FStar.Classical.give_witness_from_squash>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.Classical.give_witness_from_squash (Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.Classical.give_witness_from_squash@tok () Term)

; </end encoding FStar.Classical.give_witness_from_squash>


; <Start encoding FStar.Classical.get_equality>

(declare-fun FStar.Classical.get_equality (Term Term Term) Term)
(declare-fun Tm_refine_7c805cbd5439f1b21f6463c70e57d0f1 (Term Term Term) Term)
(declare-fun Tm_arrow_158af926c0cd4bc1ff513e80f99f4b49 () Term)
(declare-fun FStar.Classical.get_equality@tok () Term)


; </end encoding FStar.Classical.get_equality>


; <Start encoding FStar.Classical.get_forall>


(declare-fun FStar.Classical.get_forall (Term Term) Term)


(declare-fun Tm_refine_0f449c9ea4caab5b78147dd10520e018 (Term Term) Term)
(declare-fun Tm_arrow_332381d0496c43c212786cc9f5d1c320 () Term)
(declare-fun FStar.Classical.get_forall@tok () Term)



; </end encoding FStar.Classical.get_forall>


; <Start encoding FStar.Classical.impl_to_arrow>

(declare-fun FStar.Classical.impl_to_arrow (Term Term Term Term) Term)
(declare-fun Tm_arrow_156c500bdf0e99cc45ffd26a33a603a8 () Term)
(declare-fun FStar.Classical.impl_to_arrow@tok () Term)

; </end encoding FStar.Classical.impl_to_arrow>


; <Start encoding FStar.Classical.arrow_to_impl>

(declare-fun Tm_arrow_9d84457d1c8d2a3cb1cecf47a390b833 (Term Term) Term)
(declare-fun FStar.Classical.arrow_to_impl (Term Term Term) Term)

(declare-fun Tm_arrow_78d787b8a2633e2185ded4267a81cc32 () Term)
(declare-fun FStar.Classical.arrow_to_impl@tok () Term)

; </end encoding FStar.Classical.arrow_to_impl>


; <Start encoding FStar.Classical.forall_intro_gtot>



(declare-fun FStar.Classical.forall_intro_gtot (Term Term Term) Term)



(declare-fun Tm_arrow_58139f503eb3f7da2e6d21fc5f91a24e () Term)
(declare-fun FStar.Classical.forall_intro_gtot@tok () Term)


; </end encoding FStar.Classical.forall_intro_gtot>


; <Start encoding FStar.Classical.lemma_forall_intro_gtot>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.Classical.lemma_forall_intro_gtot (Term Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.Classical.lemma_forall_intro_gtot@tok () Term)

; </end encoding FStar.Classical.lemma_forall_intro_gtot>


; <Start encoding FStar.Classical.gtot_to_lemma>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.Classical.gtot_to_lemma (Term Term Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.Classical.gtot_to_lemma@tok () Term)

; </end encoding FStar.Classical.gtot_to_lemma>


; <Start encoding FStar.Classical.lemma_to_squash_gtot>


(declare-fun Tm_refine_839524df17f415c122f40f00685d3fe6 (Term Term) Term)
(declare-fun Tm_arrow_9a028cfcf6111a85dd3c28d61b4efdfd (Term Term) Term)
(declare-fun FStar.Classical.lemma_to_squash_gtot (Term Term Term Term) Term)



(declare-fun Tm_arrow_6f9100982820dfbce0fb9c6dae0cee11 () Term)
(declare-fun FStar.Classical.lemma_to_squash_gtot@tok () Term)

; </end encoding FStar.Classical.lemma_to_squash_gtot>


; <Start encoding FStar.Classical.forall_intro_squash_gtot>


(declare-fun Tm_arrow_e44b1a1960e76c65248b9976ee453bf1 (Term Term) Term)
(declare-fun FStar.Classical.forall_intro_squash_gtot (Term Term Term) Term)



(declare-fun Tm_arrow_fc21ff1d7102ebdd3a285ec7e2205a73 () Term)
(declare-fun FStar.Classical.forall_intro_squash_gtot@tok () Term)


; </end encoding FStar.Classical.forall_intro_squash_gtot>


; <Start encoding FStar.Classical.forall_intro_squash_gtot_join>



(declare-fun FStar.Classical.forall_intro_squash_gtot_join (Term Term Term) Term)



(declare-fun Tm_arrow_063aaa309a45de0b15ba96f4b908f656 () Term)
(declare-fun FStar.Classical.forall_intro_squash_gtot_join@tok () Term)


; </end encoding FStar.Classical.forall_intro_squash_gtot_join>


; <Start encoding FStar.Classical.forall_intro>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.Classical.forall_intro (Term Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.Classical.forall_intro@tok () Term)

; </end encoding FStar.Classical.forall_intro>


; <Start encoding FStar.Classical.forall_intro_with_pat>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.Classical.forall_intro_with_pat (Term Term Term Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.Classical.forall_intro_with_pat@tok () Term)

; </end encoding FStar.Classical.forall_intro_with_pat>


; <Start encoding FStar.Classical.forall_intro_sub>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.Classical.forall_intro_sub (Term Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.Classical.forall_intro_sub@tok () Term)

; </end encoding FStar.Classical.forall_intro_sub>


; <Start encoding FStar.Classical.forall_intro_2>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.Classical.forall_intro_2 (Term Term Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.Classical.forall_intro_2@tok () Term)

; </end encoding FStar.Classical.forall_intro_2>


; <Start encoding FStar.Classical.forall_intro_2_with_pat>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.Classical.forall_intro_2_with_pat (Term Term Term Term Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.Classical.forall_intro_2_with_pat@tok () Term)

; </end encoding FStar.Classical.forall_intro_2_with_pat>


; <Start encoding FStar.Classical.forall_intro_3>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.Classical.forall_intro_3 (Term Term Term Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.Classical.forall_intro_3@tok () Term)

; </end encoding FStar.Classical.forall_intro_3>


; <Start encoding FStar.Classical.forall_intro_3_with_pat>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.Classical.forall_intro_3_with_pat (Term Term Term Term Term Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.Classical.forall_intro_3_with_pat@tok () Term)

; </end encoding FStar.Classical.forall_intro_3_with_pat>


; <Start encoding FStar.Classical.forall_intro_4>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.Classical.forall_intro_4 (Term Term Term Term Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.Classical.forall_intro_4@tok () Term)

; </end encoding FStar.Classical.forall_intro_4>


; <Start encoding FStar.Classical.exists_intro>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.Classical.exists_intro (Term Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.Classical.exists_intro@tok () Term)

; </end encoding FStar.Classical.exists_intro>


; <Start encoding FStar.Classical.forall_to_exists>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.Classical.forall_to_exists (Term Term Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.Classical.forall_to_exists@tok () Term)

; </end encoding FStar.Classical.forall_to_exists>


; <Start encoding FStar.Classical.forall_to_exists_2>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.Classical.forall_to_exists_2 (Term Term Term Term Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.Classical.forall_to_exists_2@tok () Term)

; </end encoding FStar.Classical.forall_to_exists_2>


; <Start encoding FStar.Classical.impl_intro_gtot>


(declare-fun FStar.Classical.impl_intro_gtot (Term Term Term) Term)

(declare-fun Tm_arrow_d2cdd2f18b92810e3048c35d07f1c9ea () Term)
(declare-fun FStar.Classical.impl_intro_gtot@tok () Term)

; </end encoding FStar.Classical.impl_intro_gtot>


; <Start encoding FStar.Classical.impl_intro>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.Classical.impl_intro (Term Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.Classical.impl_intro@tok () Term)

; </end encoding FStar.Classical.impl_intro>


; <Start encoding FStar.Classical.exists_elim>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.Classical.exists_elim (Term Term Term Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.Classical.exists_elim@tok () Term)

; </end encoding FStar.Classical.exists_elim>


; <Start encoding FStar.Classical.move_requires>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.Classical.move_requires (Term Term Term Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.Classical.move_requires@tok () Term)

; </end encoding FStar.Classical.move_requires>


; <Start encoding FStar.Classical.forall_impl_intro>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.Classical.forall_impl_intro (Term Term Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.Classical.forall_impl_intro@tok () Term)

; </end encoding FStar.Classical.forall_impl_intro>


; <Start encoding FStar.Classical.impl_intro_gen>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.Classical.impl_intro_gen (Term Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.Classical.impl_intro_gen@tok () Term)

; </end encoding FStar.Classical.impl_intro_gen>


; <Start encoding FStar.Classical.ghost_lemma>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.Classical.ghost_lemma (Term Term Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.Classical.ghost_lemma@tok () Term)

; </end encoding FStar.Classical.ghost_lemma>


; <Start encoding FStar.Classical.or_elim>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.Classical.or_elim (Term Term Term Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.Classical.or_elim@tok () Term)

; </end encoding FStar.Classical.or_elim>


; <Start encoding FStar.Classical.excluded_middle>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.Classical.excluded_middle (Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.Classical.excluded_middle@tok () Term)

; </end encoding FStar.Classical.excluded_middle>


; UNSAT CORE: @MaxFuel_assumption, @MaxIFuel_assumption, @fuel_correspondence_Prims.pow2.fuel_instrumented, @query, constructor_distinct_Lib.IntTypes.S16, constructor_distinct_Lib.IntTypes.S32, constructor_distinct_Lib.IntTypes.SEC, equality_tok_Lib.IntTypes.S16@tok, equality_tok_Lib.IntTypes.S32@tok, equality_tok_Lib.IntTypes.SEC@tok, equation_Lib.IntTypes.bits, equation_Lib.IntTypes.range, equation_Lib.IntTypes.signed, equation_Lib.IntTypes.unsigned, equation_Lib.IntTypes.v, equation_Prims.nat, equation_Prims.pos, equation_Spec.Kyber2.Params.params_q, int_inversion, int_typing, lemma_FStar.UInt.pow2_values, primitive_Prims.op_Addition, primitive_Prims.op_Division, primitive_Prims.op_LessThanOrEqual, primitive_Prims.op_Minus, primitive_Prims.op_Multiply, primitive_Prims.op_Subtraction, projection_inverse_BoxBool_proj_0, projection_inverse_BoxInt_proj_0, refinement_interpretation_Tm_refine_2b320913041b873fce938dd17eebb3e2, refinement_interpretation_Tm_refine_542f9d4f129664613f2483a6c88bc7c2, refinement_interpretation_Tm_refine_774ba3f728d91ead8ef40be66c9802e5, refinement_interpretation_Tm_refine_83845a86f2550cdf941eeb1d9b59602b, refinement_interpretation_Tm_refine_9d3fd79fd314167f1a9c213a188da3ec, refinement_interpretation_Tm_refine_b2401a8cabe2f9a01538f32548fa9f6c, typing_Lib.IntTypes.mk_int, typing_Prims.pow2, typing_tok_Lib.IntTypes.S32@tok, typing_tok_Lib.IntTypes.SEC@tok

;;; End module FStar.Classical (174 decls; total size 12856)

;;; Start module FStar.StrongExcludedMiddle

; <Start encoding FStar.StrongExcludedMiddle.strong_excluded_middle>

(declare-fun FStar.StrongExcludedMiddle.strong_excluded_middle (Term) Term)
(declare-fun Tm_refine_2c7ecebd8a41d0890aab4251b61d6458 (Term) Term)
(declare-fun Tm_ghost_arrow_13b822d9f45311e725609e40f68f39a1 () Term)
(declare-fun FStar.StrongExcludedMiddle.strong_excluded_middle@tok () Term)


; </end encoding FStar.StrongExcludedMiddle.strong_excluded_middle>


; UNSAT CORE: @MaxFuel_assumption, @MaxIFuel_assumption, @fuel_correspondence_Prims.pow2.fuel_instrumented, @query, constructor_distinct_Lib.IntTypes.S16, constructor_distinct_Lib.IntTypes.S32, constructor_distinct_Lib.IntTypes.SEC, equality_tok_Lib.IntTypes.S16@tok, equality_tok_Lib.IntTypes.S32@tok, equality_tok_Lib.IntTypes.SEC@tok, equation_Lib.IntTypes.bits, equation_Lib.IntTypes.range, equation_Lib.IntTypes.signed, equation_Lib.IntTypes.unsigned, equation_Lib.IntTypes.v, equation_Prims.nat, equation_Prims.pos, equation_Spec.Kyber2.Params.params_q, int_inversion, int_typing, lemma_FStar.UInt.pow2_values, primitive_Prims.op_Addition, primitive_Prims.op_Division, primitive_Prims.op_LessThanOrEqual, primitive_Prims.op_Minus, primitive_Prims.op_Multiply, primitive_Prims.op_Subtraction, projection_inverse_BoxBool_proj_0, projection_inverse_BoxInt_proj_0, refinement_interpretation_Tm_refine_2b320913041b873fce938dd17eebb3e2, refinement_interpretation_Tm_refine_542f9d4f129664613f2483a6c88bc7c2, refinement_interpretation_Tm_refine_774ba3f728d91ead8ef40be66c9802e5, refinement_interpretation_Tm_refine_83845a86f2550cdf941eeb1d9b59602b, refinement_interpretation_Tm_refine_9d3fd79fd314167f1a9c213a188da3ec, refinement_interpretation_Tm_refine_b2401a8cabe2f9a01538f32548fa9f6c, typing_Lib.IntTypes.mk_int, typing_Prims.pow2, typing_tok_Lib.IntTypes.S32@tok, typing_tok_Lib.IntTypes.SEC@tok

;;; End module FStar.StrongExcludedMiddle (8 decls; total size 1833)

;;; Start module FStar.FunctionalExtensionality

; <Skipped />


; <Start encoding FStar.FunctionalExtensionality.arrow>


(declare-fun FStar.FunctionalExtensionality.arrow (Term Term) Term)

(declare-fun Tm_arrow_28022b1931e0c9114f09925e8271570a () Term)
(declare-fun FStar.FunctionalExtensionality.arrow@tok () Term)

(declare-fun Tm_arrow_a7d5cc170be69663c495e8582d2bc62a (Term Term) Term)

; </end encoding FStar.FunctionalExtensionality.arrow>


; <Start encoding FStar.FunctionalExtensionality.efun>


(declare-fun FStar.FunctionalExtensionality.efun (Term Term) Term)


(declare-fun FStar.FunctionalExtensionality.efun@tok () Term)



; </end encoding FStar.FunctionalExtensionality.efun>


; <Start encoding FStar.FunctionalExtensionality.feq>




(declare-fun FStar.FunctionalExtensionality.feq (Term Term Term Term) Term)



(declare-fun Tm_arrow_a26edf208afb0682b12235c66ccbd71c () Term)
(declare-fun FStar.FunctionalExtensionality.feq@tok () Term)




; </end encoding FStar.FunctionalExtensionality.feq>


; <Start encoding FStar.FunctionalExtensionality.on_domain>



(declare-fun FStar.FunctionalExtensionality.on_domain (Term Term Term) Term)



(declare-fun Tm_arrow_4644eedc14c2df3e417da1b7c07108e6 () Term)
(declare-fun FStar.FunctionalExtensionality.on_domain@tok () Term)


; </end encoding FStar.FunctionalExtensionality.on_domain>


; <Start encoding FStar.FunctionalExtensionality.feq_on_domain>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.FunctionalExtensionality.feq_on_domain (Term Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.FunctionalExtensionality.feq_on_domain@tok () Term)



; </end encoding FStar.FunctionalExtensionality.feq_on_domain>


; <Start encoding FStar.FunctionalExtensionality.idempotence_on_domain>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.FunctionalExtensionality.idempotence_on_domain (Term Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.FunctionalExtensionality.idempotence_on_domain@tok () Term)



; </end encoding FStar.FunctionalExtensionality.idempotence_on_domain>


; <Start encoding FStar.FunctionalExtensionality.is_restricted>



(declare-fun FStar.FunctionalExtensionality.is_restricted (Term Term Term) Term)


(declare-fun Tm_arrow_b9e5e589ff6008bf9dc6c8ac06a76d9b () Term)
(declare-fun FStar.FunctionalExtensionality.is_restricted@tok () Term)



; </end encoding FStar.FunctionalExtensionality.is_restricted>


; <Start encoding FStar.FunctionalExtensionality.restricted_t>


(declare-fun FStar.FunctionalExtensionality.restricted_t (Term Term) Term)


(declare-fun FStar.FunctionalExtensionality.restricted_t@tok () Term)


(declare-fun Tm_refine_7e4a6c5999db731b5d17d0418dfeea3e (Term Term) Term)

; </end encoding FStar.FunctionalExtensionality.restricted_t>


; <Start encoding FStar.FunctionalExtensionality.op_Hat_Subtraction_Greater>

(declare-fun FStar.FunctionalExtensionality.op_Hat_Subtraction_Greater (Term Term) Term)

(declare-fun FStar.FunctionalExtensionality.op_Hat_Subtraction_Greater@tok () Term)

(declare-fun Tm_abs_134069e179ddf4705519081c391c4e10 (Term Term) Term)

; </end encoding FStar.FunctionalExtensionality.op_Hat_Subtraction_Greater>


; <Start encoding FStar.FunctionalExtensionality.on_dom>



(declare-fun FStar.FunctionalExtensionality.on_dom (Term Term Term) Term)


(declare-fun Tm_arrow_2c8a39c5d1179d9b2dbff37a928311ac () Term)
(declare-fun FStar.FunctionalExtensionality.on_dom@tok () Term)



; </end encoding FStar.FunctionalExtensionality.on_dom>


; <Start encoding FStar.FunctionalExtensionality.on>

(declare-fun Tm_arrow_6980332764c4493a7b0df5c02f7aefbe (Term Term) Term)
(declare-fun FStar.FunctionalExtensionality.on (Term Term Term) Term)



(declare-fun Tm_arrow_eab9bf17eb33be7efca62de21f27985c () Term)
(declare-fun FStar.FunctionalExtensionality.on@tok () Term)






; </end encoding FStar.FunctionalExtensionality.on>


; <Start encoding FStar.FunctionalExtensionality.extensionality>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.FunctionalExtensionality.extensionality (Term Term Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.FunctionalExtensionality.extensionality@tok () Term)




; </end encoding FStar.FunctionalExtensionality.extensionality>


; <Start encoding FStar.FunctionalExtensionality.arrow_g>


(declare-fun FStar.FunctionalExtensionality.arrow_g (Term Term) Term)


(declare-fun FStar.FunctionalExtensionality.arrow_g@tok () Term)



; </end encoding FStar.FunctionalExtensionality.arrow_g>


; <Start encoding FStar.FunctionalExtensionality.efun_g>


(declare-fun FStar.FunctionalExtensionality.efun_g (Term Term) Term)


(declare-fun FStar.FunctionalExtensionality.efun_g@tok () Term)



; </end encoding FStar.FunctionalExtensionality.efun_g>


; <Start encoding FStar.FunctionalExtensionality.feq_g>




(declare-fun FStar.FunctionalExtensionality.feq_g (Term Term Term Term) Term)



(declare-fun Tm_arrow_361ba84e60d273d78a5743d30c9dc908 () Term)
(declare-fun FStar.FunctionalExtensionality.feq_g@tok () Term)




; </end encoding FStar.FunctionalExtensionality.feq_g>


; <Start encoding FStar.FunctionalExtensionality.on_domain_g>



(declare-fun FStar.FunctionalExtensionality.on_domain_g (Term Term Term) Term)



(declare-fun Tm_arrow_bf6371335aea4d90f7963f85ebad8f0d () Term)
(declare-fun FStar.FunctionalExtensionality.on_domain_g@tok () Term)


; </end encoding FStar.FunctionalExtensionality.on_domain_g>


; <Start encoding FStar.FunctionalExtensionality.feq_on_domain_g>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.FunctionalExtensionality.feq_on_domain_g (Term Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.FunctionalExtensionality.feq_on_domain_g@tok () Term)



; </end encoding FStar.FunctionalExtensionality.feq_on_domain_g>


; <Start encoding FStar.FunctionalExtensionality.idempotence_on_domain_g>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.FunctionalExtensionality.idempotence_on_domain_g (Term Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.FunctionalExtensionality.idempotence_on_domain_g@tok () Term)



; </end encoding FStar.FunctionalExtensionality.idempotence_on_domain_g>


; <Start encoding FStar.FunctionalExtensionality.is_restricted_g>



(declare-fun FStar.FunctionalExtensionality.is_restricted_g (Term Term Term) Term)


(declare-fun Tm_arrow_eadb252d9886eeba4938e11c03ce9b79 () Term)
(declare-fun FStar.FunctionalExtensionality.is_restricted_g@tok () Term)



; </end encoding FStar.FunctionalExtensionality.is_restricted_g>


; <Start encoding FStar.FunctionalExtensionality.restricted_g_t>


(declare-fun FStar.FunctionalExtensionality.restricted_g_t (Term Term) Term)


(declare-fun FStar.FunctionalExtensionality.restricted_g_t@tok () Term)


(declare-fun Tm_refine_9185da06fca917c5514ae63042657873 (Term Term) Term)

; </end encoding FStar.FunctionalExtensionality.restricted_g_t>


; <Start encoding FStar.FunctionalExtensionality.op_Hat_Subtraction_Greater_Greater>

(declare-fun FStar.FunctionalExtensionality.op_Hat_Subtraction_Greater_Greater (Term Term) Term)

(declare-fun FStar.FunctionalExtensionality.op_Hat_Subtraction_Greater_Greater@tok () Term)



; </end encoding FStar.FunctionalExtensionality.op_Hat_Subtraction_Greater_Greater>


; <Start encoding FStar.FunctionalExtensionality.on_dom_g>



(declare-fun FStar.FunctionalExtensionality.on_dom_g (Term Term Term) Term)


(declare-fun Tm_arrow_2e3db44d1263cf9452aaa6907eac66cc () Term)
(declare-fun FStar.FunctionalExtensionality.on_dom_g@tok () Term)



; </end encoding FStar.FunctionalExtensionality.on_dom_g>


; <Start encoding FStar.FunctionalExtensionality.on_g>


(declare-fun FStar.FunctionalExtensionality.on_g (Term Term Term) Term)



(declare-fun Tm_arrow_93a363f6461271c3e18b18593d7d03bf () Term)
(declare-fun FStar.FunctionalExtensionality.on_g@tok () Term)






; </end encoding FStar.FunctionalExtensionality.on_g>


; <Start encoding FStar.FunctionalExtensionality.extensionality_g>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.FunctionalExtensionality.extensionality_g (Term Term Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.FunctionalExtensionality.extensionality_g@tok () Term)




; </end encoding FStar.FunctionalExtensionality.extensionality_g>


; UNSAT CORE: @MaxFuel_assumption, @MaxIFuel_assumption, @fuel_correspondence_Prims.pow2.fuel_instrumented, @query, constructor_distinct_Lib.IntTypes.S16, constructor_distinct_Lib.IntTypes.S32, constructor_distinct_Lib.IntTypes.SEC, equality_tok_Lib.IntTypes.S16@tok, equality_tok_Lib.IntTypes.S32@tok, equality_tok_Lib.IntTypes.SEC@tok, equation_Lib.IntTypes.bits, equation_Lib.IntTypes.range, equation_Lib.IntTypes.signed, equation_Lib.IntTypes.unsigned, equation_Lib.IntTypes.v, equation_Prims.nat, equation_Prims.pos, equation_Spec.Kyber2.Params.params_q, int_inversion, int_typing, lemma_FStar.UInt.pow2_values, primitive_Prims.op_Addition, primitive_Prims.op_Division, primitive_Prims.op_LessThanOrEqual, primitive_Prims.op_Minus, primitive_Prims.op_Multiply, primitive_Prims.op_Subtraction, projection_inverse_BoxBool_proj_0, projection_inverse_BoxInt_proj_0, refinement_interpretation_Tm_refine_2b320913041b873fce938dd17eebb3e2, refinement_interpretation_Tm_refine_542f9d4f129664613f2483a6c88bc7c2, refinement_interpretation_Tm_refine_774ba3f728d91ead8ef40be66c9802e5, refinement_interpretation_Tm_refine_83845a86f2550cdf941eeb1d9b59602b, refinement_interpretation_Tm_refine_9d3fd79fd314167f1a9c213a188da3ec, refinement_interpretation_Tm_refine_b2401a8cabe2f9a01538f32548fa9f6c, typing_Lib.IntTypes.mk_int, typing_Prims.pow2, typing_tok_Lib.IntTypes.S32@tok, typing_tok_Lib.IntTypes.SEC@tok

;;; End module FStar.FunctionalExtensionality (232 decls; total size 9997)

;;; Start module FStar.List.Tot.Base

; <Start encoding FStar.List.Tot.Base.isEmpty>

(declare-fun FStar.List.Tot.Base.isEmpty (Term Term) Term)

(declare-fun FStar.List.Tot.Base.isEmpty@tok () Term)

; </end encoding FStar.List.Tot.Base.isEmpty>


; <Start encoding FStar.List.Tot.Base.hd>


(declare-fun FStar.List.Tot.Base.hd (Term Term) Term)


(declare-fun FStar.List.Tot.Base.hd@tok () Term)


; </end encoding FStar.List.Tot.Base.hd>


; <Start encoding FStar.List.Tot.Base.tail>


(declare-fun FStar.List.Tot.Base.tail (Term Term) Term)


(declare-fun FStar.List.Tot.Base.tail@tok () Term)


; </end encoding FStar.List.Tot.Base.tail>


; <Start encoding FStar.List.Tot.Base.tl>


(declare-fun FStar.List.Tot.Base.tl (Term Term) Term)


(declare-fun FStar.List.Tot.Base.tl@tok () Term)


; </end encoding FStar.List.Tot.Base.tl>


; <Start encoding FStar.List.Tot.Base.last>

;;;;;;;;;;;;;;;;Fuel-instrumented function name
(declare-fun FStar.List.Tot.Base.last.fuel_instrumented (Fuel Term Term) Term)
;;;;;;;;;;;;;;;;Token for fuel-instrumented partial applications
(declare-fun FStar.List.Tot.Base.last.fuel_instrumented_token () Term)
(declare-fun FStar.List.Tot.Base.last (Term Term) Term)
(declare-fun FStar.List.Tot.Base.last@tok () Term)




;;;;;;;;;;;;;;;;Fuel irrelevance
;;; Fact-ids: Name FStar.List.Tot.Base.last; Namespace FStar.List.Tot.Base
(assert (! 
;; def=FStar.List.Tot.Base.fst(59,8-59,12); use=FStar.List.Tot.Base.fst(59,8-59,12)
(forall ((@u0 Fuel) (@x1 Term) (@x2 Term))
 (! (= (FStar.List.Tot.Base.last.fuel_instrumented (SFuel @u0)
@x1
@x2)
(FStar.List.Tot.Base.last.fuel_instrumented ZFuel
@x1
@x2))
 

:pattern ((FStar.List.Tot.Base.last.fuel_instrumented (SFuel @u0)
@x1
@x2))
:qid @fuel_irrelevance_FStar.List.Tot.Base.last.fuel_instrumented))

:named @fuel_irrelevance_FStar.List.Tot.Base.last.fuel_instrumented))
;;;;;;;;;;;;;;;;Correspondence of recursive function to instrumented version
;;; Fact-ids: Name FStar.List.Tot.Base.last; Namespace FStar.List.Tot.Base
(assert (! 
;; def=FStar.List.Tot.Base.fst(59,8-59,12); use=FStar.List.Tot.Base.fst(59,8-59,12)
(forall ((@x0 Term) (@x1 Term))
 (! (= (FStar.List.Tot.Base.last @x0
@x1)
(FStar.List.Tot.Base.last.fuel_instrumented MaxFuel
@x0
@x1))
 

:pattern ((FStar.List.Tot.Base.last @x0
@x1))
:qid @fuel_correspondence_FStar.List.Tot.Base.last.fuel_instrumented))

:named @fuel_correspondence_FStar.List.Tot.Base.last.fuel_instrumented))

; </end encoding FStar.List.Tot.Base.last>


; <Start encoding FStar.List.Tot.Base.init>

;;;;;;;;;;;;;;;;Fuel-instrumented function name
(declare-fun FStar.List.Tot.Base.init.fuel_instrumented (Fuel Term Term) Term)
;;;;;;;;;;;;;;;;Token for fuel-instrumented partial applications
(declare-fun FStar.List.Tot.Base.init.fuel_instrumented_token () Term)
(declare-fun FStar.List.Tot.Base.init (Term Term) Term)
(declare-fun FStar.List.Tot.Base.init@tok () Term)




;;;;;;;;;;;;;;;;Fuel irrelevance
;;; Fact-ids: Name FStar.List.Tot.Base.init; Namespace FStar.List.Tot.Base
(assert (! 
;; def=FStar.List.Tot.Base.fst(67,8-67,12); use=FStar.List.Tot.Base.fst(67,8-67,12)
(forall ((@u0 Fuel) (@x1 Term) (@x2 Term))
 (! (= (FStar.List.Tot.Base.init.fuel_instrumented (SFuel @u0)
@x1
@x2)
(FStar.List.Tot.Base.init.fuel_instrumented ZFuel
@x1
@x2))
 

:pattern ((FStar.List.Tot.Base.init.fuel_instrumented (SFuel @u0)
@x1
@x2))
:qid @fuel_irrelevance_FStar.List.Tot.Base.init.fuel_instrumented))

:named @fuel_irrelevance_FStar.List.Tot.Base.init.fuel_instrumented))
;;;;;;;;;;;;;;;;Correspondence of recursive function to instrumented version
;;; Fact-ids: Name FStar.List.Tot.Base.init; Namespace FStar.List.Tot.Base
(assert (! 
;; def=FStar.List.Tot.Base.fst(67,8-67,12); use=FStar.List.Tot.Base.fst(67,8-67,12)
(forall ((@x0 Term) (@x1 Term))
 (! (= (FStar.List.Tot.Base.init @x0
@x1)
(FStar.List.Tot.Base.init.fuel_instrumented MaxFuel
@x0
@x1))
 

:pattern ((FStar.List.Tot.Base.init @x0
@x1))
:qid @fuel_correspondence_FStar.List.Tot.Base.init.fuel_instrumented))

:named @fuel_correspondence_FStar.List.Tot.Base.init.fuel_instrumented))

; </end encoding FStar.List.Tot.Base.init>


; <Start encoding FStar.List.Tot.Base.length>

;;;;;;;;;;;;;;;;Fuel-instrumented function name
(declare-fun FStar.List.Tot.Base.length.fuel_instrumented (Fuel Term Term) Term)
;;;;;;;;;;;;;;;;Token for fuel-instrumented partial applications
(declare-fun FStar.List.Tot.Base.length.fuel_instrumented_token () Term)
(declare-fun FStar.List.Tot.Base.length (Term Term) Term)
(declare-fun FStar.List.Tot.Base.length@tok () Term)
(declare-fun Tm_arrow_5adbd6bc13eabd8f92e79f380e1498f0 () Term)
;;;;;;;;;;;;;;;;Fuel irrelevance
;;; Fact-ids: Name FStar.List.Tot.Base.length; Namespace FStar.List.Tot.Base
(assert (! 
;; def=FStar.List.Tot.Base.fst(74,8-74,14); use=FStar.List.Tot.Base.fst(74,8-74,14)
(forall ((@u0 Fuel) (@x1 Term) (@x2 Term))
 (! (= (FStar.List.Tot.Base.length.fuel_instrumented (SFuel @u0)
@x1
@x2)
(FStar.List.Tot.Base.length.fuel_instrumented ZFuel
@x1
@x2))
 

:pattern ((FStar.List.Tot.Base.length.fuel_instrumented (SFuel @u0)
@x1
@x2))
:qid @fuel_irrelevance_FStar.List.Tot.Base.length.fuel_instrumented))

:named @fuel_irrelevance_FStar.List.Tot.Base.length.fuel_instrumented))
;;;;;;;;;;;;;;;;Correspondence of recursive function to instrumented version
;;; Fact-ids: Name FStar.List.Tot.Base.length; Namespace FStar.List.Tot.Base
(assert (! 
;; def=FStar.List.Tot.Base.fst(74,8-74,14); use=FStar.List.Tot.Base.fst(74,8-74,14)
(forall ((@x0 Term) (@x1 Term))
 (! (= (FStar.List.Tot.Base.length @x0
@x1)
(FStar.List.Tot.Base.length.fuel_instrumented MaxFuel
@x0
@x1))
 

:pattern ((FStar.List.Tot.Base.length @x0
@x1))
:qid @fuel_correspondence_FStar.List.Tot.Base.length.fuel_instrumented))

:named @fuel_correspondence_FStar.List.Tot.Base.length.fuel_instrumented))

; </end encoding FStar.List.Tot.Base.length>


; <Start encoding FStar.List.Tot.Base.nth>

;;;;;;;;;;;;;;;;Fuel-instrumented function name
(declare-fun FStar.List.Tot.Base.nth.fuel_instrumented (Fuel Term Term Term) Term)
;;;;;;;;;;;;;;;;Token for fuel-instrumented partial applications
(declare-fun FStar.List.Tot.Base.nth.fuel_instrumented_token () Term)
(declare-fun FStar.List.Tot.Base.nth (Term Term Term) Term)
(declare-fun FStar.List.Tot.Base.nth@tok () Term)
(declare-fun Tm_arrow_c96efec76dd44fb4c1c29ca8a004927d () Term)
;;;;;;;;;;;;;;;;Fuel irrelevance
;;; Fact-ids: Name FStar.List.Tot.Base.nth; Namespace FStar.List.Tot.Base
(assert (! 
;; def=FStar.List.Tot.Base.fst(82,8-82,11); use=FStar.List.Tot.Base.fst(82,8-82,11)
(forall ((@u0 Fuel) (@x1 Term) (@x2 Term) (@x3 Term))
 (! (= (FStar.List.Tot.Base.nth.fuel_instrumented (SFuel @u0)
@x1
@x2
@x3)
(FStar.List.Tot.Base.nth.fuel_instrumented ZFuel
@x1
@x2
@x3))
 

:pattern ((FStar.List.Tot.Base.nth.fuel_instrumented (SFuel @u0)
@x1
@x2
@x3))
:qid @fuel_irrelevance_FStar.List.Tot.Base.nth.fuel_instrumented))

:named @fuel_irrelevance_FStar.List.Tot.Base.nth.fuel_instrumented))
;;;;;;;;;;;;;;;;Correspondence of recursive function to instrumented version
;;; Fact-ids: Name FStar.List.Tot.Base.nth; Namespace FStar.List.Tot.Base
(assert (! 
;; def=FStar.List.Tot.Base.fst(82,8-82,11); use=FStar.List.Tot.Base.fst(82,8-82,11)
(forall ((@x0 Term) (@x1 Term) (@x2 Term))
 (! (= (FStar.List.Tot.Base.nth @x0
@x1
@x2)
(FStar.List.Tot.Base.nth.fuel_instrumented MaxFuel
@x0
@x1
@x2))
 

:pattern ((FStar.List.Tot.Base.nth @x0
@x1
@x2))
:qid @fuel_correspondence_FStar.List.Tot.Base.nth.fuel_instrumented))

:named @fuel_correspondence_FStar.List.Tot.Base.nth.fuel_instrumented))

; </end encoding FStar.List.Tot.Base.nth>


; <Start encoding FStar.List.Tot.Base.index>

;;;;;;;;;;;;;;;;Fuel-instrumented function name
(declare-fun FStar.List.Tot.Base.index.fuel_instrumented (Fuel Term Term Term) Term)
;;;;;;;;;;;;;;;;Token for fuel-instrumented partial applications
(declare-fun FStar.List.Tot.Base.index.fuel_instrumented_token () Term)
(declare-fun FStar.List.Tot.Base.index (Term Term Term) Term)
(declare-fun FStar.List.Tot.Base.index@tok () Term)
(declare-fun Tm_refine_c86aba5c6243e6b7f9a4b0ad41b4e9a0 (Term Term) Term)


(declare-fun Tm_arrow_87330224a075c52374b0ca2b4b909772 () Term)
;;;;;;;;;;;;;;;;Fuel irrelevance
;;; Fact-ids: Name FStar.List.Tot.Base.index; Namespace FStar.List.Tot.Base
(assert (! 
;; def=FStar.List.Tot.Base.fst(90,8-90,13); use=FStar.List.Tot.Base.fst(90,8-90,13)
(forall ((@u0 Fuel) (@x1 Term) (@x2 Term) (@x3 Term))
 (! (= (FStar.List.Tot.Base.index.fuel_instrumented (SFuel @u0)
@x1
@x2
@x3)
(FStar.List.Tot.Base.index.fuel_instrumented ZFuel
@x1
@x2
@x3))
 

:pattern ((FStar.List.Tot.Base.index.fuel_instrumented (SFuel @u0)
@x1
@x2
@x3))
:qid @fuel_irrelevance_FStar.List.Tot.Base.index.fuel_instrumented))

:named @fuel_irrelevance_FStar.List.Tot.Base.index.fuel_instrumented))
;;;;;;;;;;;;;;;;Correspondence of recursive function to instrumented version
;;; Fact-ids: Name FStar.List.Tot.Base.index; Namespace FStar.List.Tot.Base
(assert (! 
;; def=FStar.List.Tot.Base.fst(90,8-90,13); use=FStar.List.Tot.Base.fst(90,8-90,13)
(forall ((@x0 Term) (@x1 Term) (@x2 Term))
 (! (= (FStar.List.Tot.Base.index @x0
@x1
@x2)
(FStar.List.Tot.Base.index.fuel_instrumented MaxFuel
@x0
@x1
@x2))
 

:pattern ((FStar.List.Tot.Base.index @x0
@x1
@x2))
:qid @fuel_correspondence_FStar.List.Tot.Base.index.fuel_instrumented))

:named @fuel_correspondence_FStar.List.Tot.Base.index.fuel_instrumented))

; </end encoding FStar.List.Tot.Base.index>


; <Start encoding FStar.List.Tot.Base.count>

;;;;;;;;;;;;;;;;Fuel-instrumented function name
(declare-fun FStar.List.Tot.Base.count.fuel_instrumented (Fuel Term Term Term) Term)
;;;;;;;;;;;;;;;;Token for fuel-instrumented partial applications
(declare-fun FStar.List.Tot.Base.count.fuel_instrumented_token () Term)
(declare-fun FStar.List.Tot.Base.count (Term Term Term) Term)
(declare-fun FStar.List.Tot.Base.count@tok () Term)
(declare-fun Tm_arrow_d7494a533e0c3edea69ad484d93aa0e5 () Term)
;;;;;;;;;;;;;;;;Fuel irrelevance
;;; Fact-ids: Name FStar.List.Tot.Base.count; Namespace FStar.List.Tot.Base
(assert (! 
;; def=FStar.List.Tot.Base.fst(100,8-100,13); use=FStar.List.Tot.Base.fst(100,8-100,13)
(forall ((@u0 Fuel) (@x1 Term) (@x2 Term) (@x3 Term))
 (! (= (FStar.List.Tot.Base.count.fuel_instrumented (SFuel @u0)
@x1
@x2
@x3)
(FStar.List.Tot.Base.count.fuel_instrumented ZFuel
@x1
@x2
@x3))
 

:pattern ((FStar.List.Tot.Base.count.fuel_instrumented (SFuel @u0)
@x1
@x2
@x3))
:qid @fuel_irrelevance_FStar.List.Tot.Base.count.fuel_instrumented))

:named @fuel_irrelevance_FStar.List.Tot.Base.count.fuel_instrumented))
;;;;;;;;;;;;;;;;Correspondence of recursive function to instrumented version
;;; Fact-ids: Name FStar.List.Tot.Base.count; Namespace FStar.List.Tot.Base
(assert (! 
;; def=FStar.List.Tot.Base.fst(100,8-100,13); use=FStar.List.Tot.Base.fst(100,8-100,13)
(forall ((@x0 Term) (@x1 Term) (@x2 Term))
 (! (= (FStar.List.Tot.Base.count @x0
@x1
@x2)
(FStar.List.Tot.Base.count.fuel_instrumented MaxFuel
@x0
@x1
@x2))
 

:pattern ((FStar.List.Tot.Base.count @x0
@x1
@x2))
:qid @fuel_correspondence_FStar.List.Tot.Base.count.fuel_instrumented))

:named @fuel_correspondence_FStar.List.Tot.Base.count.fuel_instrumented))

; </end encoding FStar.List.Tot.Base.count>


; <Start encoding FStar.List.Tot.Base.rev_acc>

;;;;;;;;;;;;;;;;Fuel-instrumented function name
(declare-fun FStar.List.Tot.Base.rev_acc.fuel_instrumented (Fuel Term Term Term) Term)
;;;;;;;;;;;;;;;;Token for fuel-instrumented partial applications
(declare-fun FStar.List.Tot.Base.rev_acc.fuel_instrumented_token () Term)
(declare-fun FStar.List.Tot.Base.rev_acc (Term Term Term) Term)
(declare-fun FStar.List.Tot.Base.rev_acc@tok () Term)
(declare-fun Tm_arrow_54e38bdd456bab4cdb32b5d540c2274c () Term)
;;;;;;;;;;;;;;;;Fuel irrelevance
;;; Fact-ids: Name FStar.List.Tot.Base.rev_acc; Namespace FStar.List.Tot.Base
(assert (! 
;; def=FStar.List.Tot.Base.fst(108,8-108,15); use=FStar.List.Tot.Base.fst(108,8-108,15)
(forall ((@u0 Fuel) (@x1 Term) (@x2 Term) (@x3 Term))
 (! (= (FStar.List.Tot.Base.rev_acc.fuel_instrumented (SFuel @u0)
@x1
@x2
@x3)
(FStar.List.Tot.Base.rev_acc.fuel_instrumented ZFuel
@x1
@x2
@x3))
 

:pattern ((FStar.List.Tot.Base.rev_acc.fuel_instrumented (SFuel @u0)
@x1
@x2
@x3))
:qid @fuel_irrelevance_FStar.List.Tot.Base.rev_acc.fuel_instrumented))

:named @fuel_irrelevance_FStar.List.Tot.Base.rev_acc.fuel_instrumented))
;;;;;;;;;;;;;;;;Correspondence of recursive function to instrumented version
;;; Fact-ids: Name FStar.List.Tot.Base.rev_acc; Namespace FStar.List.Tot.Base
(assert (! 
;; def=FStar.List.Tot.Base.fst(108,8-108,15); use=FStar.List.Tot.Base.fst(108,8-108,15)
(forall ((@x0 Term) (@x1 Term) (@x2 Term))
 (! (= (FStar.List.Tot.Base.rev_acc @x0
@x1
@x2)
(FStar.List.Tot.Base.rev_acc.fuel_instrumented MaxFuel
@x0
@x1
@x2))
 

:pattern ((FStar.List.Tot.Base.rev_acc @x0
@x1
@x2))
:qid @fuel_correspondence_FStar.List.Tot.Base.rev_acc.fuel_instrumented))

:named @fuel_correspondence_FStar.List.Tot.Base.rev_acc.fuel_instrumented))

; </end encoding FStar.List.Tot.Base.rev_acc>


; <Start encoding FStar.List.Tot.Base.rev>

(declare-fun FStar.List.Tot.Base.rev (Term Term) Term)
(declare-fun Tm_arrow_f9ba16c6212a483d195bbb8ceec3eef1 () Term)
(declare-fun FStar.List.Tot.Base.rev@tok () Term)

; </end encoding FStar.List.Tot.Base.rev>


; <Start encoding FStar.List.Tot.Base.append>

;;;;;;;;;;;;;;;;Fuel-instrumented function name
(declare-fun FStar.List.Tot.Base.append.fuel_instrumented (Fuel Term Term Term) Term)
;;;;;;;;;;;;;;;;Token for fuel-instrumented partial applications
(declare-fun FStar.List.Tot.Base.append.fuel_instrumented_token () Term)
(declare-fun FStar.List.Tot.Base.append (Term Term Term) Term)
(declare-fun FStar.List.Tot.Base.append@tok () Term)

;;;;;;;;;;;;;;;;Fuel irrelevance
;;; Fact-ids: Name FStar.List.Tot.Base.append; Namespace FStar.List.Tot.Base
(assert (! 
;; def=FStar.List.Tot.Base.fst(119,8-119,14); use=FStar.List.Tot.Base.fst(119,8-119,14)
(forall ((@u0 Fuel) (@x1 Term) (@x2 Term) (@x3 Term))
 (! (= (FStar.List.Tot.Base.append.fuel_instrumented (SFuel @u0)
@x1
@x2
@x3)
(FStar.List.Tot.Base.append.fuel_instrumented ZFuel
@x1
@x2
@x3))
 

:pattern ((FStar.List.Tot.Base.append.fuel_instrumented (SFuel @u0)
@x1
@x2
@x3))
:qid @fuel_irrelevance_FStar.List.Tot.Base.append.fuel_instrumented))

:named @fuel_irrelevance_FStar.List.Tot.Base.append.fuel_instrumented))
;;;;;;;;;;;;;;;;Correspondence of recursive function to instrumented version
;;; Fact-ids: Name FStar.List.Tot.Base.append; Namespace FStar.List.Tot.Base
(assert (! 
;; def=FStar.List.Tot.Base.fst(119,8-119,14); use=FStar.List.Tot.Base.fst(119,8-119,14)
(forall ((@x0 Term) (@x1 Term) (@x2 Term))
 (! (= (FStar.List.Tot.Base.append @x0
@x1
@x2)
(FStar.List.Tot.Base.append.fuel_instrumented MaxFuel
@x0
@x1
@x2))
 

:pattern ((FStar.List.Tot.Base.append @x0
@x1
@x2))
:qid @fuel_correspondence_FStar.List.Tot.Base.append.fuel_instrumented))

:named @fuel_correspondence_FStar.List.Tot.Base.append.fuel_instrumented))

; </end encoding FStar.List.Tot.Base.append>


; <Start encoding FStar.List.Tot.Base.op_At>

(declare-fun FStar.List.Tot.Base.op_At (Term Term Term) Term)

(declare-fun FStar.List.Tot.Base.op_At@tok () Term)

; </end encoding FStar.List.Tot.Base.op_At>


; <Start encoding FStar.List.Tot.Base.snoc>

(declare-fun FStar.List.Tot.Base.snoc (Term Term) Term)
(declare-fun Tm_arrow_07ff48a1c7b541b0963ce508064e29fb () Term)
(declare-fun FStar.List.Tot.Base.snoc@tok () Term)

; </end encoding FStar.List.Tot.Base.snoc>


; <Start encoding FStar.List.Tot.Base.flatten>

;;;;;;;;;;;;;;;;Fuel-instrumented function name
(declare-fun FStar.List.Tot.Base.flatten.fuel_instrumented (Fuel Term Term) Term)
;;;;;;;;;;;;;;;;Token for fuel-instrumented partial applications
(declare-fun FStar.List.Tot.Base.flatten.fuel_instrumented_token () Term)
(declare-fun FStar.List.Tot.Base.flatten (Term Term) Term)
(declare-fun FStar.List.Tot.Base.flatten@tok () Term)
(declare-fun Tm_arrow_7e18fd6b36805c1f1c9a77e024fdec2e () Term)
;;;;;;;;;;;;;;;;Fuel irrelevance
;;; Fact-ids: Name FStar.List.Tot.Base.flatten; Namespace FStar.List.Tot.Base
(assert (! 
;; def=FStar.List.Tot.Base.fst(143,8-143,15); use=FStar.List.Tot.Base.fst(143,8-143,15)
(forall ((@u0 Fuel) (@x1 Term) (@x2 Term))
 (! (= (FStar.List.Tot.Base.flatten.fuel_instrumented (SFuel @u0)
@x1
@x2)
(FStar.List.Tot.Base.flatten.fuel_instrumented ZFuel
@x1
@x2))
 

:pattern ((FStar.List.Tot.Base.flatten.fuel_instrumented (SFuel @u0)
@x1
@x2))
:qid @fuel_irrelevance_FStar.List.Tot.Base.flatten.fuel_instrumented))

:named @fuel_irrelevance_FStar.List.Tot.Base.flatten.fuel_instrumented))
;;;;;;;;;;;;;;;;Correspondence of recursive function to instrumented version
;;; Fact-ids: Name FStar.List.Tot.Base.flatten; Namespace FStar.List.Tot.Base
(assert (! 
;; def=FStar.List.Tot.Base.fst(143,8-143,15); use=FStar.List.Tot.Base.fst(143,8-143,15)
(forall ((@x0 Term) (@x1 Term))
 (! (= (FStar.List.Tot.Base.flatten @x0
@x1)
(FStar.List.Tot.Base.flatten.fuel_instrumented MaxFuel
@x0
@x1))
 

:pattern ((FStar.List.Tot.Base.flatten @x0
@x1))
:qid @fuel_correspondence_FStar.List.Tot.Base.flatten.fuel_instrumented))

:named @fuel_correspondence_FStar.List.Tot.Base.flatten.fuel_instrumented))

; </end encoding FStar.List.Tot.Base.flatten>


; <Start encoding FStar.List.Tot.Base.map>

;;;;;;;;;;;;;;;;Fuel-instrumented function name
(declare-fun FStar.List.Tot.Base.map.fuel_instrumented (Fuel Term Term Term Term) Term)
;;;;;;;;;;;;;;;;Token for fuel-instrumented partial applications
(declare-fun FStar.List.Tot.Base.map.fuel_instrumented_token () Term)
(declare-fun FStar.List.Tot.Base.map (Term Term Term Term) Term)
(declare-fun FStar.List.Tot.Base.map@tok () Term)



(declare-fun Tm_arrow_28431dcf5044bcdd56dbe625f9e3df4e () Term)
;;;;;;;;;;;;;;;;Fuel irrelevance
;;; Fact-ids: Name FStar.List.Tot.Base.map; Namespace FStar.List.Tot.Base
(assert (! 
;; def=FStar.List.Tot.Base.fst(151,8-151,11); use=FStar.List.Tot.Base.fst(151,8-151,11)
(forall ((@u0 Fuel) (@x1 Term) (@x2 Term) (@x3 Term) (@x4 Term))
 (! (= (FStar.List.Tot.Base.map.fuel_instrumented (SFuel @u0)
@x1
@x2
@x3
@x4)
(FStar.List.Tot.Base.map.fuel_instrumented ZFuel
@x1
@x2
@x3
@x4))
 

:pattern ((FStar.List.Tot.Base.map.fuel_instrumented (SFuel @u0)
@x1
@x2
@x3
@x4))
:qid @fuel_irrelevance_FStar.List.Tot.Base.map.fuel_instrumented))

:named @fuel_irrelevance_FStar.List.Tot.Base.map.fuel_instrumented))
;;;;;;;;;;;;;;;;Correspondence of recursive function to instrumented version
;;; Fact-ids: Name FStar.List.Tot.Base.map; Namespace FStar.List.Tot.Base
(assert (! 
;; def=FStar.List.Tot.Base.fst(151,8-151,11); use=FStar.List.Tot.Base.fst(151,8-151,11)
(forall ((@x0 Term) (@x1 Term) (@x2 Term) (@x3 Term))
 (! (= (FStar.List.Tot.Base.map @x0
@x1
@x2
@x3)
(FStar.List.Tot.Base.map.fuel_instrumented MaxFuel
@x0
@x1
@x2
@x3))
 

:pattern ((FStar.List.Tot.Base.map @x0
@x1
@x2
@x3))
:qid @fuel_correspondence_FStar.List.Tot.Base.map.fuel_instrumented))

:named @fuel_correspondence_FStar.List.Tot.Base.map.fuel_instrumented))

; </end encoding FStar.List.Tot.Base.map>


; <Start encoding FStar.List.Tot.Base.mapi_init>

;;;;;;;;;;;;;;;;Fuel-instrumented function name
(declare-fun FStar.List.Tot.Base.mapi_init.fuel_instrumented (Fuel Term Term Term Term Term) Term)
;;;;;;;;;;;;;;;;Token for fuel-instrumented partial applications
(declare-fun FStar.List.Tot.Base.mapi_init.fuel_instrumented_token () Term)
(declare-fun FStar.List.Tot.Base.mapi_init (Term Term Term Term Term) Term)
(declare-fun FStar.List.Tot.Base.mapi_init@tok () Term)
(declare-fun Tm_arrow_010f318679809a99aeced42f5ba95505 (Term Term) Term)


(declare-fun Tm_arrow_9a89e146e4bb6b361bc4526b891ed1f1 () Term)
;;;;;;;;;;;;;;;;Fuel irrelevance
;;; Fact-ids: Name FStar.List.Tot.Base.mapi_init; Namespace FStar.List.Tot.Base
(assert (! 
;; def=FStar.List.Tot.Base.fst(160,8-160,17); use=FStar.List.Tot.Base.fst(160,8-160,17)
(forall ((@u0 Fuel) (@x1 Term) (@x2 Term) (@x3 Term) (@x4 Term) (@x5 Term))
 (! (= (FStar.List.Tot.Base.mapi_init.fuel_instrumented (SFuel @u0)
@x1
@x2
@x3
@x4
@x5)
(FStar.List.Tot.Base.mapi_init.fuel_instrumented ZFuel
@x1
@x2
@x3
@x4
@x5))
 

:pattern ((FStar.List.Tot.Base.mapi_init.fuel_instrumented (SFuel @u0)
@x1
@x2
@x3
@x4
@x5))
:qid @fuel_irrelevance_FStar.List.Tot.Base.mapi_init.fuel_instrumented))

:named @fuel_irrelevance_FStar.List.Tot.Base.mapi_init.fuel_instrumented))
;;;;;;;;;;;;;;;;Correspondence of recursive function to instrumented version
;;; Fact-ids: Name FStar.List.Tot.Base.mapi_init; Namespace FStar.List.Tot.Base
(assert (! 
;; def=FStar.List.Tot.Base.fst(160,8-160,17); use=FStar.List.Tot.Base.fst(160,8-160,17)
(forall ((@x0 Term) (@x1 Term) (@x2 Term) (@x3 Term) (@x4 Term))
 (! (= (FStar.List.Tot.Base.mapi_init @x0
@x1
@x2
@x3
@x4)
(FStar.List.Tot.Base.mapi_init.fuel_instrumented MaxFuel
@x0
@x1
@x2
@x3
@x4))
 

:pattern ((FStar.List.Tot.Base.mapi_init @x0
@x1
@x2
@x3
@x4))
:qid @fuel_correspondence_FStar.List.Tot.Base.mapi_init.fuel_instrumented))

:named @fuel_correspondence_FStar.List.Tot.Base.mapi_init.fuel_instrumented))

; </end encoding FStar.List.Tot.Base.mapi_init>


; <Start encoding FStar.List.Tot.Base.mapi>


(declare-fun FStar.List.Tot.Base.mapi (Term Term Term Term) Term)

(declare-fun Tm_arrow_b2a07f422fceebd0f3ee3abd5e4aeed2 () Term)
(declare-fun FStar.List.Tot.Base.mapi@tok () Term)


; </end encoding FStar.List.Tot.Base.mapi>


; <Start encoding FStar.List.Tot.Base.concatMap>

;;;;;;;;;;;;;;;;Fuel-instrumented function name
(declare-fun FStar.List.Tot.Base.concatMap.fuel_instrumented (Fuel Term Term Term Term) Term)
;;;;;;;;;;;;;;;;Token for fuel-instrumented partial applications
(declare-fun FStar.List.Tot.Base.concatMap.fuel_instrumented_token () Term)
(declare-fun FStar.List.Tot.Base.concatMap (Term Term Term Term) Term)
(declare-fun FStar.List.Tot.Base.concatMap@tok () Term)
(declare-fun Tm_arrow_121fa5bc200f7b3946a5e35040f266b9 (Term Term) Term)


(declare-fun Tm_arrow_c35dd4e5f8c08f94183bf93963fac92f () Term)
;;;;;;;;;;;;;;;;Fuel irrelevance
;;; Fact-ids: Name FStar.List.Tot.Base.concatMap; Namespace FStar.List.Tot.Base
(assert (! 
;; def=FStar.List.Tot.Base.fst(176,8-176,17); use=FStar.List.Tot.Base.fst(176,8-176,17)
(forall ((@u0 Fuel) (@x1 Term) (@x2 Term) (@x3 Term) (@x4 Term))
 (! (= (FStar.List.Tot.Base.concatMap.fuel_instrumented (SFuel @u0)
@x1
@x2
@x3
@x4)
(FStar.List.Tot.Base.concatMap.fuel_instrumented ZFuel
@x1
@x2
@x3
@x4))
 

:pattern ((FStar.List.Tot.Base.concatMap.fuel_instrumented (SFuel @u0)
@x1
@x2
@x3
@x4))
:qid @fuel_irrelevance_FStar.List.Tot.Base.concatMap.fuel_instrumented))

:named @fuel_irrelevance_FStar.List.Tot.Base.concatMap.fuel_instrumented))
;;;;;;;;;;;;;;;;Correspondence of recursive function to instrumented version
;;; Fact-ids: Name FStar.List.Tot.Base.concatMap; Namespace FStar.List.Tot.Base
(assert (! 
;; def=FStar.List.Tot.Base.fst(176,8-176,17); use=FStar.List.Tot.Base.fst(176,8-176,17)
(forall ((@x0 Term) (@x1 Term) (@x2 Term) (@x3 Term))
 (! (= (FStar.List.Tot.Base.concatMap @x0
@x1
@x2
@x3)
(FStar.List.Tot.Base.concatMap.fuel_instrumented MaxFuel
@x0
@x1
@x2
@x3))
 

:pattern ((FStar.List.Tot.Base.concatMap @x0
@x1
@x2
@x3))
:qid @fuel_correspondence_FStar.List.Tot.Base.concatMap.fuel_instrumented))

:named @fuel_correspondence_FStar.List.Tot.Base.concatMap.fuel_instrumented))

; </end encoding FStar.List.Tot.Base.concatMap>


; <Start encoding FStar.List.Tot.Base.fold_left>

;;;;;;;;;;;;;;;;Fuel-instrumented function name
(declare-fun FStar.List.Tot.Base.fold_left.fuel_instrumented (Fuel Term Term Term Term Term) Term)
;;;;;;;;;;;;;;;;Token for fuel-instrumented partial applications
(declare-fun FStar.List.Tot.Base.fold_left.fuel_instrumented_token () Term)
(declare-fun FStar.List.Tot.Base.fold_left (Term Term Term Term Term) Term)
(declare-fun FStar.List.Tot.Base.fold_left@tok () Term)
(declare-fun Tm_arrow_f0225aaf6b987d44876e7f498390aa39 (Term Term) Term)


(declare-fun Tm_arrow_230697841c1116c0d5f3958097856e6e () Term)
;;;;;;;;;;;;;;;;Fuel irrelevance
;;; Fact-ids: Name FStar.List.Tot.Base.fold_left; Namespace FStar.List.Tot.Base
(assert (! 
;; def=FStar.List.Tot.Base.fst(187,8-187,17); use=FStar.List.Tot.Base.fst(187,8-187,17)
(forall ((@u0 Fuel) (@x1 Term) (@x2 Term) (@x3 Term) (@x4 Term) (@x5 Term))
 (! (= (FStar.List.Tot.Base.fold_left.fuel_instrumented (SFuel @u0)
@x1
@x2
@x3
@x4
@x5)
(FStar.List.Tot.Base.fold_left.fuel_instrumented ZFuel
@x1
@x2
@x3
@x4
@x5))
 

:pattern ((FStar.List.Tot.Base.fold_left.fuel_instrumented (SFuel @u0)
@x1
@x2
@x3
@x4
@x5))
:qid @fuel_irrelevance_FStar.List.Tot.Base.fold_left.fuel_instrumented))

:named @fuel_irrelevance_FStar.List.Tot.Base.fold_left.fuel_instrumented))
;;;;;;;;;;;;;;;;Correspondence of recursive function to instrumented version
;;; Fact-ids: Name FStar.List.Tot.Base.fold_left; Namespace FStar.List.Tot.Base
(assert (! 
;; def=FStar.List.Tot.Base.fst(187,8-187,17); use=FStar.List.Tot.Base.fst(187,8-187,17)
(forall ((@x0 Term) (@x1 Term) (@x2 Term) (@x3 Term) (@x4 Term))
 (! (= (FStar.List.Tot.Base.fold_left @x0
@x1
@x2
@x3
@x4)
(FStar.List.Tot.Base.fold_left.fuel_instrumented MaxFuel
@x0
@x1
@x2
@x3
@x4))
 

:pattern ((FStar.List.Tot.Base.fold_left @x0
@x1
@x2
@x3
@x4))
:qid @fuel_correspondence_FStar.List.Tot.Base.fold_left.fuel_instrumented))

:named @fuel_correspondence_FStar.List.Tot.Base.fold_left.fuel_instrumented))

; </end encoding FStar.List.Tot.Base.fold_left>


; <Start encoding FStar.List.Tot.Base.fold_right>

;;;;;;;;;;;;;;;;Fuel-instrumented function name
(declare-fun FStar.List.Tot.Base.fold_right.fuel_instrumented (Fuel Term Term Term Term Term) Term)
;;;;;;;;;;;;;;;;Token for fuel-instrumented partial applications
(declare-fun FStar.List.Tot.Base.fold_right.fuel_instrumented_token () Term)
(declare-fun FStar.List.Tot.Base.fold_right (Term Term Term Term Term) Term)
(declare-fun FStar.List.Tot.Base.fold_right@tok () Term)
(declare-fun Tm_arrow_3c1d21b8f6dcc5e202b4ff1cafbaba81 (Term Term) Term)


(declare-fun Tm_arrow_105b39eeae3a464c82e64975ac399cdb () Term)
;;;;;;;;;;;;;;;;Fuel irrelevance
;;; Fact-ids: Name FStar.List.Tot.Base.fold_right; Namespace FStar.List.Tot.Base
(assert (! 
;; def=FStar.List.Tot.Base.fst(195,8-195,18); use=FStar.List.Tot.Base.fst(195,8-195,18)
(forall ((@u0 Fuel) (@x1 Term) (@x2 Term) (@x3 Term) (@x4 Term) (@x5 Term))
 (! (= (FStar.List.Tot.Base.fold_right.fuel_instrumented (SFuel @u0)
@x1
@x2
@x3
@x4
@x5)
(FStar.List.Tot.Base.fold_right.fuel_instrumented ZFuel
@x1
@x2
@x3
@x4
@x5))
 

:pattern ((FStar.List.Tot.Base.fold_right.fuel_instrumented (SFuel @u0)
@x1
@x2
@x3
@x4
@x5))
:qid @fuel_irrelevance_FStar.List.Tot.Base.fold_right.fuel_instrumented))

:named @fuel_irrelevance_FStar.List.Tot.Base.fold_right.fuel_instrumented))
;;;;;;;;;;;;;;;;Correspondence of recursive function to instrumented version
;;; Fact-ids: Name FStar.List.Tot.Base.fold_right; Namespace FStar.List.Tot.Base
(assert (! 
;; def=FStar.List.Tot.Base.fst(195,8-195,18); use=FStar.List.Tot.Base.fst(195,8-195,18)
(forall ((@x0 Term) (@x1 Term) (@x2 Term) (@x3 Term) (@x4 Term))
 (! (= (FStar.List.Tot.Base.fold_right @x0
@x1
@x2
@x3
@x4)
(FStar.List.Tot.Base.fold_right.fuel_instrumented MaxFuel
@x0
@x1
@x2
@x3
@x4))
 

:pattern ((FStar.List.Tot.Base.fold_right @x0
@x1
@x2
@x3
@x4))
:qid @fuel_correspondence_FStar.List.Tot.Base.fold_right.fuel_instrumented))

:named @fuel_correspondence_FStar.List.Tot.Base.fold_right.fuel_instrumented))

; </end encoding FStar.List.Tot.Base.fold_right>


; <Start encoding FStar.List.Tot.Base.fold_right_gtot>

;;;;;;;;;;;;;;;;Fuel-instrumented function name
(declare-fun FStar.List.Tot.Base.fold_right_gtot.fuel_instrumented (Fuel Term Term Term Term Term) Term)
;;;;;;;;;;;;;;;;Token for fuel-instrumented partial applications
(declare-fun FStar.List.Tot.Base.fold_right_gtot.fuel_instrumented_token () Term)
(declare-fun FStar.List.Tot.Base.fold_right_gtot (Term Term Term Term Term) Term)
(declare-fun FStar.List.Tot.Base.fold_right_gtot@tok () Term)
(declare-fun Tm_ghost_arrow_d7e9834b8fd0407a723f5f3f4b012fdd (Term Term) Term)


(declare-fun Tm_ghost_arrow_fab043b8cdd2296e8d98a06066e4b2d2 () Term)
;;;;;;;;;;;;;;;;Fuel irrelevance
;;; Fact-ids: Name FStar.List.Tot.Base.fold_right_gtot; Namespace FStar.List.Tot.Base
(assert (! 
;; def=FStar.List.Tot.Base.fst(201,8-201,23); use=FStar.List.Tot.Base.fst(201,8-201,23)
(forall ((@u0 Fuel) (@x1 Term) (@x2 Term) (@x3 Term) (@x4 Term) (@x5 Term))
 (! (= (FStar.List.Tot.Base.fold_right_gtot.fuel_instrumented (SFuel @u0)
@x1
@x2
@x3
@x4
@x5)
(FStar.List.Tot.Base.fold_right_gtot.fuel_instrumented ZFuel
@x1
@x2
@x3
@x4
@x5))
 

:pattern ((FStar.List.Tot.Base.fold_right_gtot.fuel_instrumented (SFuel @u0)
@x1
@x2
@x3
@x4
@x5))
:qid @fuel_irrelevance_FStar.List.Tot.Base.fold_right_gtot.fuel_instrumented))

:named @fuel_irrelevance_FStar.List.Tot.Base.fold_right_gtot.fuel_instrumented))
;;;;;;;;;;;;;;;;Correspondence of recursive function to instrumented version
;;; Fact-ids: Name FStar.List.Tot.Base.fold_right_gtot; Namespace FStar.List.Tot.Base
(assert (! 
;; def=FStar.List.Tot.Base.fst(201,8-201,23); use=FStar.List.Tot.Base.fst(201,8-201,23)
(forall ((@x0 Term) (@x1 Term) (@x2 Term) (@x3 Term) (@x4 Term))
 (! (= (FStar.List.Tot.Base.fold_right_gtot @x0
@x1
@x2
@x3
@x4)
(FStar.List.Tot.Base.fold_right_gtot.fuel_instrumented MaxFuel
@x0
@x1
@x2
@x3
@x4))
 

:pattern ((FStar.List.Tot.Base.fold_right_gtot @x0
@x1
@x2
@x3
@x4))
:qid @fuel_correspondence_FStar.List.Tot.Base.fold_right_gtot.fuel_instrumented))

:named @fuel_correspondence_FStar.List.Tot.Base.fold_right_gtot.fuel_instrumented))

; </end encoding FStar.List.Tot.Base.fold_right_gtot>


; <Start encoding FStar.List.Tot.Base.map_gtot>


(declare-fun FStar.List.Tot.Base.map_gtot (Term Term Term Term) Term)

(declare-fun Tm_ghost_arrow_d0c7be07105bf8d5ad60b7f603c725f3 () Term)
(declare-fun FStar.List.Tot.Base.map_gtot@tok () Term)

(declare-fun Tm_ghost_arrow_21583233c98863da294c5e5d657cf78a (Term Term) Term)
(declare-fun Tm_abs_469cd3853c3ff3e8cd408b5521fdbd9d (Term Term Term) Term)

; </end encoding FStar.List.Tot.Base.map_gtot>


; <Start encoding FStar.List.Tot.Base.fold_left2>

;;;;;;;;;;;;;;;;Fuel-instrumented function name
(declare-fun FStar.List.Tot.Base.fold_left2.fuel_instrumented (Fuel Term Term Term Term Term Term Term) Term)
;;;;;;;;;;;;;;;;Token for fuel-instrumented partial applications
(declare-fun FStar.List.Tot.Base.fold_left2.fuel_instrumented_token () Term)
(declare-fun FStar.List.Tot.Base.fold_left2 (Term Term Term Term Term Term Term) Term)
(declare-fun FStar.List.Tot.Base.fold_left2@tok () Term)
(declare-fun Tm_arrow_40dd30796dd695d143ec6ed01d322177 (Term Term Term) Term)
(declare-fun Tm_refine_c16bc1b61f58b349bf6fc1c94dcaf83b (Term) Term)



(declare-fun Tm_arrow_3f28d1abbd43ddded682cbec516ea7bb () Term)

;;;;;;;;;;;;;;;;Fuel irrelevance
;;; Fact-ids: Name FStar.List.Tot.Base.fold_left2; Namespace FStar.List.Tot.Base
(assert (! 
;; def=FStar.List.Tot.Base.fst(218,8-218,18); use=FStar.List.Tot.Base.fst(218,8-218,18)
(forall ((@u0 Fuel) (@x1 Term) (@x2 Term) (@x3 Term) (@x4 Term) (@x5 Term) (@x6 Term) (@x7 Term))
 (! (= (FStar.List.Tot.Base.fold_left2.fuel_instrumented (SFuel @u0)
@x1
@x2
@x3
@x4
@x5
@x6
@x7)
(FStar.List.Tot.Base.fold_left2.fuel_instrumented ZFuel
@x1
@x2
@x3
@x4
@x5
@x6
@x7))
 

:pattern ((FStar.List.Tot.Base.fold_left2.fuel_instrumented (SFuel @u0)
@x1
@x2
@x3
@x4
@x5
@x6
@x7))
:qid @fuel_irrelevance_FStar.List.Tot.Base.fold_left2.fuel_instrumented))

:named @fuel_irrelevance_FStar.List.Tot.Base.fold_left2.fuel_instrumented))
;;;;;;;;;;;;;;;;Correspondence of recursive function to instrumented version
;;; Fact-ids: Name FStar.List.Tot.Base.fold_left2; Namespace FStar.List.Tot.Base
(assert (! 
;; def=FStar.List.Tot.Base.fst(218,8-218,18); use=FStar.List.Tot.Base.fst(218,8-218,18)
(forall ((@x0 Term) (@x1 Term) (@x2 Term) (@x3 Term) (@x4 Term) (@x5 Term) (@x6 Term))
 (! (= (FStar.List.Tot.Base.fold_left2 @x0
@x1
@x2
@x3
@x4
@x5
@x6)
(FStar.List.Tot.Base.fold_left2.fuel_instrumented MaxFuel
@x0
@x1
@x2
@x3
@x4
@x5
@x6))
 

:pattern ((FStar.List.Tot.Base.fold_left2 @x0
@x1
@x2
@x3
@x4
@x5
@x6))
:qid @fuel_correspondence_FStar.List.Tot.Base.fold_left2.fuel_instrumented))

:named @fuel_correspondence_FStar.List.Tot.Base.fold_left2.fuel_instrumented))

; </end encoding FStar.List.Tot.Base.fold_left2>


; <Start encoding FStar.List.Tot.Base.mem>

;;;;;;;;;;;;;;;;Fuel-instrumented function name
(declare-fun FStar.List.Tot.Base.mem.fuel_instrumented (Fuel Term Term Term) Term)
;;;;;;;;;;;;;;;;Token for fuel-instrumented partial applications
(declare-fun FStar.List.Tot.Base.mem.fuel_instrumented_token () Term)
(declare-fun FStar.List.Tot.Base.mem (Term Term Term) Term)
(declare-fun FStar.List.Tot.Base.mem@tok () Term)
(declare-fun Tm_arrow_8b16b79a9f8fab7cb6911016a8022992 () Term)
;;;;;;;;;;;;;;;;Fuel irrelevance
;;; Fact-ids: Name FStar.List.Tot.Base.mem; Namespace FStar.List.Tot.Base
(assert (! 
;; def=FStar.List.Tot.Base.fst(230,8-230,11); use=FStar.List.Tot.Base.fst(230,8-230,11)
(forall ((@u0 Fuel) (@x1 Term) (@x2 Term) (@x3 Term))
 (! (= (FStar.List.Tot.Base.mem.fuel_instrumented (SFuel @u0)
@x1
@x2
@x3)
(FStar.List.Tot.Base.mem.fuel_instrumented ZFuel
@x1
@x2
@x3))
 

:pattern ((FStar.List.Tot.Base.mem.fuel_instrumented (SFuel @u0)
@x1
@x2
@x3))
:qid @fuel_irrelevance_FStar.List.Tot.Base.mem.fuel_instrumented))

:named @fuel_irrelevance_FStar.List.Tot.Base.mem.fuel_instrumented))
;;;;;;;;;;;;;;;;Correspondence of recursive function to instrumented version
;;; Fact-ids: Name FStar.List.Tot.Base.mem; Namespace FStar.List.Tot.Base
(assert (! 
;; def=FStar.List.Tot.Base.fst(230,8-230,11); use=FStar.List.Tot.Base.fst(230,8-230,11)
(forall ((@x0 Term) (@x1 Term) (@x2 Term))
 (! (= (FStar.List.Tot.Base.mem @x0
@x1
@x2)
(FStar.List.Tot.Base.mem.fuel_instrumented MaxFuel
@x0
@x1
@x2))
 

:pattern ((FStar.List.Tot.Base.mem @x0
@x1
@x2))
:qid @fuel_correspondence_FStar.List.Tot.Base.mem.fuel_instrumented))

:named @fuel_correspondence_FStar.List.Tot.Base.mem.fuel_instrumented))

; </end encoding FStar.List.Tot.Base.mem>


; <Start encoding FStar.List.Tot.Base.memP>

;;;;;;;;;;;;;;;;Fuel-instrumented function name
(declare-fun FStar.List.Tot.Base.memP.fuel_instrumented (Fuel Term Term Term) Term)
;;;;;;;;;;;;;;;;Token for fuel-instrumented partial applications
(declare-fun FStar.List.Tot.Base.memP.fuel_instrumented_token () Term)
(declare-fun FStar.List.Tot.Base.memP (Term Term Term) Term)
(declare-fun FStar.List.Tot.Base.memP@tok () Term)
(declare-fun Tm_arrow_9a5de17321abf8ec257671c9a474c08a () Term)
;;;;;;;;;;;;;;;;Fuel irrelevance
;;; Fact-ids: Name FStar.List.Tot.Base.memP; Namespace FStar.List.Tot.Base
(assert (! 
;; def=FStar.List.Tot.Base.fst(239,8-239,12); use=FStar.List.Tot.Base.fst(239,8-239,12)
(forall ((@u0 Fuel) (@x1 Term) (@x2 Term) (@x3 Term))
 (! (= (FStar.List.Tot.Base.memP.fuel_instrumented (SFuel @u0)
@x1
@x2
@x3)
(FStar.List.Tot.Base.memP.fuel_instrumented ZFuel
@x1
@x2
@x3))
 

:pattern ((FStar.List.Tot.Base.memP.fuel_instrumented (SFuel @u0)
@x1
@x2
@x3))
:qid @fuel_irrelevance_FStar.List.Tot.Base.memP.fuel_instrumented))

:named @fuel_irrelevance_FStar.List.Tot.Base.memP.fuel_instrumented))
;;;;;;;;;;;;;;;;Correspondence of recursive function to instrumented version
;;; Fact-ids: Name FStar.List.Tot.Base.memP; Namespace FStar.List.Tot.Base
(assert (! 
;; def=FStar.List.Tot.Base.fst(239,8-239,12); use=FStar.List.Tot.Base.fst(239,8-239,12)
(forall ((@x0 Term) (@x1 Term) (@x2 Term))
 (! (= (FStar.List.Tot.Base.memP @x0
@x1
@x2)
(FStar.List.Tot.Base.memP.fuel_instrumented MaxFuel
@x0
@x1
@x2))
 

:pattern ((FStar.List.Tot.Base.memP @x0
@x1
@x2))
:qid @fuel_correspondence_FStar.List.Tot.Base.memP.fuel_instrumented))

:named @fuel_correspondence_FStar.List.Tot.Base.memP.fuel_instrumented))

; </end encoding FStar.List.Tot.Base.memP>


; <Start encoding FStar.List.Tot.Base.contains>

(declare-fun FStar.List.Tot.Base.contains (Term) Term)
(declare-fun Tm_arrow_c7306997fce9480ecc743e5f07d84087 (Term) Term)
(declare-fun Tm_arrow_dc6bb79540975b8523aaf4f1cab2f558 () Term)
(declare-fun FStar.List.Tot.Base.contains@tok () Term)

;;;;;;;;;;;;;;;;kick_partial_app
;;; Fact-ids: Name FStar.List.Tot.Base.contains; Namespace FStar.List.Tot.Base
(assert (! (Valid (ApplyTT __uu__PartialApp
FStar.List.Tot.Base.mem@tok))
:named @kick_partial_app_ccd82d20727a12a21bc723f6ffff5e81))

; </end encoding FStar.List.Tot.Base.contains>


; <Start encoding FStar.List.Tot.Base.existsb>

;;;;;;;;;;;;;;;;Fuel-instrumented function name
(declare-fun FStar.List.Tot.Base.existsb.fuel_instrumented (Fuel Term Term Term) Term)
;;;;;;;;;;;;;;;;Token for fuel-instrumented partial applications
(declare-fun FStar.List.Tot.Base.existsb.fuel_instrumented_token () Term)
(declare-fun FStar.List.Tot.Base.existsb (Term Term Term) Term)
(declare-fun FStar.List.Tot.Base.existsb@tok () Term)
(declare-fun Tm_arrow_84543425b818e2d10a976186b8e8c250 (Term) Term)


(declare-fun Tm_arrow_98dbecc64760e6a41f037a6881cd5df8 () Term)
;;;;;;;;;;;;;;;;Fuel irrelevance
;;; Fact-ids: Name FStar.List.Tot.Base.existsb; Namespace FStar.List.Tot.Base
(assert (! 
;; def=FStar.List.Tot.Base.fst(256,8-256,15); use=FStar.List.Tot.Base.fst(256,8-256,15)
(forall ((@u0 Fuel) (@x1 Term) (@x2 Term) (@x3 Term))
 (! (= (FStar.List.Tot.Base.existsb.fuel_instrumented (SFuel @u0)
@x1
@x2
@x3)
(FStar.List.Tot.Base.existsb.fuel_instrumented ZFuel
@x1
@x2
@x3))
 

:pattern ((FStar.List.Tot.Base.existsb.fuel_instrumented (SFuel @u0)
@x1
@x2
@x3))
:qid @fuel_irrelevance_FStar.List.Tot.Base.existsb.fuel_instrumented))

:named @fuel_irrelevance_FStar.List.Tot.Base.existsb.fuel_instrumented))
;;;;;;;;;;;;;;;;Correspondence of recursive function to instrumented version
;;; Fact-ids: Name FStar.List.Tot.Base.existsb; Namespace FStar.List.Tot.Base
(assert (! 
;; def=FStar.List.Tot.Base.fst(256,8-256,15); use=FStar.List.Tot.Base.fst(256,8-256,15)
(forall ((@x0 Term) (@x1 Term) (@x2 Term))
 (! (= (FStar.List.Tot.Base.existsb @x0
@x1
@x2)
(FStar.List.Tot.Base.existsb.fuel_instrumented MaxFuel
@x0
@x1
@x2))
 

:pattern ((FStar.List.Tot.Base.existsb @x0
@x1
@x2))
:qid @fuel_correspondence_FStar.List.Tot.Base.existsb.fuel_instrumented))

:named @fuel_correspondence_FStar.List.Tot.Base.existsb.fuel_instrumented))

; </end encoding FStar.List.Tot.Base.existsb>


; <Start encoding FStar.List.Tot.Base.find>

;;;;;;;;;;;;;;;;Fuel-instrumented function name
(declare-fun FStar.List.Tot.Base.find.fuel_instrumented (Fuel Term Term Term) Term)
;;;;;;;;;;;;;;;;Token for fuel-instrumented partial applications
(declare-fun FStar.List.Tot.Base.find.fuel_instrumented_token () Term)
(declare-fun FStar.List.Tot.Base.find (Term Term Term) Term)
(declare-fun FStar.List.Tot.Base.find@tok () Term)

(declare-fun Tm_refine_3b1cb9ec3355fed185c658f53954b3fa (Term Term) Term)





(declare-fun Tm_arrow_286c509b12b9a2bb9bf1025c6fd97451 () Term)

;;;;;;;;;;;;;;;;Fuel irrelevance
;;; Fact-ids: Name FStar.List.Tot.Base.find; Namespace FStar.List.Tot.Base
(assert (! 
;; def=FStar.List.Tot.Base.fst(266,8-266,12); use=FStar.List.Tot.Base.fst(266,8-266,12)
(forall ((@u0 Fuel) (@x1 Term) (@x2 Term) (@x3 Term))
 (! (= (FStar.List.Tot.Base.find.fuel_instrumented (SFuel @u0)
@x1
@x2
@x3)
(FStar.List.Tot.Base.find.fuel_instrumented ZFuel
@x1
@x2
@x3))
 

:pattern ((FStar.List.Tot.Base.find.fuel_instrumented (SFuel @u0)
@x1
@x2
@x3))
:qid @fuel_irrelevance_FStar.List.Tot.Base.find.fuel_instrumented))

:named @fuel_irrelevance_FStar.List.Tot.Base.find.fuel_instrumented))
;;;;;;;;;;;;;;;;Correspondence of recursive function to instrumented version
;;; Fact-ids: Name FStar.List.Tot.Base.find; Namespace FStar.List.Tot.Base
(assert (! 
;; def=FStar.List.Tot.Base.fst(266,8-266,12); use=FStar.List.Tot.Base.fst(266,8-266,12)
(forall ((@x0 Term) (@x1 Term) (@x2 Term))
 (! (= (FStar.List.Tot.Base.find @x0
@x1
@x2)
(FStar.List.Tot.Base.find.fuel_instrumented MaxFuel
@x0
@x1
@x2))
 

:pattern ((FStar.List.Tot.Base.find @x0
@x1
@x2))
:qid @fuel_correspondence_FStar.List.Tot.Base.find.fuel_instrumented))

:named @fuel_correspondence_FStar.List.Tot.Base.find.fuel_instrumented))

; </end encoding FStar.List.Tot.Base.find>


; <Start encoding FStar.List.Tot.Base.mem_filter_spec>


(declare-fun Tm_refine_38ce848b2acb13502b58e6aafdc25aa7 (Term) Term)
(declare-fun FStar.List.Tot.Base.mem_filter_spec (Term Term Term Term) Term)


(declare-fun Tm_arrow_c47e94ca5002c08a880a6c9a72eea438 () Term)
(declare-fun FStar.List.Tot.Base.mem_filter_spec@tok () Term)



(declare-fun Tm_abs_50493bd82add4a6e328a03007530dbc5 (Term Term Term) Term)

; </end encoding FStar.List.Tot.Base.mem_filter_spec>


; <Start encoding FStar.List.Tot.Base.filter>

;;;;;;;;;;;;;;;;Fuel-instrumented function name
(declare-fun FStar.List.Tot.Base.filter.fuel_instrumented (Fuel Term Term Term) Term)
;;;;;;;;;;;;;;;;Token for fuel-instrumented partial applications
(declare-fun FStar.List.Tot.Base.filter.fuel_instrumented_token () Term)
(declare-fun FStar.List.Tot.Base.filter (Term Term Term) Term)
(declare-fun FStar.List.Tot.Base.filter@tok () Term)


(declare-fun Tm_refine_5583eb859eb089e77523c1e843326d1a (Term Term) Term)




(declare-fun Tm_arrow_f8bb85880254fc3fe0bb1e949008d8e9 () Term)


;;;;;;;;;;;;;;;;Fuel irrelevance
;;; Fact-ids: Name FStar.List.Tot.Base.filter; Namespace FStar.List.Tot.Base
(assert (! 
;; def=FStar.List.Tot.Base.fst(292,8-292,14); use=FStar.List.Tot.Base.fst(292,8-292,14)
(forall ((@u0 Fuel) (@x1 Term) (@x2 Term) (@x3 Term))
 (! (= (FStar.List.Tot.Base.filter.fuel_instrumented (SFuel @u0)
@x1
@x2
@x3)
(FStar.List.Tot.Base.filter.fuel_instrumented ZFuel
@x1
@x2
@x3))
 

:pattern ((FStar.List.Tot.Base.filter.fuel_instrumented (SFuel @u0)
@x1
@x2
@x3))
:qid @fuel_irrelevance_FStar.List.Tot.Base.filter.fuel_instrumented))

:named @fuel_irrelevance_FStar.List.Tot.Base.filter.fuel_instrumented))
;;;;;;;;;;;;;;;;Correspondence of recursive function to instrumented version
;;; Fact-ids: Name FStar.List.Tot.Base.filter; Namespace FStar.List.Tot.Base
(assert (! 
;; def=FStar.List.Tot.Base.fst(292,8-292,14); use=FStar.List.Tot.Base.fst(292,8-292,14)
(forall ((@x0 Term) (@x1 Term) (@x2 Term))
 (! (= (FStar.List.Tot.Base.filter @x0
@x1
@x2)
(FStar.List.Tot.Base.filter.fuel_instrumented MaxFuel
@x0
@x1
@x2))
 

:pattern ((FStar.List.Tot.Base.filter @x0
@x1
@x2))
:qid @fuel_correspondence_FStar.List.Tot.Base.filter.fuel_instrumented))

:named @fuel_correspondence_FStar.List.Tot.Base.filter.fuel_instrumented))

; </end encoding FStar.List.Tot.Base.filter>


; <Start encoding FStar.List.Tot.Base.mem_filter>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.List.Tot.Base.mem_filter (Term Term Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.List.Tot.Base.mem_filter@tok () Term)

; </end encoding FStar.List.Tot.Base.mem_filter>


; <Start encoding FStar.List.Tot.Base.mem_filter_forall>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.List.Tot.Base.mem_filter_forall (Term Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.List.Tot.Base.mem_filter_forall@tok () Term)


; </end encoding FStar.List.Tot.Base.mem_filter_forall>


; <Start encoding FStar.List.Tot.Base.for_all>

;;;;;;;;;;;;;;;;Fuel-instrumented function name
(declare-fun FStar.List.Tot.Base.for_all.fuel_instrumented (Fuel Term Term Term) Term)
;;;;;;;;;;;;;;;;Token for fuel-instrumented partial applications
(declare-fun FStar.List.Tot.Base.for_all.fuel_instrumented_token () Term)
(declare-fun FStar.List.Tot.Base.for_all (Term Term Term) Term)
(declare-fun FStar.List.Tot.Base.for_all@tok () Term)




;;;;;;;;;;;;;;;;Fuel irrelevance
;;; Fact-ids: Name FStar.List.Tot.Base.for_all; Namespace FStar.List.Tot.Base
(assert (! 
;; def=FStar.List.Tot.Base.fst(322,8-322,15); use=FStar.List.Tot.Base.fst(322,8-322,15)
(forall ((@u0 Fuel) (@x1 Term) (@x2 Term) (@x3 Term))
 (! (= (FStar.List.Tot.Base.for_all.fuel_instrumented (SFuel @u0)
@x1
@x2
@x3)
(FStar.List.Tot.Base.for_all.fuel_instrumented ZFuel
@x1
@x2
@x3))
 

:pattern ((FStar.List.Tot.Base.for_all.fuel_instrumented (SFuel @u0)
@x1
@x2
@x3))
:qid @fuel_irrelevance_FStar.List.Tot.Base.for_all.fuel_instrumented))

:named @fuel_irrelevance_FStar.List.Tot.Base.for_all.fuel_instrumented))
;;;;;;;;;;;;;;;;Correspondence of recursive function to instrumented version
;;; Fact-ids: Name FStar.List.Tot.Base.for_all; Namespace FStar.List.Tot.Base
(assert (! 
;; def=FStar.List.Tot.Base.fst(322,8-322,15); use=FStar.List.Tot.Base.fst(322,8-322,15)
(forall ((@x0 Term) (@x1 Term) (@x2 Term))
 (! (= (FStar.List.Tot.Base.for_all @x0
@x1
@x2)
(FStar.List.Tot.Base.for_all.fuel_instrumented MaxFuel
@x0
@x1
@x2))
 

:pattern ((FStar.List.Tot.Base.for_all @x0
@x1
@x2))
:qid @fuel_correspondence_FStar.List.Tot.Base.for_all.fuel_instrumented))

:named @fuel_correspondence_FStar.List.Tot.Base.for_all.fuel_instrumented))

; </end encoding FStar.List.Tot.Base.for_all>


; <Start encoding FStar.List.Tot.Base.for_all_mem>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.List.Tot.Base.for_all_mem (Term Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.List.Tot.Base.for_all_mem@tok () Term)

; </end encoding FStar.List.Tot.Base.for_all_mem>


; <Start encoding FStar.List.Tot.Base.collect>

;;;;;;;;;;;;;;;;Fuel-instrumented function name
(declare-fun FStar.List.Tot.Base.collect.fuel_instrumented (Fuel Term Term Term Term) Term)
;;;;;;;;;;;;;;;;Token for fuel-instrumented partial applications
(declare-fun FStar.List.Tot.Base.collect.fuel_instrumented_token () Term)
(declare-fun FStar.List.Tot.Base.collect (Term Term Term Term) Term)
(declare-fun FStar.List.Tot.Base.collect@tok () Term)




;;;;;;;;;;;;;;;;Fuel irrelevance
;;; Fact-ids: Name FStar.List.Tot.Base.collect; Namespace FStar.List.Tot.Base
(assert (! 
;; def=FStar.List.Tot.Base.fst(343,8-343,15); use=FStar.List.Tot.Base.fst(343,8-343,15)
(forall ((@u0 Fuel) (@x1 Term) (@x2 Term) (@x3 Term) (@x4 Term))
 (! (= (FStar.List.Tot.Base.collect.fuel_instrumented (SFuel @u0)
@x1
@x2
@x3
@x4)
(FStar.List.Tot.Base.collect.fuel_instrumented ZFuel
@x1
@x2
@x3
@x4))
 

:pattern ((FStar.List.Tot.Base.collect.fuel_instrumented (SFuel @u0)
@x1
@x2
@x3
@x4))
:qid @fuel_irrelevance_FStar.List.Tot.Base.collect.fuel_instrumented))

:named @fuel_irrelevance_FStar.List.Tot.Base.collect.fuel_instrumented))
;;;;;;;;;;;;;;;;Correspondence of recursive function to instrumented version
;;; Fact-ids: Name FStar.List.Tot.Base.collect; Namespace FStar.List.Tot.Base
(assert (! 
;; def=FStar.List.Tot.Base.fst(343,8-343,15); use=FStar.List.Tot.Base.fst(343,8-343,15)
(forall ((@x0 Term) (@x1 Term) (@x2 Term) (@x3 Term))
 (! (= (FStar.List.Tot.Base.collect @x0
@x1
@x2
@x3)
(FStar.List.Tot.Base.collect.fuel_instrumented MaxFuel
@x0
@x1
@x2
@x3))
 

:pattern ((FStar.List.Tot.Base.collect @x0
@x1
@x2
@x3))
:qid @fuel_correspondence_FStar.List.Tot.Base.collect.fuel_instrumented))

:named @fuel_correspondence_FStar.List.Tot.Base.collect.fuel_instrumented))

; </end encoding FStar.List.Tot.Base.collect>


; <Start encoding FStar.List.Tot.Base.tryFind>

;;;;;;;;;;;;;;;;Fuel-instrumented function name
(declare-fun FStar.List.Tot.Base.tryFind.fuel_instrumented (Fuel Term Term Term) Term)
;;;;;;;;;;;;;;;;Token for fuel-instrumented partial applications
(declare-fun FStar.List.Tot.Base.tryFind.fuel_instrumented_token () Term)
(declare-fun FStar.List.Tot.Base.tryFind (Term Term Term) Term)
(declare-fun FStar.List.Tot.Base.tryFind@tok () Term)



(declare-fun Tm_arrow_4ae6bca87a611585312b8b0d0d66fefe () Term)
;;;;;;;;;;;;;;;;Fuel irrelevance
;;; Fact-ids: Name FStar.List.Tot.Base.tryFind; Namespace FStar.List.Tot.Base
(assert (! 
;; def=FStar.List.Tot.Base.fst(353,8-353,15); use=FStar.List.Tot.Base.fst(353,8-353,15)
(forall ((@u0 Fuel) (@x1 Term) (@x2 Term) (@x3 Term))
 (! (= (FStar.List.Tot.Base.tryFind.fuel_instrumented (SFuel @u0)
@x1
@x2
@x3)
(FStar.List.Tot.Base.tryFind.fuel_instrumented ZFuel
@x1
@x2
@x3))
 

:pattern ((FStar.List.Tot.Base.tryFind.fuel_instrumented (SFuel @u0)
@x1
@x2
@x3))
:qid @fuel_irrelevance_FStar.List.Tot.Base.tryFind.fuel_instrumented))

:named @fuel_irrelevance_FStar.List.Tot.Base.tryFind.fuel_instrumented))
;;;;;;;;;;;;;;;;Correspondence of recursive function to instrumented version
;;; Fact-ids: Name FStar.List.Tot.Base.tryFind; Namespace FStar.List.Tot.Base
(assert (! 
;; def=FStar.List.Tot.Base.fst(353,8-353,15); use=FStar.List.Tot.Base.fst(353,8-353,15)
(forall ((@x0 Term) (@x1 Term) (@x2 Term))
 (! (= (FStar.List.Tot.Base.tryFind @x0
@x1
@x2)
(FStar.List.Tot.Base.tryFind.fuel_instrumented MaxFuel
@x0
@x1
@x2))
 

:pattern ((FStar.List.Tot.Base.tryFind @x0
@x1
@x2))
:qid @fuel_correspondence_FStar.List.Tot.Base.tryFind.fuel_instrumented))

:named @fuel_correspondence_FStar.List.Tot.Base.tryFind.fuel_instrumented))

; </end encoding FStar.List.Tot.Base.tryFind>


; <Start encoding FStar.List.Tot.Base.tryPick>

;;;;;;;;;;;;;;;;Fuel-instrumented function name
(declare-fun FStar.List.Tot.Base.tryPick.fuel_instrumented (Fuel Term Term Term Term) Term)
;;;;;;;;;;;;;;;;Token for fuel-instrumented partial applications
(declare-fun FStar.List.Tot.Base.tryPick.fuel_instrumented_token () Term)
(declare-fun FStar.List.Tot.Base.tryPick (Term Term Term Term) Term)
(declare-fun FStar.List.Tot.Base.tryPick@tok () Term)
(declare-fun Tm_arrow_4b0c7cc34485afa5854ebe5c95023d4c (Term Term) Term)


(declare-fun Tm_arrow_7fbbe8a710b97b9ed9c0d2dfb00b1641 () Term)
;;;;;;;;;;;;;;;;Fuel irrelevance
;;; Fact-ids: Name FStar.List.Tot.Base.tryPick; Namespace FStar.List.Tot.Base
(assert (! 
;; def=FStar.List.Tot.Base.fst(362,8-362,15); use=FStar.List.Tot.Base.fst(362,8-362,15)
(forall ((@u0 Fuel) (@x1 Term) (@x2 Term) (@x3 Term) (@x4 Term))
 (! (= (FStar.List.Tot.Base.tryPick.fuel_instrumented (SFuel @u0)
@x1
@x2
@x3
@x4)
(FStar.List.Tot.Base.tryPick.fuel_instrumented ZFuel
@x1
@x2
@x3
@x4))
 

:pattern ((FStar.List.Tot.Base.tryPick.fuel_instrumented (SFuel @u0)
@x1
@x2
@x3
@x4))
:qid @fuel_irrelevance_FStar.List.Tot.Base.tryPick.fuel_instrumented))

:named @fuel_irrelevance_FStar.List.Tot.Base.tryPick.fuel_instrumented))
;;;;;;;;;;;;;;;;Correspondence of recursive function to instrumented version
;;; Fact-ids: Name FStar.List.Tot.Base.tryPick; Namespace FStar.List.Tot.Base
(assert (! 
;; def=FStar.List.Tot.Base.fst(362,8-362,15); use=FStar.List.Tot.Base.fst(362,8-362,15)
(forall ((@x0 Term) (@x1 Term) (@x2 Term) (@x3 Term))
 (! (= (FStar.List.Tot.Base.tryPick @x0
@x1
@x2
@x3)
(FStar.List.Tot.Base.tryPick.fuel_instrumented MaxFuel
@x0
@x1
@x2
@x3))
 

:pattern ((FStar.List.Tot.Base.tryPick @x0
@x1
@x2
@x3))
:qid @fuel_correspondence_FStar.List.Tot.Base.tryPick.fuel_instrumented))

:named @fuel_correspondence_FStar.List.Tot.Base.tryPick.fuel_instrumented))

; </end encoding FStar.List.Tot.Base.tryPick>


; <Start encoding FStar.List.Tot.Base.choose>

;;;;;;;;;;;;;;;;Fuel-instrumented function name
(declare-fun FStar.List.Tot.Base.choose.fuel_instrumented (Fuel Term Term Term Term) Term)
;;;;;;;;;;;;;;;;Token for fuel-instrumented partial applications
(declare-fun FStar.List.Tot.Base.choose.fuel_instrumented_token () Term)
(declare-fun FStar.List.Tot.Base.choose (Term Term Term Term) Term)
(declare-fun FStar.List.Tot.Base.choose@tok () Term)



(declare-fun Tm_arrow_ee03a7411b6d8975b285ea6c772c4d89 () Term)
;;;;;;;;;;;;;;;;Fuel irrelevance
;;; Fact-ids: Name FStar.List.Tot.Base.choose; Namespace FStar.List.Tot.Base
(assert (! 
;; def=FStar.List.Tot.Base.fst(373,8-373,14); use=FStar.List.Tot.Base.fst(373,8-373,14)
(forall ((@u0 Fuel) (@x1 Term) (@x2 Term) (@x3 Term) (@x4 Term))
 (! (= (FStar.List.Tot.Base.choose.fuel_instrumented (SFuel @u0)
@x1
@x2
@x3
@x4)
(FStar.List.Tot.Base.choose.fuel_instrumented ZFuel
@x1
@x2
@x3
@x4))
 

:pattern ((FStar.List.Tot.Base.choose.fuel_instrumented (SFuel @u0)
@x1
@x2
@x3
@x4))
:qid @fuel_irrelevance_FStar.List.Tot.Base.choose.fuel_instrumented))

:named @fuel_irrelevance_FStar.List.Tot.Base.choose.fuel_instrumented))
;;;;;;;;;;;;;;;;Correspondence of recursive function to instrumented version
;;; Fact-ids: Name FStar.List.Tot.Base.choose; Namespace FStar.List.Tot.Base
(assert (! 
;; def=FStar.List.Tot.Base.fst(373,8-373,14); use=FStar.List.Tot.Base.fst(373,8-373,14)
(forall ((@x0 Term) (@x1 Term) (@x2 Term) (@x3 Term))
 (! (= (FStar.List.Tot.Base.choose @x0
@x1
@x2
@x3)
(FStar.List.Tot.Base.choose.fuel_instrumented MaxFuel
@x0
@x1
@x2
@x3))
 

:pattern ((FStar.List.Tot.Base.choose @x0
@x1
@x2
@x3))
:qid @fuel_correspondence_FStar.List.Tot.Base.choose.fuel_instrumented))

:named @fuel_correspondence_FStar.List.Tot.Base.choose.fuel_instrumented))

; </end encoding FStar.List.Tot.Base.choose>


; <Start encoding FStar.List.Tot.Base.partition>

;;;;;;;;;;;;;;;;Fuel-instrumented function name
(declare-fun FStar.List.Tot.Base.partition.fuel_instrumented (Fuel Term Term Term) Term)
;;;;;;;;;;;;;;;;Token for fuel-instrumented partial applications
(declare-fun FStar.List.Tot.Base.partition.fuel_instrumented_token () Term)
(declare-fun FStar.List.Tot.Base.partition (Term Term Term) Term)
(declare-fun FStar.List.Tot.Base.partition@tok () Term)



(declare-fun Tm_arrow_706f575815ce8a3bbd962da035d8aa14 () Term)
;;;;;;;;;;;;;;;;Fuel irrelevance
;;; Fact-ids: Name FStar.List.Tot.Base.partition; Namespace FStar.List.Tot.Base
(assert (! 
;; def=FStar.List.Tot.Base.fst(386,8-386,17); use=FStar.List.Tot.Base.fst(386,8-386,17)
(forall ((@u0 Fuel) (@x1 Term) (@x2 Term) (@x3 Term))
 (! (= (FStar.List.Tot.Base.partition.fuel_instrumented (SFuel @u0)
@x1
@x2
@x3)
(FStar.List.Tot.Base.partition.fuel_instrumented ZFuel
@x1
@x2
@x3))
 

:pattern ((FStar.List.Tot.Base.partition.fuel_instrumented (SFuel @u0)
@x1
@x2
@x3))
:qid @fuel_irrelevance_FStar.List.Tot.Base.partition.fuel_instrumented))

:named @fuel_irrelevance_FStar.List.Tot.Base.partition.fuel_instrumented))
;;;;;;;;;;;;;;;;Correspondence of recursive function to instrumented version
;;; Fact-ids: Name FStar.List.Tot.Base.partition; Namespace FStar.List.Tot.Base
(assert (! 
;; def=FStar.List.Tot.Base.fst(386,8-386,17); use=FStar.List.Tot.Base.fst(386,8-386,17)
(forall ((@x0 Term) (@x1 Term) (@x2 Term))
 (! (= (FStar.List.Tot.Base.partition @x0
@x1
@x2)
(FStar.List.Tot.Base.partition.fuel_instrumented MaxFuel
@x0
@x1
@x2))
 

:pattern ((FStar.List.Tot.Base.partition @x0
@x1
@x2))
:qid @fuel_correspondence_FStar.List.Tot.Base.partition.fuel_instrumented))

:named @fuel_correspondence_FStar.List.Tot.Base.partition.fuel_instrumented))

; </end encoding FStar.List.Tot.Base.partition>


; <Start encoding FStar.List.Tot.Base.subset>

;;;;;;;;;;;;;;;;Fuel-instrumented function name
(declare-fun FStar.List.Tot.Base.subset.fuel_instrumented (Fuel Term Term Term) Term)
;;;;;;;;;;;;;;;;Token for fuel-instrumented partial applications
(declare-fun FStar.List.Tot.Base.subset.fuel_instrumented_token () Term)
(declare-fun FStar.List.Tot.Base.subset (Term Term Term) Term)
(declare-fun FStar.List.Tot.Base.subset@tok () Term)
(declare-fun Tm_arrow_8d819a995fc33b4cb6aa699af88e8d32 () Term)
;;;;;;;;;;;;;;;;Fuel irrelevance
;;; Fact-ids: Name FStar.List.Tot.Base.subset; Namespace FStar.List.Tot.Base
(assert (! 
;; def=FStar.List.Tot.Base.fst(398,8-398,14); use=FStar.List.Tot.Base.fst(398,8-398,14)
(forall ((@u0 Fuel) (@x1 Term) (@x2 Term) (@x3 Term))
 (! (= (FStar.List.Tot.Base.subset.fuel_instrumented (SFuel @u0)
@x1
@x2
@x3)
(FStar.List.Tot.Base.subset.fuel_instrumented ZFuel
@x1
@x2
@x3))
 

:pattern ((FStar.List.Tot.Base.subset.fuel_instrumented (SFuel @u0)
@x1
@x2
@x3))
:qid @fuel_irrelevance_FStar.List.Tot.Base.subset.fuel_instrumented))

:named @fuel_irrelevance_FStar.List.Tot.Base.subset.fuel_instrumented))
;;;;;;;;;;;;;;;;Correspondence of recursive function to instrumented version
;;; Fact-ids: Name FStar.List.Tot.Base.subset; Namespace FStar.List.Tot.Base
(assert (! 
;; def=FStar.List.Tot.Base.fst(398,8-398,14); use=FStar.List.Tot.Base.fst(398,8-398,14)
(forall ((@x0 Term) (@x1 Term) (@x2 Term))
 (! (= (FStar.List.Tot.Base.subset @x0
@x1
@x2)
(FStar.List.Tot.Base.subset.fuel_instrumented MaxFuel
@x0
@x1
@x2))
 

:pattern ((FStar.List.Tot.Base.subset @x0
@x1
@x2))
:qid @fuel_correspondence_FStar.List.Tot.Base.subset.fuel_instrumented))

:named @fuel_correspondence_FStar.List.Tot.Base.subset.fuel_instrumented))

; </end encoding FStar.List.Tot.Base.subset>


; <Start encoding FStar.List.Tot.Base.noRepeats>

;;;;;;;;;;;;;;;;Fuel-instrumented function name
(declare-fun FStar.List.Tot.Base.noRepeats.fuel_instrumented (Fuel Term Term) Term)
;;;;;;;;;;;;;;;;Token for fuel-instrumented partial applications
(declare-fun FStar.List.Tot.Base.noRepeats.fuel_instrumented_token () Term)
(declare-fun FStar.List.Tot.Base.noRepeats (Term Term) Term)
(declare-fun FStar.List.Tot.Base.noRepeats@tok () Term)
(declare-fun Tm_arrow_0dd285b24907a2f8b15dedffef61afa6 () Term)
;;;;;;;;;;;;;;;;Fuel irrelevance
;;; Fact-ids: Name FStar.List.Tot.Base.noRepeats; Namespace FStar.List.Tot.Base
(assert (! 
;; def=FStar.List.Tot.Base.fst(407,8-407,17); use=FStar.List.Tot.Base.fst(407,8-407,17)
(forall ((@u0 Fuel) (@x1 Term) (@x2 Term))
 (! (= (FStar.List.Tot.Base.noRepeats.fuel_instrumented (SFuel @u0)
@x1
@x2)
(FStar.List.Tot.Base.noRepeats.fuel_instrumented ZFuel
@x1
@x2))
 

:pattern ((FStar.List.Tot.Base.noRepeats.fuel_instrumented (SFuel @u0)
@x1
@x2))
:qid @fuel_irrelevance_FStar.List.Tot.Base.noRepeats.fuel_instrumented))

:named @fuel_irrelevance_FStar.List.Tot.Base.noRepeats.fuel_instrumented))
;;;;;;;;;;;;;;;;Correspondence of recursive function to instrumented version
;;; Fact-ids: Name FStar.List.Tot.Base.noRepeats; Namespace FStar.List.Tot.Base
(assert (! 
;; def=FStar.List.Tot.Base.fst(407,8-407,17); use=FStar.List.Tot.Base.fst(407,8-407,17)
(forall ((@x0 Term) (@x1 Term))
 (! (= (FStar.List.Tot.Base.noRepeats @x0
@x1)
(FStar.List.Tot.Base.noRepeats.fuel_instrumented MaxFuel
@x0
@x1))
 

:pattern ((FStar.List.Tot.Base.noRepeats @x0
@x1))
:qid @fuel_correspondence_FStar.List.Tot.Base.noRepeats.fuel_instrumented))

:named @fuel_correspondence_FStar.List.Tot.Base.noRepeats.fuel_instrumented))

; </end encoding FStar.List.Tot.Base.noRepeats>


; <Start encoding FStar.List.Tot.Base.no_repeats_p>

;;;;;;;;;;;;;;;;Fuel-instrumented function name
(declare-fun FStar.List.Tot.Base.no_repeats_p.fuel_instrumented (Fuel Term Term) Term)
;;;;;;;;;;;;;;;;Token for fuel-instrumented partial applications
(declare-fun FStar.List.Tot.Base.no_repeats_p.fuel_instrumented_token () Term)
(declare-fun FStar.List.Tot.Base.no_repeats_p (Term Term) Term)
(declare-fun FStar.List.Tot.Base.no_repeats_p@tok () Term)
(declare-fun Tm_arrow_79c2442eab9e49d1108d2b7a240dc76e () Term)
;;;;;;;;;;;;;;;;Fuel irrelevance
;;; Fact-ids: Name FStar.List.Tot.Base.no_repeats_p; Namespace FStar.List.Tot.Base
(assert (! 
;; def=FStar.List.Tot.Base.fst(416,8-416,20); use=FStar.List.Tot.Base.fst(416,8-416,20)
(forall ((@u0 Fuel) (@x1 Term) (@x2 Term))
 (! (= (FStar.List.Tot.Base.no_repeats_p.fuel_instrumented (SFuel @u0)
@x1
@x2)
(FStar.List.Tot.Base.no_repeats_p.fuel_instrumented ZFuel
@x1
@x2))
 

:pattern ((FStar.List.Tot.Base.no_repeats_p.fuel_instrumented (SFuel @u0)
@x1
@x2))
:qid @fuel_irrelevance_FStar.List.Tot.Base.no_repeats_p.fuel_instrumented))

:named @fuel_irrelevance_FStar.List.Tot.Base.no_repeats_p.fuel_instrumented))
;;;;;;;;;;;;;;;;Correspondence of recursive function to instrumented version
;;; Fact-ids: Name FStar.List.Tot.Base.no_repeats_p; Namespace FStar.List.Tot.Base
(assert (! 
;; def=FStar.List.Tot.Base.fst(416,8-416,20); use=FStar.List.Tot.Base.fst(416,8-416,20)
(forall ((@x0 Term) (@x1 Term))
 (! (= (FStar.List.Tot.Base.no_repeats_p @x0
@x1)
(FStar.List.Tot.Base.no_repeats_p.fuel_instrumented MaxFuel
@x0
@x1))
 

:pattern ((FStar.List.Tot.Base.no_repeats_p @x0
@x1))
:qid @fuel_correspondence_FStar.List.Tot.Base.no_repeats_p.fuel_instrumented))

:named @fuel_correspondence_FStar.List.Tot.Base.no_repeats_p.fuel_instrumented))

; </end encoding FStar.List.Tot.Base.no_repeats_p>


; <Start encoding FStar.List.Tot.Base.assoc>

;;;;;;;;;;;;;;;;Fuel-instrumented function name
(declare-fun FStar.List.Tot.Base.assoc.fuel_instrumented (Fuel Term Term Term Term) Term)
;;;;;;;;;;;;;;;;Token for fuel-instrumented partial applications
(declare-fun FStar.List.Tot.Base.assoc.fuel_instrumented_token () Term)
(declare-fun FStar.List.Tot.Base.assoc (Term Term Term Term) Term)
(declare-fun FStar.List.Tot.Base.assoc@tok () Term)
(declare-fun Tm_arrow_d77cf796c5b72d2c2316c0fcdad1dd79 () Term)
;;;;;;;;;;;;;;;;Fuel irrelevance
;;; Fact-ids: Name FStar.List.Tot.Base.assoc; Namespace FStar.List.Tot.Base
(assert (! 
;; def=FStar.List.Tot.Base.fst(428,8-428,13); use=FStar.List.Tot.Base.fst(428,8-428,13)
(forall ((@u0 Fuel) (@x1 Term) (@x2 Term) (@x3 Term) (@x4 Term))
 (! (= (FStar.List.Tot.Base.assoc.fuel_instrumented (SFuel @u0)
@x1
@x2
@x3
@x4)
(FStar.List.Tot.Base.assoc.fuel_instrumented ZFuel
@x1
@x2
@x3
@x4))
 

:pattern ((FStar.List.Tot.Base.assoc.fuel_instrumented (SFuel @u0)
@x1
@x2
@x3
@x4))
:qid @fuel_irrelevance_FStar.List.Tot.Base.assoc.fuel_instrumented))

:named @fuel_irrelevance_FStar.List.Tot.Base.assoc.fuel_instrumented))
;;;;;;;;;;;;;;;;Correspondence of recursive function to instrumented version
;;; Fact-ids: Name FStar.List.Tot.Base.assoc; Namespace FStar.List.Tot.Base
(assert (! 
;; def=FStar.List.Tot.Base.fst(428,8-428,13); use=FStar.List.Tot.Base.fst(428,8-428,13)
(forall ((@x0 Term) (@x1 Term) (@x2 Term) (@x3 Term))
 (! (= (FStar.List.Tot.Base.assoc @x0
@x1
@x2
@x3)
(FStar.List.Tot.Base.assoc.fuel_instrumented MaxFuel
@x0
@x1
@x2
@x3))
 

:pattern ((FStar.List.Tot.Base.assoc @x0
@x1
@x2
@x3))
:qid @fuel_correspondence_FStar.List.Tot.Base.assoc.fuel_instrumented))

:named @fuel_correspondence_FStar.List.Tot.Base.assoc.fuel_instrumented))

; </end encoding FStar.List.Tot.Base.assoc>


; <Start encoding FStar.List.Tot.Base.split>

;;;;;;;;;;;;;;;;Fuel-instrumented function name
(declare-fun FStar.List.Tot.Base.split.fuel_instrumented (Fuel Term Term Term) Term)
;;;;;;;;;;;;;;;;Token for fuel-instrumented partial applications
(declare-fun FStar.List.Tot.Base.split.fuel_instrumented_token () Term)
(declare-fun FStar.List.Tot.Base.split (Term Term Term) Term)
(declare-fun FStar.List.Tot.Base.split@tok () Term)
(declare-fun Tm_arrow_1c3cb31b4ffa47bc6454f5b8a25e2407 () Term)
;;;;;;;;;;;;;;;;Fuel irrelevance
;;; Fact-ids: Name FStar.List.Tot.Base.split; Namespace FStar.List.Tot.Base
(assert (! 
;; def=FStar.List.Tot.Base.fst(436,8-436,13); use=FStar.List.Tot.Base.fst(436,8-436,13)
(forall ((@u0 Fuel) (@x1 Term) (@x2 Term) (@x3 Term))
 (! (= (FStar.List.Tot.Base.split.fuel_instrumented (SFuel @u0)
@x1
@x2
@x3)
(FStar.List.Tot.Base.split.fuel_instrumented ZFuel
@x1
@x2
@x3))
 

:pattern ((FStar.List.Tot.Base.split.fuel_instrumented (SFuel @u0)
@x1
@x2
@x3))
:qid @fuel_irrelevance_FStar.List.Tot.Base.split.fuel_instrumented))

:named @fuel_irrelevance_FStar.List.Tot.Base.split.fuel_instrumented))
;;;;;;;;;;;;;;;;Correspondence of recursive function to instrumented version
;;; Fact-ids: Name FStar.List.Tot.Base.split; Namespace FStar.List.Tot.Base
(assert (! 
;; def=FStar.List.Tot.Base.fst(436,8-436,13); use=FStar.List.Tot.Base.fst(436,8-436,13)
(forall ((@x0 Term) (@x1 Term) (@x2 Term))
 (! (= (FStar.List.Tot.Base.split @x0
@x1
@x2)
(FStar.List.Tot.Base.split.fuel_instrumented MaxFuel
@x0
@x1
@x2))
 

:pattern ((FStar.List.Tot.Base.split @x0
@x1
@x2))
:qid @fuel_correspondence_FStar.List.Tot.Base.split.fuel_instrumented))

:named @fuel_correspondence_FStar.List.Tot.Base.split.fuel_instrumented))

; </end encoding FStar.List.Tot.Base.split>


; <Start encoding FStar.List.Tot.Base.unzip>

(declare-fun FStar.List.Tot.Base.unzip (Term Term) Term)
(declare-fun Tm_arrow_b3053e6c1b76605139bba6cf7c4bcacb (Term Term) Term)
(declare-fun Tm_arrow_ba4ac429b1bf39803f263f6e75d9f351 () Term)
(declare-fun FStar.List.Tot.Base.unzip@tok () Term)

;;;;;;;;;;;;;;;;kick_partial_app
;;; Fact-ids: Name FStar.List.Tot.Base.unzip; Namespace FStar.List.Tot.Base
(assert (! (Valid (ApplyTT __uu__PartialApp
FStar.List.Tot.Base.split@tok))
:named @kick_partial_app_e9c1538ec6307baa2a937d74fbb429ce))

; </end encoding FStar.List.Tot.Base.unzip>


; <Start encoding FStar.List.Tot.Base.unzip3>

;;;;;;;;;;;;;;;;Fuel-instrumented function name
(declare-fun FStar.List.Tot.Base.unzip3.fuel_instrumented (Fuel Term Term Term Term) Term)
;;;;;;;;;;;;;;;;Token for fuel-instrumented partial applications
(declare-fun FStar.List.Tot.Base.unzip3.fuel_instrumented_token () Term)
(declare-fun FStar.List.Tot.Base.unzip3 (Term Term Term Term) Term)
(declare-fun FStar.List.Tot.Base.unzip3@tok () Term)
(declare-fun Tm_arrow_d40be6b496fedb6f7a46205c5824b732 () Term)
;;;;;;;;;;;;;;;;Fuel irrelevance
;;; Fact-ids: Name FStar.List.Tot.Base.unzip3; Namespace FStar.List.Tot.Base
(assert (! 
;; def=FStar.List.Tot.Base.fst(451,8-451,14); use=FStar.List.Tot.Base.fst(451,8-451,14)
(forall ((@u0 Fuel) (@x1 Term) (@x2 Term) (@x3 Term) (@x4 Term))
 (! (= (FStar.List.Tot.Base.unzip3.fuel_instrumented (SFuel @u0)
@x1
@x2
@x3
@x4)
(FStar.List.Tot.Base.unzip3.fuel_instrumented ZFuel
@x1
@x2
@x3
@x4))
 

:pattern ((FStar.List.Tot.Base.unzip3.fuel_instrumented (SFuel @u0)
@x1
@x2
@x3
@x4))
:qid @fuel_irrelevance_FStar.List.Tot.Base.unzip3.fuel_instrumented))

:named @fuel_irrelevance_FStar.List.Tot.Base.unzip3.fuel_instrumented))
;;;;;;;;;;;;;;;;Correspondence of recursive function to instrumented version
;;; Fact-ids: Name FStar.List.Tot.Base.unzip3; Namespace FStar.List.Tot.Base
(assert (! 
;; def=FStar.List.Tot.Base.fst(451,8-451,14); use=FStar.List.Tot.Base.fst(451,8-451,14)
(forall ((@x0 Term) (@x1 Term) (@x2 Term) (@x3 Term))
 (! (= (FStar.List.Tot.Base.unzip3 @x0
@x1
@x2
@x3)
(FStar.List.Tot.Base.unzip3.fuel_instrumented MaxFuel
@x0
@x1
@x2
@x3))
 

:pattern ((FStar.List.Tot.Base.unzip3 @x0
@x1
@x2
@x3))
:qid @fuel_correspondence_FStar.List.Tot.Base.unzip3.fuel_instrumented))

:named @fuel_correspondence_FStar.List.Tot.Base.unzip3.fuel_instrumented))

; </end encoding FStar.List.Tot.Base.unzip3>


; <Start encoding FStar.List.Tot.Base.splitAt>

;;;;;;;;;;;;;;;;Fuel-instrumented function name
(declare-fun FStar.List.Tot.Base.splitAt.fuel_instrumented (Fuel Term Term Term) Term)
;;;;;;;;;;;;;;;;Token for fuel-instrumented partial applications
(declare-fun FStar.List.Tot.Base.splitAt.fuel_instrumented_token () Term)
(declare-fun FStar.List.Tot.Base.splitAt (Term Term Term) Term)
(declare-fun FStar.List.Tot.Base.splitAt@tok () Term)
(declare-fun Tm_arrow_e36bd078e08c2ac2f1324fef6e0a4a22 () Term)
;;;;;;;;;;;;;;;;Fuel irrelevance
;;; Fact-ids: Name FStar.List.Tot.Base.splitAt; Namespace FStar.List.Tot.Base
(assert (! 
;; def=FStar.List.Tot.Base.fst(462,8-462,15); use=FStar.List.Tot.Base.fst(462,8-462,15)
(forall ((@u0 Fuel) (@x1 Term) (@x2 Term) (@x3 Term))
 (! (= (FStar.List.Tot.Base.splitAt.fuel_instrumented (SFuel @u0)
@x1
@x2
@x3)
(FStar.List.Tot.Base.splitAt.fuel_instrumented ZFuel
@x1
@x2
@x3))
 

:pattern ((FStar.List.Tot.Base.splitAt.fuel_instrumented (SFuel @u0)
@x1
@x2
@x3))
:qid @fuel_irrelevance_FStar.List.Tot.Base.splitAt.fuel_instrumented))

:named @fuel_irrelevance_FStar.List.Tot.Base.splitAt.fuel_instrumented))
;;;;;;;;;;;;;;;;Correspondence of recursive function to instrumented version
;;; Fact-ids: Name FStar.List.Tot.Base.splitAt; Namespace FStar.List.Tot.Base
(assert (! 
;; def=FStar.List.Tot.Base.fst(462,8-462,15); use=FStar.List.Tot.Base.fst(462,8-462,15)
(forall ((@x0 Term) (@x1 Term) (@x2 Term))
 (! (= (FStar.List.Tot.Base.splitAt @x0
@x1
@x2)
(FStar.List.Tot.Base.splitAt.fuel_instrumented MaxFuel
@x0
@x1
@x2))
 

:pattern ((FStar.List.Tot.Base.splitAt @x0
@x1
@x2))
:qid @fuel_correspondence_FStar.List.Tot.Base.splitAt.fuel_instrumented))

:named @fuel_correspondence_FStar.List.Tot.Base.splitAt.fuel_instrumented))

; </end encoding FStar.List.Tot.Base.splitAt>


; <Start encoding FStar.List.Tot.Base.lemma_splitAt_snd_length>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.List.Tot.Base.lemma_splitAt_snd_length (Term Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.List.Tot.Base.lemma_splitAt_snd_length@tok () Term)

; </end encoding FStar.List.Tot.Base.lemma_splitAt_snd_length>


; <Start encoding FStar.List.Tot.Base.unsnoc>

(declare-fun Tm_refine_3f6b38b2852708f36615f9b4db0f9ff1 (Term) Term)
(declare-fun FStar.List.Tot.Base.unsnoc (Term Term) Term)

(declare-fun Tm_arrow_f4bc61622db0c39a751170734a140783 () Term)
(declare-fun FStar.List.Tot.Base.unsnoc@tok () Term)


; </end encoding FStar.List.Tot.Base.unsnoc>


; <Start encoding FStar.List.Tot.Base.split3>


(declare-fun FStar.List.Tot.Base.split3 (Term Term Term) Term)

(declare-fun Tm_arrow_07dcb44faa0fb6172673970868e7ecff () Term)
(declare-fun FStar.List.Tot.Base.split3@tok () Term)


; </end encoding FStar.List.Tot.Base.split3>


; <Start encoding FStar.List.Tot.Base.partition_length>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.List.Tot.Base.partition_length (Term Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.List.Tot.Base.partition_length@tok () Term)

; </end encoding FStar.List.Tot.Base.partition_length>


; <Start encoding FStar.List.Tot.Base.bool_of_compare>

(declare-fun Tm_arrow_9877f854fbaabbcfda94f6c19b32ae3f (Term) Term)
(declare-fun FStar.List.Tot.Base.bool_of_compare (Term Term Term Term) Term)

(declare-fun Tm_arrow_a2f219461d35e20b7bc771538ca96429 () Term)
(declare-fun FStar.List.Tot.Base.bool_of_compare@tok () Term)


; </end encoding FStar.List.Tot.Base.bool_of_compare>


; <Start encoding FStar.List.Tot.Base.compare_of_bool>

(declare-fun Tm_arrow_c8126b87a2c25bb477df4a7a6b0eea9e (Term) Term)
(declare-fun FStar.List.Tot.Base.compare_of_bool (Term Term Term Term) Term)

(declare-fun Tm_arrow_8b54d4820d055c327440d0d4811d3a33 () Term)
(declare-fun FStar.List.Tot.Base.compare_of_bool@tok () Term)


; </end encoding FStar.List.Tot.Base.compare_of_bool>


; <Start encoding FStar.List.Tot.Base.compare_of_bool_of_compare>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.List.Tot.Base.compare_of_bool_of_compare (Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.List.Tot.Base.compare_of_bool_of_compare@tok () Term)

; </end encoding FStar.List.Tot.Base.compare_of_bool_of_compare>


; <Start encoding FStar.List.Tot.Base.sortWith>

;;;;;;;;;;;;;;;;Fuel-instrumented function name
(declare-fun FStar.List.Tot.Base.sortWith.fuel_instrumented (Fuel Term Term Term) Term)
;;;;;;;;;;;;;;;;Token for fuel-instrumented partial applications
(declare-fun FStar.List.Tot.Base.sortWith.fuel_instrumented_token () Term)
(declare-fun FStar.List.Tot.Base.sortWith (Term Term Term) Term)
(declare-fun FStar.List.Tot.Base.sortWith@tok () Term)



(declare-fun Tm_arrow_d29fb5884447b657cb725f9be68c5ba6 () Term)
;;;;;;;;;;;;;;;;kick_partial_app
;;; Fact-ids: Name FStar.List.Tot.Base.sortWith; Namespace FStar.List.Tot.Base
(assert (! (Valid (ApplyTT __uu__PartialApp
FStar.List.Tot.Base.bool_of_compare@tok))
:named @kick_partial_app_6123e8040f356c82d11b245dda0e1ccc))
;;;;;;;;;;;;;;;;Fuel irrelevance
;;; Fact-ids: Name FStar.List.Tot.Base.sortWith; Namespace FStar.List.Tot.Base
(assert (! 
;; def=FStar.List.Tot.Base.fst(542,8-542,16); use=FStar.List.Tot.Base.fst(542,8-542,16)
(forall ((@u0 Fuel) (@x1 Term) (@x2 Term) (@x3 Term))
 (! (= (FStar.List.Tot.Base.sortWith.fuel_instrumented (SFuel @u0)
@x1
@x2
@x3)
(FStar.List.Tot.Base.sortWith.fuel_instrumented ZFuel
@x1
@x2
@x3))
 

:pattern ((FStar.List.Tot.Base.sortWith.fuel_instrumented (SFuel @u0)
@x1
@x2
@x3))
:qid @fuel_irrelevance_FStar.List.Tot.Base.sortWith.fuel_instrumented))

:named @fuel_irrelevance_FStar.List.Tot.Base.sortWith.fuel_instrumented))
;;;;;;;;;;;;;;;;Correspondence of recursive function to instrumented version
;;; Fact-ids: Name FStar.List.Tot.Base.sortWith; Namespace FStar.List.Tot.Base
(assert (! 
;; def=FStar.List.Tot.Base.fst(542,8-542,16); use=FStar.List.Tot.Base.fst(542,8-542,16)
(forall ((@x0 Term) (@x1 Term) (@x2 Term))
 (! (= (FStar.List.Tot.Base.sortWith @x0
@x1
@x2)
(FStar.List.Tot.Base.sortWith.fuel_instrumented MaxFuel
@x0
@x1
@x2))
 

:pattern ((FStar.List.Tot.Base.sortWith @x0
@x1
@x2))
:qid @fuel_correspondence_FStar.List.Tot.Base.sortWith.fuel_instrumented))

:named @fuel_correspondence_FStar.List.Tot.Base.sortWith.fuel_instrumented))

; </end encoding FStar.List.Tot.Base.sortWith>


; <Start encoding FStar.List.Tot.Base.strict_prefix_of>

;;;;;;;;;;;;;;;;Fuel-instrumented function name
(declare-fun FStar.List.Tot.Base.strict_prefix_of.fuel_instrumented (Fuel Term Term Term) Term)
;;;;;;;;;;;;;;;;Token for fuel-instrumented partial applications
(declare-fun FStar.List.Tot.Base.strict_prefix_of.fuel_instrumented_token () Term)
(declare-fun FStar.List.Tot.Base.strict_prefix_of (Term Term Term) Term)
(declare-fun FStar.List.Tot.Base.strict_prefix_of@tok () Term)
(declare-fun Tm_refine_da3062322c9bea8d5b2058386775b91a () Term)

(declare-fun Tm_arrow_1d91178a138c1826d6a199b1613394f1 () Term)

;;;;;;;;;;;;;;;;Fuel irrelevance
;;; Fact-ids: Name FStar.List.Tot.Base.strict_prefix_of; Namespace FStar.List.Tot.Base
(assert (! 
;; def=FStar.List.Tot.Base.fst(551,8-551,24); use=FStar.List.Tot.Base.fst(551,8-551,24)
(forall ((@u0 Fuel) (@x1 Term) (@x2 Term) (@x3 Term))
 (! (= (FStar.List.Tot.Base.strict_prefix_of.fuel_instrumented (SFuel @u0)
@x1
@x2
@x3)
(FStar.List.Tot.Base.strict_prefix_of.fuel_instrumented ZFuel
@x1
@x2
@x3))
 

:pattern ((FStar.List.Tot.Base.strict_prefix_of.fuel_instrumented (SFuel @u0)
@x1
@x2
@x3))
:qid @fuel_irrelevance_FStar.List.Tot.Base.strict_prefix_of.fuel_instrumented))

:named @fuel_irrelevance_FStar.List.Tot.Base.strict_prefix_of.fuel_instrumented))
;;;;;;;;;;;;;;;;Correspondence of recursive function to instrumented version
;;; Fact-ids: Name FStar.List.Tot.Base.strict_prefix_of; Namespace FStar.List.Tot.Base
(assert (! 
;; def=FStar.List.Tot.Base.fst(551,8-551,24); use=FStar.List.Tot.Base.fst(551,8-551,24)
(forall ((@x0 Term) (@x1 Term) (@x2 Term))
 (! (= (FStar.List.Tot.Base.strict_prefix_of @x0
@x1
@x2)
(FStar.List.Tot.Base.strict_prefix_of.fuel_instrumented MaxFuel
@x0
@x1
@x2))
 

:pattern ((FStar.List.Tot.Base.strict_prefix_of @x0
@x1
@x2))
:qid @fuel_correspondence_FStar.List.Tot.Base.strict_prefix_of.fuel_instrumented))

:named @fuel_correspondence_FStar.List.Tot.Base.strict_prefix_of.fuel_instrumented))

; </end encoding FStar.List.Tot.Base.strict_prefix_of>


; <Start encoding FStar.List.Tot.Base.list_unref>

;;;;;;;;;;;;;;;;Fuel-instrumented function name
(declare-fun FStar.List.Tot.Base.list_unref.fuel_instrumented (Fuel Term Term Term) Term)
;;;;;;;;;;;;;;;;Token for fuel-instrumented partial applications
(declare-fun FStar.List.Tot.Base.list_unref.fuel_instrumented_token () Term)
(declare-fun FStar.List.Tot.Base.list_unref (Term Term Term) Term)
(declare-fun FStar.List.Tot.Base.list_unref@tok () Term)

(declare-fun Tm_refine_9f8cb5a84b67f50c9d5f87a914037545 (Term Term) Term)





(declare-fun Tm_arrow_6b3a7706fc085133138f00ee506ef176 () Term)
;;;;;;;;;;;;;;;;Fuel irrelevance
;;; Fact-ids: Name FStar.List.Tot.Base.list_unref; Namespace FStar.List.Tot.Base
(assert (! 
;; def=FStar.List.Tot.Base.fst(561,8-561,18); use=FStar.List.Tot.Base.fst(561,8-561,18)
(forall ((@u0 Fuel) (@x1 Term) (@x2 Term) (@x3 Term))
 (! (= (FStar.List.Tot.Base.list_unref.fuel_instrumented (SFuel @u0)
@x1
@x2
@x3)
(FStar.List.Tot.Base.list_unref.fuel_instrumented ZFuel
@x1
@x2
@x3))
 

:pattern ((FStar.List.Tot.Base.list_unref.fuel_instrumented (SFuel @u0)
@x1
@x2
@x3))
:qid @fuel_irrelevance_FStar.List.Tot.Base.list_unref.fuel_instrumented))

:named @fuel_irrelevance_FStar.List.Tot.Base.list_unref.fuel_instrumented))
;;;;;;;;;;;;;;;;Correspondence of recursive function to instrumented version
;;; Fact-ids: Name FStar.List.Tot.Base.list_unref; Namespace FStar.List.Tot.Base
(assert (! 
;; def=FStar.List.Tot.Base.fst(561,8-561,18); use=FStar.List.Tot.Base.fst(561,8-561,18)
(forall ((@x0 Term) (@x1 Term) (@x2 Term))
 (! (= (FStar.List.Tot.Base.list_unref @x0
@x1
@x2)
(FStar.List.Tot.Base.list_unref.fuel_instrumented MaxFuel
@x0
@x1
@x2))
 

:pattern ((FStar.List.Tot.Base.list_unref @x0
@x1
@x2))
:qid @fuel_correspondence_FStar.List.Tot.Base.list_unref.fuel_instrumented))

:named @fuel_correspondence_FStar.List.Tot.Base.list_unref.fuel_instrumented))

; </end encoding FStar.List.Tot.Base.list_unref>


; <Start encoding FStar.List.Tot.Base.list_refb>

;;;;;;;;;;;;;;;;Fuel-instrumented function name
(declare-fun FStar.List.Tot.Base.list_refb.fuel_instrumented (Fuel Term Term Term) Term)
;;;;;;;;;;;;;;;;Token for fuel-instrumented partial applications
(declare-fun FStar.List.Tot.Base.list_refb.fuel_instrumented_token () Term)
(declare-fun FStar.List.Tot.Base.list_refb (Term Term Term) Term)
(declare-fun FStar.List.Tot.Base.list_refb@tok () Term)

(declare-fun Tm_refine_3dfaece5a1f8e27ecb1367ff50145048 (Term Term) Term)





(declare-fun Tm_refine_b3daba88e15ae8a9be9dd341522270b2 (Term Term Term Term) Term)

(declare-fun Tm_refine_1d1ddbacd892e41ad4ba585e87296d2e (Term Term Term) Term)










(declare-fun Tm_arrow_73c684a5823f2875fcceead4ce671ea8 () Term)






;;;;;;;;;;;;;;;;Fuel irrelevance
;;; Fact-ids: Name FStar.List.Tot.Base.list_refb; Namespace FStar.List.Tot.Base
(assert (! 
;; def=FStar.List.Tot.Base.fst(571,8-571,17); use=FStar.List.Tot.Base.fst(571,8-571,17)
(forall ((@u0 Fuel) (@x1 Term) (@x2 Term) (@x3 Term))
 (! (= (FStar.List.Tot.Base.list_refb.fuel_instrumented (SFuel @u0)
@x1
@x2
@x3)
(FStar.List.Tot.Base.list_refb.fuel_instrumented ZFuel
@x1
@x2
@x3))
 

:pattern ((FStar.List.Tot.Base.list_refb.fuel_instrumented (SFuel @u0)
@x1
@x2
@x3))
:qid @fuel_irrelevance_FStar.List.Tot.Base.list_refb.fuel_instrumented))

:named @fuel_irrelevance_FStar.List.Tot.Base.list_refb.fuel_instrumented))
;;;;;;;;;;;;;;;;Correspondence of recursive function to instrumented version
;;; Fact-ids: Name FStar.List.Tot.Base.list_refb; Namespace FStar.List.Tot.Base
(assert (! 
;; def=FStar.List.Tot.Base.fst(571,8-571,17); use=FStar.List.Tot.Base.fst(571,8-571,17)
(forall ((@x0 Term) (@x1 Term) (@x2 Term))
 (! (= (FStar.List.Tot.Base.list_refb @x0
@x1
@x2)
(FStar.List.Tot.Base.list_refb.fuel_instrumented MaxFuel
@x0
@x1
@x2))
 

:pattern ((FStar.List.Tot.Base.list_refb @x0
@x1
@x2))
:qid @fuel_correspondence_FStar.List.Tot.Base.list_refb.fuel_instrumented))

:named @fuel_correspondence_FStar.List.Tot.Base.list_refb.fuel_instrumented))

; </end encoding FStar.List.Tot.Base.list_refb>


; <Start encoding FStar.List.Tot.Base.list_ref>

;;;;;;;;;;;;;;;;Fuel-instrumented function name
(declare-fun FStar.List.Tot.Base.list_ref.fuel_instrumented (Fuel Term Term Term) Term)
;;;;;;;;;;;;;;;;Token for fuel-instrumented partial applications
(declare-fun FStar.List.Tot.Base.list_ref.fuel_instrumented_token () Term)
(declare-fun FStar.List.Tot.Base.list_ref (Term Term Term) Term)
(declare-fun FStar.List.Tot.Base.list_ref@tok () Term)
(declare-fun Tm_arrow_81e65de2755319ee661cc1adc7d951e3 (Term) Term)
(declare-fun Tm_refine_751cc4d3e845537c495f9d7e1deb8aa9 (Term Term) Term)





(declare-fun Tm_refine_f61b92c00df29b87346e52dcf7670926 (Term Term Term Term) Term)

(declare-fun Tm_refine_16f0c42812e28aba7e30bc8c275306fb (Term Term Term) Term)










(declare-fun Tm_arrow_73f29356f974e35d230fb85375ad3965 () Term)






;;;;;;;;;;;;;;;;Fuel irrelevance
;;; Fact-ids: Name FStar.List.Tot.Base.list_ref; Namespace FStar.List.Tot.Base
(assert (! 
;; def=FStar.List.Tot.Base.fst(581,8-581,16); use=FStar.List.Tot.Base.fst(581,8-581,16)
(forall ((@u0 Fuel) (@x1 Term) (@x2 Term) (@x3 Term))
 (! (= (FStar.List.Tot.Base.list_ref.fuel_instrumented (SFuel @u0)
@x1
@x2
@x3)
(FStar.List.Tot.Base.list_ref.fuel_instrumented ZFuel
@x1
@x2
@x3))
 

:pattern ((FStar.List.Tot.Base.list_ref.fuel_instrumented (SFuel @u0)
@x1
@x2
@x3))
:qid @fuel_irrelevance_FStar.List.Tot.Base.list_ref.fuel_instrumented))

:named @fuel_irrelevance_FStar.List.Tot.Base.list_ref.fuel_instrumented))
;;;;;;;;;;;;;;;;Correspondence of recursive function to instrumented version
;;; Fact-ids: Name FStar.List.Tot.Base.list_ref; Namespace FStar.List.Tot.Base
(assert (! 
;; def=FStar.List.Tot.Base.fst(581,8-581,16); use=FStar.List.Tot.Base.fst(581,8-581,16)
(forall ((@x0 Term) (@x1 Term) (@x2 Term))
 (! (= (FStar.List.Tot.Base.list_ref @x0
@x1
@x2)
(FStar.List.Tot.Base.list_ref.fuel_instrumented MaxFuel
@x0
@x1
@x2))
 

:pattern ((FStar.List.Tot.Base.list_ref @x0
@x1
@x2))
:qid @fuel_correspondence_FStar.List.Tot.Base.list_ref.fuel_instrumented))

:named @fuel_correspondence_FStar.List.Tot.Base.list_ref.fuel_instrumented))

; </end encoding FStar.List.Tot.Base.list_ref>


; UNSAT CORE: @MaxFuel_assumption, @MaxIFuel_assumption, @fuel_correspondence_Prims.pow2.fuel_instrumented, @query, constructor_distinct_Lib.IntTypes.S16, constructor_distinct_Lib.IntTypes.S32, constructor_distinct_Lib.IntTypes.SEC, equality_tok_Lib.IntTypes.S16@tok, equality_tok_Lib.IntTypes.S32@tok, equality_tok_Lib.IntTypes.SEC@tok, equation_Lib.IntTypes.bits, equation_Lib.IntTypes.range, equation_Lib.IntTypes.signed, equation_Lib.IntTypes.unsigned, equation_Lib.IntTypes.v, equation_Prims.nat, equation_Prims.pos, equation_Spec.Kyber2.Params.params_q, int_inversion, int_typing, lemma_FStar.UInt.pow2_values, primitive_Prims.op_Addition, primitive_Prims.op_Division, primitive_Prims.op_LessThanOrEqual, primitive_Prims.op_Minus, primitive_Prims.op_Multiply, primitive_Prims.op_Subtraction, projection_inverse_BoxBool_proj_0, projection_inverse_BoxInt_proj_0, refinement_interpretation_Tm_refine_2b320913041b873fce938dd17eebb3e2, refinement_interpretation_Tm_refine_542f9d4f129664613f2483a6c88bc7c2, refinement_interpretation_Tm_refine_774ba3f728d91ead8ef40be66c9802e5, refinement_interpretation_Tm_refine_83845a86f2550cdf941eeb1d9b59602b, refinement_interpretation_Tm_refine_9d3fd79fd314167f1a9c213a188da3ec, refinement_interpretation_Tm_refine_b2401a8cabe2f9a01538f32548fa9f6c, typing_Lib.IntTypes.mk_int, typing_Prims.pow2, typing_tok_Lib.IntTypes.S32@tok, typing_tok_Lib.IntTypes.SEC@tok

;;; End module FStar.List.Tot.Base (637 decls; total size 82294)

;;; Start module FStar.List.Tot.Properties

; <Start encoding FStar.List.Tot.Properties.llist>

(declare-fun FStar.List.Tot.Properties.llist (Term Term) Term)
(declare-fun Tm_arrow_67c7b2626869cb316f118144000415b9 () Term)
(declare-fun FStar.List.Tot.Properties.llist@tok () Term)
(declare-fun Tm_refine_fbb3412f12fd58a91571022d7c9fa36d (Term Term) Term)

; </end encoding FStar.List.Tot.Properties.llist>


; <Start encoding FStar.List.Tot.Properties.mem_empty>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.List.Tot.Properties.mem_empty (Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.List.Tot.Properties.mem_empty@tok () Term)

; </end encoding FStar.List.Tot.Properties.mem_empty>


; <Start encoding FStar.List.Tot.Properties.mem_existsb>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.List.Tot.Properties.mem_existsb (Term Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.List.Tot.Properties.mem_existsb@tok () Term)

; </end encoding FStar.List.Tot.Properties.mem_existsb>


; <Start encoding FStar.List.Tot.Properties.mem_count>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.List.Tot.Properties.mem_count (Term Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.List.Tot.Properties.mem_count@tok () Term)

; </end encoding FStar.List.Tot.Properties.mem_count>


; <Start encoding FStar.List.Tot.Properties.rev_acc_length>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.List.Tot.Properties.rev_acc_length (Term Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.List.Tot.Properties.rev_acc_length@tok () Term)

; </end encoding FStar.List.Tot.Properties.rev_acc_length>


; <Start encoding FStar.List.Tot.Properties.rev_length>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.List.Tot.Properties.rev_length (Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.List.Tot.Properties.rev_length@tok () Term)

; </end encoding FStar.List.Tot.Properties.rev_length>


; <Start encoding FStar.List.Tot.Properties.rev_acc_mem>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.List.Tot.Properties.rev_acc_mem (Term Term Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.List.Tot.Properties.rev_acc_mem@tok () Term)

; </end encoding FStar.List.Tot.Properties.rev_acc_mem>


; <Start encoding FStar.List.Tot.Properties.rev_mem>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.List.Tot.Properties.rev_mem (Term Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.List.Tot.Properties.rev_mem@tok () Term)

; </end encoding FStar.List.Tot.Properties.rev_mem>


; <Start encoding FStar.List.Tot.Properties.append_nil_l>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.List.Tot.Properties.append_nil_l (Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.List.Tot.Properties.append_nil_l@tok () Term)

; </end encoding FStar.List.Tot.Properties.append_nil_l>


; <Start encoding FStar.List.Tot.Properties.append_l_nil>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.List.Tot.Properties.append_l_nil (Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.List.Tot.Properties.append_l_nil@tok () Term)

; </end encoding FStar.List.Tot.Properties.append_l_nil>


; <Start encoding FStar.List.Tot.Properties.append_cons_l>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.List.Tot.Properties.append_cons_l (Term Term Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.List.Tot.Properties.append_cons_l@tok () Term)

; </end encoding FStar.List.Tot.Properties.append_cons_l>


; <Start encoding FStar.List.Tot.Properties.append_l_cons>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.List.Tot.Properties.append_l_cons (Term Term Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.List.Tot.Properties.append_l_cons@tok () Term)

; </end encoding FStar.List.Tot.Properties.append_l_cons>


; <Start encoding FStar.List.Tot.Properties.append_assoc>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.List.Tot.Properties.append_assoc (Term Term Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.List.Tot.Properties.append_assoc@tok () Term)

; </end encoding FStar.List.Tot.Properties.append_assoc>


; <Start encoding FStar.List.Tot.Properties.append_length>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.List.Tot.Properties.append_length (Term Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.List.Tot.Properties.append_length@tok () Term)

; </end encoding FStar.List.Tot.Properties.append_length>


; <Start encoding FStar.List.Tot.Properties.append_mem>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.List.Tot.Properties.append_mem (Term Term Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.List.Tot.Properties.append_mem@tok () Term)

; </end encoding FStar.List.Tot.Properties.append_mem>


; <Start encoding FStar.List.Tot.Properties.append_mem_forall>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.List.Tot.Properties.append_mem_forall (Term Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.List.Tot.Properties.append_mem_forall@tok () Term)

; </end encoding FStar.List.Tot.Properties.append_mem_forall>


; <Start encoding FStar.List.Tot.Properties.append_count>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.List.Tot.Properties.append_count (Term Term Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.List.Tot.Properties.append_count@tok () Term)

; </end encoding FStar.List.Tot.Properties.append_count>


; <Start encoding FStar.List.Tot.Properties.append_count_forall>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.List.Tot.Properties.append_count_forall (Term Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.List.Tot.Properties.append_count_forall@tok () Term)

; </end encoding FStar.List.Tot.Properties.append_count_forall>


; <Start encoding FStar.List.Tot.Properties.append_eq_nil>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.List.Tot.Properties.append_eq_nil (Term Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.List.Tot.Properties.append_eq_nil@tok () Term)

; </end encoding FStar.List.Tot.Properties.append_eq_nil>


; <Start encoding FStar.List.Tot.Properties.append_eq_singl>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.List.Tot.Properties.append_eq_singl (Term Term Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.List.Tot.Properties.append_eq_singl@tok () Term)

; </end encoding FStar.List.Tot.Properties.append_eq_singl>


; <Start encoding FStar.List.Tot.Properties.append_inv_head>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.List.Tot.Properties.append_inv_head (Term Term Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.List.Tot.Properties.append_inv_head@tok () Term)

; </end encoding FStar.List.Tot.Properties.append_inv_head>


; <Start encoding FStar.List.Tot.Properties.append_inv_tail>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.List.Tot.Properties.append_inv_tail (Term Term Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.List.Tot.Properties.append_inv_tail@tok () Term)

; </end encoding FStar.List.Tot.Properties.append_inv_tail>


; <Start encoding FStar.List.Tot.Properties.append_length_inv_head>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.List.Tot.Properties.append_length_inv_head (Term Term Term Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.List.Tot.Properties.append_length_inv_head@tok () Term)

; </end encoding FStar.List.Tot.Properties.append_length_inv_head>


; <Start encoding FStar.List.Tot.Properties.append_length_inv_tail>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.List.Tot.Properties.append_length_inv_tail (Term Term Term Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.List.Tot.Properties.append_length_inv_tail@tok () Term)

; </end encoding FStar.List.Tot.Properties.append_length_inv_tail>


; <Start encoding FStar.List.Tot.Properties.lemma_append_last>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.List.Tot.Properties.lemma_append_last (Term Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.List.Tot.Properties.lemma_append_last@tok () Term)

; </end encoding FStar.List.Tot.Properties.lemma_append_last>


; <Start encoding FStar.List.Tot.Properties.rev'>

;;;;;;;;;;;;;;;;Fuel-instrumented function name
(declare-fun FStar.List.Tot.Properties.rev_.fuel_instrumented (Fuel Term Term) Term)
;;;;;;;;;;;;;;;;Token for fuel-instrumented partial applications
(declare-fun FStar.List.Tot.Properties.rev_.fuel_instrumented_token () Term)
(declare-fun FStar.List.Tot.Properties.rev_ (Term Term) Term)
(declare-fun FStar.List.Tot.Properties.rev_@tok () Term)

;;;;;;;;;;;;;;;;Fuel irrelevance
;;; Fact-ids: Name FStar.List.Tot.Properties.rev'; Namespace FStar.List.Tot.Properties
(assert (! 
;; def=FStar.List.Tot.Properties.fst(230,8-230,12); use=FStar.List.Tot.Properties.fst(230,8-230,12)
(forall ((@u0 Fuel) (@x1 Term) (@x2 Term))
 (! (= (FStar.List.Tot.Properties.rev_.fuel_instrumented (SFuel @u0)
@x1
@x2)
(FStar.List.Tot.Properties.rev_.fuel_instrumented ZFuel
@x1
@x2))
 

:pattern ((FStar.List.Tot.Properties.rev_.fuel_instrumented (SFuel @u0)
@x1
@x2))
:qid @fuel_irrelevance_FStar.List.Tot.Properties.rev_.fuel_instrumented))

:named @fuel_irrelevance_FStar.List.Tot.Properties.rev_.fuel_instrumented))
;;;;;;;;;;;;;;;;Correspondence of recursive function to instrumented version
;;; Fact-ids: Name FStar.List.Tot.Properties.rev'; Namespace FStar.List.Tot.Properties
(assert (! 
;; def=FStar.List.Tot.Properties.fst(230,8-230,12); use=FStar.List.Tot.Properties.fst(230,8-230,12)
(forall ((@x0 Term) (@x1 Term))
 (! (= (FStar.List.Tot.Properties.rev_ @x0
@x1)
(FStar.List.Tot.Properties.rev_.fuel_instrumented MaxFuel
@x0
@x1))
 

:pattern ((FStar.List.Tot.Properties.rev_ @x0
@x1))
:qid @fuel_correspondence_FStar.List.Tot.Properties.rev_.fuel_instrumented))

:named @fuel_correspondence_FStar.List.Tot.Properties.rev_.fuel_instrumented))

; </end encoding FStar.List.Tot.Properties.rev'>


; <Start encoding FStar.List.Tot.Properties.rev'T>

(declare-fun FStar.List.Tot.Properties.rev_T (Term) Term)
(declare-fun Tm_arrow_f34ce2ad5441b4bd300fa100b397737d (Term) Term)
(declare-fun Tm_arrow_42c6b27a859866d5307ff94c9f459cb1 () Term)
(declare-fun FStar.List.Tot.Properties.rev_T@tok () Term)

;;;;;;;;;;;;;;;;kick_partial_app
;;; Fact-ids: Name FStar.List.Tot.Properties.rev'T; Namespace FStar.List.Tot.Properties
(assert (! (Valid (ApplyTT __uu__PartialApp
FStar.List.Tot.Properties.rev_@tok))
:named @kick_partial_app_6780e2e9ce16d5330b5fda76b7bde9c5))

; </end encoding FStar.List.Tot.Properties.rev'T>


; <Start encoding FStar.List.Tot.Properties.rev_acc_rev'>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.List.Tot.Properties.rev_acc_rev_ (Term Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.List.Tot.Properties.rev_acc_rev_@tok () Term)

; </end encoding FStar.List.Tot.Properties.rev_acc_rev'>


; <Start encoding FStar.List.Tot.Properties.rev_rev'>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.List.Tot.Properties.rev_rev_ (Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.List.Tot.Properties.rev_rev_@tok () Term)

; </end encoding FStar.List.Tot.Properties.rev_rev'>


; <Start encoding FStar.List.Tot.Properties.rev'_append>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.List.Tot.Properties.rev__append (Term Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.List.Tot.Properties.rev__append@tok () Term)

; </end encoding FStar.List.Tot.Properties.rev'_append>


; <Start encoding FStar.List.Tot.Properties.rev_append>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.List.Tot.Properties.rev_append (Term Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.List.Tot.Properties.rev_append@tok () Term)

; </end encoding FStar.List.Tot.Properties.rev_append>


; <Start encoding FStar.List.Tot.Properties.rev'_involutive>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.List.Tot.Properties.rev__involutive (Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.List.Tot.Properties.rev__involutive@tok () Term)

; </end encoding FStar.List.Tot.Properties.rev'_involutive>


; <Start encoding FStar.List.Tot.Properties.rev_involutive>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.List.Tot.Properties.rev_involutive (Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.List.Tot.Properties.rev_involutive@tok () Term)

; </end encoding FStar.List.Tot.Properties.rev_involutive>


; <Start encoding FStar.List.Tot.Properties.lemma_snoc_length>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.List.Tot.Properties.lemma_snoc_length (Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.List.Tot.Properties.lemma_snoc_length@tok () Term)

; </end encoding FStar.List.Tot.Properties.lemma_snoc_length>


; <Start encoding FStar.List.Tot.Properties.rev'_list_ind>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.List.Tot.Properties.rev__list_ind (Term Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.List.Tot.Properties.rev__list_ind@tok () Term)

; </end encoding FStar.List.Tot.Properties.rev'_list_ind>


; <Start encoding FStar.List.Tot.Properties.rev_ind>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.List.Tot.Properties.rev_ind (Term Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.List.Tot.Properties.rev_ind@tok () Term)

; </end encoding FStar.List.Tot.Properties.rev_ind>


; <Start encoding FStar.List.Tot.Properties.map_lemma>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.List.Tot.Properties.map_lemma (Term Term Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.List.Tot.Properties.map_lemma@tok () Term)


; </end encoding FStar.List.Tot.Properties.map_lemma>


; <Start encoding FStar.List.Tot.Properties.lemma_unsnoc_snoc>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.List.Tot.Properties.lemma_unsnoc_snoc (Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.List.Tot.Properties.lemma_unsnoc_snoc@tok () Term)
(declare-fun Tm_refine_e88aba6d4c79a5625ab4330932edf7ed (Term) Term)

; </end encoding FStar.List.Tot.Properties.lemma_unsnoc_snoc>


; <Start encoding FStar.List.Tot.Properties.lemma_snoc_unsnoc>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.List.Tot.Properties.lemma_snoc_unsnoc (Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.List.Tot.Properties.lemma_snoc_unsnoc@tok () Term)

; </end encoding FStar.List.Tot.Properties.lemma_snoc_unsnoc>


; <Start encoding FStar.List.Tot.Properties.lemma_unsnoc_length>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.List.Tot.Properties.lemma_unsnoc_length (Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.List.Tot.Properties.lemma_unsnoc_length@tok () Term)

; </end encoding FStar.List.Tot.Properties.lemma_unsnoc_length>


; <Start encoding FStar.List.Tot.Properties.lemma_unsnoc_append>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.List.Tot.Properties.lemma_unsnoc_append (Term Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.List.Tot.Properties.lemma_unsnoc_append@tok () Term)

; </end encoding FStar.List.Tot.Properties.lemma_unsnoc_append>


; <Start encoding FStar.List.Tot.Properties.lemma_unsnoc_is_last>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.List.Tot.Properties.lemma_unsnoc_is_last (Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.List.Tot.Properties.lemma_unsnoc_is_last@tok () Term)

; </end encoding FStar.List.Tot.Properties.lemma_unsnoc_is_last>


; <Start encoding FStar.List.Tot.Properties.lemma_unsnoc_index>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.List.Tot.Properties.lemma_unsnoc_index (Term Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.List.Tot.Properties.lemma_unsnoc_index@tok () Term)

; </end encoding FStar.List.Tot.Properties.lemma_unsnoc_index>


; <Start encoding FStar.List.Tot.Properties.split_using>

;;;;;;;;;;;;;;;;Fuel-instrumented function name
(declare-fun FStar.List.Tot.Properties.split_using.fuel_instrumented (Fuel Term Term Term) Term)
;;;;;;;;;;;;;;;;Token for fuel-instrumented partial applications
(declare-fun FStar.List.Tot.Properties.split_using.fuel_instrumented_token () Term)
(declare-fun FStar.List.Tot.Properties.split_using (Term Term Term) Term)
(declare-fun FStar.List.Tot.Properties.split_using@tok () Term)
(declare-fun Tm_refine_ca5b6dc4e0a851997703798a1ffc5f70 (Term Term) Term)


(declare-fun Tm_ghost_arrow_583c096a402961cd40d8b718fb07bacc () Term)
;;;;;;;;;;;;;;;;Fuel irrelevance
;;; Fact-ids: Name FStar.List.Tot.Properties.split_using; Namespace FStar.List.Tot.Properties
(assert (! 
;; def=FStar.List.Tot.Properties.fst(380,8-380,19); use=FStar.List.Tot.Properties.fst(380,8-380,19)
(forall ((@u0 Fuel) (@x1 Term) (@x2 Term) (@x3 Term))
 (! (= (FStar.List.Tot.Properties.split_using.fuel_instrumented (SFuel @u0)
@x1
@x2
@x3)
(FStar.List.Tot.Properties.split_using.fuel_instrumented ZFuel
@x1
@x2
@x3))
 

:pattern ((FStar.List.Tot.Properties.split_using.fuel_instrumented (SFuel @u0)
@x1
@x2
@x3))
:qid @fuel_irrelevance_FStar.List.Tot.Properties.split_using.fuel_instrumented))

:named @fuel_irrelevance_FStar.List.Tot.Properties.split_using.fuel_instrumented))
;;;;;;;;;;;;;;;;Correspondence of recursive function to instrumented version
;;; Fact-ids: Name FStar.List.Tot.Properties.split_using; Namespace FStar.List.Tot.Properties
(assert (! 
;; def=FStar.List.Tot.Properties.fst(380,8-380,19); use=FStar.List.Tot.Properties.fst(380,8-380,19)
(forall ((@x0 Term) (@x1 Term) (@x2 Term))
 (! (= (FStar.List.Tot.Properties.split_using @x0
@x1
@x2)
(FStar.List.Tot.Properties.split_using.fuel_instrumented MaxFuel
@x0
@x1
@x2))
 

:pattern ((FStar.List.Tot.Properties.split_using @x0
@x1
@x2))
:qid @fuel_correspondence_FStar.List.Tot.Properties.split_using.fuel_instrumented))

:named @fuel_correspondence_FStar.List.Tot.Properties.split_using.fuel_instrumented))

; </end encoding FStar.List.Tot.Properties.split_using>


; <Start encoding FStar.List.Tot.Properties.lemma_split_using>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.List.Tot.Properties.lemma_split_using (Term Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.List.Tot.Properties.lemma_split_using@tok () Term)

; </end encoding FStar.List.Tot.Properties.lemma_split_using>


; <Start encoding FStar.List.Tot.Properties.index_of>

;;;;;;;;;;;;;;;;Fuel-instrumented function name
(declare-fun FStar.List.Tot.Properties.index_of.fuel_instrumented (Fuel Term Term Term) Term)
;;;;;;;;;;;;;;;;Token for fuel-instrumented partial applications
(declare-fun FStar.List.Tot.Properties.index_of.fuel_instrumented_token () Term)
(declare-fun FStar.List.Tot.Properties.index_of (Term Term Term) Term)
(declare-fun FStar.List.Tot.Properties.index_of@tok () Term)

(declare-fun Tm_refine_cd45ecc9daf74409c394004efbaa3338 (Term Term Term) Term)



(declare-fun Tm_ghost_arrow_d9cd5e48f458f8c211c59f9048af3929 () Term)

;;;;;;;;;;;;;;;;Fuel irrelevance
;;; Fact-ids: Name FStar.List.Tot.Properties.index_of; Namespace FStar.List.Tot.Properties
(assert (! 
;; def=FStar.List.Tot.Properties.fst(421,8-421,16); use=FStar.List.Tot.Properties.fst(421,8-421,16)
(forall ((@u0 Fuel) (@x1 Term) (@x2 Term) (@x3 Term))
 (! (= (FStar.List.Tot.Properties.index_of.fuel_instrumented (SFuel @u0)
@x1
@x2
@x3)
(FStar.List.Tot.Properties.index_of.fuel_instrumented ZFuel
@x1
@x2
@x3))
 

:pattern ((FStar.List.Tot.Properties.index_of.fuel_instrumented (SFuel @u0)
@x1
@x2
@x3))
:qid @fuel_irrelevance_FStar.List.Tot.Properties.index_of.fuel_instrumented))

:named @fuel_irrelevance_FStar.List.Tot.Properties.index_of.fuel_instrumented))
;;;;;;;;;;;;;;;;Correspondence of recursive function to instrumented version
;;; Fact-ids: Name FStar.List.Tot.Properties.index_of; Namespace FStar.List.Tot.Properties
(assert (! 
;; def=FStar.List.Tot.Properties.fst(421,8-421,16); use=FStar.List.Tot.Properties.fst(421,8-421,16)
(forall ((@x0 Term) (@x1 Term) (@x2 Term))
 (! (= (FStar.List.Tot.Properties.index_of @x0
@x1
@x2)
(FStar.List.Tot.Properties.index_of.fuel_instrumented MaxFuel
@x0
@x1
@x2))
 

:pattern ((FStar.List.Tot.Properties.index_of @x0
@x1
@x2))
:qid @fuel_correspondence_FStar.List.Tot.Properties.index_of.fuel_instrumented))

:named @fuel_correspondence_FStar.List.Tot.Properties.index_of.fuel_instrumented))

; </end encoding FStar.List.Tot.Properties.index_of>


; <Start encoding FStar.List.Tot.Properties.partition_mem>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.List.Tot.Properties.partition_mem (Term Term Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.List.Tot.Properties.partition_mem@tok () Term)

; </end encoding FStar.List.Tot.Properties.partition_mem>


; <Start encoding FStar.List.Tot.Properties.partition_mem_forall>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.List.Tot.Properties.partition_mem_forall (Term Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.List.Tot.Properties.partition_mem_forall@tok () Term)

; </end encoding FStar.List.Tot.Properties.partition_mem_forall>


; <Start encoding FStar.List.Tot.Properties.partition_mem_p_forall>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.List.Tot.Properties.partition_mem_p_forall (Term Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.List.Tot.Properties.partition_mem_p_forall@tok () Term)

; </end encoding FStar.List.Tot.Properties.partition_mem_p_forall>


; <Start encoding FStar.List.Tot.Properties.partition_count>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.List.Tot.Properties.partition_count (Term Term Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.List.Tot.Properties.partition_count@tok () Term)

; </end encoding FStar.List.Tot.Properties.partition_count>


; <Start encoding FStar.List.Tot.Properties.partition_count_forall>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.List.Tot.Properties.partition_count_forall (Term Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.List.Tot.Properties.partition_count_forall@tok () Term)

; </end encoding FStar.List.Tot.Properties.partition_count_forall>


; <Start encoding FStar.List.Tot.Properties.sortWith_permutation>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.List.Tot.Properties.sortWith_permutation (Term Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.List.Tot.Properties.sortWith_permutation@tok () Term)

; </end encoding FStar.List.Tot.Properties.sortWith_permutation>


; <Start encoding FStar.List.Tot.Properties.sorted>

;;;;;;;;;;;;;;;;Fuel-instrumented function name
(declare-fun FStar.List.Tot.Properties.sorted.fuel_instrumented (Fuel Term Term Term) Term)
;;;;;;;;;;;;;;;;Token for fuel-instrumented partial applications
(declare-fun FStar.List.Tot.Properties.sorted.fuel_instrumented_token () Term)
(declare-fun FStar.List.Tot.Properties.sorted (Term Term Term) Term)
(declare-fun FStar.List.Tot.Properties.sorted@tok () Term)



(declare-fun Tm_arrow_3ceaaa0abe084cc4615eb380e8d5e0cc () Term)
;;;;;;;;;;;;;;;;Fuel irrelevance
;;; Fact-ids: Name FStar.List.Tot.Properties.sorted; Namespace FStar.List.Tot.Properties
(assert (! 
;; def=FStar.List.Tot.Properties.fst(512,8-512,14); use=FStar.List.Tot.Properties.fst(512,8-512,14)
(forall ((@u0 Fuel) (@x1 Term) (@x2 Term) (@x3 Term))
 (! (= (FStar.List.Tot.Properties.sorted.fuel_instrumented (SFuel @u0)
@x1
@x2
@x3)
(FStar.List.Tot.Properties.sorted.fuel_instrumented ZFuel
@x1
@x2
@x3))
 

:pattern ((FStar.List.Tot.Properties.sorted.fuel_instrumented (SFuel @u0)
@x1
@x2
@x3))
:qid @fuel_irrelevance_FStar.List.Tot.Properties.sorted.fuel_instrumented))

:named @fuel_irrelevance_FStar.List.Tot.Properties.sorted.fuel_instrumented))
;;;;;;;;;;;;;;;;Correspondence of recursive function to instrumented version
;;; Fact-ids: Name FStar.List.Tot.Properties.sorted; Namespace FStar.List.Tot.Properties
(assert (! 
;; def=FStar.List.Tot.Properties.fst(512,8-512,14); use=FStar.List.Tot.Properties.fst(512,8-512,14)
(forall ((@x0 Term) (@x1 Term) (@x2 Term))
 (! (= (FStar.List.Tot.Properties.sorted @x0
@x1
@x2)
(FStar.List.Tot.Properties.sorted.fuel_instrumented MaxFuel
@x0
@x1
@x2))
 

:pattern ((FStar.List.Tot.Properties.sorted @x0
@x1
@x2))
:qid @fuel_correspondence_FStar.List.Tot.Properties.sorted.fuel_instrumented))

:named @fuel_correspondence_FStar.List.Tot.Properties.sorted.fuel_instrumented))

; </end encoding FStar.List.Tot.Properties.sorted>


; <Start encoding FStar.List.Tot.Properties.total_order>


(declare-fun FStar.List.Tot.Properties.total_order (Term Term) Term)

(declare-fun Tm_arrow_92649d42e4d7df07b51f92b06355903e () Term)
(declare-fun FStar.List.Tot.Properties.total_order@tok () Term)


; </end encoding FStar.List.Tot.Properties.total_order>


; <Start encoding FStar.List.Tot.Properties.append_sorted>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.List.Tot.Properties.append_sorted (Term Term Term Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.List.Tot.Properties.append_sorted@tok () Term)

(declare-fun Tm_refine_828abd88abe59cf052738363f3952d7b (Term Term) Term)


; </end encoding FStar.List.Tot.Properties.append_sorted>


; <Start encoding FStar.List.Tot.Properties.sortWith_sorted>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.List.Tot.Properties.sortWith_sorted (Term Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.List.Tot.Properties.sortWith_sorted@tok () Term)

; </end encoding FStar.List.Tot.Properties.sortWith_sorted>


; <Start encoding FStar.List.Tot.Properties.mem_memP>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.List.Tot.Properties.mem_memP (Term Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.List.Tot.Properties.mem_memP@tok () Term)

; </end encoding FStar.List.Tot.Properties.mem_memP>


; <Start encoding FStar.List.Tot.Properties.lemma_index_memP>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.List.Tot.Properties.lemma_index_memP (Term Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.List.Tot.Properties.lemma_index_memP@tok () Term)
(declare-fun Tm_refine_bf2fa1226f2c9a0f6671df3e80ddcb8e (Term Term) Term)

; </end encoding FStar.List.Tot.Properties.lemma_index_memP>


; <Start encoding FStar.List.Tot.Properties.memP_empty>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.List.Tot.Properties.memP_empty (Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.List.Tot.Properties.memP_empty@tok () Term)

; </end encoding FStar.List.Tot.Properties.memP_empty>


; <Start encoding FStar.List.Tot.Properties.memP_existsb>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.List.Tot.Properties.memP_existsb (Term Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.List.Tot.Properties.memP_existsb@tok () Term)

; </end encoding FStar.List.Tot.Properties.memP_existsb>


; <Start encoding FStar.List.Tot.Properties.memP_map_intro>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.List.Tot.Properties.memP_map_intro (Term Term Term Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.List.Tot.Properties.memP_map_intro@tok () Term)

; </end encoding FStar.List.Tot.Properties.memP_map_intro>


; <Start encoding FStar.List.Tot.Properties.memP_map_elim>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.List.Tot.Properties.memP_map_elim (Term Term Term Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.List.Tot.Properties.memP_map_elim@tok () Term)

; </end encoding FStar.List.Tot.Properties.memP_map_elim>


; <Start encoding FStar.List.Tot.Properties.noRepeats_nil>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.List.Tot.Properties.noRepeats_nil (Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.List.Tot.Properties.noRepeats_nil@tok () Term)

; </end encoding FStar.List.Tot.Properties.noRepeats_nil>


; <Start encoding FStar.List.Tot.Properties.noRepeats_cons>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.List.Tot.Properties.noRepeats_cons (Term Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.List.Tot.Properties.noRepeats_cons@tok () Term)

; </end encoding FStar.List.Tot.Properties.noRepeats_cons>


; <Start encoding FStar.List.Tot.Properties.noRepeats_append_elim>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.List.Tot.Properties.noRepeats_append_elim (Term Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.List.Tot.Properties.noRepeats_append_elim@tok () Term)

; </end encoding FStar.List.Tot.Properties.noRepeats_append_elim>


; <Start encoding FStar.List.Tot.Properties.noRepeats_append_intro>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.List.Tot.Properties.noRepeats_append_intro (Term Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.List.Tot.Properties.noRepeats_append_intro@tok () Term)

; </end encoding FStar.List.Tot.Properties.noRepeats_append_intro>


; <Start encoding FStar.List.Tot.Properties.assoc_nil>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.List.Tot.Properties.assoc_nil (Term Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.List.Tot.Properties.assoc_nil@tok () Term)

; </end encoding FStar.List.Tot.Properties.assoc_nil>


; <Start encoding FStar.List.Tot.Properties.assoc_cons_eq>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.List.Tot.Properties.assoc_cons_eq (Term Term Term Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.List.Tot.Properties.assoc_cons_eq@tok () Term)

; </end encoding FStar.List.Tot.Properties.assoc_cons_eq>


; <Start encoding FStar.List.Tot.Properties.assoc_cons_not_eq>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.List.Tot.Properties.assoc_cons_not_eq (Term Term Term Term Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.List.Tot.Properties.assoc_cons_not_eq@tok () Term)

; </end encoding FStar.List.Tot.Properties.assoc_cons_not_eq>


; <Start encoding FStar.List.Tot.Properties.assoc_append_elim_r>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.List.Tot.Properties.assoc_append_elim_r (Term Term Term Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.List.Tot.Properties.assoc_append_elim_r@tok () Term)

; </end encoding FStar.List.Tot.Properties.assoc_append_elim_r>


; <Start encoding FStar.List.Tot.Properties.assoc_append_elim_l>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.List.Tot.Properties.assoc_append_elim_l (Term Term Term Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.List.Tot.Properties.assoc_append_elim_l@tok () Term)

; </end encoding FStar.List.Tot.Properties.assoc_append_elim_l>


; <Start encoding FStar.List.Tot.Properties.assoc_memP_some>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.List.Tot.Properties.assoc_memP_some (Term Term Term Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.List.Tot.Properties.assoc_memP_some@tok () Term)

; </end encoding FStar.List.Tot.Properties.assoc_memP_some>


; <Start encoding FStar.List.Tot.Properties.assoc_memP_none>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.List.Tot.Properties.assoc_memP_none (Term Term Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.List.Tot.Properties.assoc_memP_none@tok () Term)

; </end encoding FStar.List.Tot.Properties.assoc_memP_none>


; <Start encoding FStar.List.Tot.Properties.assoc_mem>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.List.Tot.Properties.assoc_mem (Term Term Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.List.Tot.Properties.assoc_mem@tok () Term)

; </end encoding FStar.List.Tot.Properties.assoc_mem>


; <Start encoding FStar.List.Tot.Properties.fold_left_invar>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.List.Tot.Properties.fold_left_invar (Term Term Term Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.List.Tot.Properties.fold_left_invar@tok () Term)

; </end encoding FStar.List.Tot.Properties.fold_left_invar>


; <Start encoding FStar.List.Tot.Properties.fold_left_map>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.List.Tot.Properties.fold_left_map (Term Term Term Term Term Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.List.Tot.Properties.fold_left_map@tok () Term)

; </end encoding FStar.List.Tot.Properties.fold_left_map>


; <Start encoding FStar.List.Tot.Properties.map_append>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.List.Tot.Properties.map_append (Term Term Term Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.List.Tot.Properties.map_append@tok () Term)

; </end encoding FStar.List.Tot.Properties.map_append>


; <Start encoding FStar.List.Tot.Properties.fold_left_append>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.List.Tot.Properties.fold_left_append (Term Term Term Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.List.Tot.Properties.fold_left_append@tok () Term)

; </end encoding FStar.List.Tot.Properties.fold_left_append>


; <Start encoding FStar.List.Tot.Properties.fold_left_monoid>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.List.Tot.Properties.fold_left_monoid (Term Term Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.List.Tot.Properties.fold_left_monoid@tok () Term)

; </end encoding FStar.List.Tot.Properties.fold_left_monoid>


; <Start encoding FStar.List.Tot.Properties.fold_left_append_monoid>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.List.Tot.Properties.fold_left_append_monoid (Term Term Term Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.List.Tot.Properties.fold_left_append_monoid@tok () Term)

; </end encoding FStar.List.Tot.Properties.fold_left_append_monoid>


; <Start encoding FStar.List.Tot.Properties.index_extensionality_aux>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.List.Tot.Properties.index_extensionality_aux (Term Term Term Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.List.Tot.Properties.index_extensionality_aux@tok () Term)

; </end encoding FStar.List.Tot.Properties.index_extensionality_aux>


; <Start encoding FStar.List.Tot.Properties.index_extensionality>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.List.Tot.Properties.index_extensionality (Term Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.List.Tot.Properties.index_extensionality@tok () Term)

; </end encoding FStar.List.Tot.Properties.index_extensionality>


; <Start encoding FStar.List.Tot.Properties.strict_prefix_of_nil>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.List.Tot.Properties.strict_prefix_of_nil (Term Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.List.Tot.Properties.strict_prefix_of_nil@tok () Term)

; </end encoding FStar.List.Tot.Properties.strict_prefix_of_nil>


; <Start encoding FStar.List.Tot.Properties.strict_prefix_of_or_eq_nil>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.List.Tot.Properties.strict_prefix_of_or_eq_nil (Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.List.Tot.Properties.strict_prefix_of_or_eq_nil@tok () Term)

; </end encoding FStar.List.Tot.Properties.strict_prefix_of_or_eq_nil>


; <Start encoding FStar.List.Tot.Properties.strict_prefix_of_cons>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.List.Tot.Properties.strict_prefix_of_cons (Term Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.List.Tot.Properties.strict_prefix_of_cons@tok () Term)

; </end encoding FStar.List.Tot.Properties.strict_prefix_of_cons>


; <Start encoding FStar.List.Tot.Properties.strict_prefix_of_trans>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.List.Tot.Properties.strict_prefix_of_trans (Term Term Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.List.Tot.Properties.strict_prefix_of_trans@tok () Term)

; </end encoding FStar.List.Tot.Properties.strict_prefix_of_trans>


; <Start encoding FStar.List.Tot.Properties.strict_prefix_of_correct>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.List.Tot.Properties.strict_prefix_of_correct (Term Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.List.Tot.Properties.strict_prefix_of_correct@tok () Term)

; </end encoding FStar.List.Tot.Properties.strict_prefix_of_correct>


; <Start encoding FStar.List.Tot.Properties.map_strict_prefix_of>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.List.Tot.Properties.map_strict_prefix_of (Term Term Term Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.List.Tot.Properties.map_strict_prefix_of@tok () Term)

; </end encoding FStar.List.Tot.Properties.map_strict_prefix_of>


; <Start encoding FStar.List.Tot.Properties.mem_strict_prefix_of>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.List.Tot.Properties.mem_strict_prefix_of (Term Term Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.List.Tot.Properties.mem_strict_prefix_of@tok () Term)

; </end encoding FStar.List.Tot.Properties.mem_strict_prefix_of>


; <Start encoding FStar.List.Tot.Properties.strict_prefix_of_exists_append>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.List.Tot.Properties.strict_prefix_of_exists_append (Term Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.List.Tot.Properties.strict_prefix_of_exists_append@tok () Term)

; </end encoding FStar.List.Tot.Properties.strict_prefix_of_exists_append>


; <Start encoding FStar.List.Tot.Properties.strict_prefix_of_or_eq_exists_append>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.List.Tot.Properties.strict_prefix_of_or_eq_exists_append (Term Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.List.Tot.Properties.strict_prefix_of_or_eq_exists_append@tok () Term)

; </end encoding FStar.List.Tot.Properties.strict_prefix_of_or_eq_exists_append>


; <Start encoding FStar.List.Tot.Properties.precedes_tl>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.List.Tot.Properties.precedes_tl (Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.List.Tot.Properties.precedes_tl@tok () Term)

; </end encoding FStar.List.Tot.Properties.precedes_tl>


; <Start encoding FStar.List.Tot.Properties.precedes_append_cons_r>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.List.Tot.Properties.precedes_append_cons_r (Term Term Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.List.Tot.Properties.precedes_append_cons_r@tok () Term)

; </end encoding FStar.List.Tot.Properties.precedes_append_cons_r>


; <Start encoding FStar.List.Tot.Properties.precedes_append_cons_prod_r>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.List.Tot.Properties.precedes_append_cons_prod_r (Term Term Term Term Term Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.List.Tot.Properties.precedes_append_cons_prod_r@tok () Term)

; </end encoding FStar.List.Tot.Properties.precedes_append_cons_prod_r>


; <Start encoding FStar.List.Tot.Properties.memP_precedes>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.List.Tot.Properties.memP_precedes (Term Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.List.Tot.Properties.memP_precedes@tok () Term)

; </end encoding FStar.List.Tot.Properties.memP_precedes>


; <Start encoding FStar.List.Tot.Properties.assoc_precedes>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.List.Tot.Properties.assoc_precedes (Term Term Term Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.List.Tot.Properties.assoc_precedes@tok () Term)

; </end encoding FStar.List.Tot.Properties.assoc_precedes>


; <Start encoding FStar.List.Tot.Properties.find_none>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.List.Tot.Properties.find_none (Term Term Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.List.Tot.Properties.find_none@tok () Term)

; </end encoding FStar.List.Tot.Properties.find_none>


; <Start encoding FStar.List.Tot.Properties.append_init_last>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.List.Tot.Properties.append_init_last (Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.List.Tot.Properties.append_init_last@tok () Term)

; </end encoding FStar.List.Tot.Properties.append_init_last>


; <Start encoding FStar.List.Tot.Properties.init_last_def>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.List.Tot.Properties.init_last_def (Term Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.List.Tot.Properties.init_last_def@tok () Term)

; </end encoding FStar.List.Tot.Properties.init_last_def>


; <Start encoding FStar.List.Tot.Properties.init_last_inj>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.List.Tot.Properties.init_last_inj (Term Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.List.Tot.Properties.init_last_inj@tok () Term)

; </end encoding FStar.List.Tot.Properties.init_last_inj>


; UNSAT CORE: @MaxFuel_assumption, @MaxIFuel_assumption, @fuel_correspondence_Prims.pow2.fuel_instrumented, @query, constructor_distinct_Lib.IntTypes.S16, constructor_distinct_Lib.IntTypes.S32, constructor_distinct_Lib.IntTypes.SEC, equality_tok_Lib.IntTypes.S16@tok, equality_tok_Lib.IntTypes.S32@tok, equality_tok_Lib.IntTypes.SEC@tok, equation_Lib.IntTypes.bits, equation_Lib.IntTypes.range, equation_Lib.IntTypes.signed, equation_Lib.IntTypes.unsigned, equation_Lib.IntTypes.v, equation_Prims.nat, equation_Prims.pos, equation_Spec.Kyber2.Params.params_q, int_inversion, int_typing, lemma_FStar.UInt.pow2_values, primitive_Prims.op_Addition, primitive_Prims.op_Division, primitive_Prims.op_LessThanOrEqual, primitive_Prims.op_Minus, primitive_Prims.op_Multiply, primitive_Prims.op_Subtraction, projection_inverse_BoxBool_proj_0, projection_inverse_BoxInt_proj_0, refinement_interpretation_Tm_refine_2b320913041b873fce938dd17eebb3e2, refinement_interpretation_Tm_refine_542f9d4f129664613f2483a6c88bc7c2, refinement_interpretation_Tm_refine_774ba3f728d91ead8ef40be66c9802e5, refinement_interpretation_Tm_refine_83845a86f2550cdf941eeb1d9b59602b, refinement_interpretation_Tm_refine_9d3fd79fd314167f1a9c213a188da3ec, refinement_interpretation_Tm_refine_b2401a8cabe2f9a01538f32548fa9f6c, typing_Lib.IntTypes.mk_int, typing_Prims.pow2, typing_tok_Lib.IntTypes.S32@tok, typing_tok_Lib.IntTypes.SEC@tok

;;; End module FStar.List.Tot.Properties (449 decls; total size 47771)

;;; Start module FStar.List.Tot

; UNSAT CORE: @MaxFuel_assumption, @MaxIFuel_assumption, @fuel_correspondence_Prims.pow2.fuel_instrumented, @query, constructor_distinct_Lib.IntTypes.S16, constructor_distinct_Lib.IntTypes.S32, constructor_distinct_Lib.IntTypes.SEC, equality_tok_Lib.IntTypes.S16@tok, equality_tok_Lib.IntTypes.S32@tok, equality_tok_Lib.IntTypes.SEC@tok, equation_Lib.IntTypes.bits, equation_Lib.IntTypes.range, equation_Lib.IntTypes.signed, equation_Lib.IntTypes.unsigned, equation_Lib.IntTypes.v, equation_Prims.nat, equation_Prims.pos, equation_Spec.Kyber2.Params.params_q, int_inversion, int_typing, lemma_FStar.UInt.pow2_values, primitive_Prims.op_Addition, primitive_Prims.op_Division, primitive_Prims.op_LessThanOrEqual, primitive_Prims.op_Minus, primitive_Prims.op_Multiply, primitive_Prims.op_Subtraction, projection_inverse_BoxBool_proj_0, projection_inverse_BoxInt_proj_0, refinement_interpretation_Tm_refine_2b320913041b873fce938dd17eebb3e2, refinement_interpretation_Tm_refine_542f9d4f129664613f2483a6c88bc7c2, refinement_interpretation_Tm_refine_774ba3f728d91ead8ef40be66c9802e5, refinement_interpretation_Tm_refine_83845a86f2550cdf941eeb1d9b59602b, refinement_interpretation_Tm_refine_9d3fd79fd314167f1a9c213a188da3ec, refinement_interpretation_Tm_refine_b2401a8cabe2f9a01538f32548fa9f6c, typing_Lib.IntTypes.mk_int, typing_Prims.pow2, typing_tok_Lib.IntTypes.S32@tok, typing_tok_Lib.IntTypes.SEC@tok

;;; End module FStar.List.Tot (1 decls; total size 1400)

;;; Start module FStar.Seq.Base

; <Start encoding FStar.Seq.Base.seq>

(declare-fun FStar.Seq.Base.seq (Term) Term)

(declare-fun FStar.Seq.Base.seq@tok () Term)

; </end encoding FStar.Seq.Base.seq>


; <Start encoding FStar.Seq.Base.seq__uu___haseq>


; </end encoding FStar.Seq.Base.seq__uu___haseq>


; <Start encoding FStar.Seq.Base.length>

(declare-fun FStar.Seq.Base.length (Term Term) Term)
(declare-fun Tm_arrow_d2c01593e1ccf972aadc4bced72f8166 () Term)
(declare-fun FStar.Seq.Base.length@tok () Term)

; </end encoding FStar.Seq.Base.length>


; <Start encoding FStar.Seq.Base.index>

(declare-fun Tm_refine_d83f8da8ef6c1cb9f71d1465c1bb1c55 (Term Term) Term)
(declare-fun FStar.Seq.Base.index (Term Term Term) Term)

(declare-fun Tm_arrow_1910ef5262f2ee8e712b6609a232b1ea () Term)
(declare-fun FStar.Seq.Base.index@tok () Term)

; </end encoding FStar.Seq.Base.index>


; <Start encoding FStar.Seq.Base.cons>

(declare-fun FStar.Seq.Base.cons (Term Term Term) Term)
(declare-fun Tm_arrow_62ad6018b578ef7ed3c0e74bdebff729 () Term)
(declare-fun FStar.Seq.Base.cons@tok () Term)

; </end encoding FStar.Seq.Base.cons>


; <Start encoding FStar.Seq.Base.hd>

(declare-fun Tm_refine_167ef714932ec832fb671890fc3eee6c (Term) Term)
(declare-fun FStar.Seq.Base.hd (Term Term) Term)

(declare-fun Tm_arrow_fde6b9111cb8aaf87a1b6689af62ed69 () Term)
(declare-fun FStar.Seq.Base.hd@tok () Term)

; </end encoding FStar.Seq.Base.hd>


; <Start encoding FStar.Seq.Base.tl>


(declare-fun FStar.Seq.Base.tl (Term Term) Term)

(declare-fun Tm_arrow_3db93b3d63ab329f9ab58ee76fda4c87 () Term)
(declare-fun FStar.Seq.Base.tl@tok () Term)

; </end encoding FStar.Seq.Base.tl>


; <Start encoding FStar.Seq.Base.create>

(declare-fun FStar.Seq.Base.create (Term Term Term) Term)
(declare-fun Tm_arrow_b5b3d4fcc48eb666a8878550e50df9fb () Term)
(declare-fun FStar.Seq.Base.create@tok () Term)

; </end encoding FStar.Seq.Base.create>


; <Start encoding FStar.Seq.Base.init_aux>

(declare-fun Tm_refine_c1424615841f28cac7fc34e92b7ff33c (Term) Term)

(declare-fun Tm_arrow_44bb45ed5c2534b346e0f58ea5033251 (Term Term) Term)
(declare-fun FStar.Seq.Base.init_aux (Term Term Term Term) Term)



(declare-fun Tm_arrow_da6bbab10714c064205223f9990745bd () Term)
(declare-fun FStar.Seq.Base.init_aux@tok () Term)

; </end encoding FStar.Seq.Base.init_aux>


; <Start encoding FStar.Seq.Base.init>



(declare-fun FStar.Seq.Base.init (Term Term Term) Term)


(declare-fun Tm_arrow_d638d84259a58eff38c91944355ac313 () Term)
(declare-fun FStar.Seq.Base.init@tok () Term)

; </end encoding FStar.Seq.Base.init>


; <Start encoding FStar.Seq.Base.empty>

(declare-fun FStar.Seq.Base.empty (Term) Term)
(declare-fun Tm_refine_b913a3f691ca99086652e0a655e72f17 (Term) Term)
(declare-fun Tm_arrow_c39fb4e3e203a822394c714f70ec2d2c () Term)
(declare-fun FStar.Seq.Base.empty@tok () Term)


; </end encoding FStar.Seq.Base.empty>


; <Start encoding FStar.Seq.Base.createEmpty>

(declare-fun FStar.Seq.Base.createEmpty (Term) Term)


(declare-fun FStar.Seq.Base.createEmpty@tok () Term)


; </end encoding FStar.Seq.Base.createEmpty>


; <Start encoding FStar.Seq.Base.lemma_empty>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.Seq.Base.lemma_empty (Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.Seq.Base.lemma_empty@tok () Term)

; </end encoding FStar.Seq.Base.lemma_empty>


; <Start encoding FStar.Seq.Base.upd>


(declare-fun FStar.Seq.Base.upd (Term Term Term Term) Term)

(declare-fun Tm_arrow_12766e98f50c8b91e296bbc369061265 () Term)
(declare-fun FStar.Seq.Base.upd@tok () Term)

; </end encoding FStar.Seq.Base.upd>


; <Start encoding FStar.Seq.Base.append>

(declare-fun FStar.Seq.Base.append (Term Term Term) Term)
(declare-fun Tm_arrow_22c1b165cc91e8aafbceb8b36244be8e () Term)
(declare-fun FStar.Seq.Base.append@tok () Term)

; </end encoding FStar.Seq.Base.append>


; <Start encoding FStar.Seq.Base.op_At_Bar>

(declare-fun FStar.Seq.Base.op_At_Bar (Term Term Term) Term)

(declare-fun FStar.Seq.Base.op_At_Bar@tok () Term)

; </end encoding FStar.Seq.Base.op_At_Bar>


; <Start encoding FStar.Seq.Base.slice>

(declare-fun Tm_refine_81407705a0828c2c1b1976675443f647 (Term Term Term) Term)
(declare-fun FStar.Seq.Base.slice (Term Term Term Term) Term)

(declare-fun Tm_arrow_f59809c98fadf275c00ce819f5868628 () Term)
(declare-fun FStar.Seq.Base.slice@tok () Term)

; </end encoding FStar.Seq.Base.slice>


; <Start encoding FStar.Seq.Base.lemma_create_len>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.Seq.Base.lemma_create_len (Term Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.Seq.Base.lemma_create_len@tok () Term)

; </end encoding FStar.Seq.Base.lemma_create_len>


; <Start encoding FStar.Seq.Base.lemma_init_aux_len>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.Seq.Base.lemma_init_aux_len (Term Term Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.Seq.Base.lemma_init_aux_len@tok () Term)




; </end encoding FStar.Seq.Base.lemma_init_aux_len>


; <Start encoding FStar.Seq.Base.lemma_init_len>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.Seq.Base.lemma_init_len (Term Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.Seq.Base.lemma_init_len@tok () Term)



; </end encoding FStar.Seq.Base.lemma_init_len>


; <Start encoding FStar.Seq.Base.lemma_len_upd>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.Seq.Base.lemma_len_upd (Term Term Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.Seq.Base.lemma_len_upd@tok () Term)
(declare-fun Tm_refine_2ca062977a42c36634b89c1c4f193f79 (Term Term) Term)

; </end encoding FStar.Seq.Base.lemma_len_upd>


; <Start encoding FStar.Seq.Base.lemma_len_append>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.Seq.Base.lemma_len_append (Term Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.Seq.Base.lemma_len_append@tok () Term)

; </end encoding FStar.Seq.Base.lemma_len_append>


; <Start encoding FStar.Seq.Base.lemma_len_slice>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.Seq.Base.lemma_len_slice (Term Term Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.Seq.Base.lemma_len_slice@tok () Term)


; </end encoding FStar.Seq.Base.lemma_len_slice>


; <Start encoding FStar.Seq.Base.lemma_index_create>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.Seq.Base.lemma_index_create (Term Term Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.Seq.Base.lemma_index_create@tok () Term)


; </end encoding FStar.Seq.Base.lemma_index_create>


; <Start encoding FStar.Seq.Base.lemma_index_upd1>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.Seq.Base.lemma_index_upd1 (Term Term Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.Seq.Base.lemma_index_upd1@tok () Term)


; </end encoding FStar.Seq.Base.lemma_index_upd1>


; <Start encoding FStar.Seq.Base.lemma_index_upd2>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.Seq.Base.lemma_index_upd2 (Term Term Term Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.Seq.Base.lemma_index_upd2@tok () Term)

(declare-fun Tm_refine_df81b3f17797c6f405c1dbb191651292 (Term Term Term) Term)

; </end encoding FStar.Seq.Base.lemma_index_upd2>


; <Start encoding FStar.Seq.Base.lemma_index_app1>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.Seq.Base.lemma_index_app1 (Term Term Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.Seq.Base.lemma_index_app1@tok () Term)


; </end encoding FStar.Seq.Base.lemma_index_app1>


; <Start encoding FStar.Seq.Base.lemma_index_app2>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.Seq.Base.lemma_index_app2 (Term Term Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.Seq.Base.lemma_index_app2@tok () Term)
(declare-fun Tm_refine_ac201cf927190d39c033967b63cb957b (Term Term Term) Term)

; </end encoding FStar.Seq.Base.lemma_index_app2>


; <Start encoding FStar.Seq.Base.lemma_index_slice>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.Seq.Base.lemma_index_slice (Term Term Term Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.Seq.Base.lemma_index_slice@tok () Term)
(declare-fun Tm_refine_d3d07693cd71377864ef84dc97d10ec1 (Term Term Term) Term)
(declare-fun Tm_refine_35a0739c434508f48d0bb1d5cd5df9e8 (Term Term) Term)

; </end encoding FStar.Seq.Base.lemma_index_slice>


; <Start encoding FStar.Seq.Base.hasEq_lemma>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.Seq.Base.hasEq_lemma (Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.Seq.Base.hasEq_lemma@tok () Term)

; </end encoding FStar.Seq.Base.hasEq_lemma>


; <Start encoding FStar.Seq.Base.equal>

(declare-fun FStar.Seq.Base.equal (Term Term Term) Term)
(declare-fun Tm_arrow_2ed6082b86d605508c94c4b8a46966f5 () Term)
(declare-fun FStar.Seq.Base.equal@tok () Term)

; </end encoding FStar.Seq.Base.equal>


; <Start encoding FStar.Seq.Base.eq_i>

;;;;;;;;;;;;;;;;Fuel-instrumented function name
(declare-fun FStar.Seq.Base.eq_i.fuel_instrumented (Fuel Term Term Term Term) Term)
;;;;;;;;;;;;;;;;Token for fuel-instrumented partial applications
(declare-fun FStar.Seq.Base.eq_i.fuel_instrumented_token () Term)
(declare-fun FStar.Seq.Base.eq_i (Term Term Term Term) Term)
(declare-fun FStar.Seq.Base.eq_i@tok () Term)
(declare-fun Tm_refine_4639d389381bee5cf8cf77b7a6585074 (Term Term) Term)
(declare-fun Tm_refine_b361ba8089a6e963921008d537e799a1 (Term Term) Term)
(declare-fun Tm_refine_331c14d442c5ee89a4fce6ea305c920f (Term Term Term) Term)
(declare-fun Tm_refine_51f956555266662f5f0ed4aac81d10bc (Term Term Term Term) Term)






(declare-fun Tm_arrow_e5286e13b5c071949ebc5146fbef7d7f () Term)


;;;;;;;;;;;;;;;;Fuel irrelevance
;;; Fact-ids: Name FStar.Seq.Base.eq_i; Namespace FStar.Seq.Base
(assert (! 
;; def=FStar.Seq.Base.fst(194,8-194,12); use=FStar.Seq.Base.fst(194,8-194,12)
(forall ((@u0 Fuel) (@x1 Term) (@x2 Term) (@x3 Term) (@x4 Term))
 (! (= (FStar.Seq.Base.eq_i.fuel_instrumented (SFuel @u0)
@x1
@x2
@x3
@x4)
(FStar.Seq.Base.eq_i.fuel_instrumented ZFuel
@x1
@x2
@x3
@x4))
 

:pattern ((FStar.Seq.Base.eq_i.fuel_instrumented (SFuel @u0)
@x1
@x2
@x3
@x4))
:qid @fuel_irrelevance_FStar.Seq.Base.eq_i.fuel_instrumented))

:named @fuel_irrelevance_FStar.Seq.Base.eq_i.fuel_instrumented))
;;;;;;;;;;;;;;;;Correspondence of recursive function to instrumented version
;;; Fact-ids: Name FStar.Seq.Base.eq_i; Namespace FStar.Seq.Base
(assert (! 
;; def=FStar.Seq.Base.fst(194,8-194,12); use=FStar.Seq.Base.fst(194,8-194,12)
(forall ((@x0 Term) (@x1 Term) (@x2 Term) (@x3 Term))
 (! (= (FStar.Seq.Base.eq_i @x0
@x1
@x2
@x3)
(FStar.Seq.Base.eq_i.fuel_instrumented MaxFuel
@x0
@x1
@x2
@x3))
 

:pattern ((FStar.Seq.Base.eq_i @x0
@x1
@x2
@x3))
:qid @fuel_correspondence_FStar.Seq.Base.eq_i.fuel_instrumented))

:named @fuel_correspondence_FStar.Seq.Base.eq_i.fuel_instrumented))

; </end encoding FStar.Seq.Base.eq_i>


; <Start encoding FStar.Seq.Base.eq>

(declare-fun FStar.Seq.Base.eq (Term Term Term) Term)
(declare-fun Tm_refine_1c0effbdef48f9b00a1efb7b571fbb69 (Term Term Term) Term)
(declare-fun Tm_arrow_70ef1e4b9388d8aa6e0d17c5aeed02a7 () Term)
(declare-fun FStar.Seq.Base.eq@tok () Term)


; </end encoding FStar.Seq.Base.eq>


; <Start encoding FStar.Seq.Base.lemma_eq_intro>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.Seq.Base.lemma_eq_intro (Term Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.Seq.Base.lemma_eq_intro@tok () Term)


; </end encoding FStar.Seq.Base.lemma_eq_intro>


; <Start encoding FStar.Seq.Base.lemma_eq_refl>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.Seq.Base.lemma_eq_refl (Term Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.Seq.Base.lemma_eq_refl@tok () Term)

; </end encoding FStar.Seq.Base.lemma_eq_refl>


; <Start encoding FStar.Seq.Base.lemma_eq_elim>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.Seq.Base.lemma_eq_elim (Term Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.Seq.Base.lemma_eq_elim@tok () Term)

; </end encoding FStar.Seq.Base.lemma_eq_elim>


; <Start encoding FStar.Seq.Base.append_assoc>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.Seq.Base.append_assoc (Term Term Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.Seq.Base.append_assoc@tok () Term)

; </end encoding FStar.Seq.Base.append_assoc>


; <Start encoding FStar.Seq.Base.append_empty_l>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.Seq.Base.append_empty_l (Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.Seq.Base.append_empty_l@tok () Term)

; </end encoding FStar.Seq.Base.append_empty_l>


; <Start encoding FStar.Seq.Base.append_empty_r>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.Seq.Base.append_empty_r (Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.Seq.Base.append_empty_r@tok () Term)

; </end encoding FStar.Seq.Base.append_empty_r>


; <Start encoding FStar.Seq.Base.init_index_aux>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.Seq.Base.init_index_aux (Term Term Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.Seq.Base.init_index_aux@tok () Term)

; </end encoding FStar.Seq.Base.init_index_aux>


; <Start encoding FStar.Seq.Base.init_index>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.Seq.Base.init_index (Term Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.Seq.Base.init_index@tok () Term)

; </end encoding FStar.Seq.Base.init_index>


; <Start encoding FStar.Seq.Base.init_index_>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.Seq.Base.init_index_ (Term Term Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.Seq.Base.init_index_@tok () Term)



; </end encoding FStar.Seq.Base.init_index_>


; <Start encoding FStar.Seq.Base.lemma_equal_instances_implies_equal_types>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.Seq.Base.lemma_equal_instances_implies_equal_types (Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.Seq.Base.lemma_equal_instances_implies_equal_types@tok () Term)

; </end encoding FStar.Seq.Base.lemma_equal_instances_implies_equal_types>


; UNSAT CORE: @MaxFuel_assumption, @MaxIFuel_assumption, @fuel_correspondence_Prims.pow2.fuel_instrumented, @query, constructor_distinct_Lib.IntTypes.S16, constructor_distinct_Lib.IntTypes.S32, constructor_distinct_Lib.IntTypes.SEC, equality_tok_Lib.IntTypes.S16@tok, equality_tok_Lib.IntTypes.S32@tok, equality_tok_Lib.IntTypes.SEC@tok, equation_Lib.IntTypes.bits, equation_Lib.IntTypes.range, equation_Lib.IntTypes.signed, equation_Lib.IntTypes.unsigned, equation_Lib.IntTypes.v, equation_Prims.nat, equation_Prims.pos, equation_Spec.Kyber2.Params.params_q, int_inversion, int_typing, lemma_FStar.UInt.pow2_values, primitive_Prims.op_Addition, primitive_Prims.op_Division, primitive_Prims.op_LessThanOrEqual, primitive_Prims.op_Minus, primitive_Prims.op_Multiply, primitive_Prims.op_Subtraction, projection_inverse_BoxBool_proj_0, projection_inverse_BoxInt_proj_0, refinement_interpretation_Tm_refine_2b320913041b873fce938dd17eebb3e2, refinement_interpretation_Tm_refine_542f9d4f129664613f2483a6c88bc7c2, refinement_interpretation_Tm_refine_774ba3f728d91ead8ef40be66c9802e5, refinement_interpretation_Tm_refine_83845a86f2550cdf941eeb1d9b59602b, refinement_interpretation_Tm_refine_9d3fd79fd314167f1a9c213a188da3ec, refinement_interpretation_Tm_refine_b2401a8cabe2f9a01538f32548fa9f6c, typing_Lib.IntTypes.mk_int, typing_Prims.pow2, typing_tok_Lib.IntTypes.S32@tok, typing_tok_Lib.IntTypes.SEC@tok

;;; End module FStar.Seq.Base (249 decls; total size 16926)

;;; Start module FStar.Squash

; <Start encoding FStar.Squash.return_squash>

(declare-fun FStar.Squash.return_squash (Term Term) Term)
(declare-fun Tm_arrow_66188dd3b00b7ac9b3910d6e97360d1e () Term)
(declare-fun FStar.Squash.return_squash@tok () Term)

; </end encoding FStar.Squash.return_squash>


; <Start encoding FStar.Squash.bind_squash>

(declare-fun Tm_arrow_50bc60bebdf75c69c78dc800e0364d6b (Term Term) Term)
(declare-fun FStar.Squash.bind_squash (Term Term Term Term) Term)

(declare-fun Tm_arrow_dd301c13dceb52611925e3e0985c3aa8 () Term)
(declare-fun FStar.Squash.bind_squash@tok () Term)

; </end encoding FStar.Squash.bind_squash>


; <Start encoding FStar.Squash.push_squash>



(declare-fun FStar.Squash.push_squash (Term Term Term) Term)



(declare-fun Tm_arrow_897bf5c14b806d39ad41e0bfef45d28a () Term)
(declare-fun FStar.Squash.push_squash@tok () Term)


; </end encoding FStar.Squash.push_squash>


; <Start encoding FStar.Squash.get_proof>

(declare-fun FStar.Squash.get_proof (Term) Term)
(declare-fun Tm_refine_7fdd091adbcfc3810a61ff266cf2272b (Term) Term)
(declare-fun Tm_arrow_92023635b661ef4cb5183e1ccd313c6b () Term)
(declare-fun FStar.Squash.get_proof@tok () Term)


; </end encoding FStar.Squash.get_proof>


; <Start encoding FStar.Squash.give_proof>

(declare-fun FStar.Squash.give_proof (Term Term) Term)

(declare-fun Tm_arrow_d002f3b74726aef4cc35f50b77083fcc () Term)
(declare-fun FStar.Squash.give_proof@tok () Term)


; </end encoding FStar.Squash.give_proof>


; <Start encoding FStar.Squash.proof_irrelevance>

(declare-fun FStar.Squash.proof_irrelevance (Term Term Term) Term)
(declare-fun Tm_arrow_7ac0b87e5d98524d87dc021609cde900 () Term)
(declare-fun FStar.Squash.proof_irrelevance@tok () Term)

; </end encoding FStar.Squash.proof_irrelevance>


; <Start encoding FStar.Squash.squash_double_arrow>



(declare-fun FStar.Squash.squash_double_arrow (Term Term Term) Term)



(declare-fun Tm_arrow_4135086bd057eee0b1997d9de0b75d33 () Term)
(declare-fun FStar.Squash.squash_double_arrow@tok () Term)


; </end encoding FStar.Squash.squash_double_arrow>


; <Start encoding FStar.Squash.push_sum>



(declare-fun Tm_abs_ecb85cab59105fe548fc5ca9d671c8f9 (Term Term) Term)
(declare-fun FStar.Squash.push_sum (Term Term Term) Term)



(declare-fun Tm_arrow_c6e83d6817933b3336a5e86b07e67062 () Term)
(declare-fun FStar.Squash.push_sum@tok () Term)

; </end encoding FStar.Squash.push_sum>


; <Start encoding FStar.Squash.squash_double_sum>




(declare-fun FStar.Squash.squash_double_sum (Term Term Term) Term)



(declare-fun Tm_arrow_a0b7ea9677fa75d0acf0c901c148bbdc () Term)
(declare-fun FStar.Squash.squash_double_sum@tok () Term)

; </end encoding FStar.Squash.squash_double_sum>


; <Start encoding FStar.Squash.map_squash>


(declare-fun FStar.Squash.map_squash (Term Term Term Term) Term)

(declare-fun Tm_arrow_f71a078a3b73bb8e8cddd83bc4ca236a () Term)
(declare-fun FStar.Squash.map_squash@tok () Term)

; </end encoding FStar.Squash.map_squash>


; <Start encoding FStar.Squash.join_squash>

(declare-fun FStar.Squash.join_squash (Term Term) Term)
(declare-fun Tm_arrow_b9fdb1273189be7b55b74e1c4ecfb366 () Term)
(declare-fun FStar.Squash.join_squash@tok () Term)

; </end encoding FStar.Squash.join_squash>


; UNSAT CORE: @MaxFuel_assumption, @MaxIFuel_assumption, @fuel_correspondence_Prims.pow2.fuel_instrumented, @query, constructor_distinct_Lib.IntTypes.S16, constructor_distinct_Lib.IntTypes.S32, constructor_distinct_Lib.IntTypes.SEC, equality_tok_Lib.IntTypes.S16@tok, equality_tok_Lib.IntTypes.S32@tok, equality_tok_Lib.IntTypes.SEC@tok, equation_Lib.IntTypes.bits, equation_Lib.IntTypes.range, equation_Lib.IntTypes.signed, equation_Lib.IntTypes.unsigned, equation_Lib.IntTypes.v, equation_Prims.nat, equation_Prims.pos, equation_Spec.Kyber2.Params.params_q, int_inversion, int_typing, lemma_FStar.UInt.pow2_values, primitive_Prims.op_Addition, primitive_Prims.op_Division, primitive_Prims.op_LessThanOrEqual, primitive_Prims.op_Minus, primitive_Prims.op_Multiply, primitive_Prims.op_Subtraction, projection_inverse_BoxBool_proj_0, projection_inverse_BoxInt_proj_0, refinement_interpretation_Tm_refine_2b320913041b873fce938dd17eebb3e2, refinement_interpretation_Tm_refine_542f9d4f129664613f2483a6c88bc7c2, refinement_interpretation_Tm_refine_774ba3f728d91ead8ef40be66c9802e5, refinement_interpretation_Tm_refine_83845a86f2550cdf941eeb1d9b59602b, refinement_interpretation_Tm_refine_9d3fd79fd314167f1a9c213a188da3ec, refinement_interpretation_Tm_refine_b2401a8cabe2f9a01538f32548fa9f6c, typing_Lib.IntTypes.mk_int, typing_Prims.pow2, typing_tok_Lib.IntTypes.S32@tok, typing_tok_Lib.IntTypes.SEC@tok

;;; End module FStar.Squash (88 decls; total size 4624)

;;; Start module FStar.Seq.Properties

; <Skipped />


; <Start encoding FStar.Seq.Properties.lseq>

(declare-fun FStar.Seq.Properties.lseq (Term Term) Term)

(declare-fun FStar.Seq.Properties.lseq@tok () Term)
(declare-fun Tm_refine_a0cd7d06c5da6444b6b51b319febde8e (Term Term) Term)

; </end encoding FStar.Seq.Properties.lseq>


; <Start encoding FStar.Seq.Properties.indexable>

(declare-fun FStar.Seq.Properties.indexable (Term Term Term) Term)
(declare-fun Tm_arrow_2c0367dd991d12c77178c7fe63f076c5 () Term)
(declare-fun FStar.Seq.Properties.indexable@tok () Term)

; </end encoding FStar.Seq.Properties.indexable>


; <Start encoding FStar.Seq.Properties.lemma_append_inj_l>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.Seq.Properties.lemma_append_inj_l (Term Term Term Term Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.Seq.Properties.lemma_append_inj_l@tok () Term)

; </end encoding FStar.Seq.Properties.lemma_append_inj_l>


; <Start encoding FStar.Seq.Properties.lemma_append_inj_r>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.Seq.Properties.lemma_append_inj_r (Term Term Term Term Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.Seq.Properties.lemma_append_inj_r@tok () Term)

; </end encoding FStar.Seq.Properties.lemma_append_inj_r>


; <Start encoding FStar.Seq.Properties.lemma_append_len_disj>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.Seq.Properties.lemma_append_len_disj (Term Term Term Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.Seq.Properties.lemma_append_len_disj@tok () Term)

; </end encoding FStar.Seq.Properties.lemma_append_len_disj>


; <Start encoding FStar.Seq.Properties.lemma_append_inj>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.Seq.Properties.lemma_append_inj (Term Term Term Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.Seq.Properties.lemma_append_inj@tok () Term)

; </end encoding FStar.Seq.Properties.lemma_append_inj>


; <Start encoding FStar.Seq.Properties.head>


(declare-fun FStar.Seq.Properties.head (Term Term) Term)


(declare-fun FStar.Seq.Properties.head@tok () Term)


; </end encoding FStar.Seq.Properties.head>


; <Start encoding FStar.Seq.Properties.tail>


(declare-fun FStar.Seq.Properties.tail (Term Term) Term)


(declare-fun FStar.Seq.Properties.tail@tok () Term)


; </end encoding FStar.Seq.Properties.tail>


; <Start encoding FStar.Seq.Properties.lemma_head_append>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.Seq.Properties.lemma_head_append (Term Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.Seq.Properties.lemma_head_append@tok () Term)

; </end encoding FStar.Seq.Properties.lemma_head_append>


; <Start encoding FStar.Seq.Properties.lemma_tail_append>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.Seq.Properties.lemma_tail_append (Term Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.Seq.Properties.lemma_tail_append@tok () Term)

; </end encoding FStar.Seq.Properties.lemma_tail_append>


; <Start encoding FStar.Seq.Properties.last>


(declare-fun FStar.Seq.Properties.last (Term Term) Term)


(declare-fun FStar.Seq.Properties.last@tok () Term)


; </end encoding FStar.Seq.Properties.last>


; <Start encoding FStar.Seq.Properties.cons>

(declare-fun FStar.Seq.Properties.cons (Term Term Term) Term)

(declare-fun FStar.Seq.Properties.cons@tok () Term)

; </end encoding FStar.Seq.Properties.cons>


; <Start encoding FStar.Seq.Properties.lemma_cons_inj>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.Seq.Properties.lemma_cons_inj (Term Term Term Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.Seq.Properties.lemma_cons_inj@tok () Term)

; </end encoding FStar.Seq.Properties.lemma_cons_inj>


; <Start encoding FStar.Seq.Properties.split>

(declare-fun Tm_refine_17631fa6304dcc08d028bd475a6dd078 (Term Term) Term)
(declare-fun FStar.Seq.Properties.split (Term Term Term) Term)

(declare-fun Tm_arrow_e8094a245058e1a3364fcb54e52c4b61 () Term)
(declare-fun FStar.Seq.Properties.split@tok () Term)


; </end encoding FStar.Seq.Properties.split>


; <Start encoding FStar.Seq.Properties.lemma_split>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.Seq.Properties.lemma_split (Term Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.Seq.Properties.lemma_split@tok () Term)

; </end encoding FStar.Seq.Properties.lemma_split>


; <Start encoding FStar.Seq.Properties.split_eq>


(declare-fun FStar.Seq.Properties.split_eq (Term Term Term) Term)

(declare-fun Tm_refine_78d42c5dbba01ee594272daa6bb0579c (Term Term) Term)
(declare-fun Tm_arrow_b88932abf1506cfe956c7a113bc65f4b () Term)
(declare-fun FStar.Seq.Properties.split_eq@tok () Term)



; </end encoding FStar.Seq.Properties.split_eq>


; <Start encoding FStar.Seq.Properties.count>

;;;;;;;;;;;;;;;;Fuel-instrumented function name
(declare-fun FStar.Seq.Properties.count.fuel_instrumented (Fuel Term Term Term) Term)
;;;;;;;;;;;;;;;;Token for fuel-instrumented partial applications
(declare-fun FStar.Seq.Properties.count.fuel_instrumented_token () Term)
(declare-fun FStar.Seq.Properties.count (Term Term Term) Term)
(declare-fun FStar.Seq.Properties.count@tok () Term)
(declare-fun Tm_arrow_b68daf91c98458f9ea85290d85674a2e () Term)
;;;;;;;;;;;;;;;;Fuel irrelevance
;;; Fact-ids: Name FStar.Seq.Properties.count; Namespace FStar.Seq.Properties
(assert (! 
;; def=FStar.Seq.Properties.fst(101,8-101,13); use=FStar.Seq.Properties.fst(101,8-101,13)
(forall ((@u0 Fuel) (@x1 Term) (@x2 Term) (@x3 Term))
 (! (= (FStar.Seq.Properties.count.fuel_instrumented (SFuel @u0)
@x1
@x2
@x3)
(FStar.Seq.Properties.count.fuel_instrumented ZFuel
@x1
@x2
@x3))
 

:pattern ((FStar.Seq.Properties.count.fuel_instrumented (SFuel @u0)
@x1
@x2
@x3))
:qid @fuel_irrelevance_FStar.Seq.Properties.count.fuel_instrumented))

:named @fuel_irrelevance_FStar.Seq.Properties.count.fuel_instrumented))
;;;;;;;;;;;;;;;;Correspondence of recursive function to instrumented version
;;; Fact-ids: Name FStar.Seq.Properties.count; Namespace FStar.Seq.Properties
(assert (! 
;; def=FStar.Seq.Properties.fst(101,8-101,13); use=FStar.Seq.Properties.fst(101,8-101,13)
(forall ((@x0 Term) (@x1 Term) (@x2 Term))
 (! (= (FStar.Seq.Properties.count @x0
@x1
@x2)
(FStar.Seq.Properties.count.fuel_instrumented MaxFuel
@x0
@x1
@x2))
 

:pattern ((FStar.Seq.Properties.count @x0
@x1
@x2))
:qid @fuel_correspondence_FStar.Seq.Properties.count.fuel_instrumented))

:named @fuel_correspondence_FStar.Seq.Properties.count.fuel_instrumented))

; </end encoding FStar.Seq.Properties.count>


; <Start encoding FStar.Seq.Properties.mem>

(declare-fun FStar.Seq.Properties.mem (Term Term Term) Term)
(declare-fun Tm_arrow_8b9021eb78c56c0f1820182c3a3e44b5 () Term)
(declare-fun FStar.Seq.Properties.mem@tok () Term)

; </end encoding FStar.Seq.Properties.mem>


; <Skipped />


; <Start encoding FStar.Seq.Properties.mem_index>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.Seq.Properties.mem_index (Term Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.Seq.Properties.mem_index@tok () Term)

; </end encoding FStar.Seq.Properties.mem_index>


; <Start encoding FStar.Seq.Properties.index_mem>

;;;;;;;;;;;;;;;;Fuel-instrumented function name
(declare-fun FStar.Seq.Properties.index_mem.fuel_instrumented (Fuel Term Term Term) Term)
;;;;;;;;;;;;;;;;Token for fuel-instrumented partial applications
(declare-fun FStar.Seq.Properties.index_mem.fuel_instrumented_token () Term)
(declare-fun FStar.Seq.Properties.index_mem (Term Term Term) Term)
(declare-fun FStar.Seq.Properties.index_mem@tok () Term)
(declare-fun Tm_refine_7c92df3cf71635bc41483532e738d828 (Term Term Term) Term)

(declare-fun Tm_arrow_12def5646e9a05cc547dd67c2eeaec45 () Term)

;;;;;;;;;;;;;;;;Fuel irrelevance
;;; Fact-ids: Name FStar.Seq.Properties.index_mem; Namespace FStar.Seq.Properties
(assert (! 
;; def=FStar.Seq.Properties.fst(122,8-122,17); use=FStar.Seq.Properties.fst(122,8-122,17)
(forall ((@u0 Fuel) (@x1 Term) (@x2 Term) (@x3 Term))
 (! (= (FStar.Seq.Properties.index_mem.fuel_instrumented (SFuel @u0)
@x1
@x2
@x3)
(FStar.Seq.Properties.index_mem.fuel_instrumented ZFuel
@x1
@x2
@x3))
 

:pattern ((FStar.Seq.Properties.index_mem.fuel_instrumented (SFuel @u0)
@x1
@x2
@x3))
:qid @fuel_irrelevance_FStar.Seq.Properties.index_mem.fuel_instrumented))

:named @fuel_irrelevance_FStar.Seq.Properties.index_mem.fuel_instrumented))
;;;;;;;;;;;;;;;;Correspondence of recursive function to instrumented version
;;; Fact-ids: Name FStar.Seq.Properties.index_mem; Namespace FStar.Seq.Properties
(assert (! 
;; def=FStar.Seq.Properties.fst(122,8-122,17); use=FStar.Seq.Properties.fst(122,8-122,17)
(forall ((@x0 Term) (@x1 Term) (@x2 Term))
 (! (= (FStar.Seq.Properties.index_mem @x0
@x1
@x2)
(FStar.Seq.Properties.index_mem.fuel_instrumented MaxFuel
@x0
@x1
@x2))
 

:pattern ((FStar.Seq.Properties.index_mem @x0
@x1
@x2))
:qid @fuel_correspondence_FStar.Seq.Properties.index_mem.fuel_instrumented))

:named @fuel_correspondence_FStar.Seq.Properties.index_mem.fuel_instrumented))

; </end encoding FStar.Seq.Properties.index_mem>


; <Skipped />


; <Start encoding FStar.Seq.Properties.swap>



(declare-fun FStar.Seq.Properties.swap (Term Term Term Term) Term)


(declare-fun Tm_arrow_ed5530d89236443143d2d084ddc97069 () Term)
(declare-fun FStar.Seq.Properties.swap@tok () Term)



; </end encoding FStar.Seq.Properties.swap>


; <Start encoding FStar.Seq.Properties.lemma_slice_append>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.Seq.Properties.lemma_slice_append (Term Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.Seq.Properties.lemma_slice_append@tok () Term)

; </end encoding FStar.Seq.Properties.lemma_slice_append>


; <Start encoding FStar.Seq.Properties.lemma_slice_first_in_append>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.Seq.Properties.lemma_slice_first_in_append (Term Term Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.Seq.Properties.lemma_slice_first_in_append@tok () Term)

; </end encoding FStar.Seq.Properties.lemma_slice_first_in_append>


; <Start encoding FStar.Seq.Properties.slice_upd>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.Seq.Properties.slice_upd (Term Term Term Term Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.Seq.Properties.slice_upd@tok () Term)



; </end encoding FStar.Seq.Properties.slice_upd>


; <Start encoding FStar.Seq.Properties.upd_slice>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.Seq.Properties.upd_slice (Term Term Term Term Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.Seq.Properties.upd_slice@tok () Term)



; </end encoding FStar.Seq.Properties.upd_slice>


; <Start encoding FStar.Seq.Properties.lemma_append_cons>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.Seq.Properties.lemma_append_cons (Term Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.Seq.Properties.lemma_append_cons@tok () Term)

; </end encoding FStar.Seq.Properties.lemma_append_cons>


; <Start encoding FStar.Seq.Properties.lemma_tl>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.Seq.Properties.lemma_tl (Term Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.Seq.Properties.lemma_tl@tok () Term)

; </end encoding FStar.Seq.Properties.lemma_tl>


; <Start encoding FStar.Seq.Properties.sorted>

;;;;;;;;;;;;;;;;Fuel-instrumented function name
(declare-fun FStar.Seq.Properties.sorted.fuel_instrumented (Fuel Term Term Term) Term)
;;;;;;;;;;;;;;;;Token for fuel-instrumented partial applications
(declare-fun FStar.Seq.Properties.sorted.fuel_instrumented_token () Term)
(declare-fun FStar.Seq.Properties.sorted (Term Term Term) Term)
(declare-fun FStar.Seq.Properties.sorted@tok () Term)



(declare-fun Tm_arrow_28685b742721099a6ab3847e4434a96d () Term)
;;;;;;;;;;;;;;;;Fuel irrelevance
;;; Fact-ids: Name FStar.Seq.Properties.sorted; Namespace FStar.Seq.Properties
(assert (! 
;; def=FStar.Seq.Properties.fst(175,8-175,14); use=FStar.Seq.Properties.fst(175,8-175,14)
(forall ((@u0 Fuel) (@x1 Term) (@x2 Term) (@x3 Term))
 (! (= (FStar.Seq.Properties.sorted.fuel_instrumented (SFuel @u0)
@x1
@x2
@x3)
(FStar.Seq.Properties.sorted.fuel_instrumented ZFuel
@x1
@x2
@x3))
 

:pattern ((FStar.Seq.Properties.sorted.fuel_instrumented (SFuel @u0)
@x1
@x2
@x3))
:qid @fuel_irrelevance_FStar.Seq.Properties.sorted.fuel_instrumented))

:named @fuel_irrelevance_FStar.Seq.Properties.sorted.fuel_instrumented))
;;;;;;;;;;;;;;;;Correspondence of recursive function to instrumented version
;;; Fact-ids: Name FStar.Seq.Properties.sorted; Namespace FStar.Seq.Properties
(assert (! 
;; def=FStar.Seq.Properties.fst(175,8-175,14); use=FStar.Seq.Properties.fst(175,8-175,14)
(forall ((@x0 Term) (@x1 Term) (@x2 Term))
 (! (= (FStar.Seq.Properties.sorted @x0
@x1
@x2)
(FStar.Seq.Properties.sorted.fuel_instrumented MaxFuel
@x0
@x1
@x2))
 

:pattern ((FStar.Seq.Properties.sorted @x0
@x1
@x2))
:qid @fuel_correspondence_FStar.Seq.Properties.sorted.fuel_instrumented))

:named @fuel_correspondence_FStar.Seq.Properties.sorted.fuel_instrumented))

; </end encoding FStar.Seq.Properties.sorted>


; <Skipped />


; <Start encoding FStar.Seq.Properties.sorted_feq>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.Seq.Properties.sorted_feq (Term Term Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.Seq.Properties.sorted_feq@tok () Term)

; </end encoding FStar.Seq.Properties.sorted_feq>


; <Start encoding FStar.Seq.Properties.lemma_append_count>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.Seq.Properties.lemma_append_count (Term Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.Seq.Properties.lemma_append_count@tok () Term)

; </end encoding FStar.Seq.Properties.lemma_append_count>


; <Start encoding FStar.Seq.Properties.lemma_append_count_aux>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.Seq.Properties.lemma_append_count_aux (Term Term Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.Seq.Properties.lemma_append_count_aux@tok () Term)

; </end encoding FStar.Seq.Properties.lemma_append_count_aux>


; <Start encoding FStar.Seq.Properties.lemma_mem_inversion>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.Seq.Properties.lemma_mem_inversion (Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.Seq.Properties.lemma_mem_inversion@tok () Term)

; </end encoding FStar.Seq.Properties.lemma_mem_inversion>


; <Start encoding FStar.Seq.Properties.lemma_mem_count>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.Seq.Properties.lemma_mem_count (Term Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.Seq.Properties.lemma_mem_count@tok () Term)

; </end encoding FStar.Seq.Properties.lemma_mem_count>


; <Start encoding FStar.Seq.Properties.lemma_count_slice>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.Seq.Properties.lemma_count_slice (Term Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.Seq.Properties.lemma_count_slice@tok () Term)

; </end encoding FStar.Seq.Properties.lemma_count_slice>


; <Start encoding FStar.Seq.Properties.total_order>


(declare-fun FStar.Seq.Properties.total_order (Term Term) Term)

(declare-fun Tm_arrow_1118b25cace7451b1e5dfdfe482dbb64 () Term)
(declare-fun FStar.Seq.Properties.total_order@tok () Term)


; </end encoding FStar.Seq.Properties.total_order>


; <Start encoding FStar.Seq.Properties.tot_ord>

(declare-fun FStar.Seq.Properties.tot_ord (Term) Term)
(declare-fun Tm_arrow_7e9afc6da5407011473323ad80ff51bf () Term)
(declare-fun FStar.Seq.Properties.tot_ord@tok () Term)

(declare-fun Tm_refine_a01e88865b4bbd2f0a4bcb261b6760a8 (Term) Term)

; </end encoding FStar.Seq.Properties.tot_ord>


; <Start encoding FStar.Seq.Properties.sorted_concat_lemma>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.Seq.Properties.sorted_concat_lemma (Term Term Term Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.Seq.Properties.sorted_concat_lemma@tok () Term)

; </end encoding FStar.Seq.Properties.sorted_concat_lemma>


; <Start encoding FStar.Seq.Properties.split_5>

(declare-fun Tm_refine_55108d29d63192475ca95f591039cc18 (Term Term Term) Term)
(declare-fun FStar.Seq.Properties.split_5 (Term Term Term Term) Term)

(declare-fun Tm_refine_03fdfb031367b218884098aa9d386676 (Term Term Term Term) Term)
(declare-fun Tm_arrow_1ab34f107de5525c681399e3c671c330 () Term)
(declare-fun FStar.Seq.Properties.split_5@tok () Term)


; </end encoding FStar.Seq.Properties.split_5>


; <Start encoding FStar.Seq.Properties.lemma_swap_permutes_aux_frag_eq>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.Seq.Properties.lemma_swap_permutes_aux_frag_eq (Term Term Term Term Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.Seq.Properties.lemma_swap_permutes_aux_frag_eq@tok () Term)

; </end encoding FStar.Seq.Properties.lemma_swap_permutes_aux_frag_eq>


; <Skipped />


; <Start encoding FStar.Seq.Properties.lemma_swap_permutes_aux>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.Seq.Properties.lemma_swap_permutes_aux (Term Term Term Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.Seq.Properties.lemma_swap_permutes_aux@tok () Term)

; </end encoding FStar.Seq.Properties.lemma_swap_permutes_aux>


; <Skipped />


; <Skipped />


; <Start encoding FStar.Seq.Properties.permutation>

(declare-fun FStar.Seq.Properties.permutation (Term Term Term) Term)
(declare-fun Tm_arrow_05517904f5779069bb79d90a352f1386 () Term)
(declare-fun FStar.Seq.Properties.permutation@tok () Term)

; </end encoding FStar.Seq.Properties.permutation>


; <Start encoding FStar.Seq.Properties.lemma_swap_permutes>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.Seq.Properties.lemma_swap_permutes (Term Term Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.Seq.Properties.lemma_swap_permutes@tok () Term)

; </end encoding FStar.Seq.Properties.lemma_swap_permutes>


; <Skipped />


; <Start encoding FStar.Seq.Properties.perm_len>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.Seq.Properties.perm_len (Term Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.Seq.Properties.perm_len@tok () Term)

; </end encoding FStar.Seq.Properties.perm_len>


; <Start encoding FStar.Seq.Properties.cons_perm>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.Seq.Properties.cons_perm (Term Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.Seq.Properties.cons_perm@tok () Term)

; </end encoding FStar.Seq.Properties.cons_perm>


; <Skipped />


; <Start encoding FStar.Seq.Properties.lemma_mem_append>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.Seq.Properties.lemma_mem_append (Term Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.Seq.Properties.lemma_mem_append@tok () Term)

; </end encoding FStar.Seq.Properties.lemma_mem_append>


; <Start encoding FStar.Seq.Properties.lemma_slice_cons>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.Seq.Properties.lemma_slice_cons (Term Term Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.Seq.Properties.lemma_slice_cons@tok () Term)

; </end encoding FStar.Seq.Properties.lemma_slice_cons>


; <Start encoding FStar.Seq.Properties.lemma_slice_snoc>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.Seq.Properties.lemma_slice_snoc (Term Term Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.Seq.Properties.lemma_slice_snoc@tok () Term)

; </end encoding FStar.Seq.Properties.lemma_slice_snoc>


; <Start encoding FStar.Seq.Properties.lemma_ordering_lo_snoc>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.Seq.Properties.lemma_ordering_lo_snoc (Term Term Term Term Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.Seq.Properties.lemma_ordering_lo_snoc@tok () Term)

; </end encoding FStar.Seq.Properties.lemma_ordering_lo_snoc>


; <Start encoding FStar.Seq.Properties.lemma_ordering_hi_cons>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.Seq.Properties.lemma_ordering_hi_cons (Term Term Term Term Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.Seq.Properties.lemma_ordering_hi_cons@tok () Term)

; </end encoding FStar.Seq.Properties.lemma_ordering_hi_cons>


; <Skipped />


; <Start encoding FStar.Seq.Properties.swap_frame_lo>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.Seq.Properties.swap_frame_lo (Term Term Term Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.Seq.Properties.swap_frame_lo@tok () Term)

; </end encoding FStar.Seq.Properties.swap_frame_lo>


; <Start encoding FStar.Seq.Properties.swap_frame_lo'>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.Seq.Properties.swap_frame_lo_ (Term Term Term Term Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.Seq.Properties.swap_frame_lo_@tok () Term)

; </end encoding FStar.Seq.Properties.swap_frame_lo'>


; <Start encoding FStar.Seq.Properties.swap_frame_hi>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.Seq.Properties.swap_frame_hi (Term Term Term Term Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.Seq.Properties.swap_frame_hi@tok () Term)

; </end encoding FStar.Seq.Properties.swap_frame_hi>


; <Start encoding FStar.Seq.Properties.lemma_swap_slice_commute>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.Seq.Properties.lemma_swap_slice_commute (Term Term Term Term Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.Seq.Properties.lemma_swap_slice_commute@tok () Term)

; </end encoding FStar.Seq.Properties.lemma_swap_slice_commute>


; <Start encoding FStar.Seq.Properties.lemma_swap_permutes_slice>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.Seq.Properties.lemma_swap_permutes_slice (Term Term Term Term Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.Seq.Properties.lemma_swap_permutes_slice@tok () Term)

; </end encoding FStar.Seq.Properties.lemma_swap_permutes_slice>


; <Skipped />


; <Start encoding FStar.Seq.Properties.splice>



(declare-fun FStar.Seq.Properties.splice (Term Term Term Term Term) Term)


(declare-fun Tm_arrow_c43a25ef505b9db21532cdb95f3c9f68 () Term)
(declare-fun FStar.Seq.Properties.splice@tok () Term)



; </end encoding FStar.Seq.Properties.splice>


; <Start encoding FStar.Seq.Properties.replace_subseq>


(declare-fun Tm_refine_5542011d20872a6178aad9a072f1b686 (Term Term Term) Term)
(declare-fun FStar.Seq.Properties.replace_subseq (Term Term Term Term Term) Term)


(declare-fun Tm_arrow_9fa775abc8f8f9c4e6df626212cddc6a () Term)
(declare-fun FStar.Seq.Properties.replace_subseq@tok () Term)



; </end encoding FStar.Seq.Properties.replace_subseq>


; <Start encoding FStar.Seq.Properties.splice_refl>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.Seq.Properties.splice_refl (Term Term Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.Seq.Properties.splice_refl@tok () Term)

; </end encoding FStar.Seq.Properties.splice_refl>


; <Start encoding FStar.Seq.Properties.lemma_swap_splice>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.Seq.Properties.lemma_swap_splice (Term Term Term Term Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.Seq.Properties.lemma_swap_splice@tok () Term)

; </end encoding FStar.Seq.Properties.lemma_swap_splice>


; <Start encoding FStar.Seq.Properties.lemma_seq_frame_hi>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.Seq.Properties.lemma_seq_frame_hi (Term Term Term Term Term Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.Seq.Properties.lemma_seq_frame_hi@tok () Term)

; </end encoding FStar.Seq.Properties.lemma_seq_frame_hi>


; <Start encoding FStar.Seq.Properties.lemma_seq_frame_lo>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.Seq.Properties.lemma_seq_frame_lo (Term Term Term Term Term Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.Seq.Properties.lemma_seq_frame_lo@tok () Term)

; </end encoding FStar.Seq.Properties.lemma_seq_frame_lo>


; <Start encoding FStar.Seq.Properties.lemma_tail_slice>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.Seq.Properties.lemma_tail_slice (Term Term Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.Seq.Properties.lemma_tail_slice@tok () Term)
(declare-fun Tm_refine_b138bd5848d4184f7632587e6e4bcf9f (Term Term Term) Term)

; </end encoding FStar.Seq.Properties.lemma_tail_slice>


; <Start encoding FStar.Seq.Properties.lemma_weaken_frame_right>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.Seq.Properties.lemma_weaken_frame_right (Term Term Term Term Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.Seq.Properties.lemma_weaken_frame_right@tok () Term)

; </end encoding FStar.Seq.Properties.lemma_weaken_frame_right>


; <Start encoding FStar.Seq.Properties.lemma_weaken_frame_left>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.Seq.Properties.lemma_weaken_frame_left (Term Term Term Term Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.Seq.Properties.lemma_weaken_frame_left@tok () Term)

; </end encoding FStar.Seq.Properties.lemma_weaken_frame_left>


; <Start encoding FStar.Seq.Properties.lemma_trans_frame>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.Seq.Properties.lemma_trans_frame (Term Term Term Term Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.Seq.Properties.lemma_trans_frame@tok () Term)

; </end encoding FStar.Seq.Properties.lemma_trans_frame>


; <Start encoding FStar.Seq.Properties.lemma_weaken_perm_left>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.Seq.Properties.lemma_weaken_perm_left (Term Term Term Term Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.Seq.Properties.lemma_weaken_perm_left@tok () Term)

; </end encoding FStar.Seq.Properties.lemma_weaken_perm_left>


; <Start encoding FStar.Seq.Properties.lemma_weaken_perm_right>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.Seq.Properties.lemma_weaken_perm_right (Term Term Term Term Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.Seq.Properties.lemma_weaken_perm_right@tok () Term)

; </end encoding FStar.Seq.Properties.lemma_weaken_perm_right>


; <Start encoding FStar.Seq.Properties.lemma_trans_perm>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.Seq.Properties.lemma_trans_perm (Term Term Term Term Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.Seq.Properties.lemma_trans_perm@tok () Term)

; </end encoding FStar.Seq.Properties.lemma_trans_perm>


; <Start encoding FStar.Seq.Properties.snoc>

(declare-fun FStar.Seq.Properties.snoc (Term Term Term) Term)
(declare-fun Tm_arrow_f9b27de7c4505538c6110afe14403cc8 () Term)
(declare-fun FStar.Seq.Properties.snoc@tok () Term)

; </end encoding FStar.Seq.Properties.snoc>


; <Start encoding FStar.Seq.Properties.lemma_cons_snoc>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.Seq.Properties.lemma_cons_snoc (Term Term Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.Seq.Properties.lemma_cons_snoc@tok () Term)

; </end encoding FStar.Seq.Properties.lemma_cons_snoc>


; <Start encoding FStar.Seq.Properties.lemma_tail_snoc>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.Seq.Properties.lemma_tail_snoc (Term Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.Seq.Properties.lemma_tail_snoc@tok () Term)

; </end encoding FStar.Seq.Properties.lemma_tail_snoc>


; <Start encoding FStar.Seq.Properties.lemma_snoc_inj>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.Seq.Properties.lemma_snoc_inj (Term Term Term Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.Seq.Properties.lemma_snoc_inj@tok () Term)

; </end encoding FStar.Seq.Properties.lemma_snoc_inj>


; <Skipped />


; <Start encoding FStar.Seq.Properties.lemma_mem_snoc>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.Seq.Properties.lemma_mem_snoc (Term Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.Seq.Properties.lemma_mem_snoc@tok () Term)

; </end encoding FStar.Seq.Properties.lemma_mem_snoc>


; <Start encoding FStar.Seq.Properties.find_l>

;;;;;;;;;;;;;;;;Fuel-instrumented function name
(declare-fun FStar.Seq.Properties.find_l.fuel_instrumented (Fuel Term Term Term) Term)
;;;;;;;;;;;;;;;;Token for fuel-instrumented partial applications
(declare-fun FStar.Seq.Properties.find_l.fuel_instrumented_token () Term)
(declare-fun FStar.Seq.Properties.find_l (Term Term Term) Term)
(declare-fun FStar.Seq.Properties.find_l@tok () Term)

(declare-fun Tm_refine_aba7638072c8f1ba6a01b95ec6f9a485 (Term Term) Term)



(declare-fun Tm_arrow_fd183dc9552028fd54abfbe4a84f515a () Term)

;;;;;;;;;;;;;;;;Fuel irrelevance
;;; Fact-ids: Name FStar.Seq.Properties.find_l; Namespace FStar.Seq.Properties
(assert (! 
;; def=FStar.Seq.Properties.fst(547,8-547,14); use=FStar.Seq.Properties.fst(547,8-547,14)
(forall ((@u0 Fuel) (@x1 Term) (@x2 Term) (@x3 Term))
 (! (= (FStar.Seq.Properties.find_l.fuel_instrumented (SFuel @u0)
@x1
@x2
@x3)
(FStar.Seq.Properties.find_l.fuel_instrumented ZFuel
@x1
@x2
@x3))
 

:pattern ((FStar.Seq.Properties.find_l.fuel_instrumented (SFuel @u0)
@x1
@x2
@x3))
:qid @fuel_irrelevance_FStar.Seq.Properties.find_l.fuel_instrumented))

:named @fuel_irrelevance_FStar.Seq.Properties.find_l.fuel_instrumented))
;;;;;;;;;;;;;;;;Correspondence of recursive function to instrumented version
;;; Fact-ids: Name FStar.Seq.Properties.find_l; Namespace FStar.Seq.Properties
(assert (! 
;; def=FStar.Seq.Properties.fst(547,8-547,14); use=FStar.Seq.Properties.fst(547,8-547,14)
(forall ((@x0 Term) (@x1 Term) (@x2 Term))
 (! (= (FStar.Seq.Properties.find_l @x0
@x1
@x2)
(FStar.Seq.Properties.find_l.fuel_instrumented MaxFuel
@x0
@x1
@x2))
 

:pattern ((FStar.Seq.Properties.find_l @x0
@x1
@x2))
:qid @fuel_correspondence_FStar.Seq.Properties.find_l.fuel_instrumented))

:named @fuel_correspondence_FStar.Seq.Properties.find_l.fuel_instrumented))

; </end encoding FStar.Seq.Properties.find_l>


; <Start encoding FStar.Seq.Properties.ghost_find_l>

;;;;;;;;;;;;;;;;Fuel-instrumented function name
(declare-fun FStar.Seq.Properties.ghost_find_l.fuel_instrumented (Fuel Term Term Term) Term)
;;;;;;;;;;;;;;;;Token for fuel-instrumented partial applications
(declare-fun FStar.Seq.Properties.ghost_find_l.fuel_instrumented_token () Term)
(declare-fun FStar.Seq.Properties.ghost_find_l (Term Term Term) Term)
(declare-fun FStar.Seq.Properties.ghost_find_l@tok () Term)
(declare-fun Tm_ghost_arrow_9a34a9deaac3ca72ad48c3ec79b6656c (Term) Term)




(declare-fun Tm_ghost_arrow_3f8a537d0d54200d690f80a370cf9031 () Term)

;;;;;;;;;;;;;;;;Fuel irrelevance
;;; Fact-ids: Name FStar.Seq.Properties.ghost_find_l; Namespace FStar.Seq.Properties
(assert (! 
;; def=FStar.Seq.Properties.fst(554,8-554,20); use=FStar.Seq.Properties.fst(554,8-554,20)
(forall ((@u0 Fuel) (@x1 Term) (@x2 Term) (@x3 Term))
 (! (= (FStar.Seq.Properties.ghost_find_l.fuel_instrumented (SFuel @u0)
@x1
@x2
@x3)
(FStar.Seq.Properties.ghost_find_l.fuel_instrumented ZFuel
@x1
@x2
@x3))
 

:pattern ((FStar.Seq.Properties.ghost_find_l.fuel_instrumented (SFuel @u0)
@x1
@x2
@x3))
:qid @fuel_irrelevance_FStar.Seq.Properties.ghost_find_l.fuel_instrumented))

:named @fuel_irrelevance_FStar.Seq.Properties.ghost_find_l.fuel_instrumented))
;;;;;;;;;;;;;;;;Correspondence of recursive function to instrumented version
;;; Fact-ids: Name FStar.Seq.Properties.ghost_find_l; Namespace FStar.Seq.Properties
(assert (! 
;; def=FStar.Seq.Properties.fst(554,8-554,20); use=FStar.Seq.Properties.fst(554,8-554,20)
(forall ((@x0 Term) (@x1 Term) (@x2 Term))
 (! (= (FStar.Seq.Properties.ghost_find_l @x0
@x1
@x2)
(FStar.Seq.Properties.ghost_find_l.fuel_instrumented MaxFuel
@x0
@x1
@x2))
 

:pattern ((FStar.Seq.Properties.ghost_find_l @x0
@x1
@x2))
:qid @fuel_correspondence_FStar.Seq.Properties.ghost_find_l.fuel_instrumented))

:named @fuel_correspondence_FStar.Seq.Properties.ghost_find_l.fuel_instrumented))

; </end encoding FStar.Seq.Properties.ghost_find_l>


; <Start encoding FStar.Seq.Properties.find_append_some>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.Seq.Properties.find_append_some (Term Term Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.Seq.Properties.find_append_some@tok () Term)

; </end encoding FStar.Seq.Properties.find_append_some>


; <Start encoding FStar.Seq.Properties.find_append_none>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.Seq.Properties.find_append_none (Term Term Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.Seq.Properties.find_append_none@tok () Term)

; </end encoding FStar.Seq.Properties.find_append_none>


; <Start encoding FStar.Seq.Properties.find_append_none_s2>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.Seq.Properties.find_append_none_s2 (Term Term Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.Seq.Properties.find_append_none_s2@tok () Term)

; </end encoding FStar.Seq.Properties.find_append_none_s2>


; <Start encoding FStar.Seq.Properties.find_snoc>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.Seq.Properties.find_snoc (Term Term Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.Seq.Properties.find_snoc@tok () Term)

; </end encoding FStar.Seq.Properties.find_snoc>


; <Start encoding FStar.Seq.Properties.un_snoc>

(declare-fun Tm_refine_5739deb21d8cba89243fec27b35b7ef0 (Term) Term)
(declare-fun FStar.Seq.Properties.un_snoc (Term Term) Term)

(declare-fun Tm_refine_16326afaeb5f4d93ab294cc4a965de3e (Term Term) Term)
(declare-fun Tm_arrow_30c2910b2510bbce2598a79ba00a0209 () Term)
(declare-fun FStar.Seq.Properties.un_snoc@tok () Term)



; </end encoding FStar.Seq.Properties.un_snoc>


; <Start encoding FStar.Seq.Properties.un_snoc_snoc>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.Seq.Properties.un_snoc_snoc (Term Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.Seq.Properties.un_snoc_snoc@tok () Term)

; </end encoding FStar.Seq.Properties.un_snoc_snoc>


; <Start encoding FStar.Seq.Properties.find_r>

;;;;;;;;;;;;;;;;Fuel-instrumented function name
(declare-fun FStar.Seq.Properties.find_r.fuel_instrumented (Fuel Term Term Term) Term)
;;;;;;;;;;;;;;;;Token for fuel-instrumented partial applications
(declare-fun FStar.Seq.Properties.find_r.fuel_instrumented_token () Term)
(declare-fun FStar.Seq.Properties.find_r (Term Term Term) Term)
(declare-fun FStar.Seq.Properties.find_r@tok () Term)







;;;;;;;;;;;;;;;;Fuel irrelevance
;;; Fact-ids: Name FStar.Seq.Properties.find_r; Namespace FStar.Seq.Properties
(assert (! 
;; def=FStar.Seq.Properties.fst(612,8-612,14); use=FStar.Seq.Properties.fst(612,8-612,14)
(forall ((@u0 Fuel) (@x1 Term) (@x2 Term) (@x3 Term))
 (! (= (FStar.Seq.Properties.find_r.fuel_instrumented (SFuel @u0)
@x1
@x2
@x3)
(FStar.Seq.Properties.find_r.fuel_instrumented ZFuel
@x1
@x2
@x3))
 

:pattern ((FStar.Seq.Properties.find_r.fuel_instrumented (SFuel @u0)
@x1
@x2
@x3))
:qid @fuel_irrelevance_FStar.Seq.Properties.find_r.fuel_instrumented))

:named @fuel_irrelevance_FStar.Seq.Properties.find_r.fuel_instrumented))
;;;;;;;;;;;;;;;;Correspondence of recursive function to instrumented version
;;; Fact-ids: Name FStar.Seq.Properties.find_r; Namespace FStar.Seq.Properties
(assert (! 
;; def=FStar.Seq.Properties.fst(612,8-612,14); use=FStar.Seq.Properties.fst(612,8-612,14)
(forall ((@x0 Term) (@x1 Term) (@x2 Term))
 (! (= (FStar.Seq.Properties.find_r @x0
@x1
@x2)
(FStar.Seq.Properties.find_r.fuel_instrumented MaxFuel
@x0
@x1
@x2))
 

:pattern ((FStar.Seq.Properties.find_r @x0
@x1
@x2))
:qid @fuel_correspondence_FStar.Seq.Properties.find_r.fuel_instrumented))

:named @fuel_correspondence_FStar.Seq.Properties.find_r.fuel_instrumented))

; </end encoding FStar.Seq.Properties.find_r>


; <Skipped />


; <Start encoding FStar.Seq.Properties.found>

(declare-fun FStar.Seq.Properties.found (Term) Term)
(declare-fun Tm_arrow_591bcdc53dc583ecc77b1bc5436f9a59 () Term)
(declare-fun FStar.Seq.Properties.found@tok () Term)

; </end encoding FStar.Seq.Properties.found>


; <Start encoding FStar.Seq.Properties.seq_find_aux>

;;;;;;;;;;;;;;;;Fuel-instrumented function name
(declare-fun FStar.Seq.Properties.seq_find_aux.fuel_instrumented (Fuel Term Term Term Term) Term)
;;;;;;;;;;;;;;;;Token for fuel-instrumented partial applications
(declare-fun FStar.Seq.Properties.seq_find_aux.fuel_instrumented_token () Term)
(declare-fun FStar.Seq.Properties.seq_find_aux (Term Term Term Term) Term)
(declare-fun FStar.Seq.Properties.seq_find_aux@tok () Term)


(declare-fun Tm_refine_564e05c43cb7c1f4e1de1a4fb2fd28c8 (Term Term Term) Term)


(declare-fun Tm_refine_eceee487dc5f997fef8ec356a5ed69a1 (Term Term Term) Term)









(declare-fun Tm_arrow_80e1fce2fc22bd81078942999677feae () Term)



;;;;;;;;;;;;;;;;Fuel irrelevance
;;; Fact-ids: Name FStar.Seq.Properties.seq_find_aux; Namespace FStar.Seq.Properties
(assert (! 
;; def=FStar.Seq.Properties.fst(631,8-631,20); use=FStar.Seq.Properties.fst(631,8-631,20)
(forall ((@u0 Fuel) (@x1 Term) (@x2 Term) (@x3 Term) (@x4 Term))
 (! (= (FStar.Seq.Properties.seq_find_aux.fuel_instrumented (SFuel @u0)
@x1
@x2
@x3
@x4)
(FStar.Seq.Properties.seq_find_aux.fuel_instrumented ZFuel
@x1
@x2
@x3
@x4))
 

:pattern ((FStar.Seq.Properties.seq_find_aux.fuel_instrumented (SFuel @u0)
@x1
@x2
@x3
@x4))
:qid @fuel_irrelevance_FStar.Seq.Properties.seq_find_aux.fuel_instrumented))

:named @fuel_irrelevance_FStar.Seq.Properties.seq_find_aux.fuel_instrumented))
;;;;;;;;;;;;;;;;Correspondence of recursive function to instrumented version
;;; Fact-ids: Name FStar.Seq.Properties.seq_find_aux; Namespace FStar.Seq.Properties
(assert (! 
;; def=FStar.Seq.Properties.fst(631,8-631,20); use=FStar.Seq.Properties.fst(631,8-631,20)
(forall ((@x0 Term) (@x1 Term) (@x2 Term) (@x3 Term))
 (! (= (FStar.Seq.Properties.seq_find_aux @x0
@x1
@x2
@x3)
(FStar.Seq.Properties.seq_find_aux.fuel_instrumented MaxFuel
@x0
@x1
@x2
@x3))
 

:pattern ((FStar.Seq.Properties.seq_find_aux @x0
@x1
@x2
@x3))
:qid @fuel_correspondence_FStar.Seq.Properties.seq_find_aux.fuel_instrumented))

:named @fuel_correspondence_FStar.Seq.Properties.seq_find_aux.fuel_instrumented))

; </end encoding FStar.Seq.Properties.seq_find_aux>


; <Start encoding FStar.Seq.Properties.seq_find>


(declare-fun FStar.Seq.Properties.seq_find (Term Term Term) Term)




(declare-fun Tm_arrow_fa0cd0aaf804af216be20b328cb3ec09 () Term)
(declare-fun FStar.Seq.Properties.seq_find@tok () Term)





; </end encoding FStar.Seq.Properties.seq_find>


; <Start encoding FStar.Seq.Properties.find_mem>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.Seq.Properties.find_mem (Term Term Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.Seq.Properties.find_mem@tok () Term)

; </end encoding FStar.Seq.Properties.find_mem>


; <Start encoding FStar.Seq.Properties.for_all>


(declare-fun FStar.Seq.Properties.for_all (Term Term Term) Term)


(declare-fun Tm_refine_307fd373d8b3749096cf164b41cf1984 (Term Term Term) Term)
(declare-fun Tm_arrow_098d0ddce18f722cb743337c9d7dd0b9 () Term)
(declare-fun FStar.Seq.Properties.for_all@tok () Term)




(declare-fun Tm_abs_e818836335067047224d0c19c4cabb2d (Term Term) Term)

; </end encoding FStar.Seq.Properties.for_all>


; <Skipped />


; <Start encoding FStar.Seq.Properties.seq_mem_k>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.Seq.Properties.seq_mem_k (Term Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.Seq.Properties.seq_mem_k@tok () Term)


; </end encoding FStar.Seq.Properties.seq_mem_k>


; <Start encoding FStar.Seq.Properties.seq_to_list>

;;;;;;;;;;;;;;;;Fuel-instrumented function name
(declare-fun FStar.Seq.Properties.seq_to_list.fuel_instrumented (Fuel Term Term) Term)
;;;;;;;;;;;;;;;;Token for fuel-instrumented partial applications
(declare-fun FStar.Seq.Properties.seq_to_list.fuel_instrumented_token () Term)
(declare-fun FStar.Seq.Properties.seq_to_list (Term Term) Term)
(declare-fun FStar.Seq.Properties.seq_to_list@tok () Term)
(declare-fun Tm_refine_c4e3a92f9bd1d01a07e4fb66c5de2e7e (Term Term) Term)

(declare-fun Tm_arrow_7d1aeb9cf9244f8c50e0ad901486a03b () Term)

;;;;;;;;;;;;;;;;Fuel irrelevance
;;; Fact-ids: Name FStar.Seq.Properties.seq_to_list; Namespace FStar.Seq.Properties
(assert (! 
;; def=FStar.Seq.Properties.fst(682,8-682,19); use=FStar.Seq.Properties.fst(682,8-682,19)
(forall ((@u0 Fuel) (@x1 Term) (@x2 Term))
 (! (= (FStar.Seq.Properties.seq_to_list.fuel_instrumented (SFuel @u0)
@x1
@x2)
(FStar.Seq.Properties.seq_to_list.fuel_instrumented ZFuel
@x1
@x2))
 

:pattern ((FStar.Seq.Properties.seq_to_list.fuel_instrumented (SFuel @u0)
@x1
@x2))
:qid @fuel_irrelevance_FStar.Seq.Properties.seq_to_list.fuel_instrumented))

:named @fuel_irrelevance_FStar.Seq.Properties.seq_to_list.fuel_instrumented))
;;;;;;;;;;;;;;;;Correspondence of recursive function to instrumented version
;;; Fact-ids: Name FStar.Seq.Properties.seq_to_list; Namespace FStar.Seq.Properties
(assert (! 
;; def=FStar.Seq.Properties.fst(682,8-682,19); use=FStar.Seq.Properties.fst(682,8-682,19)
(forall ((@x0 Term) (@x1 Term))
 (! (= (FStar.Seq.Properties.seq_to_list @x0
@x1)
(FStar.Seq.Properties.seq_to_list.fuel_instrumented MaxFuel
@x0
@x1))
 

:pattern ((FStar.Seq.Properties.seq_to_list @x0
@x1))
:qid @fuel_correspondence_FStar.Seq.Properties.seq_to_list.fuel_instrumented))

:named @fuel_correspondence_FStar.Seq.Properties.seq_to_list.fuel_instrumented))

; </end encoding FStar.Seq.Properties.seq_to_list>


; <Start encoding FStar.Seq.Properties.seq_of_list>

(declare-fun FStar.Seq.Properties.seq_of_list (Term Term) Term)
(declare-fun Tm_refine_d2d1ea66f2b3a92c2deb42edcbb784ce (Term Term) Term)
(declare-fun Tm_arrow_4966fa2986a35d9c0803c863a2768cbd () Term)
(declare-fun FStar.Seq.Properties.seq_of_list@tok () Term)


; </end encoding FStar.Seq.Properties.seq_of_list>


; <Start encoding FStar.Seq.Properties.lemma_seq_of_list_induction>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.Seq.Properties.lemma_seq_of_list_induction (Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.Seq.Properties.lemma_seq_of_list_induction@tok () Term)

; </end encoding FStar.Seq.Properties.lemma_seq_of_list_induction>


; <Start encoding FStar.Seq.Properties.lemma_seq_list_bij>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.Seq.Properties.lemma_seq_list_bij (Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.Seq.Properties.lemma_seq_list_bij@tok () Term)

; </end encoding FStar.Seq.Properties.lemma_seq_list_bij>


; <Start encoding FStar.Seq.Properties.lemma_list_seq_bij>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.Seq.Properties.lemma_list_seq_bij (Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.Seq.Properties.lemma_list_seq_bij@tok () Term)

; </end encoding FStar.Seq.Properties.lemma_list_seq_bij>


; <Start encoding FStar.Seq.Properties.createL_post>

(declare-fun FStar.Seq.Properties.createL_post (Term Term Term) Term)
(declare-fun Tm_arrow_befeea9093c61a572da65bfe7ce35cff () Term)
(declare-fun FStar.Seq.Properties.createL_post@tok () Term)
(declare-fun Tm_refine_1780a0fddfda88c43d203b562c6d3f5b () Term)

; </end encoding FStar.Seq.Properties.createL_post>


; <Start encoding FStar.Seq.Properties.createL>

(declare-fun FStar.Seq.Properties.createL (Term Term) Term)

(declare-fun Tm_refine_29f54a8a92d732b7f4111928d707db68 (Term Term) Term)
(declare-fun Tm_arrow_6a7bb2ee242e4d89b8744d9965334de3 () Term)
(declare-fun FStar.Seq.Properties.createL@tok () Term)



; </end encoding FStar.Seq.Properties.createL>


; <Start encoding FStar.Seq.Properties.lemma_index_is_nth>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.Seq.Properties.lemma_index_is_nth (Term Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.Seq.Properties.lemma_index_is_nth@tok () Term)

; </end encoding FStar.Seq.Properties.lemma_index_is_nth>


; <Start encoding FStar.Seq.Properties.contains>

(declare-fun FStar.Seq.Properties.contains (Term Term Term) Term)
(declare-fun Tm_arrow_65d0102b1211a5d233193433129106a1 () Term)
(declare-fun FStar.Seq.Properties.contains@tok () Term)

; </end encoding FStar.Seq.Properties.contains>


; <Start encoding FStar.Seq.Properties.contains_intro>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.Seq.Properties.contains_intro (Term Term Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.Seq.Properties.contains_intro@tok () Term)

; </end encoding FStar.Seq.Properties.contains_intro>


; <Start encoding FStar.Seq.Properties.contains_elim>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.Seq.Properties.contains_elim (Term Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.Seq.Properties.contains_elim@tok () Term)

; </end encoding FStar.Seq.Properties.contains_elim>


; <Start encoding FStar.Seq.Properties.lemma_contains_empty>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.Seq.Properties.lemma_contains_empty (Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.Seq.Properties.lemma_contains_empty@tok () Term)

; </end encoding FStar.Seq.Properties.lemma_contains_empty>


; <Start encoding FStar.Seq.Properties.lemma_contains_singleton>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.Seq.Properties.lemma_contains_singleton (Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.Seq.Properties.lemma_contains_singleton@tok () Term)

; </end encoding FStar.Seq.Properties.lemma_contains_singleton>


; <Start encoding FStar.Seq.Properties.intro_append_contains_from_disjunction>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.Seq.Properties.intro_append_contains_from_disjunction (Term Term Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.Seq.Properties.intro_append_contains_from_disjunction@tok () Term)

; </end encoding FStar.Seq.Properties.intro_append_contains_from_disjunction>


; <Start encoding FStar.Seq.Properties.append_contains_equiv>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.Seq.Properties.append_contains_equiv (Term Term Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.Seq.Properties.append_contains_equiv@tok () Term)

; </end encoding FStar.Seq.Properties.append_contains_equiv>


; <Start encoding FStar.Seq.Properties.contains_snoc>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.Seq.Properties.contains_snoc (Term Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.Seq.Properties.contains_snoc@tok () Term)

; </end encoding FStar.Seq.Properties.contains_snoc>


; <Start encoding FStar.Seq.Properties.lemma_find_l_contains>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.Seq.Properties.lemma_find_l_contains (Term Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.Seq.Properties.lemma_find_l_contains@tok () Term)

; </end encoding FStar.Seq.Properties.lemma_find_l_contains>


; <Start encoding FStar.Seq.Properties.contains_cons>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.Seq.Properties.contains_cons (Term Term Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.Seq.Properties.contains_cons@tok () Term)

; </end encoding FStar.Seq.Properties.contains_cons>


; <Start encoding FStar.Seq.Properties.append_cons_snoc>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.Seq.Properties.append_cons_snoc (Term Term Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.Seq.Properties.append_cons_snoc@tok () Term)

; </end encoding FStar.Seq.Properties.append_cons_snoc>


; <Start encoding FStar.Seq.Properties.append_slices>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.Seq.Properties.append_slices (Term Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.Seq.Properties.append_slices@tok () Term)

; </end encoding FStar.Seq.Properties.append_slices>


; <Skipped />


; <Start encoding FStar.Seq.Properties.find_l_none_no_index>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.Seq.Properties.find_l_none_no_index (Term Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.Seq.Properties.find_l_none_no_index@tok () Term)

; </end encoding FStar.Seq.Properties.find_l_none_no_index>


; <Start encoding FStar.Seq.Properties.suffix_of>

(declare-fun FStar.Seq.Properties.suffix_of (Term Term Term) Term)

(declare-fun FStar.Seq.Properties.suffix_of@tok () Term)

; </end encoding FStar.Seq.Properties.suffix_of>


; <Start encoding FStar.Seq.Properties.cons_head_tail>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.Seq.Properties.cons_head_tail (Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.Seq.Properties.cons_head_tail@tok () Term)


; </end encoding FStar.Seq.Properties.cons_head_tail>


; <Start encoding FStar.Seq.Properties.head_cons>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.Seq.Properties.head_cons (Term Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.Seq.Properties.head_cons@tok () Term)

; </end encoding FStar.Seq.Properties.head_cons>


; <Start encoding FStar.Seq.Properties.suffix_of_tail>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.Seq.Properties.suffix_of_tail (Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.Seq.Properties.suffix_of_tail@tok () Term)


; </end encoding FStar.Seq.Properties.suffix_of_tail>


; <Start encoding FStar.Seq.Properties.index_cons_l>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.Seq.Properties.index_cons_l (Term Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.Seq.Properties.index_cons_l@tok () Term)

; </end encoding FStar.Seq.Properties.index_cons_l>


; <Start encoding FStar.Seq.Properties.index_cons_r>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.Seq.Properties.index_cons_r (Term Term Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.Seq.Properties.index_cons_r@tok () Term)

; </end encoding FStar.Seq.Properties.index_cons_r>


; <Start encoding FStar.Seq.Properties.append_cons>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.Seq.Properties.append_cons (Term Term Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.Seq.Properties.append_cons@tok () Term)

; </end encoding FStar.Seq.Properties.append_cons>


; <Start encoding FStar.Seq.Properties.index_tail>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.Seq.Properties.index_tail (Term Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.Seq.Properties.index_tail@tok () Term)

; </end encoding FStar.Seq.Properties.index_tail>


; <Start encoding FStar.Seq.Properties.mem_cons>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.Seq.Properties.mem_cons (Term Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.Seq.Properties.mem_cons@tok () Term)

; </end encoding FStar.Seq.Properties.mem_cons>


; <Start encoding FStar.Seq.Properties.snoc_slice_index>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.Seq.Properties.snoc_slice_index (Term Term Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.Seq.Properties.snoc_slice_index@tok () Term)
(declare-fun Tm_refine_095c5722edf0f79bcd7dce7bd084c7b5 (Term Term Term) Term)

; </end encoding FStar.Seq.Properties.snoc_slice_index>


; <Start encoding FStar.Seq.Properties.cons_index_slice>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.Seq.Properties.cons_index_slice (Term Term Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.Seq.Properties.cons_index_slice@tok () Term)
(declare-fun Tm_refine_09d2e9ab3b9c121b24316d151747e281 (Term Term Term) Term)

; </end encoding FStar.Seq.Properties.cons_index_slice>


; <Start encoding FStar.Seq.Properties.slice_is_empty>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.Seq.Properties.slice_is_empty (Term Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.Seq.Properties.slice_is_empty@tok () Term)


; </end encoding FStar.Seq.Properties.slice_is_empty>


; <Start encoding FStar.Seq.Properties.slice_length>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.Seq.Properties.slice_length (Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.Seq.Properties.slice_length@tok () Term)

; </end encoding FStar.Seq.Properties.slice_length>


; <Start encoding FStar.Seq.Properties.slice_slice>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.Seq.Properties.slice_slice (Term Term Term Term Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.Seq.Properties.slice_slice@tok () Term)

(declare-fun Tm_refine_1ba8fd8bb363097813064c67740b2de5 (Term Term Term) Term)

; </end encoding FStar.Seq.Properties.slice_slice>


; <Start encoding FStar.Seq.Properties.lemma_seq_of_list_index>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.Seq.Properties.lemma_seq_of_list_index (Term Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.Seq.Properties.lemma_seq_of_list_index@tok () Term)


; </end encoding FStar.Seq.Properties.lemma_seq_of_list_index>


; <Start encoding FStar.Seq.Properties.of_list>

(declare-fun FStar.Seq.Properties.of_list (Term Term) Term)
(declare-fun Tm_arrow_474463878fff5c7c9c02e4f0b8b84aa8 () Term)
(declare-fun FStar.Seq.Properties.of_list@tok () Term)

; </end encoding FStar.Seq.Properties.of_list>


; <Start encoding FStar.Seq.Properties.seq_of_list_tl>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.Seq.Properties.seq_of_list_tl (Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.Seq.Properties.seq_of_list_tl@tok () Term)

; </end encoding FStar.Seq.Properties.seq_of_list_tl>


; <Start encoding FStar.Seq.Properties.mem_seq_of_list>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.Seq.Properties.mem_seq_of_list (Term Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.Seq.Properties.mem_seq_of_list@tok () Term)

; </end encoding FStar.Seq.Properties.mem_seq_of_list>


; <Skipped />


; <Start encoding FStar.Seq.Properties.explode_and>

;;;;;;;;;;;;;;;;Fuel-instrumented function name
(declare-fun FStar.Seq.Properties.explode_and.fuel_instrumented (Fuel Term Term Term Term) Term)
;;;;;;;;;;;;;;;;Token for fuel-instrumented partial applications
(declare-fun FStar.Seq.Properties.explode_and.fuel_instrumented_token () Term)
(declare-fun FStar.Seq.Properties.explode_and (Term Term Term Term) Term)
(declare-fun FStar.Seq.Properties.explode_and@tok () Term)
(declare-fun Tm_refine_5885c715bf599d471c43c6b7dcb2413b (Term Term) Term)
(declare-fun Tm_refine_c731267dd71b747abfd9fc75f6f2da81 (Term Term Term) Term)




(declare-fun Tm_arrow_62bce6f622c5bc90fd46048dee6dae55 () Term)
;;;;;;;;;;;;;;;;Fuel irrelevance
;;; Fact-ids: Name FStar.Seq.Properties.explode_and; Namespace FStar.Seq.Properties
(assert (! 
;; def=FStar.Seq.Properties.fst(1018,8-1018,19); use=FStar.Seq.Properties.fst(1018,8-1018,19)
(forall ((@u0 Fuel) (@x1 Term) (@x2 Term) (@x3 Term) (@x4 Term))
 (! (= (FStar.Seq.Properties.explode_and.fuel_instrumented (SFuel @u0)
@x1
@x2
@x3
@x4)
(FStar.Seq.Properties.explode_and.fuel_instrumented ZFuel
@x1
@x2
@x3
@x4))
 

:pattern ((FStar.Seq.Properties.explode_and.fuel_instrumented (SFuel @u0)
@x1
@x2
@x3
@x4))
:qid @fuel_irrelevance_FStar.Seq.Properties.explode_and.fuel_instrumented))

:named @fuel_irrelevance_FStar.Seq.Properties.explode_and.fuel_instrumented))
;;;;;;;;;;;;;;;;Correspondence of recursive function to instrumented version
;;; Fact-ids: Name FStar.Seq.Properties.explode_and; Namespace FStar.Seq.Properties
(assert (! 
;; def=FStar.Seq.Properties.fst(1018,8-1018,19); use=FStar.Seq.Properties.fst(1018,8-1018,19)
(forall ((@x0 Term) (@x1 Term) (@x2 Term) (@x3 Term))
 (! (= (FStar.Seq.Properties.explode_and @x0
@x1
@x2
@x3)
(FStar.Seq.Properties.explode_and.fuel_instrumented MaxFuel
@x0
@x1
@x2
@x3))
 

:pattern ((FStar.Seq.Properties.explode_and @x0
@x1
@x2
@x3))
:qid @fuel_correspondence_FStar.Seq.Properties.explode_and.fuel_instrumented))

:named @fuel_correspondence_FStar.Seq.Properties.explode_and.fuel_instrumented))

; </end encoding FStar.Seq.Properties.explode_and>


; <Start encoding FStar.Seq.Properties.pointwise_and>

(declare-fun Tm_refine_9f068c7f6ce275579028a195ac18485b (Term) Term)
(declare-fun Tm_refine_1ad818e6438a897337e89a3053cb2002 (Term Term) Term)
(declare-fun FStar.Seq.Properties.pointwise_and (Term Term Term) Term)


(declare-fun Tm_arrow_1d69c34f503e87805d9fa1b40bc9b696 () Term)
(declare-fun FStar.Seq.Properties.pointwise_and@tok () Term)



; </end encoding FStar.Seq.Properties.pointwise_and>


; <Start encoding FStar.Seq.Properties.intro_of_list'>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.Seq.Properties.intro_of_list_ (Term Term Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.Seq.Properties.intro_of_list_@tok () Term)

; </end encoding FStar.Seq.Properties.intro_of_list'>


; <Start encoding FStar.Seq.Properties.intro_of_list>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.Seq.Properties.intro_of_list (Term Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.Seq.Properties.intro_of_list@tok () Term)

; </end encoding FStar.Seq.Properties.intro_of_list>


; <Start encoding FStar.Seq.Properties.elim_of_list'>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.Seq.Properties.elim_of_list_ (Term Term Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.Seq.Properties.elim_of_list_@tok () Term)

; </end encoding FStar.Seq.Properties.elim_of_list'>


; <Start encoding FStar.Seq.Properties.elim_of_list>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.Seq.Properties.elim_of_list (Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.Seq.Properties.elim_of_list@tok () Term)

; </end encoding FStar.Seq.Properties.elim_of_list>


; <Skipped />


; <Start encoding FStar.Seq.Properties.sortWith>


(declare-fun FStar.Seq.Properties.sortWith (Term Term Term) Term)

(declare-fun Tm_arrow_783d577ed6adadfd234f2ce68178463f () Term)
(declare-fun FStar.Seq.Properties.sortWith@tok () Term)


; </end encoding FStar.Seq.Properties.sortWith>


; <Start encoding FStar.Seq.Properties.lemma_seq_to_list_permutation>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.Seq.Properties.lemma_seq_to_list_permutation (Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.Seq.Properties.lemma_seq_to_list_permutation@tok () Term)

; </end encoding FStar.Seq.Properties.lemma_seq_to_list_permutation>


; <Start encoding FStar.Seq.Properties.lemma_seq_of_list_permutation>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.Seq.Properties.lemma_seq_of_list_permutation (Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.Seq.Properties.lemma_seq_of_list_permutation@tok () Term)

; </end encoding FStar.Seq.Properties.lemma_seq_of_list_permutation>


; <Start encoding FStar.Seq.Properties.lemma_seq_of_list_sorted>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.Seq.Properties.lemma_seq_of_list_sorted (Term Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.Seq.Properties.lemma_seq_of_list_sorted@tok () Term)

; </end encoding FStar.Seq.Properties.lemma_seq_of_list_sorted>


; <Start encoding FStar.Seq.Properties.lemma_seq_sortwith_correctness>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.Seq.Properties.lemma_seq_sortwith_correctness (Term Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.Seq.Properties.lemma_seq_sortwith_correctness@tok () Term)

; </end encoding FStar.Seq.Properties.lemma_seq_sortwith_correctness>


; <Start encoding FStar.Seq.Properties.sort_lseq>

(declare-fun FStar.Seq.Properties.sort_lseq (Term Term Term Term) Term)
(declare-fun Tm_refine_896d0573468d5c87de125067e75d7d47 (Term Term Term Term) Term)
(declare-fun Tm_arrow_3fb7de3746e0ee65d4a1a51ab385c639 () Term)
(declare-fun FStar.Seq.Properties.sort_lseq@tok () Term)

;;;;;;;;;;;;;;;;kick_partial_app
;;; Fact-ids: Name FStar.Seq.Properties.sort_lseq; Namespace FStar.Seq.Properties
(assert (! (Valid (ApplyTT __uu__PartialApp
FStar.List.Tot.Base.compare_of_bool@tok))
:named @kick_partial_app_168a5a7933bf2aec40b9569f3322d078))

; </end encoding FStar.Seq.Properties.sort_lseq>


; UNSAT CORE: @MaxFuel_assumption, @MaxIFuel_assumption, @fuel_correspondence_Prims.pow2.fuel_instrumented, @query, constructor_distinct_Lib.IntTypes.S16, constructor_distinct_Lib.IntTypes.S32, constructor_distinct_Lib.IntTypes.SEC, equality_tok_Lib.IntTypes.S16@tok, equality_tok_Lib.IntTypes.S32@tok, equality_tok_Lib.IntTypes.SEC@tok, equation_Lib.IntTypes.bits, equation_Lib.IntTypes.range, equation_Lib.IntTypes.signed, equation_Lib.IntTypes.unsigned, equation_Lib.IntTypes.v, equation_Prims.nat, equation_Prims.pos, equation_Spec.Kyber2.Params.params_q, int_inversion, int_typing, lemma_FStar.UInt.pow2_values, primitive_Prims.op_Addition, primitive_Prims.op_Division, primitive_Prims.op_LessThanOrEqual, primitive_Prims.op_Minus, primitive_Prims.op_Multiply, primitive_Prims.op_Subtraction, projection_inverse_BoxBool_proj_0, projection_inverse_BoxInt_proj_0, refinement_interpretation_Tm_refine_2b320913041b873fce938dd17eebb3e2, refinement_interpretation_Tm_refine_542f9d4f129664613f2483a6c88bc7c2, refinement_interpretation_Tm_refine_774ba3f728d91ead8ef40be66c9802e5, refinement_interpretation_Tm_refine_83845a86f2550cdf941eeb1d9b59602b, refinement_interpretation_Tm_refine_9d3fd79fd314167f1a9c213a188da3ec, refinement_interpretation_Tm_refine_b2401a8cabe2f9a01538f32548fa9f6c, typing_Lib.IntTypes.mk_int, typing_Prims.pow2, typing_tok_Lib.IntTypes.S32@tok, typing_tok_Lib.IntTypes.SEC@tok

;;; End module FStar.Seq.Properties (797 decls; total size 67180)

;;; Start module FStar.Seq

; UNSAT CORE: @MaxFuel_assumption, @MaxIFuel_assumption, @fuel_correspondence_Prims.pow2.fuel_instrumented, @query, constructor_distinct_Lib.IntTypes.S16, constructor_distinct_Lib.IntTypes.S32, constructor_distinct_Lib.IntTypes.SEC, equality_tok_Lib.IntTypes.S16@tok, equality_tok_Lib.IntTypes.S32@tok, equality_tok_Lib.IntTypes.SEC@tok, equation_Lib.IntTypes.bits, equation_Lib.IntTypes.range, equation_Lib.IntTypes.signed, equation_Lib.IntTypes.unsigned, equation_Lib.IntTypes.v, equation_Prims.nat, equation_Prims.pos, equation_Spec.Kyber2.Params.params_q, int_inversion, int_typing, lemma_FStar.UInt.pow2_values, primitive_Prims.op_Addition, primitive_Prims.op_Division, primitive_Prims.op_LessThanOrEqual, primitive_Prims.op_Minus, primitive_Prims.op_Multiply, primitive_Prims.op_Subtraction, projection_inverse_BoxBool_proj_0, projection_inverse_BoxInt_proj_0, refinement_interpretation_Tm_refine_2b320913041b873fce938dd17eebb3e2, refinement_interpretation_Tm_refine_542f9d4f129664613f2483a6c88bc7c2, refinement_interpretation_Tm_refine_774ba3f728d91ead8ef40be66c9802e5, refinement_interpretation_Tm_refine_83845a86f2550cdf941eeb1d9b59602b, refinement_interpretation_Tm_refine_9d3fd79fd314167f1a9c213a188da3ec, refinement_interpretation_Tm_refine_b2401a8cabe2f9a01538f32548fa9f6c, typing_Lib.IntTypes.mk_int, typing_Prims.pow2, typing_tok_Lib.IntTypes.S32@tok, typing_tok_Lib.IntTypes.SEC@tok

;;; End module FStar.Seq (1 decls; total size 1400)

;;; Start module FStar.Math.Lib

; <Start encoding FStar.Math.Lib.lemma_div_def>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.Math.Lib.lemma_div_def (Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.Math.Lib.lemma_div_def@tok () Term)

; </end encoding FStar.Math.Lib.lemma_div_def>


; <Start encoding FStar.Math.Lib.mul_lemma>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.Math.Lib.mul_lemma (Term Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.Math.Lib.mul_lemma@tok () Term)

; </end encoding FStar.Math.Lib.mul_lemma>


; <Start encoding FStar.Math.Lib.mul_lemma'>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.Math.Lib.mul_lemma_ (Term Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.Math.Lib.mul_lemma_@tok () Term)

; </end encoding FStar.Math.Lib.mul_lemma'>


; <Start encoding FStar.Math.Lib.mul_div_lemma>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.Math.Lib.mul_div_lemma (Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.Math.Lib.mul_div_lemma@tok () Term)

; </end encoding FStar.Math.Lib.mul_div_lemma>


; <Start encoding FStar.Math.Lib.slash_decr_axiom>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.Math.Lib.slash_decr_axiom (Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.Math.Lib.slash_decr_axiom@tok () Term)

; </end encoding FStar.Math.Lib.slash_decr_axiom>


; <Start encoding FStar.Math.Lib.lemma_mul_minus_distr_l>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.Math.Lib.lemma_mul_minus_distr_l (Term Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.Math.Lib.lemma_mul_minus_distr_l@tok () Term)

; </end encoding FStar.Math.Lib.lemma_mul_minus_distr_l>


; <Skipped />


; <Start encoding FStar.Math.Lib.slash_star_axiom>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.Math.Lib.slash_star_axiom (Term Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.Math.Lib.slash_star_axiom@tok () Term)

; </end encoding FStar.Math.Lib.slash_star_axiom>


; <Skipped />


; <Start encoding FStar.Math.Lib.log_2>

;;;;;;;;;;;;;;;;Fuel-instrumented function name
(declare-fun FStar.Math.Lib.log_2.fuel_instrumented (Fuel Term) Term)
;;;;;;;;;;;;;;;;Token for fuel-instrumented partial applications
(declare-fun FStar.Math.Lib.log_2.fuel_instrumented_token () Term)
(declare-fun FStar.Math.Lib.log_2 (Term) Term)
(declare-fun FStar.Math.Lib.log_2@tok () Term)
(declare-fun Tm_arrow_195a91d0390990c5da9b9b2c7b2e9a5f () Term)
;;;;;;;;;;;;;;;;Fuel irrelevance
;;; Fact-ids: Name FStar.Math.Lib.log_2; Namespace FStar.Math.Lib
(assert (! 
;; def=FStar.Math.Lib.fst(54,8-54,13); use=FStar.Math.Lib.fst(54,8-54,13)
(forall ((@u0 Fuel) (@x1 Term))
 (! (= (FStar.Math.Lib.log_2.fuel_instrumented (SFuel @u0)
@x1)
(FStar.Math.Lib.log_2.fuel_instrumented ZFuel
@x1))
 

:pattern ((FStar.Math.Lib.log_2.fuel_instrumented (SFuel @u0)
@x1))
:qid @fuel_irrelevance_FStar.Math.Lib.log_2.fuel_instrumented))

:named @fuel_irrelevance_FStar.Math.Lib.log_2.fuel_instrumented))
;;;;;;;;;;;;;;;;Correspondence of recursive function to instrumented version
;;; Fact-ids: Name FStar.Math.Lib.log_2; Namespace FStar.Math.Lib
(assert (! 
;; def=FStar.Math.Lib.fst(54,8-54,13); use=FStar.Math.Lib.fst(54,8-54,13)
(forall ((@x0 Term))
 (! (= (FStar.Math.Lib.log_2 @x0)
(FStar.Math.Lib.log_2.fuel_instrumented MaxFuel
@x0))
 

:pattern ((FStar.Math.Lib.log_2 @x0))
:qid @fuel_correspondence_FStar.Math.Lib.log_2.fuel_instrumented))

:named @fuel_correspondence_FStar.Math.Lib.log_2.fuel_instrumented))

; </end encoding FStar.Math.Lib.log_2>


; <Start encoding FStar.Math.Lib.powx>

;;;;;;;;;;;;;;;;Fuel-instrumented function name
(declare-fun FStar.Math.Lib.powx.fuel_instrumented (Fuel Term Term) Term)
;;;;;;;;;;;;;;;;Token for fuel-instrumented partial applications
(declare-fun FStar.Math.Lib.powx.fuel_instrumented_token () Term)
(declare-fun FStar.Math.Lib.powx (Term Term) Term)
(declare-fun FStar.Math.Lib.powx@tok () Term)
(declare-fun Tm_arrow_97e79e8898be25d1baac7492eb8157a8 () Term)
;;;;;;;;;;;;;;;;Fuel irrelevance
;;; Fact-ids: Name FStar.Math.Lib.powx; Namespace FStar.Math.Lib
(assert (! 
;; def=FStar.Math.Lib.fst(59,8-59,12); use=FStar.Math.Lib.fst(59,8-59,12)
(forall ((@u0 Fuel) (@x1 Term) (@x2 Term))
 (! (= (FStar.Math.Lib.powx.fuel_instrumented (SFuel @u0)
@x1
@x2)
(FStar.Math.Lib.powx.fuel_instrumented ZFuel
@x1
@x2))
 

:pattern ((FStar.Math.Lib.powx.fuel_instrumented (SFuel @u0)
@x1
@x2))
:qid @fuel_irrelevance_FStar.Math.Lib.powx.fuel_instrumented))

:named @fuel_irrelevance_FStar.Math.Lib.powx.fuel_instrumented))
;;;;;;;;;;;;;;;;Correspondence of recursive function to instrumented version
;;; Fact-ids: Name FStar.Math.Lib.powx; Namespace FStar.Math.Lib
(assert (! 
;; def=FStar.Math.Lib.fst(59,8-59,12); use=FStar.Math.Lib.fst(59,8-59,12)
(forall ((@x0 Term) (@x1 Term))
 (! (= (FStar.Math.Lib.powx @x0
@x1)
(FStar.Math.Lib.powx.fuel_instrumented MaxFuel
@x0
@x1))
 

:pattern ((FStar.Math.Lib.powx @x0
@x1))
:qid @fuel_correspondence_FStar.Math.Lib.powx.fuel_instrumented))

:named @fuel_correspondence_FStar.Math.Lib.powx.fuel_instrumented))

; </end encoding FStar.Math.Lib.powx>


; <Start encoding FStar.Math.Lib.abs>

(declare-fun FStar.Math.Lib.abs (Term) Term)
(declare-fun Tm_refine_5b706f1316bc4c0722dc2171363a324f (Term) Term)
(declare-fun Tm_arrow_485462bf1365ac4f0407149110b772cd () Term)
(declare-fun FStar.Math.Lib.abs@tok () Term)


; </end encoding FStar.Math.Lib.abs>


; <Start encoding FStar.Math.Lib.max>

(declare-fun FStar.Math.Lib.max (Term Term) Term)
(declare-fun Tm_refine_3b1de445e68d5a7cbfc9e637b6d5fe5c (Term Term) Term)
(declare-fun Tm_arrow_6cac7a49c19aab6d14a44dce4ddd50d7 () Term)
(declare-fun FStar.Math.Lib.max@tok () Term)


; </end encoding FStar.Math.Lib.max>


; <Start encoding FStar.Math.Lib.min>

(declare-fun FStar.Math.Lib.min (Term Term) Term)
(declare-fun Tm_refine_75a39246caf92bd7ba0c54b533ac97ba (Term Term) Term)
(declare-fun Tm_arrow_f1c63d0f3ff3d4c0a4e173563f61a3ec () Term)
(declare-fun FStar.Math.Lib.min@tok () Term)


; </end encoding FStar.Math.Lib.min>


; <Start encoding FStar.Math.Lib.div>

(declare-fun FStar.Math.Lib.div (Term Term) Term)
(declare-fun Tm_refine_2a75ac9e9041407930877285ccf479d9 (Term) Term)
(declare-fun Tm_arrow_bb819be7118d7bfb2cedbf3c6477c362 () Term)
(declare-fun FStar.Math.Lib.div@tok () Term)


; </end encoding FStar.Math.Lib.div>


; <Start encoding FStar.Math.Lib.div_non_eucl>

(declare-fun FStar.Math.Lib.div_non_eucl (Term Term) Term)
(declare-fun Tm_refine_0ffeb4b35eb66c9dc7f43d49d6f24837 (Term Term) Term)
(declare-fun Tm_arrow_7c4dc753d10246d9d92341a1295260f4 () Term)
(declare-fun FStar.Math.Lib.div_non_eucl@tok () Term)


; </end encoding FStar.Math.Lib.div_non_eucl>


; <Start encoding FStar.Math.Lib.shift_left>

(declare-fun FStar.Math.Lib.shift_left (Term Term) Term)
(declare-fun Tm_refine_180a7ec928fc00449a9ff97fd83eb9f7 (Term Term) Term)
(declare-fun Tm_arrow_ebb8ce92eba15a16c00c7e434e88c84b () Term)
(declare-fun FStar.Math.Lib.shift_left@tok () Term)


; </end encoding FStar.Math.Lib.shift_left>


; <Start encoding FStar.Math.Lib.arithmetic_shift_right>

(declare-fun FStar.Math.Lib.arithmetic_shift_right (Term Term) Term)
(declare-fun Tm_refine_1b8188dd620bafffed7e311591823814 (Term Term) Term)
(declare-fun Tm_arrow_0d2ab070c39795db6825f9a2ab12fa9a () Term)
(declare-fun FStar.Math.Lib.arithmetic_shift_right@tok () Term)


; </end encoding FStar.Math.Lib.arithmetic_shift_right>


; <Start encoding FStar.Math.Lib.signed_modulo>

(declare-fun FStar.Math.Lib.signed_modulo (Term Term) Term)
(declare-fun Tm_refine_7f910f581ef6c422e545ac01d1c8b2f5 (Term Term) Term)
(declare-fun Tm_arrow_735d78cef45a99c351b2596c50444f63 () Term)
(declare-fun FStar.Math.Lib.signed_modulo@tok () Term)


; </end encoding FStar.Math.Lib.signed_modulo>


; <Start encoding FStar.Math.Lib.op_Plus_Percent>

(declare-fun FStar.Math.Lib.op_Plus_Percent (Term Term) Term)
(declare-fun Tm_refine_d653f98e8ce399d5b7ea191c117fe516 (Term Term) Term)
(declare-fun Tm_arrow_47a9b4ba9fff686aea1b155fa584e4a2 () Term)
(declare-fun FStar.Math.Lib.op_Plus_Percent@tok () Term)


; </end encoding FStar.Math.Lib.op_Plus_Percent>


; <Start encoding FStar.Math.Lib.powx_lemma1>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.Math.Lib.powx_lemma1 (Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.Math.Lib.powx_lemma1@tok () Term)

; </end encoding FStar.Math.Lib.powx_lemma1>


; <Start encoding FStar.Math.Lib.powx_lemma2>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.Math.Lib.powx_lemma2 (Term Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.Math.Lib.powx_lemma2@tok () Term)

; </end encoding FStar.Math.Lib.powx_lemma2>


; <Start encoding FStar.Math.Lib.abs_mul_lemma>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.Math.Lib.abs_mul_lemma (Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.Math.Lib.abs_mul_lemma@tok () Term)

; </end encoding FStar.Math.Lib.abs_mul_lemma>


; <Start encoding FStar.Math.Lib.signed_modulo_property>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.Math.Lib.signed_modulo_property (Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.Math.Lib.signed_modulo_property@tok () Term)

; </end encoding FStar.Math.Lib.signed_modulo_property>


; <Start encoding FStar.Math.Lib.div_non_eucl_decr_lemma>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.Math.Lib.div_non_eucl_decr_lemma (Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.Math.Lib.div_non_eucl_decr_lemma@tok () Term)

; </end encoding FStar.Math.Lib.div_non_eucl_decr_lemma>


; <Start encoding FStar.Math.Lib.div_non_eucl_bigger_denom_lemma>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.Math.Lib.div_non_eucl_bigger_denom_lemma (Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.Math.Lib.div_non_eucl_bigger_denom_lemma@tok () Term)

; </end encoding FStar.Math.Lib.div_non_eucl_bigger_denom_lemma>


; UNSAT CORE: @MaxFuel_assumption, @MaxIFuel_assumption, @fuel_correspondence_Prims.pow2.fuel_instrumented, @query, constructor_distinct_Lib.IntTypes.S16, constructor_distinct_Lib.IntTypes.S32, constructor_distinct_Lib.IntTypes.SEC, equality_tok_Lib.IntTypes.S16@tok, equality_tok_Lib.IntTypes.S32@tok, equality_tok_Lib.IntTypes.SEC@tok, equation_Lib.IntTypes.bits, equation_Lib.IntTypes.range, equation_Lib.IntTypes.signed, equation_Lib.IntTypes.unsigned, equation_Lib.IntTypes.v, equation_Prims.nat, equation_Prims.pos, equation_Spec.Kyber2.Params.params_q, int_inversion, int_typing, lemma_FStar.UInt.pow2_values, primitive_Prims.op_Addition, primitive_Prims.op_Division, primitive_Prims.op_LessThanOrEqual, primitive_Prims.op_Minus, primitive_Prims.op_Multiply, primitive_Prims.op_Subtraction, projection_inverse_BoxBool_proj_0, projection_inverse_BoxInt_proj_0, refinement_interpretation_Tm_refine_2b320913041b873fce938dd17eebb3e2, refinement_interpretation_Tm_refine_542f9d4f129664613f2483a6c88bc7c2, refinement_interpretation_Tm_refine_774ba3f728d91ead8ef40be66c9802e5, refinement_interpretation_Tm_refine_83845a86f2550cdf941eeb1d9b59602b, refinement_interpretation_Tm_refine_9d3fd79fd314167f1a9c213a188da3ec, refinement_interpretation_Tm_refine_b2401a8cabe2f9a01538f32548fa9f6c, typing_Lib.IntTypes.mk_int, typing_Prims.pow2, typing_tok_Lib.IntTypes.S32@tok, typing_tok_Lib.IntTypes.SEC@tok

;;; End module FStar.Math.Lib (136 decls; total size 12127)

;;; Start module FStar.Math.Lemmas

; <Skipped />


; <Start encoding FStar.Math.Lemmas.euclidean_div_axiom>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.Math.Lemmas.euclidean_div_axiom (Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.Math.Lemmas.euclidean_div_axiom@tok () Term)

; </end encoding FStar.Math.Lemmas.euclidean_div_axiom>


; <Start encoding FStar.Math.Lemmas.lemma_eucl_div_bound>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.Math.Lemmas.lemma_eucl_div_bound (Term Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.Math.Lemmas.lemma_eucl_div_bound@tok () Term)

; </end encoding FStar.Math.Lemmas.lemma_eucl_div_bound>


; <Start encoding FStar.Math.Lemmas.lemma_mult_le_left>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.Math.Lemmas.lemma_mult_le_left (Term Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.Math.Lemmas.lemma_mult_le_left@tok () Term)

; </end encoding FStar.Math.Lemmas.lemma_mult_le_left>


; <Start encoding FStar.Math.Lemmas.lemma_mult_le_right>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.Math.Lemmas.lemma_mult_le_right (Term Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.Math.Lemmas.lemma_mult_le_right@tok () Term)

; </end encoding FStar.Math.Lemmas.lemma_mult_le_right>


; <Start encoding FStar.Math.Lemmas.lemma_mult_lt_left>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.Math.Lemmas.lemma_mult_lt_left (Term Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.Math.Lemmas.lemma_mult_lt_left@tok () Term)

; </end encoding FStar.Math.Lemmas.lemma_mult_lt_left>


; <Start encoding FStar.Math.Lemmas.lemma_mult_lt_right>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.Math.Lemmas.lemma_mult_lt_right (Term Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.Math.Lemmas.lemma_mult_lt_right@tok () Term)

; </end encoding FStar.Math.Lemmas.lemma_mult_lt_right>


; <Start encoding FStar.Math.Lemmas.lemma_mult_lt_sqr>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.Math.Lemmas.lemma_mult_lt_sqr (Term Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.Math.Lemmas.lemma_mult_lt_sqr@tok () Term)

; </end encoding FStar.Math.Lemmas.lemma_mult_lt_sqr>


; <Start encoding FStar.Math.Lemmas.distributivity_add_left>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.Math.Lemmas.distributivity_add_left (Term Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.Math.Lemmas.distributivity_add_left@tok () Term)

; </end encoding FStar.Math.Lemmas.distributivity_add_left>


; <Start encoding FStar.Math.Lemmas.distributivity_add_right>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.Math.Lemmas.distributivity_add_right (Term Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.Math.Lemmas.distributivity_add_right@tok () Term)

; </end encoding FStar.Math.Lemmas.distributivity_add_right>


; <Start encoding FStar.Math.Lemmas.distributivity_sub_left>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.Math.Lemmas.distributivity_sub_left (Term Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.Math.Lemmas.distributivity_sub_left@tok () Term)

; </end encoding FStar.Math.Lemmas.distributivity_sub_left>


; <Start encoding FStar.Math.Lemmas.distributivity_sub_right>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.Math.Lemmas.distributivity_sub_right (Term Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.Math.Lemmas.distributivity_sub_right@tok () Term)

; </end encoding FStar.Math.Lemmas.distributivity_sub_right>


; <Start encoding FStar.Math.Lemmas.paren_mul_left>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.Math.Lemmas.paren_mul_left (Term Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.Math.Lemmas.paren_mul_left@tok () Term)

; </end encoding FStar.Math.Lemmas.paren_mul_left>


; <Start encoding FStar.Math.Lemmas.paren_mul_right>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.Math.Lemmas.paren_mul_right (Term Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.Math.Lemmas.paren_mul_right@tok () Term)

; </end encoding FStar.Math.Lemmas.paren_mul_right>


; <Start encoding FStar.Math.Lemmas.paren_add_left>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.Math.Lemmas.paren_add_left (Term Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.Math.Lemmas.paren_add_left@tok () Term)

; </end encoding FStar.Math.Lemmas.paren_add_left>


; <Start encoding FStar.Math.Lemmas.paren_add_right>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.Math.Lemmas.paren_add_right (Term Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.Math.Lemmas.paren_add_right@tok () Term)

; </end encoding FStar.Math.Lemmas.paren_add_right>


; <Start encoding FStar.Math.Lemmas.addition_is_associative>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.Math.Lemmas.addition_is_associative (Term Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.Math.Lemmas.addition_is_associative@tok () Term)

; </end encoding FStar.Math.Lemmas.addition_is_associative>


; <Start encoding FStar.Math.Lemmas.subtraction_is_distributive>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.Math.Lemmas.subtraction_is_distributive (Term Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.Math.Lemmas.subtraction_is_distributive@tok () Term)

; </end encoding FStar.Math.Lemmas.subtraction_is_distributive>


; <Start encoding FStar.Math.Lemmas.swap_add_plus_minus>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.Math.Lemmas.swap_add_plus_minus (Term Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.Math.Lemmas.swap_add_plus_minus@tok () Term)

; </end encoding FStar.Math.Lemmas.swap_add_plus_minus>


; <Start encoding FStar.Math.Lemmas.swap_mul>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.Math.Lemmas.swap_mul (Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.Math.Lemmas.swap_mul@tok () Term)

; </end encoding FStar.Math.Lemmas.swap_mul>


; <Start encoding FStar.Math.Lemmas.neg_mul_left>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.Math.Lemmas.neg_mul_left (Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.Math.Lemmas.neg_mul_left@tok () Term)

; </end encoding FStar.Math.Lemmas.neg_mul_left>


; <Start encoding FStar.Math.Lemmas.neg_mul_right>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.Math.Lemmas.neg_mul_right (Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.Math.Lemmas.neg_mul_right@tok () Term)

; </end encoding FStar.Math.Lemmas.neg_mul_right>


; <Start encoding FStar.Math.Lemmas.swap_neg_mul>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.Math.Lemmas.swap_neg_mul (Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.Math.Lemmas.swap_neg_mul@tok () Term)

; </end encoding FStar.Math.Lemmas.swap_neg_mul>


; <Start encoding FStar.Math.Lemmas.mul_binds_tighter>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.Math.Lemmas.mul_binds_tighter (Term Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.Math.Lemmas.mul_binds_tighter@tok () Term)

; </end encoding FStar.Math.Lemmas.mul_binds_tighter>


; <Skipped />


; <Start encoding FStar.Math.Lemmas.mul_ineq1>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.Math.Lemmas.mul_ineq1 (Term Term Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.Math.Lemmas.mul_ineq1@tok () Term)

; </end encoding FStar.Math.Lemmas.mul_ineq1>


; <Skipped />


; <Start encoding FStar.Math.Lemmas.nat_times_nat_is_nat>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.Math.Lemmas.nat_times_nat_is_nat (Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.Math.Lemmas.nat_times_nat_is_nat@tok () Term)

; </end encoding FStar.Math.Lemmas.nat_times_nat_is_nat>


; <Start encoding FStar.Math.Lemmas.pos_times_pos_is_pos>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.Math.Lemmas.pos_times_pos_is_pos (Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.Math.Lemmas.pos_times_pos_is_pos@tok () Term)

; </end encoding FStar.Math.Lemmas.pos_times_pos_is_pos>


; <Start encoding FStar.Math.Lemmas.nat_over_pos_is_nat>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.Math.Lemmas.nat_over_pos_is_nat (Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.Math.Lemmas.nat_over_pos_is_nat@tok () Term)

; </end encoding FStar.Math.Lemmas.nat_over_pos_is_nat>


; <Skipped />


; <Start encoding FStar.Math.Lemmas.pow2_double_sum>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.Math.Lemmas.pow2_double_sum (Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.Math.Lemmas.pow2_double_sum@tok () Term)

; </end encoding FStar.Math.Lemmas.pow2_double_sum>


; <Start encoding FStar.Math.Lemmas.pow2_double_mult>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.Math.Lemmas.pow2_double_mult (Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.Math.Lemmas.pow2_double_mult@tok () Term)

; </end encoding FStar.Math.Lemmas.pow2_double_mult>


; <Start encoding FStar.Math.Lemmas.pow2_lt_compat>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.Math.Lemmas.pow2_lt_compat (Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.Math.Lemmas.pow2_lt_compat@tok () Term)

; </end encoding FStar.Math.Lemmas.pow2_lt_compat>


; <Start encoding FStar.Math.Lemmas.pow2_le_compat>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.Math.Lemmas.pow2_le_compat (Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.Math.Lemmas.pow2_le_compat@tok () Term)

; </end encoding FStar.Math.Lemmas.pow2_le_compat>


; <Start encoding FStar.Math.Lemmas.pow2_plus>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.Math.Lemmas.pow2_plus (Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.Math.Lemmas.pow2_plus@tok () Term)

; </end encoding FStar.Math.Lemmas.pow2_plus>


; <Start encoding FStar.Math.Lemmas.pow2_minus>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.Math.Lemmas.pow2_minus (Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.Math.Lemmas.pow2_minus@tok () Term)

; </end encoding FStar.Math.Lemmas.pow2_minus>


; <Skipped />


; <Start encoding FStar.Math.Lemmas.multiply_fractions>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.Math.Lemmas.multiply_fractions (Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.Math.Lemmas.multiply_fractions@tok () Term)

; </end encoding FStar.Math.Lemmas.multiply_fractions>


; <Start encoding FStar.Math.Lemmas.modulo_lemma>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.Math.Lemmas.modulo_lemma (Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.Math.Lemmas.modulo_lemma@tok () Term)

; </end encoding FStar.Math.Lemmas.modulo_lemma>


; <Start encoding FStar.Math.Lemmas.lemma_div_mod>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.Math.Lemmas.lemma_div_mod (Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.Math.Lemmas.lemma_div_mod@tok () Term)

; </end encoding FStar.Math.Lemmas.lemma_div_mod>


; <Start encoding FStar.Math.Lemmas.lemma_mod_lt>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.Math.Lemmas.lemma_mod_lt (Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.Math.Lemmas.lemma_mod_lt@tok () Term)

; </end encoding FStar.Math.Lemmas.lemma_mod_lt>


; <Start encoding FStar.Math.Lemmas.lemma_div_lt_nat>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.Math.Lemmas.lemma_div_lt_nat (Term Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.Math.Lemmas.lemma_div_lt_nat@tok () Term)

; </end encoding FStar.Math.Lemmas.lemma_div_lt_nat>


; <Start encoding FStar.Math.Lemmas.lemma_div_lt>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.Math.Lemmas.lemma_div_lt (Term Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.Math.Lemmas.lemma_div_lt@tok () Term)

; </end encoding FStar.Math.Lemmas.lemma_div_lt>


; <Start encoding FStar.Math.Lemmas.bounded_multiple_is_zero>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.Math.Lemmas.bounded_multiple_is_zero (Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.Math.Lemmas.bounded_multiple_is_zero@tok () Term)

; </end encoding FStar.Math.Lemmas.bounded_multiple_is_zero>


; <Start encoding FStar.Math.Lemmas.small_div>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.Math.Lemmas.small_div (Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.Math.Lemmas.small_div@tok () Term)

; </end encoding FStar.Math.Lemmas.small_div>


; <Start encoding FStar.Math.Lemmas.small_mod>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.Math.Lemmas.small_mod (Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.Math.Lemmas.small_mod@tok () Term)

; </end encoding FStar.Math.Lemmas.small_mod>


; <Start encoding FStar.Math.Lemmas.lt_multiple_is_equal>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.Math.Lemmas.lt_multiple_is_equal (Term Term Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.Math.Lemmas.lt_multiple_is_equal@tok () Term)

; </end encoding FStar.Math.Lemmas.lt_multiple_is_equal>


; <Skipped />


; <Start encoding FStar.Math.Lemmas.lemma_mod_plus_0>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.Math.Lemmas.lemma_mod_plus_0 (Term Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.Math.Lemmas.lemma_mod_plus_0@tok () Term)

; </end encoding FStar.Math.Lemmas.lemma_mod_plus_0>


; <Skipped />


; <Start encoding FStar.Math.Lemmas.lemma_mod_plus_1>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.Math.Lemmas.lemma_mod_plus_1 (Term Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.Math.Lemmas.lemma_mod_plus_1@tok () Term)

; </end encoding FStar.Math.Lemmas.lemma_mod_plus_1>


; <Start encoding FStar.Math.Lemmas.lemma_eq_trans_2>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.Math.Lemmas.lemma_eq_trans_2 (Term Term Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.Math.Lemmas.lemma_eq_trans_2@tok () Term)

; </end encoding FStar.Math.Lemmas.lemma_eq_trans_2>


; <Start encoding FStar.Math.Lemmas.lemma_mod_plus>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.Math.Lemmas.lemma_mod_plus (Term Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.Math.Lemmas.lemma_mod_plus@tok () Term)

; </end encoding FStar.Math.Lemmas.lemma_mod_plus>


; <Start encoding FStar.Math.Lemmas.add_div_mod_1>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.Math.Lemmas.add_div_mod_1 (Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.Math.Lemmas.add_div_mod_1@tok () Term)

; </end encoding FStar.Math.Lemmas.add_div_mod_1>


; <Skipped />


; <Start encoding FStar.Math.Lemmas.sub_div_mod_1>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.Math.Lemmas.sub_div_mod_1 (Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.Math.Lemmas.sub_div_mod_1@tok () Term)

; </end encoding FStar.Math.Lemmas.sub_div_mod_1>


; <Skipped />


; <Skipped />


; <Start encoding FStar.Math.Lemmas.lemma_div_mod_plus>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.Math.Lemmas.lemma_div_mod_plus (Term Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.Math.Lemmas.lemma_div_mod_plus@tok () Term)

; </end encoding FStar.Math.Lemmas.lemma_div_mod_plus>


; <Skipped />


; <Start encoding FStar.Math.Lemmas.lemma_div_plus>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.Math.Lemmas.lemma_div_plus (Term Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.Math.Lemmas.lemma_div_plus@tok () Term)

; </end encoding FStar.Math.Lemmas.lemma_div_plus>


; <Start encoding FStar.Math.Lemmas.cancel_mul_div>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.Math.Lemmas.cancel_mul_div (Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.Math.Lemmas.cancel_mul_div@tok () Term)

; </end encoding FStar.Math.Lemmas.cancel_mul_div>


; <Start encoding FStar.Math.Lemmas.cancel_mul_mod>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.Math.Lemmas.cancel_mul_mod (Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.Math.Lemmas.cancel_mul_mod@tok () Term)

; </end encoding FStar.Math.Lemmas.cancel_mul_mod>


; <Skipped />


; <Start encoding FStar.Math.Lemmas.mod_add_both>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.Math.Lemmas.mod_add_both (Term Term Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.Math.Lemmas.mod_add_both@tok () Term)

; </end encoding FStar.Math.Lemmas.mod_add_both>


; <Skipped />


; <Start encoding FStar.Math.Lemmas.lemma_mod_add_distr>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.Math.Lemmas.lemma_mod_add_distr (Term Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.Math.Lemmas.lemma_mod_add_distr@tok () Term)

; </end encoding FStar.Math.Lemmas.lemma_mod_add_distr>


; <Start encoding FStar.Math.Lemmas.lemma_mod_sub_distr>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.Math.Lemmas.lemma_mod_sub_distr (Term Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.Math.Lemmas.lemma_mod_sub_distr@tok () Term)

; </end encoding FStar.Math.Lemmas.lemma_mod_sub_distr>


; <Start encoding FStar.Math.Lemmas.lemma_mod_sub_0>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.Math.Lemmas.lemma_mod_sub_0 (Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.Math.Lemmas.lemma_mod_sub_0@tok () Term)

; </end encoding FStar.Math.Lemmas.lemma_mod_sub_0>


; <Skipped />


; <Start encoding FStar.Math.Lemmas.lemma_mod_sub_1>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.Math.Lemmas.lemma_mod_sub_1 (Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.Math.Lemmas.lemma_mod_sub_1@tok () Term)

; </end encoding FStar.Math.Lemmas.lemma_mod_sub_1>


; <Skipped />


; <Skipped />


; <Start encoding FStar.Math.Lemmas.lemma_mod_mul_distr_l_0>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.Math.Lemmas.lemma_mod_mul_distr_l_0 (Term Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.Math.Lemmas.lemma_mod_mul_distr_l_0@tok () Term)

; </end encoding FStar.Math.Lemmas.lemma_mod_mul_distr_l_0>


; <Skipped />


; <Start encoding FStar.Math.Lemmas.lemma_mod_mul_distr_l>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.Math.Lemmas.lemma_mod_mul_distr_l (Term Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.Math.Lemmas.lemma_mod_mul_distr_l@tok () Term)

; </end encoding FStar.Math.Lemmas.lemma_mod_mul_distr_l>


; <Skipped />


; <Start encoding FStar.Math.Lemmas.lemma_mod_mul_distr_r>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.Math.Lemmas.lemma_mod_mul_distr_r (Term Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.Math.Lemmas.lemma_mod_mul_distr_r@tok () Term)

; </end encoding FStar.Math.Lemmas.lemma_mod_mul_distr_r>


; <Skipped />


; <Start encoding FStar.Math.Lemmas.lemma_mod_injective>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.Math.Lemmas.lemma_mod_injective (Term Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.Math.Lemmas.lemma_mod_injective@tok () Term)

; </end encoding FStar.Math.Lemmas.lemma_mod_injective>


; <Start encoding FStar.Math.Lemmas.lemma_mul_sub_distr>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.Math.Lemmas.lemma_mul_sub_distr (Term Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.Math.Lemmas.lemma_mul_sub_distr@tok () Term)

; </end encoding FStar.Math.Lemmas.lemma_mul_sub_distr>


; <Start encoding FStar.Math.Lemmas.lemma_div_exact>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.Math.Lemmas.lemma_div_exact (Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.Math.Lemmas.lemma_div_exact@tok () Term)

; </end encoding FStar.Math.Lemmas.lemma_div_exact>


; <Start encoding FStar.Math.Lemmas.div_exact_r>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.Math.Lemmas.div_exact_r (Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.Math.Lemmas.div_exact_r@tok () Term)

; </end encoding FStar.Math.Lemmas.div_exact_r>


; <Skipped />


; <Start encoding FStar.Math.Lemmas.lemma_mod_spec>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.Math.Lemmas.lemma_mod_spec (Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.Math.Lemmas.lemma_mod_spec@tok () Term)

; </end encoding FStar.Math.Lemmas.lemma_mod_spec>


; <Start encoding FStar.Math.Lemmas.lemma_mod_spec2>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.Math.Lemmas.lemma_mod_spec2 (Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.Math.Lemmas.lemma_mod_spec2@tok () Term)

; </end encoding FStar.Math.Lemmas.lemma_mod_spec2>


; <Start encoding FStar.Math.Lemmas.lemma_mod_plus_distr_l>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.Math.Lemmas.lemma_mod_plus_distr_l (Term Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.Math.Lemmas.lemma_mod_plus_distr_l@tok () Term)

; </end encoding FStar.Math.Lemmas.lemma_mod_plus_distr_l>


; <Start encoding FStar.Math.Lemmas.lemma_mod_plus_distr_r>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.Math.Lemmas.lemma_mod_plus_distr_r (Term Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.Math.Lemmas.lemma_mod_plus_distr_r@tok () Term)

; </end encoding FStar.Math.Lemmas.lemma_mod_plus_distr_r>


; <Skipped />


; <Start encoding FStar.Math.Lemmas.lemma_mod_plus_mul_distr>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.Math.Lemmas.lemma_mod_plus_mul_distr (Term Term Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.Math.Lemmas.lemma_mod_plus_mul_distr@tok () Term)

; </end encoding FStar.Math.Lemmas.lemma_mod_plus_mul_distr>


; <Skipped />


; <Start encoding FStar.Math.Lemmas.lemma_mod_mod>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.Math.Lemmas.lemma_mod_mod (Term Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.Math.Lemmas.lemma_mod_mod@tok () Term)

; </end encoding FStar.Math.Lemmas.lemma_mod_mod>


; <Start encoding FStar.Math.Lemmas.euclidean_division_definition>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.Math.Lemmas.euclidean_division_definition (Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.Math.Lemmas.euclidean_division_definition@tok () Term)

; </end encoding FStar.Math.Lemmas.euclidean_division_definition>


; <Start encoding FStar.Math.Lemmas.modulo_range_lemma>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.Math.Lemmas.modulo_range_lemma (Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.Math.Lemmas.modulo_range_lemma@tok () Term)

; </end encoding FStar.Math.Lemmas.modulo_range_lemma>


; <Start encoding FStar.Math.Lemmas.small_modulo_lemma_1>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.Math.Lemmas.small_modulo_lemma_1 (Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.Math.Lemmas.small_modulo_lemma_1@tok () Term)

; </end encoding FStar.Math.Lemmas.small_modulo_lemma_1>


; <Start encoding FStar.Math.Lemmas.small_modulo_lemma_2>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.Math.Lemmas.small_modulo_lemma_2 (Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.Math.Lemmas.small_modulo_lemma_2@tok () Term)

; </end encoding FStar.Math.Lemmas.small_modulo_lemma_2>


; <Start encoding FStar.Math.Lemmas.small_division_lemma_1>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.Math.Lemmas.small_division_lemma_1 (Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.Math.Lemmas.small_division_lemma_1@tok () Term)

; </end encoding FStar.Math.Lemmas.small_division_lemma_1>


; <Start encoding FStar.Math.Lemmas.small_division_lemma_2>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.Math.Lemmas.small_division_lemma_2 (Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.Math.Lemmas.small_division_lemma_2@tok () Term)

; </end encoding FStar.Math.Lemmas.small_division_lemma_2>


; <Start encoding FStar.Math.Lemmas.multiplication_order_lemma>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.Math.Lemmas.multiplication_order_lemma (Term Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.Math.Lemmas.multiplication_order_lemma@tok () Term)

; </end encoding FStar.Math.Lemmas.multiplication_order_lemma>


; <Start encoding FStar.Math.Lemmas.division_propriety>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.Math.Lemmas.division_propriety (Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.Math.Lemmas.division_propriety@tok () Term)

; </end encoding FStar.Math.Lemmas.division_propriety>


; <Start encoding FStar.Math.Lemmas.division_definition_lemma_1>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.Math.Lemmas.division_definition_lemma_1 (Term Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.Math.Lemmas.division_definition_lemma_1@tok () Term)

; </end encoding FStar.Math.Lemmas.division_definition_lemma_1>


; <Start encoding FStar.Math.Lemmas.division_definition_lemma_2>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.Math.Lemmas.division_definition_lemma_2 (Term Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.Math.Lemmas.division_definition_lemma_2@tok () Term)

; </end encoding FStar.Math.Lemmas.division_definition_lemma_2>


; <Start encoding FStar.Math.Lemmas.division_definition>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.Math.Lemmas.division_definition (Term Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.Math.Lemmas.division_definition@tok () Term)

; </end encoding FStar.Math.Lemmas.division_definition>


; <Start encoding FStar.Math.Lemmas.multiple_division_lemma>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.Math.Lemmas.multiple_division_lemma (Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.Math.Lemmas.multiple_division_lemma@tok () Term)

; </end encoding FStar.Math.Lemmas.multiple_division_lemma>


; <Start encoding FStar.Math.Lemmas.multiple_modulo_lemma>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.Math.Lemmas.multiple_modulo_lemma (Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.Math.Lemmas.multiple_modulo_lemma@tok () Term)

; </end encoding FStar.Math.Lemmas.multiple_modulo_lemma>


; <Start encoding FStar.Math.Lemmas.division_addition_lemma>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.Math.Lemmas.division_addition_lemma (Term Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.Math.Lemmas.division_addition_lemma@tok () Term)

; </end encoding FStar.Math.Lemmas.division_addition_lemma>


; <Start encoding FStar.Math.Lemmas.lemma_div_le_>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.Math.Lemmas.lemma_div_le_ (Term Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.Math.Lemmas.lemma_div_le_@tok () Term)

; </end encoding FStar.Math.Lemmas.lemma_div_le_>


; <Start encoding FStar.Math.Lemmas.lemma_div_le>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.Math.Lemmas.lemma_div_le (Term Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.Math.Lemmas.lemma_div_le@tok () Term)

; </end encoding FStar.Math.Lemmas.lemma_div_le>


; <Skipped />


; <Start encoding FStar.Math.Lemmas.division_sub_lemma>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.Math.Lemmas.division_sub_lemma (Term Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.Math.Lemmas.division_sub_lemma@tok () Term)

; </end encoding FStar.Math.Lemmas.division_sub_lemma>


; <Skipped />


; <Skipped />


; <Start encoding FStar.Math.Lemmas.modulo_distributivity>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.Math.Lemmas.modulo_distributivity (Term Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.Math.Lemmas.modulo_distributivity@tok () Term)

; </end encoding FStar.Math.Lemmas.modulo_distributivity>


; <Start encoding FStar.Math.Lemmas.modulo_addition_lemma>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.Math.Lemmas.modulo_addition_lemma (Term Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.Math.Lemmas.modulo_addition_lemma@tok () Term)

; </end encoding FStar.Math.Lemmas.modulo_addition_lemma>


; <Start encoding FStar.Math.Lemmas.lemma_mod_sub>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.Math.Lemmas.lemma_mod_sub (Term Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.Math.Lemmas.lemma_mod_sub@tok () Term)

; </end encoding FStar.Math.Lemmas.lemma_mod_sub>


; <Start encoding FStar.Math.Lemmas.mod_mult_exact>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.Math.Lemmas.mod_mult_exact (Term Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.Math.Lemmas.mod_mult_exact@tok () Term)

; </end encoding FStar.Math.Lemmas.mod_mult_exact>


; <Start encoding FStar.Math.Lemmas.mod_mul_div_exact>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.Math.Lemmas.mod_mul_div_exact (Term Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.Math.Lemmas.mod_mul_div_exact@tok () Term)

; </end encoding FStar.Math.Lemmas.mod_mul_div_exact>


; <Skipped />


; <Start encoding FStar.Math.Lemmas.mod_pow2_div2>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.Math.Lemmas.mod_pow2_div2 (Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.Math.Lemmas.mod_pow2_div2@tok () Term)

; </end encoding FStar.Math.Lemmas.mod_pow2_div2>


; <Skipped />


; <Start encoding FStar.Math.Lemmas.division_multiplication_lemma>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.Math.Lemmas.division_multiplication_lemma (Term Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.Math.Lemmas.division_multiplication_lemma@tok () Term)

; </end encoding FStar.Math.Lemmas.division_multiplication_lemma>


; <Start encoding FStar.Math.Lemmas.lemma_mul_pos_pos_is_pos>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.Math.Lemmas.lemma_mul_pos_pos_is_pos (Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.Math.Lemmas.lemma_mul_pos_pos_is_pos@tok () Term)

; </end encoding FStar.Math.Lemmas.lemma_mul_pos_pos_is_pos>


; <Start encoding FStar.Math.Lemmas.lemma_mul_nat_pos_is_nat>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.Math.Lemmas.lemma_mul_nat_pos_is_nat (Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.Math.Lemmas.lemma_mul_nat_pos_is_nat@tok () Term)

; </end encoding FStar.Math.Lemmas.lemma_mul_nat_pos_is_nat>


; <Skipped />


; <Start encoding FStar.Math.Lemmas.modulo_division_lemma_0>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.Math.Lemmas.modulo_division_lemma_0 (Term Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.Math.Lemmas.modulo_division_lemma_0@tok () Term)

; </end encoding FStar.Math.Lemmas.modulo_division_lemma_0>


; <Skipped />


; <Start encoding FStar.Math.Lemmas.modulo_division_lemma>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.Math.Lemmas.modulo_division_lemma (Term Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.Math.Lemmas.modulo_division_lemma@tok () Term)

; </end encoding FStar.Math.Lemmas.modulo_division_lemma>


; <Skipped />


; <Start encoding FStar.Math.Lemmas.modulo_modulo_lemma>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.Math.Lemmas.modulo_modulo_lemma (Term Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.Math.Lemmas.modulo_modulo_lemma@tok () Term)

; </end encoding FStar.Math.Lemmas.modulo_modulo_lemma>


; <Skipped />


; <Start encoding FStar.Math.Lemmas.pow2_multiplication_division_lemma_1>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.Math.Lemmas.pow2_multiplication_division_lemma_1 (Term Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.Math.Lemmas.pow2_multiplication_division_lemma_1@tok () Term)

; </end encoding FStar.Math.Lemmas.pow2_multiplication_division_lemma_1>


; <Start encoding FStar.Math.Lemmas.pow2_multiplication_division_lemma_2>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.Math.Lemmas.pow2_multiplication_division_lemma_2 (Term Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.Math.Lemmas.pow2_multiplication_division_lemma_2@tok () Term)

; </end encoding FStar.Math.Lemmas.pow2_multiplication_division_lemma_2>


; <Start encoding FStar.Math.Lemmas.pow2_multiplication_modulo_lemma_1>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.Math.Lemmas.pow2_multiplication_modulo_lemma_1 (Term Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.Math.Lemmas.pow2_multiplication_modulo_lemma_1@tok () Term)

; </end encoding FStar.Math.Lemmas.pow2_multiplication_modulo_lemma_1>


; <Skipped />


; <Start encoding FStar.Math.Lemmas.pow2_multiplication_modulo_lemma_2>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.Math.Lemmas.pow2_multiplication_modulo_lemma_2 (Term Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.Math.Lemmas.pow2_multiplication_modulo_lemma_2@tok () Term)

; </end encoding FStar.Math.Lemmas.pow2_multiplication_modulo_lemma_2>


; <Skipped />


; <Start encoding FStar.Math.Lemmas.pow2_modulo_division_lemma_1>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.Math.Lemmas.pow2_modulo_division_lemma_1 (Term Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.Math.Lemmas.pow2_modulo_division_lemma_1@tok () Term)

; </end encoding FStar.Math.Lemmas.pow2_modulo_division_lemma_1>


; <Start encoding FStar.Math.Lemmas.pow2_modulo_division_lemma_2>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.Math.Lemmas.pow2_modulo_division_lemma_2 (Term Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.Math.Lemmas.pow2_modulo_division_lemma_2@tok () Term)

; </end encoding FStar.Math.Lemmas.pow2_modulo_division_lemma_2>


; <Start encoding FStar.Math.Lemmas.pow2_modulo_modulo_lemma_1>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.Math.Lemmas.pow2_modulo_modulo_lemma_1 (Term Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.Math.Lemmas.pow2_modulo_modulo_lemma_1@tok () Term)

; </end encoding FStar.Math.Lemmas.pow2_modulo_modulo_lemma_1>


; <Start encoding FStar.Math.Lemmas.pow2_modulo_modulo_lemma_2>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.Math.Lemmas.pow2_modulo_modulo_lemma_2 (Term Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.Math.Lemmas.pow2_modulo_modulo_lemma_2@tok () Term)

; </end encoding FStar.Math.Lemmas.pow2_modulo_modulo_lemma_2>


; <Start encoding FStar.Math.Lemmas.modulo_add>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.Math.Lemmas.modulo_add (Term Term Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.Math.Lemmas.modulo_add@tok () Term)

; </end encoding FStar.Math.Lemmas.modulo_add>


; <Start encoding FStar.Math.Lemmas.lemma_mod_twice>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.Math.Lemmas.lemma_mod_twice (Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.Math.Lemmas.lemma_mod_twice@tok () Term)

; </end encoding FStar.Math.Lemmas.lemma_mod_twice>


; <Start encoding FStar.Math.Lemmas.modulo_sub>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.Math.Lemmas.modulo_sub (Term Term Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.Math.Lemmas.modulo_sub@tok () Term)

; </end encoding FStar.Math.Lemmas.modulo_sub>


; <Start encoding FStar.Math.Lemmas.lemma_mod_plus_injective>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.Math.Lemmas.lemma_mod_plus_injective (Term Term Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.Math.Lemmas.lemma_mod_plus_injective@tok () Term)

; </end encoding FStar.Math.Lemmas.lemma_mod_plus_injective>


; UNSAT CORE: @MaxFuel_assumption, @MaxIFuel_assumption, @fuel_correspondence_Prims.pow2.fuel_instrumented, @query, constructor_distinct_Lib.IntTypes.S16, constructor_distinct_Lib.IntTypes.S32, constructor_distinct_Lib.IntTypes.SEC, equality_tok_Lib.IntTypes.S16@tok, equality_tok_Lib.IntTypes.S32@tok, equality_tok_Lib.IntTypes.SEC@tok, equation_Lib.IntTypes.bits, equation_Lib.IntTypes.range, equation_Lib.IntTypes.signed, equation_Lib.IntTypes.unsigned, equation_Lib.IntTypes.v, equation_Prims.nat, equation_Prims.pos, equation_Spec.Kyber2.Params.params_q, int_inversion, int_typing, lemma_FStar.UInt.pow2_values, primitive_Prims.op_Addition, primitive_Prims.op_Division, primitive_Prims.op_LessThanOrEqual, primitive_Prims.op_Minus, primitive_Prims.op_Multiply, primitive_Prims.op_Subtraction, projection_inverse_BoxBool_proj_0, projection_inverse_BoxInt_proj_0, refinement_interpretation_Tm_refine_2b320913041b873fce938dd17eebb3e2, refinement_interpretation_Tm_refine_542f9d4f129664613f2483a6c88bc7c2, refinement_interpretation_Tm_refine_774ba3f728d91ead8ef40be66c9802e5, refinement_interpretation_Tm_refine_83845a86f2550cdf941eeb1d9b59602b, refinement_interpretation_Tm_refine_9d3fd79fd314167f1a9c213a188da3ec, refinement_interpretation_Tm_refine_b2401a8cabe2f9a01538f32548fa9f6c, typing_Lib.IntTypes.mk_int, typing_Prims.pow2, typing_tok_Lib.IntTypes.S32@tok, typing_tok_Lib.IntTypes.SEC@tok

;;; End module FStar.Math.Lemmas (482 decls; total size 43633)

;;; Start module FStar.BitVector

; <Start encoding FStar.BitVector.bv_t>

(declare-fun FStar.BitVector.bv_t (Term) Term)
(declare-fun Tm_arrow_9974df5c311cfcfa7100bc7bef095e1e () Term)
(declare-fun FStar.BitVector.bv_t@tok () Term)
(declare-fun Tm_refine_e2d5d62a90ceed8a6faf9d20615f4e1e (Term) Term)

; </end encoding FStar.BitVector.bv_t>


; <Start encoding FStar.BitVector.zero_vec>

(declare-fun FStar.BitVector.zero_vec (Term) Term)
(declare-fun Tm_arrow_b6d52a9c4babaef5c45b062eb8723782 () Term)
(declare-fun FStar.BitVector.zero_vec@tok () Term)

; </end encoding FStar.BitVector.zero_vec>


; <Start encoding FStar.BitVector.elem_vec>


(declare-fun FStar.BitVector.elem_vec (Term Term) Term)

(declare-fun Tm_arrow_6880b3a4da9e8c38f1dbaa400eb50d7d () Term)
(declare-fun FStar.BitVector.elem_vec@tok () Term)


; </end encoding FStar.BitVector.elem_vec>


; <Start encoding FStar.BitVector.ones_vec>

(declare-fun FStar.BitVector.ones_vec (Term) Term)

(declare-fun FStar.BitVector.ones_vec@tok () Term)

; </end encoding FStar.BitVector.ones_vec>


; <Start encoding FStar.BitVector.logand_vec>

;;;;;;;;;;;;;;;;Fuel-instrumented function name
(declare-fun FStar.BitVector.logand_vec.fuel_instrumented (Fuel Term Term Term) Term)
;;;;;;;;;;;;;;;;Token for fuel-instrumented partial applications
(declare-fun FStar.BitVector.logand_vec.fuel_instrumented_token () Term)
(declare-fun FStar.BitVector.logand_vec (Term Term Term) Term)
(declare-fun FStar.BitVector.logand_vec@tok () Term)
(declare-fun Tm_arrow_d5001f682a0789c7aa8e67d06058b034 () Term)
;;;;;;;;;;;;;;;;Fuel irrelevance
;;; Fact-ids: Name FStar.BitVector.logand_vec; Namespace FStar.BitVector
(assert (! 
;; def=FStar.BitVector.fst(34,8-34,18); use=FStar.BitVector.fst(34,8-34,18)
(forall ((@u0 Fuel) (@x1 Term) (@x2 Term) (@x3 Term))
 (! (= (FStar.BitVector.logand_vec.fuel_instrumented (SFuel @u0)
@x1
@x2
@x3)
(FStar.BitVector.logand_vec.fuel_instrumented ZFuel
@x1
@x2
@x3))
 

:pattern ((FStar.BitVector.logand_vec.fuel_instrumented (SFuel @u0)
@x1
@x2
@x3))
:qid @fuel_irrelevance_FStar.BitVector.logand_vec.fuel_instrumented))

:named @fuel_irrelevance_FStar.BitVector.logand_vec.fuel_instrumented))
;;;;;;;;;;;;;;;;Correspondence of recursive function to instrumented version
;;; Fact-ids: Name FStar.BitVector.logand_vec; Namespace FStar.BitVector
(assert (! 
;; def=FStar.BitVector.fst(34,8-34,18); use=FStar.BitVector.fst(34,8-34,18)
(forall ((@x0 Term) (@x1 Term) (@x2 Term))
 (! (= (FStar.BitVector.logand_vec @x0
@x1
@x2)
(FStar.BitVector.logand_vec.fuel_instrumented MaxFuel
@x0
@x1
@x2))
 

:pattern ((FStar.BitVector.logand_vec @x0
@x1
@x2))
:qid @fuel_correspondence_FStar.BitVector.logand_vec.fuel_instrumented))

:named @fuel_correspondence_FStar.BitVector.logand_vec.fuel_instrumented))

; </end encoding FStar.BitVector.logand_vec>


; <Start encoding FStar.BitVector.logxor_vec>

;;;;;;;;;;;;;;;;Fuel-instrumented function name
(declare-fun FStar.BitVector.logxor_vec.fuel_instrumented (Fuel Term Term Term) Term)
;;;;;;;;;;;;;;;;Token for fuel-instrumented partial applications
(declare-fun FStar.BitVector.logxor_vec.fuel_instrumented_token () Term)
(declare-fun FStar.BitVector.logxor_vec (Term Term Term) Term)
(declare-fun FStar.BitVector.logxor_vec@tok () Term)

;;;;;;;;;;;;;;;;Fuel irrelevance
;;; Fact-ids: Name FStar.BitVector.logxor_vec; Namespace FStar.BitVector
(assert (! 
;; def=FStar.BitVector.fst(39,8-39,18); use=FStar.BitVector.fst(39,8-39,18)
(forall ((@u0 Fuel) (@x1 Term) (@x2 Term) (@x3 Term))
 (! (= (FStar.BitVector.logxor_vec.fuel_instrumented (SFuel @u0)
@x1
@x2
@x3)
(FStar.BitVector.logxor_vec.fuel_instrumented ZFuel
@x1
@x2
@x3))
 

:pattern ((FStar.BitVector.logxor_vec.fuel_instrumented (SFuel @u0)
@x1
@x2
@x3))
:qid @fuel_irrelevance_FStar.BitVector.logxor_vec.fuel_instrumented))

:named @fuel_irrelevance_FStar.BitVector.logxor_vec.fuel_instrumented))
;;;;;;;;;;;;;;;;Correspondence of recursive function to instrumented version
;;; Fact-ids: Name FStar.BitVector.logxor_vec; Namespace FStar.BitVector
(assert (! 
;; def=FStar.BitVector.fst(39,8-39,18); use=FStar.BitVector.fst(39,8-39,18)
(forall ((@x0 Term) (@x1 Term) (@x2 Term))
 (! (= (FStar.BitVector.logxor_vec @x0
@x1
@x2)
(FStar.BitVector.logxor_vec.fuel_instrumented MaxFuel
@x0
@x1
@x2))
 

:pattern ((FStar.BitVector.logxor_vec @x0
@x1
@x2))
:qid @fuel_correspondence_FStar.BitVector.logxor_vec.fuel_instrumented))

:named @fuel_correspondence_FStar.BitVector.logxor_vec.fuel_instrumented))

; </end encoding FStar.BitVector.logxor_vec>


; <Start encoding FStar.BitVector.logor_vec>

;;;;;;;;;;;;;;;;Fuel-instrumented function name
(declare-fun FStar.BitVector.logor_vec.fuel_instrumented (Fuel Term Term Term) Term)
;;;;;;;;;;;;;;;;Token for fuel-instrumented partial applications
(declare-fun FStar.BitVector.logor_vec.fuel_instrumented_token () Term)
(declare-fun FStar.BitVector.logor_vec (Term Term Term) Term)
(declare-fun FStar.BitVector.logor_vec@tok () Term)

;;;;;;;;;;;;;;;;Fuel irrelevance
;;; Fact-ids: Name FStar.BitVector.logor_vec; Namespace FStar.BitVector
(assert (! 
;; def=FStar.BitVector.fst(44,8-44,17); use=FStar.BitVector.fst(44,8-44,17)
(forall ((@u0 Fuel) (@x1 Term) (@x2 Term) (@x3 Term))
 (! (= (FStar.BitVector.logor_vec.fuel_instrumented (SFuel @u0)
@x1
@x2
@x3)
(FStar.BitVector.logor_vec.fuel_instrumented ZFuel
@x1
@x2
@x3))
 

:pattern ((FStar.BitVector.logor_vec.fuel_instrumented (SFuel @u0)
@x1
@x2
@x3))
:qid @fuel_irrelevance_FStar.BitVector.logor_vec.fuel_instrumented))

:named @fuel_irrelevance_FStar.BitVector.logor_vec.fuel_instrumented))
;;;;;;;;;;;;;;;;Correspondence of recursive function to instrumented version
;;; Fact-ids: Name FStar.BitVector.logor_vec; Namespace FStar.BitVector
(assert (! 
;; def=FStar.BitVector.fst(44,8-44,17); use=FStar.BitVector.fst(44,8-44,17)
(forall ((@x0 Term) (@x1 Term) (@x2 Term))
 (! (= (FStar.BitVector.logor_vec @x0
@x1
@x2)
(FStar.BitVector.logor_vec.fuel_instrumented MaxFuel
@x0
@x1
@x2))
 

:pattern ((FStar.BitVector.logor_vec @x0
@x1
@x2))
:qid @fuel_correspondence_FStar.BitVector.logor_vec.fuel_instrumented))

:named @fuel_correspondence_FStar.BitVector.logor_vec.fuel_instrumented))

; </end encoding FStar.BitVector.logor_vec>


; <Start encoding FStar.BitVector.lognot_vec>

;;;;;;;;;;;;;;;;Fuel-instrumented function name
(declare-fun FStar.BitVector.lognot_vec.fuel_instrumented (Fuel Term Term) Term)
;;;;;;;;;;;;;;;;Token for fuel-instrumented partial applications
(declare-fun FStar.BitVector.lognot_vec.fuel_instrumented_token () Term)
(declare-fun FStar.BitVector.lognot_vec (Term Term) Term)
(declare-fun FStar.BitVector.lognot_vec@tok () Term)
(declare-fun Tm_arrow_190e27813ba14c0d36577dc3d47778da () Term)
;;;;;;;;;;;;;;;;Fuel irrelevance
;;; Fact-ids: Name FStar.BitVector.lognot_vec; Namespace FStar.BitVector
(assert (! 
;; def=FStar.BitVector.fst(49,8-49,18); use=FStar.BitVector.fst(49,8-49,18)
(forall ((@u0 Fuel) (@x1 Term) (@x2 Term))
 (! (= (FStar.BitVector.lognot_vec.fuel_instrumented (SFuel @u0)
@x1
@x2)
(FStar.BitVector.lognot_vec.fuel_instrumented ZFuel
@x1
@x2))
 

:pattern ((FStar.BitVector.lognot_vec.fuel_instrumented (SFuel @u0)
@x1
@x2))
:qid @fuel_irrelevance_FStar.BitVector.lognot_vec.fuel_instrumented))

:named @fuel_irrelevance_FStar.BitVector.lognot_vec.fuel_instrumented))
;;;;;;;;;;;;;;;;Correspondence of recursive function to instrumented version
;;; Fact-ids: Name FStar.BitVector.lognot_vec; Namespace FStar.BitVector
(assert (! 
;; def=FStar.BitVector.fst(49,8-49,18); use=FStar.BitVector.fst(49,8-49,18)
(forall ((@x0 Term) (@x1 Term))
 (! (= (FStar.BitVector.lognot_vec @x0
@x1)
(FStar.BitVector.lognot_vec.fuel_instrumented MaxFuel
@x0
@x1))
 

:pattern ((FStar.BitVector.lognot_vec @x0
@x1))
:qid @fuel_correspondence_FStar.BitVector.lognot_vec.fuel_instrumented))

:named @fuel_correspondence_FStar.BitVector.lognot_vec.fuel_instrumented))

; </end encoding FStar.BitVector.lognot_vec>


; <Start encoding FStar.BitVector.logand_vec_definition>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.BitVector.logand_vec_definition (Term Term Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.BitVector.logand_vec_definition@tok () Term)


; </end encoding FStar.BitVector.logand_vec_definition>


; <Start encoding FStar.BitVector.logxor_vec_definition>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.BitVector.logxor_vec_definition (Term Term Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.BitVector.logxor_vec_definition@tok () Term)


; </end encoding FStar.BitVector.logxor_vec_definition>


; <Start encoding FStar.BitVector.logor_vec_definition>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.BitVector.logor_vec_definition (Term Term Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.BitVector.logor_vec_definition@tok () Term)


; </end encoding FStar.BitVector.logor_vec_definition>


; <Start encoding FStar.BitVector.lognot_vec_definition>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.BitVector.lognot_vec_definition (Term Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.BitVector.lognot_vec_definition@tok () Term)


; </end encoding FStar.BitVector.lognot_vec_definition>


; <Start encoding FStar.BitVector.lemma_xor_bounded>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.BitVector.lemma_xor_bounded (Term Term Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.BitVector.lemma_xor_bounded@tok () Term)

; </end encoding FStar.BitVector.lemma_xor_bounded>


; <Start encoding FStar.BitVector.is_subset_vec>

(declare-fun FStar.BitVector.is_subset_vec (Term Term Term) Term)
(declare-fun Tm_arrow_b51a0c80adeae3f31b1215853bb34fe1 () Term)
(declare-fun FStar.BitVector.is_subset_vec@tok () Term)

; </end encoding FStar.BitVector.is_subset_vec>


; <Start encoding FStar.BitVector.is_superset_vec>

(declare-fun FStar.BitVector.is_superset_vec (Term Term Term) Term)

(declare-fun FStar.BitVector.is_superset_vec@tok () Term)

; </end encoding FStar.BitVector.is_superset_vec>


; <Start encoding FStar.BitVector.lemma_slice_subset_vec>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.BitVector.lemma_slice_subset_vec (Term Term Term Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.BitVector.lemma_slice_subset_vec@tok () Term)

; </end encoding FStar.BitVector.lemma_slice_subset_vec>


; <Start encoding FStar.BitVector.lemma_slice_superset_vec>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.BitVector.lemma_slice_superset_vec (Term Term Term Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.BitVector.lemma_slice_superset_vec@tok () Term)

; </end encoding FStar.BitVector.lemma_slice_superset_vec>


; <Start encoding FStar.BitVector.shift_left_vec>

(declare-fun FStar.BitVector.shift_left_vec (Term Term Term) Term)
(declare-fun Tm_arrow_ccbebd343bd3a7caba5f263c2ba5f3be () Term)
(declare-fun FStar.BitVector.shift_left_vec@tok () Term)

; </end encoding FStar.BitVector.shift_left_vec>


; <Start encoding FStar.BitVector.shift_right_vec>

(declare-fun FStar.BitVector.shift_right_vec (Term Term Term) Term)

(declare-fun FStar.BitVector.shift_right_vec@tok () Term)

; </end encoding FStar.BitVector.shift_right_vec>


; <Start encoding FStar.BitVector.shift_arithmetic_right_vec>

(declare-fun FStar.BitVector.shift_arithmetic_right_vec (Term Term Term) Term)

(declare-fun FStar.BitVector.shift_arithmetic_right_vec@tok () Term)

; </end encoding FStar.BitVector.shift_arithmetic_right_vec>


; <Start encoding FStar.BitVector.shift_left_vec_lemma_1>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.BitVector.shift_left_vec_lemma_1 (Term Term Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.BitVector.shift_left_vec_lemma_1@tok () Term)
(declare-fun Tm_refine_6ccf0869e6825997ab860bb25791c11f (Term Term) Term)

; </end encoding FStar.BitVector.shift_left_vec_lemma_1>


; <Start encoding FStar.BitVector.shift_left_vec_lemma_2>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.BitVector.shift_left_vec_lemma_2 (Term Term Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.BitVector.shift_left_vec_lemma_2@tok () Term)
(declare-fun Tm_refine_e8e1ad4b2203cd724d5b8b2dba0a5826 (Term Term) Term)

; </end encoding FStar.BitVector.shift_left_vec_lemma_2>


; <Start encoding FStar.BitVector.shift_right_vec_lemma_1>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.BitVector.shift_right_vec_lemma_1 (Term Term Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.BitVector.shift_right_vec_lemma_1@tok () Term)
(declare-fun Tm_refine_34425c23b534b8a294f8f063dd9faa4b (Term Term) Term)

; </end encoding FStar.BitVector.shift_right_vec_lemma_1>


; <Start encoding FStar.BitVector.shift_right_vec_lemma_2>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.BitVector.shift_right_vec_lemma_2 (Term Term Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.BitVector.shift_right_vec_lemma_2@tok () Term)
(declare-fun Tm_refine_c0ec47abc53a2509e744dad22ccf8191 (Term Term) Term)

; </end encoding FStar.BitVector.shift_right_vec_lemma_2>


; <Start encoding FStar.BitVector.shift_arithmetic_right_vec_lemma_1>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.BitVector.shift_arithmetic_right_vec_lemma_1 (Term Term Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.BitVector.shift_arithmetic_right_vec_lemma_1@tok () Term)


; </end encoding FStar.BitVector.shift_arithmetic_right_vec_lemma_1>


; <Start encoding FStar.BitVector.shift_arithmetic_right_vec_lemma_2>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.BitVector.shift_arithmetic_right_vec_lemma_2 (Term Term Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.BitVector.shift_arithmetic_right_vec_lemma_2@tok () Term)


; </end encoding FStar.BitVector.shift_arithmetic_right_vec_lemma_2>


; UNSAT CORE: @MaxFuel_assumption, @MaxIFuel_assumption, @fuel_correspondence_Prims.pow2.fuel_instrumented, @query, constructor_distinct_Lib.IntTypes.S16, constructor_distinct_Lib.IntTypes.S32, constructor_distinct_Lib.IntTypes.SEC, equality_tok_Lib.IntTypes.S16@tok, equality_tok_Lib.IntTypes.S32@tok, equality_tok_Lib.IntTypes.SEC@tok, equation_Lib.IntTypes.bits, equation_Lib.IntTypes.range, equation_Lib.IntTypes.signed, equation_Lib.IntTypes.unsigned, equation_Lib.IntTypes.v, equation_Prims.nat, equation_Prims.pos, equation_Spec.Kyber2.Params.params_q, int_inversion, int_typing, lemma_FStar.UInt.pow2_values, primitive_Prims.op_Addition, primitive_Prims.op_Division, primitive_Prims.op_LessThanOrEqual, primitive_Prims.op_Minus, primitive_Prims.op_Multiply, primitive_Prims.op_Subtraction, projection_inverse_BoxBool_proj_0, projection_inverse_BoxInt_proj_0, refinement_interpretation_Tm_refine_2b320913041b873fce938dd17eebb3e2, refinement_interpretation_Tm_refine_542f9d4f129664613f2483a6c88bc7c2, refinement_interpretation_Tm_refine_774ba3f728d91ead8ef40be66c9802e5, refinement_interpretation_Tm_refine_83845a86f2550cdf941eeb1d9b59602b, refinement_interpretation_Tm_refine_9d3fd79fd314167f1a9c213a188da3ec, refinement_interpretation_Tm_refine_b2401a8cabe2f9a01538f32548fa9f6c, typing_Lib.IntTypes.mk_int, typing_Prims.pow2, typing_tok_Lib.IntTypes.S32@tok, typing_tok_Lib.IntTypes.SEC@tok

;;; End module FStar.BitVector (148 decls; total size 16000)

;;; Start module FStar.UInt

; <Skipped />


; <Start encoding FStar.UInt.pow2_values>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.UInt.pow2_values (Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.UInt.pow2_values@tok () Term)
;;;;;;;;;;;;;;;;Lemma: FStar.UInt.pow2_values
;;; Fact-ids: Name FStar.UInt.pow2_values; Namespace FStar.UInt
(assert (! (forall ((@x0 Term))
 (! (implies (HasType @x0
Prims.nat)
(let ((@lb1 @x0))
(ite (= @lb1
(BoxInt 0))

;; def=FStar.UInt.fst(30,11-30,14); use=FStar.UInt.fst(41,4-41,15)
(= (Prims.pow2.fuel_instrumented ZFuel
@x0)
(BoxInt 1))

(ite (= @lb1
(BoxInt 1))

;; def=FStar.UInt.fst(31,11-31,14); use=FStar.UInt.fst(41,4-41,15)
(= (Prims.pow2.fuel_instrumented ZFuel
@x0)
(BoxInt 2))

(ite (= @lb1
(BoxInt 8))

;; def=FStar.UInt.fst(32,11-32,16); use=FStar.UInt.fst(41,4-41,15)
(= (Prims.pow2.fuel_instrumented ZFuel
@x0)
(BoxInt 256))

(ite (= @lb1
(BoxInt 16))

;; def=FStar.UInt.fst(33,11-33,18); use=FStar.UInt.fst(41,4-41,15)
(= (Prims.pow2.fuel_instrumented ZFuel
@x0)
(BoxInt 65536))

(ite (= @lb1
(BoxInt 31))

;; def=FStar.UInt.fst(34,11-34,23); use=FStar.UInt.fst(41,4-41,15)
(= (Prims.pow2.fuel_instrumented ZFuel
@x0)
(BoxInt 2147483648))

(ite (= @lb1
(BoxInt 32))

;; def=FStar.UInt.fst(35,11-35,23); use=FStar.UInt.fst(41,4-41,15)
(= (Prims.pow2.fuel_instrumented ZFuel
@x0)
(BoxInt 4294967296))

(ite (= @lb1
(BoxInt 63))

;; def=FStar.UInt.fst(36,11-36,32); use=FStar.UInt.fst(41,4-41,15)
(= (Prims.pow2.fuel_instrumented ZFuel
@x0)
(BoxInt 9223372036854775808))

(ite (= @lb1
(BoxInt 64))

;; def=FStar.UInt.fst(37,11-37,33); use=FStar.UInt.fst(41,4-41,15)
(= (Prims.pow2.fuel_instrumented ZFuel
@x0)
(BoxInt 18446744073709551616))

(implies (= @lb1
(BoxInt 128))

;; def=FStar.UInt.fst(38,12-38,49); use=FStar.UInt.fst(41,4-41,15)
(= (Prims.pow2.fuel_instrumented ZFuel
@x0)
(BoxInt 340282366920938463463374607431768211456))
)))))))))))
 

:pattern ((Prims.pow2.fuel_instrumented ZFuel
@x0))
:qid lemma_FStar.UInt.pow2_values))
:named lemma_FStar.UInt.pow2_values))

; </end encoding FStar.UInt.pow2_values>


; <Start encoding FStar.UInt.max_int>

(declare-fun FStar.UInt.max_int (Term) Term)
(declare-fun Tm_arrow_fc34ca66de2f262c06145b17fb7ed6cb () Term)
(declare-fun FStar.UInt.max_int@tok () Term)

; </end encoding FStar.UInt.max_int>


; <Start encoding FStar.UInt.min_int>

(declare-fun FStar.UInt.min_int (Term) Term)

(declare-fun FStar.UInt.min_int@tok () Term)

; </end encoding FStar.UInt.min_int>


; <Start encoding FStar.UInt.fits>

(declare-fun FStar.UInt.fits (Term Term) Term)
(declare-fun Tm_arrow_dea48782e508c14fa98dcf9716548804 () Term)
(declare-fun FStar.UInt.fits@tok () Term)

; </end encoding FStar.UInt.fits>


; <Start encoding FStar.UInt.size>

(declare-fun FStar.UInt.size (Term Term) Term)
(declare-fun Tm_arrow_f4ec8f8bfe492e31741a15356024bbaa () Term)
(declare-fun FStar.UInt.size@tok () Term)

; </end encoding FStar.UInt.size>


; <Start encoding FStar.UInt.uint_t>

(declare-fun FStar.UInt.uint_t (Term) Term)

(declare-fun FStar.UInt.uint_t@tok () Term)
(declare-fun Tm_refine_f13070840248fced9d9d60d77bdae3ec (Term) Term)

; </end encoding FStar.UInt.uint_t>


; <Start encoding FStar.UInt.zero>

(declare-fun FStar.UInt.zero (Term) Term)
(declare-fun Tm_arrow_f1dd811328ea3b27fc410fa0f52880f7 () Term)
(declare-fun FStar.UInt.zero@tok () Term)

; </end encoding FStar.UInt.zero>


; <Skipped />


; <Start encoding FStar.UInt.pow2_n>


(declare-fun FStar.UInt.pow2_n (Term Term) Term)

(declare-fun Tm_arrow_8d41edd1e7b665db26512e6c6d9ece64 () Term)
(declare-fun FStar.UInt.pow2_n@tok () Term)


; </end encoding FStar.UInt.pow2_n>


; <Start encoding FStar.UInt.one>

(declare-fun FStar.UInt.one (Term) Term)
(declare-fun Tm_arrow_89d370fa478cfd1f85a8759662ce0390 () Term)
(declare-fun FStar.UInt.one@tok () Term)

; </end encoding FStar.UInt.one>


; <Skipped />


; <Start encoding FStar.UInt.ones>

(declare-fun FStar.UInt.ones (Term) Term)

(declare-fun FStar.UInt.ones@tok () Term)

; </end encoding FStar.UInt.ones>


; <Start encoding FStar.UInt.incr>

(declare-fun FStar.UInt.incr (Term Term) Term)
(declare-fun Tm_refine_22e8629663f0cb1c9de86e57e73778e3 (Term) Term)
(declare-fun Tm_arrow_e8e04e4a1022a7343e76760b76915c9e () Term)
(declare-fun FStar.UInt.incr@tok () Term)


; </end encoding FStar.UInt.incr>


; <Start encoding FStar.UInt.decr>

(declare-fun FStar.UInt.decr (Term Term) Term)

(declare-fun Tm_arrow_2a167fb2d2f3f00bff7b73f048db0e83 () Term)
(declare-fun FStar.UInt.decr@tok () Term)


; </end encoding FStar.UInt.decr>


; <Start encoding FStar.UInt.incr_underspec>

(declare-fun FStar.UInt.incr_underspec (Term Term) Term)
(declare-fun Tm_refine_6a367e92d5b1ca10009a43bd430dd796 (Term Term) Term)
(declare-fun Tm_arrow_fb114bd2e9239af1296268eb30490ff7 () Term)
(declare-fun FStar.UInt.incr_underspec@tok () Term)


; </end encoding FStar.UInt.incr_underspec>


; <Start encoding FStar.UInt.decr_underspec>

(declare-fun FStar.UInt.decr_underspec (Term Term) Term)
(declare-fun Tm_refine_fa3c796c533e86dc9f3e3ffc647718f6 (Term Term) Term)
(declare-fun Tm_arrow_f1853f30408c6d0beb7795897a3ab5bc () Term)
(declare-fun FStar.UInt.decr_underspec@tok () Term)


; </end encoding FStar.UInt.decr_underspec>


; <Start encoding FStar.UInt.incr_mod>

(declare-fun FStar.UInt.incr_mod (Term Term) Term)
(declare-fun Tm_arrow_a565732dbe0b43ae2274b1f24341f11b () Term)
(declare-fun FStar.UInt.incr_mod@tok () Term)

; </end encoding FStar.UInt.incr_mod>


; <Start encoding FStar.UInt.decr_mod>

(declare-fun FStar.UInt.decr_mod (Term Term) Term)

(declare-fun FStar.UInt.decr_mod@tok () Term)

; </end encoding FStar.UInt.decr_mod>


; <Start encoding FStar.UInt.add>

(declare-fun FStar.UInt.add (Term Term Term) Term)

(declare-fun Tm_arrow_ea9f73d61c207ec4508af75e87c5ca13 () Term)
(declare-fun FStar.UInt.add@tok () Term)


; </end encoding FStar.UInt.add>


; <Start encoding FStar.UInt.add_underspec>

(declare-fun FStar.UInt.add_underspec (Term Term Term) Term)
(declare-fun Tm_refine_c7a9b50c1b5983f8171c03368a208e31 (Term Term Term) Term)
(declare-fun Tm_arrow_880847ba34dd402fb6567384684864a6 () Term)
(declare-fun FStar.UInt.add_underspec@tok () Term)


; </end encoding FStar.UInt.add_underspec>


; <Start encoding FStar.UInt.add_mod>

(declare-fun FStar.UInt.add_mod (Term Term Term) Term)
(declare-fun Tm_arrow_2f3c6a962eb1cbbfd959311c0f20b277 () Term)
(declare-fun FStar.UInt.add_mod@tok () Term)

; </end encoding FStar.UInt.add_mod>


; <Start encoding FStar.UInt.sub>

(declare-fun FStar.UInt.sub (Term Term Term) Term)

(declare-fun Tm_arrow_974b47e4388c1a4055fe210bb6a11687 () Term)
(declare-fun FStar.UInt.sub@tok () Term)


; </end encoding FStar.UInt.sub>


; <Start encoding FStar.UInt.sub_underspec>

(declare-fun FStar.UInt.sub_underspec (Term Term Term) Term)
(declare-fun Tm_refine_109ae46bb20ad559af297346ec64ae4e (Term Term Term) Term)
(declare-fun Tm_arrow_1479a03f646b965be1bfedb2ee360f95 () Term)
(declare-fun FStar.UInt.sub_underspec@tok () Term)


; </end encoding FStar.UInt.sub_underspec>


; <Start encoding FStar.UInt.sub_mod>

(declare-fun FStar.UInt.sub_mod (Term Term Term) Term)

(declare-fun FStar.UInt.sub_mod@tok () Term)

; </end encoding FStar.UInt.sub_mod>


; <Start encoding FStar.UInt.mul>

(declare-fun FStar.UInt.mul (Term Term Term) Term)

(declare-fun Tm_arrow_45e02637bbbba15e6760300e4a62b58d () Term)
(declare-fun FStar.UInt.mul@tok () Term)


; </end encoding FStar.UInt.mul>


; <Start encoding FStar.UInt.mul_underspec>

(declare-fun FStar.UInt.mul_underspec (Term Term Term) Term)
(declare-fun Tm_refine_ea207e5cce50229e615af011837e59a5 (Term Term Term) Term)
(declare-fun Tm_arrow_1f5fca1fff06689d84a49261819dc580 () Term)
(declare-fun FStar.UInt.mul_underspec@tok () Term)


; </end encoding FStar.UInt.mul_underspec>


; <Start encoding FStar.UInt.mul_mod>

(declare-fun FStar.UInt.mul_mod (Term Term Term) Term)

(declare-fun FStar.UInt.mul_mod@tok () Term)

; </end encoding FStar.UInt.mul_mod>


; <Start encoding FStar.UInt.lt_square_div_lt>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.UInt.lt_square_div_lt (Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.UInt.lt_square_div_lt@tok () Term)

; </end encoding FStar.UInt.lt_square_div_lt>


; <Start encoding FStar.UInt.mul_div>

(declare-fun FStar.UInt.mul_div (Term Term Term) Term)

(declare-fun FStar.UInt.mul_div@tok () Term)

; </end encoding FStar.UInt.mul_div>


; <Start encoding FStar.UInt.div>

(declare-fun Tm_refine_0722e9115d2a1be8d90527397d01011c (Term) Term)
(declare-fun FStar.UInt.div (Term Term Term) Term)

(declare-fun Tm_refine_e49d79feeb1e96b29b0f01b06f8dac23 (Term Term Term) Term)
(declare-fun Tm_arrow_6ebc7a9e6ff34015952a4168421980bf () Term)
(declare-fun FStar.UInt.div@tok () Term)



; </end encoding FStar.UInt.div>


; <Start encoding FStar.UInt.div_underspec>


(declare-fun FStar.UInt.div_underspec (Term Term Term) Term)

(declare-fun Tm_refine_fafbb762e9b0100ba27aa174122ddaa3 (Term Term Term) Term)
(declare-fun Tm_arrow_ed1485a952a27dc4770fb0182ab26e79 () Term)
(declare-fun FStar.UInt.div_underspec@tok () Term)


; </end encoding FStar.UInt.div_underspec>


; <Start encoding FStar.UInt.div_size>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.UInt.div_size (Term Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.UInt.div_size@tok () Term)

; </end encoding FStar.UInt.div_size>


; <Start encoding FStar.UInt.udiv>


(declare-fun FStar.UInt.udiv (Term Term Term) Term)


(declare-fun Tm_arrow_2b6a409bd2eeb88753b2b6fe89b0d0a9 () Term)
(declare-fun FStar.UInt.udiv@tok () Term)



; </end encoding FStar.UInt.udiv>


; <Start encoding FStar.UInt.mod>


(declare-fun FStar.UInt.mod (Term Term Term) Term)

(declare-fun Tm_arrow_6ae50616ce0b08fd950ce0be5e711193 () Term)
(declare-fun FStar.UInt.mod@tok () Term)


; </end encoding FStar.UInt.mod>


; <Start encoding FStar.UInt.eq>

(declare-fun FStar.UInt.eq (Term Term Term) Term)
(declare-fun Tm_arrow_ed25d9271888f66e143c5c59e11fb3a9 () Term)
(declare-fun FStar.UInt.eq@tok () Term)

; </end encoding FStar.UInt.eq>


; <Start encoding FStar.UInt.gt>

(declare-fun FStar.UInt.gt (Term Term Term) Term)

(declare-fun FStar.UInt.gt@tok () Term)

; </end encoding FStar.UInt.gt>


; <Start encoding FStar.UInt.gte>

(declare-fun FStar.UInt.gte (Term Term Term) Term)

(declare-fun FStar.UInt.gte@tok () Term)

; </end encoding FStar.UInt.gte>


; <Start encoding FStar.UInt.lt>

(declare-fun FStar.UInt.lt (Term Term Term) Term)

(declare-fun FStar.UInt.lt@tok () Term)

; </end encoding FStar.UInt.lt>


; <Start encoding FStar.UInt.lte>

(declare-fun FStar.UInt.lte (Term Term Term) Term)

(declare-fun FStar.UInt.lte@tok () Term)

; </end encoding FStar.UInt.lte>


; <Skipped />


; <Start encoding FStar.UInt.to_uint_t>

(declare-fun FStar.UInt.to_uint_t (Term Term) Term)
(declare-fun Tm_arrow_d5257ef463a03617bca88873b50f4e96 () Term)
(declare-fun FStar.UInt.to_uint_t@tok () Term)

; </end encoding FStar.UInt.to_uint_t>


; <Start encoding FStar.UInt.to_vec>

;;;;;;;;;;;;;;;;Fuel-instrumented function name
(declare-fun FStar.UInt.to_vec.fuel_instrumented (Fuel Term Term) Term)
;;;;;;;;;;;;;;;;Token for fuel-instrumented partial applications
(declare-fun FStar.UInt.to_vec.fuel_instrumented_token () Term)
(declare-fun FStar.UInt.to_vec (Term Term) Term)
(declare-fun FStar.UInt.to_vec@tok () Term)
(declare-fun Tm_arrow_50c9ac04c4da2f9a3a1512bf3cfd180e () Term)
;;;;;;;;;;;;;;;;Fuel irrelevance
;;; Fact-ids: Name FStar.UInt.to_vec; Namespace FStar.UInt
(assert (! 
;; def=FStar.UInt.fst(231,8-231,14); use=FStar.UInt.fst(231,8-231,14)
(forall ((@u0 Fuel) (@x1 Term) (@x2 Term))
 (! (= (FStar.UInt.to_vec.fuel_instrumented (SFuel @u0)
@x1
@x2)
(FStar.UInt.to_vec.fuel_instrumented ZFuel
@x1
@x2))
 

:pattern ((FStar.UInt.to_vec.fuel_instrumented (SFuel @u0)
@x1
@x2))
:qid @fuel_irrelevance_FStar.UInt.to_vec.fuel_instrumented))

:named @fuel_irrelevance_FStar.UInt.to_vec.fuel_instrumented))
;;;;;;;;;;;;;;;;Correspondence of recursive function to instrumented version
;;; Fact-ids: Name FStar.UInt.to_vec; Namespace FStar.UInt
(assert (! 
;; def=FStar.UInt.fst(231,8-231,14); use=FStar.UInt.fst(231,8-231,14)
(forall ((@x0 Term) (@x1 Term))
 (! (= (FStar.UInt.to_vec @x0
@x1)
(FStar.UInt.to_vec.fuel_instrumented MaxFuel
@x0
@x1))
 

:pattern ((FStar.UInt.to_vec @x0
@x1))
:qid @fuel_correspondence_FStar.UInt.to_vec.fuel_instrumented))

:named @fuel_correspondence_FStar.UInt.to_vec.fuel_instrumented))

; </end encoding FStar.UInt.to_vec>


; <Start encoding FStar.UInt.from_vec>

;;;;;;;;;;;;;;;;Fuel-instrumented function name
(declare-fun FStar.UInt.from_vec.fuel_instrumented (Fuel Term Term) Term)
;;;;;;;;;;;;;;;;Token for fuel-instrumented partial applications
(declare-fun FStar.UInt.from_vec.fuel_instrumented_token () Term)
(declare-fun FStar.UInt.from_vec (Term Term) Term)
(declare-fun FStar.UInt.from_vec@tok () Term)
(declare-fun Tm_arrow_3a21f80bb386ebae30b30ec5363d47ef () Term)
;;;;;;;;;;;;;;;;Fuel irrelevance
;;; Fact-ids: Name FStar.UInt.from_vec; Namespace FStar.UInt
(assert (! 
;; def=FStar.UInt.fst(236,8-236,16); use=FStar.UInt.fst(236,8-236,16)
(forall ((@u0 Fuel) (@x1 Term) (@x2 Term))
 (! (= (FStar.UInt.from_vec.fuel_instrumented (SFuel @u0)
@x1
@x2)
(FStar.UInt.from_vec.fuel_instrumented ZFuel
@x1
@x2))
 

:pattern ((FStar.UInt.from_vec.fuel_instrumented (SFuel @u0)
@x1
@x2))
:qid @fuel_irrelevance_FStar.UInt.from_vec.fuel_instrumented))

:named @fuel_irrelevance_FStar.UInt.from_vec.fuel_instrumented))
;;;;;;;;;;;;;;;;Correspondence of recursive function to instrumented version
;;; Fact-ids: Name FStar.UInt.from_vec; Namespace FStar.UInt
(assert (! 
;; def=FStar.UInt.fst(236,8-236,16); use=FStar.UInt.fst(236,8-236,16)
(forall ((@x0 Term) (@x1 Term))
 (! (= (FStar.UInt.from_vec @x0
@x1)
(FStar.UInt.from_vec.fuel_instrumented MaxFuel
@x0
@x1))
 

:pattern ((FStar.UInt.from_vec @x0
@x1))
:qid @fuel_correspondence_FStar.UInt.from_vec.fuel_instrumented))

:named @fuel_correspondence_FStar.UInt.from_vec.fuel_instrumented))

; </end encoding FStar.UInt.from_vec>


; <Start encoding FStar.UInt.to_vec_lemma_1>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.UInt.to_vec_lemma_1 (Term Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.UInt.to_vec_lemma_1@tok () Term)

; </end encoding FStar.UInt.to_vec_lemma_1>


; <Start encoding FStar.UInt.to_vec_lemma_2>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.UInt.to_vec_lemma_2 (Term Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.UInt.to_vec_lemma_2@tok () Term)

; </end encoding FStar.UInt.to_vec_lemma_2>


; <Start encoding FStar.UInt.inverse_aux>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.UInt.inverse_aux (Term Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.UInt.inverse_aux@tok () Term)


; </end encoding FStar.UInt.inverse_aux>


; <Start encoding FStar.UInt.inverse_vec_lemma>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.UInt.inverse_vec_lemma (Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.UInt.inverse_vec_lemma@tok () Term)

; </end encoding FStar.UInt.inverse_vec_lemma>


; <Start encoding FStar.UInt.inverse_num_lemma>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.UInt.inverse_num_lemma (Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.UInt.inverse_num_lemma@tok () Term)

; </end encoding FStar.UInt.inverse_num_lemma>


; <Start encoding FStar.UInt.from_vec_lemma_1>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.UInt.from_vec_lemma_1 (Term Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.UInt.from_vec_lemma_1@tok () Term)

; </end encoding FStar.UInt.from_vec_lemma_1>


; <Start encoding FStar.UInt.from_vec_lemma_2>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.UInt.from_vec_lemma_2 (Term Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.UInt.from_vec_lemma_2@tok () Term)

; </end encoding FStar.UInt.from_vec_lemma_2>


; <Skipped />


; <Start encoding FStar.UInt.from_vec_aux>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.UInt.from_vec_aux (Term Term Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.UInt.from_vec_aux@tok () Term)

; </end encoding FStar.UInt.from_vec_aux>


; <Start encoding FStar.UInt.seq_slice_lemma>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.UInt.seq_slice_lemma (Term Term Term Term Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.UInt.seq_slice_lemma@tok () Term)

; </end encoding FStar.UInt.seq_slice_lemma>


; <Skipped />


; <Start encoding FStar.UInt.from_vec_propriety>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.UInt.from_vec_propriety (Term Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.UInt.from_vec_propriety@tok () Term)

; </end encoding FStar.UInt.from_vec_propriety>


; <Skipped />


; <Start encoding FStar.UInt.append_lemma>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.UInt.append_lemma (Term Term Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.UInt.append_lemma@tok () Term)

; </end encoding FStar.UInt.append_lemma>


; <Start encoding FStar.UInt.slice_left_lemma>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.UInt.slice_left_lemma (Term Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.UInt.slice_left_lemma@tok () Term)

; </end encoding FStar.UInt.slice_left_lemma>


; <Start encoding FStar.UInt.slice_right_lemma>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.UInt.slice_right_lemma (Term Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.UInt.slice_right_lemma@tok () Term)

; </end encoding FStar.UInt.slice_right_lemma>


; <Skipped />


; <Start encoding FStar.UInt.zero_to_vec_lemma>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.UInt.zero_to_vec_lemma (Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.UInt.zero_to_vec_lemma@tok () Term)


; </end encoding FStar.UInt.zero_to_vec_lemma>


; <Start encoding FStar.UInt.zero_from_vec_lemma>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.UInt.zero_from_vec_lemma (Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.UInt.zero_from_vec_lemma@tok () Term)

; </end encoding FStar.UInt.zero_from_vec_lemma>


; <Start encoding FStar.UInt.one_to_vec_lemma>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.UInt.one_to_vec_lemma (Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.UInt.one_to_vec_lemma@tok () Term)


; </end encoding FStar.UInt.one_to_vec_lemma>


; <Start encoding FStar.UInt.pow2_to_vec_lemma>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.UInt.pow2_to_vec_lemma (Term Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.UInt.pow2_to_vec_lemma@tok () Term)



; </end encoding FStar.UInt.pow2_to_vec_lemma>


; <Start encoding FStar.UInt.pow2_from_vec_lemma>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.UInt.pow2_from_vec_lemma (Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.UInt.pow2_from_vec_lemma@tok () Term)


; </end encoding FStar.UInt.pow2_from_vec_lemma>


; <Start encoding FStar.UInt.ones_to_vec_lemma>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.UInt.ones_to_vec_lemma (Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.UInt.ones_to_vec_lemma@tok () Term)


; </end encoding FStar.UInt.ones_to_vec_lemma>


; <Start encoding FStar.UInt.ones_from_vec_lemma>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.UInt.ones_from_vec_lemma (Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.UInt.ones_from_vec_lemma@tok () Term)

; </end encoding FStar.UInt.ones_from_vec_lemma>


; <Start encoding FStar.UInt.nth>


(declare-fun FStar.UInt.nth (Term Term Term) Term)

(declare-fun Tm_arrow_3fc70c4ae2acbd923fa94b8473fca72c () Term)
(declare-fun FStar.UInt.nth@tok () Term)


; </end encoding FStar.UInt.nth>


; <Start encoding FStar.UInt.nth_lemma>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.UInt.nth_lemma (Term Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.UInt.nth_lemma@tok () Term)

; </end encoding FStar.UInt.nth_lemma>


; <Start encoding FStar.UInt.zero_nth_lemma>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.UInt.zero_nth_lemma (Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.UInt.zero_nth_lemma@tok () Term)


; </end encoding FStar.UInt.zero_nth_lemma>


; <Start encoding FStar.UInt.pow2_nth_lemma>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.UInt.pow2_nth_lemma (Term Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.UInt.pow2_nth_lemma@tok () Term)



; </end encoding FStar.UInt.pow2_nth_lemma>


; <Start encoding FStar.UInt.one_nth_lemma>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.UInt.one_nth_lemma (Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.UInt.one_nth_lemma@tok () Term)


; </end encoding FStar.UInt.one_nth_lemma>


; <Start encoding FStar.UInt.ones_nth_lemma>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.UInt.ones_nth_lemma (Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.UInt.ones_nth_lemma@tok () Term)


; </end encoding FStar.UInt.ones_nth_lemma>


; <Start encoding FStar.UInt.logand>

(declare-fun FStar.UInt.logand (Term Term Term) Term)
(declare-fun Tm_arrow_f4d897275479f32ec94ab14cea117895 () Term)
(declare-fun FStar.UInt.logand@tok () Term)

; </end encoding FStar.UInt.logand>


; <Start encoding FStar.UInt.logxor>

(declare-fun FStar.UInt.logxor (Term Term Term) Term)

(declare-fun FStar.UInt.logxor@tok () Term)

; </end encoding FStar.UInt.logxor>


; <Start encoding FStar.UInt.logor>

(declare-fun FStar.UInt.logor (Term Term Term) Term)

(declare-fun FStar.UInt.logor@tok () Term)

; </end encoding FStar.UInt.logor>


; <Start encoding FStar.UInt.lognot>

(declare-fun FStar.UInt.lognot (Term Term) Term)
(declare-fun Tm_arrow_7e93208f7d6c7796851172614443345f () Term)
(declare-fun FStar.UInt.lognot@tok () Term)

; </end encoding FStar.UInt.lognot>


; <Start encoding FStar.UInt.logand_definition>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.UInt.logand_definition (Term Term Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.UInt.logand_definition@tok () Term)


; </end encoding FStar.UInt.logand_definition>


; <Start encoding FStar.UInt.logxor_definition>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.UInt.logxor_definition (Term Term Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.UInt.logxor_definition@tok () Term)


; </end encoding FStar.UInt.logxor_definition>


; <Start encoding FStar.UInt.logor_definition>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.UInt.logor_definition (Term Term Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.UInt.logor_definition@tok () Term)


; </end encoding FStar.UInt.logor_definition>


; <Start encoding FStar.UInt.lognot_definition>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.UInt.lognot_definition (Term Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.UInt.lognot_definition@tok () Term)


; </end encoding FStar.UInt.lognot_definition>


; <Start encoding FStar.UInt.minus>

(declare-fun FStar.UInt.minus (Term Term) Term)

(declare-fun FStar.UInt.minus@tok () Term)

; </end encoding FStar.UInt.minus>


; <Start encoding FStar.UInt.logand_commutative>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.UInt.logand_commutative (Term Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.UInt.logand_commutative@tok () Term)

; </end encoding FStar.UInt.logand_commutative>


; <Start encoding FStar.UInt.logand_associative>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.UInt.logand_associative (Term Term Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.UInt.logand_associative@tok () Term)

; </end encoding FStar.UInt.logand_associative>


; <Start encoding FStar.UInt.logand_self>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.UInt.logand_self (Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.UInt.logand_self@tok () Term)

; </end encoding FStar.UInt.logand_self>


; <Start encoding FStar.UInt.logand_lemma_1>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.UInt.logand_lemma_1 (Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.UInt.logand_lemma_1@tok () Term)

; </end encoding FStar.UInt.logand_lemma_1>


; <Start encoding FStar.UInt.logand_lemma_2>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.UInt.logand_lemma_2 (Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.UInt.logand_lemma_2@tok () Term)

; </end encoding FStar.UInt.logand_lemma_2>


; <Start encoding FStar.UInt.subset_vec_le_lemma>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.UInt.subset_vec_le_lemma (Term Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.UInt.subset_vec_le_lemma@tok () Term)

; </end encoding FStar.UInt.subset_vec_le_lemma>


; <Start encoding FStar.UInt.logand_le>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.UInt.logand_le (Term Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.UInt.logand_le@tok () Term)

; </end encoding FStar.UInt.logand_le>


; <Start encoding FStar.UInt.logxor_commutative>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.UInt.logxor_commutative (Term Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.UInt.logxor_commutative@tok () Term)

; </end encoding FStar.UInt.logxor_commutative>


; <Start encoding FStar.UInt.logxor_associative>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.UInt.logxor_associative (Term Term Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.UInt.logxor_associative@tok () Term)

; </end encoding FStar.UInt.logxor_associative>


; <Start encoding FStar.UInt.logxor_self>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.UInt.logxor_self (Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.UInt.logxor_self@tok () Term)

; </end encoding FStar.UInt.logxor_self>


; <Start encoding FStar.UInt.logxor_lemma_1>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.UInt.logxor_lemma_1 (Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.UInt.logxor_lemma_1@tok () Term)

; </end encoding FStar.UInt.logxor_lemma_1>


; <Start encoding FStar.UInt.logxor_lemma_2>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.UInt.logxor_lemma_2 (Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.UInt.logxor_lemma_2@tok () Term)

; </end encoding FStar.UInt.logxor_lemma_2>


; <Skipped />


; <Start encoding FStar.UInt.xor>

(declare-fun FStar.UInt.xor (Term Term) Term)
(declare-fun Tm_arrow_a41b9b98d4288401e09e5c3b51ccc4f5 () Term)
(declare-fun FStar.UInt.xor@tok () Term)

; </end encoding FStar.UInt.xor>


; <Start encoding FStar.UInt.xor_lemma>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.UInt.xor_lemma (Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.UInt.xor_lemma@tok () Term)

; </end encoding FStar.UInt.xor_lemma>


; <Start encoding FStar.UInt.logxor_inv>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.UInt.logxor_inv (Term Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.UInt.logxor_inv@tok () Term)

; </end encoding FStar.UInt.logxor_inv>


; <Start encoding FStar.UInt.logxor_neq_nonzero>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.UInt.logxor_neq_nonzero (Term Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.UInt.logxor_neq_nonzero@tok () Term)

; </end encoding FStar.UInt.logxor_neq_nonzero>


; <Start encoding FStar.UInt.logor_commutative>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.UInt.logor_commutative (Term Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.UInt.logor_commutative@tok () Term)

; </end encoding FStar.UInt.logor_commutative>


; <Start encoding FStar.UInt.logor_associative>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.UInt.logor_associative (Term Term Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.UInt.logor_associative@tok () Term)

; </end encoding FStar.UInt.logor_associative>


; <Start encoding FStar.UInt.logor_self>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.UInt.logor_self (Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.UInt.logor_self@tok () Term)

; </end encoding FStar.UInt.logor_self>


; <Start encoding FStar.UInt.logor_lemma_1>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.UInt.logor_lemma_1 (Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.UInt.logor_lemma_1@tok () Term)

; </end encoding FStar.UInt.logor_lemma_1>


; <Start encoding FStar.UInt.logor_lemma_2>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.UInt.logor_lemma_2 (Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.UInt.logor_lemma_2@tok () Term)

; </end encoding FStar.UInt.logor_lemma_2>


; <Skipped />


; <Start encoding FStar.UInt.superset_vec_ge_lemma>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.UInt.superset_vec_ge_lemma (Term Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.UInt.superset_vec_ge_lemma@tok () Term)

; </end encoding FStar.UInt.superset_vec_ge_lemma>


; <Start encoding FStar.UInt.logor_ge>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.UInt.logor_ge (Term Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.UInt.logor_ge@tok () Term)

; </end encoding FStar.UInt.logor_ge>


; <Start encoding FStar.UInt.lognot_self>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.UInt.lognot_self (Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.UInt.lognot_self@tok () Term)

; </end encoding FStar.UInt.lognot_self>


; <Start encoding FStar.UInt.lognot_lemma_1>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.UInt.lognot_lemma_1 (Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.UInt.lognot_lemma_1@tok () Term)

; </end encoding FStar.UInt.lognot_lemma_1>


; <Start encoding FStar.UInt.to_vec_mod_pow2>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.UInt.to_vec_mod_pow2 (Term Term Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.UInt.to_vec_mod_pow2@tok () Term)
(declare-fun Tm_refine_f353e0d2a0ab8139a636e79f194142e5 (Term Term) Term)

; </end encoding FStar.UInt.to_vec_mod_pow2>


; <Start encoding FStar.UInt.to_vec_lt_pow2>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.UInt.to_vec_lt_pow2 (Term Term Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.UInt.to_vec_lt_pow2@tok () Term)


; </end encoding FStar.UInt.to_vec_lt_pow2>


; <Skipped />


; <Start encoding FStar.UInt.index_to_vec_ones>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.UInt.index_to_vec_ones (Term Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.UInt.index_to_vec_ones@tok () Term)
(declare-fun Tm_refine_7e0b9b2dbca36eab00de093c1b701c6d (Term) Term)


; </end encoding FStar.UInt.index_to_vec_ones>


; <Skipped />


; <Start encoding FStar.UInt.logor_disjoint>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.UInt.logor_disjoint (Term Term Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.UInt.logor_disjoint@tok () Term)

; </end encoding FStar.UInt.logor_disjoint>


; <Start encoding FStar.UInt.logand_mask>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.UInt.logand_mask (Term Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.UInt.logand_mask@tok () Term)

; </end encoding FStar.UInt.logand_mask>


; <Start encoding FStar.UInt.shift_left>

(declare-fun FStar.UInt.shift_left (Term Term Term) Term)
(declare-fun Tm_arrow_88bed77db23726a0c4c74cf2019c096b () Term)
(declare-fun FStar.UInt.shift_left@tok () Term)

; </end encoding FStar.UInt.shift_left>


; <Start encoding FStar.UInt.shift_right>

(declare-fun FStar.UInt.shift_right (Term Term Term) Term)

(declare-fun FStar.UInt.shift_right@tok () Term)

; </end encoding FStar.UInt.shift_right>


; <Start encoding FStar.UInt.shift_left_lemma_1>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.UInt.shift_left_lemma_1 (Term Term Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.UInt.shift_left_lemma_1@tok () Term)


; </end encoding FStar.UInt.shift_left_lemma_1>


; <Start encoding FStar.UInt.shift_left_lemma_2>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.UInt.shift_left_lemma_2 (Term Term Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.UInt.shift_left_lemma_2@tok () Term)


; </end encoding FStar.UInt.shift_left_lemma_2>


; <Start encoding FStar.UInt.shift_right_lemma_1>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.UInt.shift_right_lemma_1 (Term Term Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.UInt.shift_right_lemma_1@tok () Term)


; </end encoding FStar.UInt.shift_right_lemma_1>


; <Start encoding FStar.UInt.shift_right_lemma_2>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.UInt.shift_right_lemma_2 (Term Term Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.UInt.shift_right_lemma_2@tok () Term)


; </end encoding FStar.UInt.shift_right_lemma_2>


; <Start encoding FStar.UInt.shift_left_logand_lemma>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.UInt.shift_left_logand_lemma (Term Term Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.UInt.shift_left_logand_lemma@tok () Term)

; </end encoding FStar.UInt.shift_left_logand_lemma>


; <Start encoding FStar.UInt.shift_right_logand_lemma>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.UInt.shift_right_logand_lemma (Term Term Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.UInt.shift_right_logand_lemma@tok () Term)

; </end encoding FStar.UInt.shift_right_logand_lemma>


; <Start encoding FStar.UInt.shift_left_logxor_lemma>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.UInt.shift_left_logxor_lemma (Term Term Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.UInt.shift_left_logxor_lemma@tok () Term)

; </end encoding FStar.UInt.shift_left_logxor_lemma>


; <Start encoding FStar.UInt.shift_right_logxor_lemma>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.UInt.shift_right_logxor_lemma (Term Term Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.UInt.shift_right_logxor_lemma@tok () Term)

; </end encoding FStar.UInt.shift_right_logxor_lemma>


; <Start encoding FStar.UInt.shift_left_logor_lemma>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.UInt.shift_left_logor_lemma (Term Term Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.UInt.shift_left_logor_lemma@tok () Term)

; </end encoding FStar.UInt.shift_left_logor_lemma>


; <Start encoding FStar.UInt.shift_right_logor_lemma>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.UInt.shift_right_logor_lemma (Term Term Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.UInt.shift_right_logor_lemma@tok () Term)

; </end encoding FStar.UInt.shift_right_logor_lemma>


; <Start encoding FStar.UInt.shift_left_value_aux_1>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.UInt.shift_left_value_aux_1 (Term Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.UInt.shift_left_value_aux_1@tok () Term)

; </end encoding FStar.UInt.shift_left_value_aux_1>


; <Start encoding FStar.UInt.shift_left_value_aux_2>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.UInt.shift_left_value_aux_2 (Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.UInt.shift_left_value_aux_2@tok () Term)

; </end encoding FStar.UInt.shift_left_value_aux_2>


; <Start encoding FStar.UInt.shift_left_value_aux_3>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.UInt.shift_left_value_aux_3 (Term Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.UInt.shift_left_value_aux_3@tok () Term)

; </end encoding FStar.UInt.shift_left_value_aux_3>


; <Start encoding FStar.UInt.shift_left_value_lemma>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.UInt.shift_left_value_lemma (Term Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.UInt.shift_left_value_lemma@tok () Term)

; </end encoding FStar.UInt.shift_left_value_lemma>


; <Start encoding FStar.UInt.shift_right_value_aux_1>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.UInt.shift_right_value_aux_1 (Term Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.UInt.shift_right_value_aux_1@tok () Term)

; </end encoding FStar.UInt.shift_right_value_aux_1>


; <Start encoding FStar.UInt.shift_right_value_aux_2>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.UInt.shift_right_value_aux_2 (Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.UInt.shift_right_value_aux_2@tok () Term)

; </end encoding FStar.UInt.shift_right_value_aux_2>


; <Start encoding FStar.UInt.shift_right_value_aux_3>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.UInt.shift_right_value_aux_3 (Term Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.UInt.shift_right_value_aux_3@tok () Term)

; </end encoding FStar.UInt.shift_right_value_aux_3>


; <Start encoding FStar.UInt.shift_right_value_lemma>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.UInt.shift_right_value_lemma (Term Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.UInt.shift_right_value_lemma@tok () Term)

; </end encoding FStar.UInt.shift_right_value_lemma>


; <Start encoding FStar.UInt.msb>

(declare-fun FStar.UInt.msb (Term Term) Term)
(declare-fun Tm_arrow_d4ac65fa6e48f26152e66f6f5f032db4 () Term)
(declare-fun FStar.UInt.msb@tok () Term)

; </end encoding FStar.UInt.msb>


; <Skipped />


; <Start encoding FStar.UInt.lemma_msb_pow2>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.UInt.lemma_msb_pow2 (Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.UInt.lemma_msb_pow2@tok () Term)

; </end encoding FStar.UInt.lemma_msb_pow2>


; <Start encoding FStar.UInt.plus_one_mod>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.UInt.plus_one_mod (Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.UInt.plus_one_mod@tok () Term)

; </end encoding FStar.UInt.plus_one_mod>


; <Start encoding FStar.UInt.lemma_minus_zero>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.UInt.lemma_minus_zero (Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.UInt.lemma_minus_zero@tok () Term)

; </end encoding FStar.UInt.lemma_minus_zero>


; <Start encoding FStar.UInt.lemma_msb_gte>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.UInt.lemma_msb_gte (Term Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.UInt.lemma_msb_gte@tok () Term)

; </end encoding FStar.UInt.lemma_msb_gte>


; <Skipped />


; <Skipped />


; <Start encoding FStar.UInt.lemma_uint_mod>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.UInt.lemma_uint_mod (Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.UInt.lemma_uint_mod@tok () Term)

; </end encoding FStar.UInt.lemma_uint_mod>


; <Skipped />


; <Start encoding FStar.UInt.lemma_add_sub_cancel>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.UInt.lemma_add_sub_cancel (Term Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.UInt.lemma_add_sub_cancel@tok () Term)

; </end encoding FStar.UInt.lemma_add_sub_cancel>


; <Start encoding FStar.UInt.lemma_mod_sub_distr_l>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.UInt.lemma_mod_sub_distr_l (Term Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.UInt.lemma_mod_sub_distr_l@tok () Term)

; </end encoding FStar.UInt.lemma_mod_sub_distr_l>


; <Start encoding FStar.UInt.lemma_sub_add_cancel>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.UInt.lemma_sub_add_cancel (Term Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.UInt.lemma_sub_add_cancel@tok () Term)

; </end encoding FStar.UInt.lemma_sub_add_cancel>


; <Start encoding FStar.UInt.zero_extend_vec>

(declare-fun FStar.UInt.zero_extend_vec (Term Term) Term)
(declare-fun Tm_arrow_dcb1e97275faab10b7eb1bdfcfbde371 () Term)
(declare-fun FStar.UInt.zero_extend_vec@tok () Term)

; </end encoding FStar.UInt.zero_extend_vec>


; <Start encoding FStar.UInt.one_extend_vec>

(declare-fun FStar.UInt.one_extend_vec (Term Term) Term)

(declare-fun FStar.UInt.one_extend_vec@tok () Term)

; </end encoding FStar.UInt.one_extend_vec>


; <Start encoding FStar.UInt.zero_extend>

(declare-fun FStar.UInt.zero_extend (Term Term) Term)
(declare-fun Tm_arrow_8a55f1e2e0fc60c6f44b88ae88621b5f () Term)
(declare-fun FStar.UInt.zero_extend@tok () Term)

; </end encoding FStar.UInt.zero_extend>


; <Start encoding FStar.UInt.one_extend>

(declare-fun FStar.UInt.one_extend (Term Term) Term)

(declare-fun FStar.UInt.one_extend@tok () Term)

; </end encoding FStar.UInt.one_extend>


; <Start encoding FStar.UInt.lemma_zero_extend>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.UInt.lemma_zero_extend (Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.UInt.lemma_zero_extend@tok () Term)
(declare-fun Tm_refine_a2362280d81dbd526f1fa3f771e8faad (Term) Term)

; </end encoding FStar.UInt.lemma_zero_extend>


; <Start encoding FStar.UInt.lemma_one_extend>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.UInt.lemma_one_extend (Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.UInt.lemma_one_extend@tok () Term)

; </end encoding FStar.UInt.lemma_one_extend>


; <Start encoding FStar.UInt.lemma_lognot_zero_ext>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.UInt.lemma_lognot_zero_ext (Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.UInt.lemma_lognot_zero_ext@tok () Term)

; </end encoding FStar.UInt.lemma_lognot_zero_ext>


; <Start encoding FStar.UInt.lemma_lognot_one_ext>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.UInt.lemma_lognot_one_ext (Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.UInt.lemma_lognot_one_ext@tok () Term)

; </end encoding FStar.UInt.lemma_lognot_one_ext>


; <Skipped />


; <Start encoding FStar.UInt.lemma_lognot_value_mod>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.UInt.lemma_lognot_value_mod (Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.UInt.lemma_lognot_value_mod@tok () Term)

; </end encoding FStar.UInt.lemma_lognot_value_mod>


; <Start encoding FStar.UInt.lemma_lognot_value_zero>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.UInt.lemma_lognot_value_zero (Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.UInt.lemma_lognot_value_zero@tok () Term)

; </end encoding FStar.UInt.lemma_lognot_value_zero>


; <Skipped />


; <Start encoding FStar.UInt.lemma_mod_variation>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.UInt.lemma_mod_variation (Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.UInt.lemma_mod_variation@tok () Term)

; </end encoding FStar.UInt.lemma_mod_variation>


; <Skipped />


; <Skipped />


; <Start encoding FStar.UInt.lemma_one_mod_pow2>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.UInt.lemma_one_mod_pow2 (Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.UInt.lemma_one_mod_pow2@tok () Term)

; </end encoding FStar.UInt.lemma_one_mod_pow2>


; <Skipped />


; <Skipped />


; <Start encoding FStar.UInt.lemma_lognot_value_variation>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.UInt.lemma_lognot_value_variation (Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.UInt.lemma_lognot_value_variation@tok () Term)

; </end encoding FStar.UInt.lemma_lognot_value_variation>


; <Skipped />


; <Start encoding FStar.UInt.lemma_lognot_value_nonzero>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.UInt.lemma_lognot_value_nonzero (Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.UInt.lemma_lognot_value_nonzero@tok () Term)

; </end encoding FStar.UInt.lemma_lognot_value_nonzero>


; <Start encoding FStar.UInt.lemma_lognot_value>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.UInt.lemma_lognot_value (Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.UInt.lemma_lognot_value@tok () Term)

; </end encoding FStar.UInt.lemma_lognot_value>


; <Start encoding FStar.UInt.lemma_minus_eq_zero_sub>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.UInt.lemma_minus_eq_zero_sub (Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.UInt.lemma_minus_eq_zero_sub@tok () Term)

; </end encoding FStar.UInt.lemma_minus_eq_zero_sub>


; UNSAT CORE: @MaxFuel_assumption, @MaxIFuel_assumption, @fuel_correspondence_Prims.pow2.fuel_instrumented, @query, constructor_distinct_Lib.IntTypes.S16, constructor_distinct_Lib.IntTypes.S32, constructor_distinct_Lib.IntTypes.SEC, equality_tok_Lib.IntTypes.S16@tok, equality_tok_Lib.IntTypes.S32@tok, equality_tok_Lib.IntTypes.SEC@tok, equation_Lib.IntTypes.bits, equation_Lib.IntTypes.range, equation_Lib.IntTypes.signed, equation_Lib.IntTypes.unsigned, equation_Lib.IntTypes.v, equation_Prims.nat, equation_Prims.pos, equation_Spec.Kyber2.Params.params_q, int_inversion, int_typing, lemma_FStar.UInt.pow2_values, primitive_Prims.op_Addition, primitive_Prims.op_Division, primitive_Prims.op_LessThanOrEqual, primitive_Prims.op_Minus, primitive_Prims.op_Multiply, primitive_Prims.op_Subtraction, projection_inverse_BoxBool_proj_0, projection_inverse_BoxInt_proj_0, refinement_interpretation_Tm_refine_2b320913041b873fce938dd17eebb3e2, refinement_interpretation_Tm_refine_542f9d4f129664613f2483a6c88bc7c2, refinement_interpretation_Tm_refine_774ba3f728d91ead8ef40be66c9802e5, refinement_interpretation_Tm_refine_83845a86f2550cdf941eeb1d9b59602b, refinement_interpretation_Tm_refine_9d3fd79fd314167f1a9c213a188da3ec, refinement_interpretation_Tm_refine_b2401a8cabe2f9a01538f32548fa9f6c, typing_Lib.IntTypes.mk_int, typing_Prims.pow2, typing_tok_Lib.IntTypes.S32@tok, typing_tok_Lib.IntTypes.SEC@tok

;;; End module FStar.UInt (753 decls; total size 51773)

;;; Start module FStar.Int

; <Skipped />


; <Start encoding FStar.Int.pow2_values>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.Int.pow2_values (Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.Int.pow2_values@tok () Term)

; </end encoding FStar.Int.pow2_values>


; <Start encoding FStar.Int.max_int>

(declare-fun FStar.Int.max_int (Term) Term)
(declare-fun Tm_arrow_08643d78e274903c12e67630bc27e2ff () Term)
(declare-fun FStar.Int.max_int@tok () Term)

; </end encoding FStar.Int.max_int>


; <Start encoding FStar.Int.min_int>

(declare-fun FStar.Int.min_int (Term) Term)

(declare-fun FStar.Int.min_int@tok () Term)

; </end encoding FStar.Int.min_int>


; <Start encoding FStar.Int.fits>

(declare-fun FStar.Int.fits (Term Term) Term)
(declare-fun Tm_arrow_0cc3774076f9b140636f49c6b11206ea () Term)
(declare-fun FStar.Int.fits@tok () Term)

; </end encoding FStar.Int.fits>


; <Start encoding FStar.Int.size>

(declare-fun FStar.Int.size (Term Term) Term)
(declare-fun Tm_arrow_7146999d8e685cab1fa5e885783d4ad4 () Term)
(declare-fun FStar.Int.size@tok () Term)

; </end encoding FStar.Int.size>


; <Start encoding FStar.Int.int_t>

(declare-fun FStar.Int.int_t (Term) Term)
(declare-fun Tm_arrow_e214da407f361f6aa0144228799685d1 () Term)
(declare-fun FStar.Int.int_t@tok () Term)
(declare-fun Tm_refine_c156ecc6eab05d1687a383ef171435eb (Term) Term)

; </end encoding FStar.Int.int_t>


; <Start encoding FStar.Int.op_Slash>


(declare-fun FStar.Int.op_Slash (Term Term) Term)

(declare-fun Tm_arrow_2c2bb042329e2e757b97305bbc29732f () Term)
(declare-fun FStar.Int.op_Slash@tok () Term)


; </end encoding FStar.Int.op_Slash>


; <Start encoding FStar.Int.op_At_Percent>

(declare-fun Tm_refine_6f861454c283cab7fef581bd2f2d57c5 () Term)
(declare-fun FStar.Int.op_At_Percent (Term Term) Term)

(declare-fun Tm_arrow_3896a5194433b12d044f39d7e0b679dc () Term)
(declare-fun FStar.Int.op_At_Percent@tok () Term)


; </end encoding FStar.Int.op_At_Percent>


; <Start encoding FStar.Int.zero>

(declare-fun FStar.Int.zero (Term) Term)
(declare-fun Tm_arrow_cb14a53d8f51c2a1b5f2e44ec1c55960 () Term)
(declare-fun FStar.Int.zero@tok () Term)

; </end encoding FStar.Int.zero>


; <Skipped />


; <Start encoding FStar.Int.pow2_n>

(declare-fun Tm_refine_cf74cf5c1e7834b84db9cc7ebce886a3 (Term) Term)
(declare-fun FStar.Int.pow2_n (Term Term) Term)

(declare-fun Tm_arrow_42409e57c55f2a2d0836412885dba252 () Term)
(declare-fun FStar.Int.pow2_n@tok () Term)


; </end encoding FStar.Int.pow2_n>


; <Start encoding FStar.Int.pow2_minus_one>

(declare-fun Tm_refine_4fe9a5df27ca5859eef8add9fc6819fb () Term)

(declare-fun FStar.Int.pow2_minus_one (Term Term) Term)


(declare-fun Tm_arrow_81be2ee4e7a1e46c9526aae5e34753cd () Term)
(declare-fun FStar.Int.pow2_minus_one@tok () Term)



; </end encoding FStar.Int.pow2_minus_one>


; <Start encoding FStar.Int.one>


(declare-fun FStar.Int.one (Term) Term)

(declare-fun Tm_arrow_e2450f3af7bd5b3af47241cdfb1c2db6 () Term)
(declare-fun FStar.Int.one@tok () Term)


; </end encoding FStar.Int.one>


; <Skipped />


; <Start encoding FStar.Int.ones>

(declare-fun FStar.Int.ones (Term) Term)

(declare-fun FStar.Int.ones@tok () Term)

; </end encoding FStar.Int.ones>


; <Start encoding FStar.Int.incr>

(declare-fun FStar.Int.incr (Term Term) Term)
(declare-fun Tm_refine_dcbbaccec0a9dbd3681a14f97d5258f4 (Term) Term)
(declare-fun Tm_arrow_6a595e67db857b4e04ea431fd250db84 () Term)
(declare-fun FStar.Int.incr@tok () Term)


; </end encoding FStar.Int.incr>


; <Start encoding FStar.Int.decr>

(declare-fun FStar.Int.decr (Term Term) Term)

(declare-fun Tm_arrow_9932ad821a47221f73f30476224722b3 () Term)
(declare-fun FStar.Int.decr@tok () Term)


; </end encoding FStar.Int.decr>


; <Start encoding FStar.Int.incr_underspec>

(declare-fun FStar.Int.incr_underspec (Term Term) Term)
(declare-fun Tm_refine_d4a5cafc6f5a0f55c9100191cf1c919d (Term Term) Term)
(declare-fun Tm_arrow_7da78e36e44c2863a3eea73f058069f8 () Term)
(declare-fun FStar.Int.incr_underspec@tok () Term)


; </end encoding FStar.Int.incr_underspec>


; <Start encoding FStar.Int.decr_underspec>

(declare-fun FStar.Int.decr_underspec (Term Term) Term)
(declare-fun Tm_refine_fe0f51cc65c8d431b43406ae8d7f7c7c (Term Term) Term)
(declare-fun Tm_arrow_f8ffe0a78d6e5b3dac71656ff7d0fc5a () Term)
(declare-fun FStar.Int.decr_underspec@tok () Term)


; </end encoding FStar.Int.decr_underspec>


; <Start encoding FStar.Int.incr_mod>

(declare-fun FStar.Int.incr_mod (Term Term) Term)
(declare-fun Tm_arrow_d4f13608b577247ae2db20b2380b2245 () Term)
(declare-fun FStar.Int.incr_mod@tok () Term)

; </end encoding FStar.Int.incr_mod>


; <Start encoding FStar.Int.decr_mod>

(declare-fun FStar.Int.decr_mod (Term Term) Term)

(declare-fun FStar.Int.decr_mod@tok () Term)

; </end encoding FStar.Int.decr_mod>


; <Start encoding FStar.Int.add>

(declare-fun FStar.Int.add (Term Term Term) Term)

(declare-fun Tm_arrow_cbeba074d8c79f94519373cfde34463f () Term)
(declare-fun FStar.Int.add@tok () Term)


; </end encoding FStar.Int.add>


; <Start encoding FStar.Int.add_underspec>

(declare-fun FStar.Int.add_underspec (Term Term Term) Term)
(declare-fun Tm_refine_7bd0fa444597c4ebd4664ae6a997600a (Term Term Term) Term)
(declare-fun Tm_arrow_5c387c335d6e6391b1c81e806fbecc03 () Term)
(declare-fun FStar.Int.add_underspec@tok () Term)


; </end encoding FStar.Int.add_underspec>


; <Skipped />


; <Start encoding FStar.Int.add_mod>

(declare-fun FStar.Int.add_mod (Term Term Term) Term)
(declare-fun Tm_arrow_18a34a79f38620fd3e207686d0d0d13e () Term)
(declare-fun FStar.Int.add_mod@tok () Term)

; </end encoding FStar.Int.add_mod>


; <Start encoding FStar.Int.sub>

(declare-fun FStar.Int.sub (Term Term Term) Term)

(declare-fun Tm_arrow_d5e0171e91c640344190e488b3c3a2c8 () Term)
(declare-fun FStar.Int.sub@tok () Term)


; </end encoding FStar.Int.sub>


; <Start encoding FStar.Int.sub_underspec>

(declare-fun FStar.Int.sub_underspec (Term Term Term) Term)
(declare-fun Tm_refine_b4c298e8d79868eb1409c37bf0adba2a (Term Term Term) Term)
(declare-fun Tm_arrow_f42d521160539850f1993d34e8fc87c9 () Term)
(declare-fun FStar.Int.sub_underspec@tok () Term)


; </end encoding FStar.Int.sub_underspec>


; <Start encoding FStar.Int.sub_mod>

(declare-fun FStar.Int.sub_mod (Term Term Term) Term)

(declare-fun FStar.Int.sub_mod@tok () Term)

; </end encoding FStar.Int.sub_mod>


; <Start encoding FStar.Int.mul>

(declare-fun FStar.Int.mul (Term Term Term) Term)

(declare-fun Tm_arrow_59f7075a28af88a37cc8d77ed622794d () Term)
(declare-fun FStar.Int.mul@tok () Term)


; </end encoding FStar.Int.mul>


; <Start encoding FStar.Int.mul_underspec>

(declare-fun FStar.Int.mul_underspec (Term Term Term) Term)
(declare-fun Tm_refine_e0808d72dd3bcd98cbd025f677f0b52b (Term Term Term) Term)
(declare-fun Tm_arrow_c3825549d78bf3b47b1fc19cca6efb0a () Term)
(declare-fun FStar.Int.mul_underspec@tok () Term)


; </end encoding FStar.Int.mul_underspec>


; <Start encoding FStar.Int.mul_mod>

(declare-fun FStar.Int.mul_mod (Term Term Term) Term)

(declare-fun FStar.Int.mul_mod@tok () Term)

; </end encoding FStar.Int.mul_mod>


; <Skipped />


; <Start encoding FStar.Int.div>

(declare-fun Tm_refine_83ac8ca0eae25a164d9f9c0d728fbff9 (Term) Term)
(declare-fun FStar.Int.div (Term Term Term) Term)

(declare-fun Tm_refine_70714641831ff35b8943074d85fc7551 (Term Term Term) Term)
(declare-fun Tm_arrow_59a1c11be2fac6a30b2acdbfbf1eda90 () Term)
(declare-fun FStar.Int.div@tok () Term)



; </end encoding FStar.Int.div>


; <Start encoding FStar.Int.div_underspec>


(declare-fun FStar.Int.div_underspec (Term Term Term) Term)

(declare-fun Tm_refine_af4cbfe65dbbaeb55593b4625c2c5048 (Term Term Term) Term)
(declare-fun Tm_arrow_0f80d94a97a6b0663b1915a2060513cc () Term)
(declare-fun FStar.Int.div_underspec@tok () Term)


; </end encoding FStar.Int.div_underspec>


; <Start encoding FStar.Int.div_size>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.Int.div_size (Term Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.Int.div_size@tok () Term)

; </end encoding FStar.Int.div_size>


; <Start encoding FStar.Int.udiv>

(declare-fun Tm_refine_8506aeb4dd19f2072121aa1df21f1bb2 (Term) Term)

(declare-fun FStar.Int.udiv (Term Term Term) Term)



(declare-fun Tm_arrow_82b3f90612854f7c40f1bdc10bed000c () Term)
(declare-fun FStar.Int.udiv@tok () Term)




; </end encoding FStar.Int.udiv>


; <Start encoding FStar.Int.mod>


(declare-fun FStar.Int.mod (Term Term Term) Term)

(declare-fun Tm_arrow_d683be1bb1ee9de66cbbf189f68ec0e5 () Term)
(declare-fun FStar.Int.mod@tok () Term)


; </end encoding FStar.Int.mod>


; <Start encoding FStar.Int.eq>

(declare-fun FStar.Int.eq (Term Term Term) Term)
(declare-fun Tm_arrow_8a34ac1c572f737da4642094a6f8e213 () Term)
(declare-fun FStar.Int.eq@tok () Term)

; </end encoding FStar.Int.eq>


; <Start encoding FStar.Int.gt>

(declare-fun FStar.Int.gt (Term Term Term) Term)

(declare-fun FStar.Int.gt@tok () Term)

; </end encoding FStar.Int.gt>


; <Start encoding FStar.Int.gte>

(declare-fun FStar.Int.gte (Term Term Term) Term)

(declare-fun FStar.Int.gte@tok () Term)

; </end encoding FStar.Int.gte>


; <Start encoding FStar.Int.lt>

(declare-fun FStar.Int.lt (Term Term Term) Term)

(declare-fun FStar.Int.lt@tok () Term)

; </end encoding FStar.Int.lt>


; <Start encoding FStar.Int.lte>

(declare-fun FStar.Int.lte (Term Term Term) Term)

(declare-fun FStar.Int.lte@tok () Term)

; </end encoding FStar.Int.lte>


; <Skipped />


; <Start encoding FStar.Int.to_uint>

(declare-fun FStar.Int.to_uint (Term Term) Term)
(declare-fun Tm_arrow_3e678eb9a841c4f9b41c85aeb802f0f1 () Term)
(declare-fun FStar.Int.to_uint@tok () Term)

; </end encoding FStar.Int.to_uint>


; <Start encoding FStar.Int.from_uint>

(declare-fun FStar.Int.from_uint (Term Term) Term)
(declare-fun Tm_arrow_c31ea52198bde53869920a7d3bc4602c () Term)
(declare-fun FStar.Int.from_uint@tok () Term)

; </end encoding FStar.Int.from_uint>


; <Start encoding FStar.Int.to_uint_injective>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.Int.to_uint_injective (Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.Int.to_uint_injective@tok () Term)

; </end encoding FStar.Int.to_uint_injective>


; <Start encoding FStar.Int.to_int_t>

(declare-fun FStar.Int.to_int_t (Term Term) Term)
(declare-fun Tm_arrow_4814b4e3e94f328f65fd76f9d65943d4 () Term)
(declare-fun FStar.Int.to_int_t@tok () Term)

; </end encoding FStar.Int.to_int_t>


; <Start encoding FStar.Int.to_vec>

(declare-fun FStar.Int.to_vec (Term Term) Term)
(declare-fun Tm_arrow_45e09970c9488f8db22355eb21b4b697 () Term)
(declare-fun FStar.Int.to_vec@tok () Term)

; </end encoding FStar.Int.to_vec>


; <Start encoding FStar.Int.from_vec>

(declare-fun FStar.Int.from_vec (Term Term) Term)
(declare-fun Tm_arrow_82852c1e83761b67bc6fcca3c7b80d79 () Term)
(declare-fun FStar.Int.from_vec@tok () Term)

; </end encoding FStar.Int.from_vec>


; <Start encoding FStar.Int.to_vec_lemma_1>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.Int.to_vec_lemma_1 (Term Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.Int.to_vec_lemma_1@tok () Term)

; </end encoding FStar.Int.to_vec_lemma_1>


; <Start encoding FStar.Int.to_vec_lemma_2>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.Int.to_vec_lemma_2 (Term Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.Int.to_vec_lemma_2@tok () Term)

; </end encoding FStar.Int.to_vec_lemma_2>


; <Start encoding FStar.Int.inverse_aux>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.Int.inverse_aux (Term Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.Int.inverse_aux@tok () Term)


; </end encoding FStar.Int.inverse_aux>


; <Start encoding FStar.Int.inverse_vec_lemma>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.Int.inverse_vec_lemma (Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.Int.inverse_vec_lemma@tok () Term)

; </end encoding FStar.Int.inverse_vec_lemma>


; <Start encoding FStar.Int.inverse_num_lemma>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.Int.inverse_num_lemma (Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.Int.inverse_num_lemma@tok () Term)

; </end encoding FStar.Int.inverse_num_lemma>


; <Start encoding FStar.Int.from_vec_lemma_1>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.Int.from_vec_lemma_1 (Term Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.Int.from_vec_lemma_1@tok () Term)

; </end encoding FStar.Int.from_vec_lemma_1>


; <Start encoding FStar.Int.from_vec_lemma_2>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.Int.from_vec_lemma_2 (Term Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.Int.from_vec_lemma_2@tok () Term)

; </end encoding FStar.Int.from_vec_lemma_2>


; <Start encoding FStar.Int.zero_to_vec_lemma>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.Int.zero_to_vec_lemma (Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.Int.zero_to_vec_lemma@tok () Term)


; </end encoding FStar.Int.zero_to_vec_lemma>


; <Start encoding FStar.Int.zero_from_vec_lemma>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.Int.zero_from_vec_lemma (Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.Int.zero_from_vec_lemma@tok () Term)

; </end encoding FStar.Int.zero_from_vec_lemma>


; <Start encoding FStar.Int.one_to_vec_lemma>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.Int.one_to_vec_lemma (Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.Int.one_to_vec_lemma@tok () Term)



; </end encoding FStar.Int.one_to_vec_lemma>


; <Skipped />


; <Start encoding FStar.Int.pow2_to_vec_lemma>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.Int.pow2_to_vec_lemma (Term Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.Int.pow2_to_vec_lemma@tok () Term)



; </end encoding FStar.Int.pow2_to_vec_lemma>


; <Skipped />


; <Start encoding FStar.Int.pow2_from_vec_lemma>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.Int.pow2_from_vec_lemma (Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.Int.pow2_from_vec_lemma@tok () Term)
(declare-fun Tm_refine_b555e04c50662c1d4e406318a3bd8d8d (Term) Term)

; </end encoding FStar.Int.pow2_from_vec_lemma>


; <Start encoding FStar.Int.ones_to_vec_lemma>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.Int.ones_to_vec_lemma (Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.Int.ones_to_vec_lemma@tok () Term)


; </end encoding FStar.Int.ones_to_vec_lemma>


; <Start encoding FStar.Int.ones_from_vec_lemma>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.Int.ones_from_vec_lemma (Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.Int.ones_from_vec_lemma@tok () Term)

; </end encoding FStar.Int.ones_from_vec_lemma>


; <Start encoding FStar.Int.nth>


(declare-fun FStar.Int.nth (Term Term Term) Term)

(declare-fun Tm_arrow_4019956ce842311d665dc67ac9fd8b34 () Term)
(declare-fun FStar.Int.nth@tok () Term)


; </end encoding FStar.Int.nth>


; <Start encoding FStar.Int.nth_lemma>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.Int.nth_lemma (Term Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.Int.nth_lemma@tok () Term)

; </end encoding FStar.Int.nth_lemma>


; <Start encoding FStar.Int.zero_nth_lemma>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.Int.zero_nth_lemma (Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.Int.zero_nth_lemma@tok () Term)


; </end encoding FStar.Int.zero_nth_lemma>


; <Start encoding FStar.Int.one_nth_lemma>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.Int.one_nth_lemma (Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.Int.one_nth_lemma@tok () Term)



; </end encoding FStar.Int.one_nth_lemma>


; <Start encoding FStar.Int.ones_nth_lemma>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.Int.ones_nth_lemma (Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.Int.ones_nth_lemma@tok () Term)


; </end encoding FStar.Int.ones_nth_lemma>


; <Start encoding FStar.Int.logand>

(declare-fun FStar.Int.logand (Term Term Term) Term)

(declare-fun FStar.Int.logand@tok () Term)

; </end encoding FStar.Int.logand>


; <Start encoding FStar.Int.logxor>

(declare-fun FStar.Int.logxor (Term Term Term) Term)

(declare-fun FStar.Int.logxor@tok () Term)

; </end encoding FStar.Int.logxor>


; <Start encoding FStar.Int.logor>

(declare-fun FStar.Int.logor (Term Term Term) Term)

(declare-fun FStar.Int.logor@tok () Term)

; </end encoding FStar.Int.logor>


; <Start encoding FStar.Int.lognot>

(declare-fun FStar.Int.lognot (Term Term) Term)

(declare-fun FStar.Int.lognot@tok () Term)

; </end encoding FStar.Int.lognot>


; <Start encoding FStar.Int.logand_definition>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.Int.logand_definition (Term Term Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.Int.logand_definition@tok () Term)


; </end encoding FStar.Int.logand_definition>


; <Start encoding FStar.Int.logxor_definition>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.Int.logxor_definition (Term Term Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.Int.logxor_definition@tok () Term)


; </end encoding FStar.Int.logxor_definition>


; <Start encoding FStar.Int.logor_definition>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.Int.logor_definition (Term Term Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.Int.logor_definition@tok () Term)


; </end encoding FStar.Int.logor_definition>


; <Start encoding FStar.Int.lognot_definition>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.Int.lognot_definition (Term Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.Int.lognot_definition@tok () Term)


; </end encoding FStar.Int.lognot_definition>


; <Start encoding FStar.Int.minus>


(declare-fun FStar.Int.minus (Term Term) Term)

(declare-fun Tm_arrow_04cc0f7bdc56c0cf812e46ad027a361f () Term)
(declare-fun FStar.Int.minus@tok () Term)


; </end encoding FStar.Int.minus>


; <Start encoding FStar.Int.logand_commutative>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.Int.logand_commutative (Term Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.Int.logand_commutative@tok () Term)

; </end encoding FStar.Int.logand_commutative>


; <Start encoding FStar.Int.logand_associative>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.Int.logand_associative (Term Term Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.Int.logand_associative@tok () Term)

; </end encoding FStar.Int.logand_associative>


; <Start encoding FStar.Int.logand_self>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.Int.logand_self (Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.Int.logand_self@tok () Term)

; </end encoding FStar.Int.logand_self>


; <Start encoding FStar.Int.logand_lemma_1>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.Int.logand_lemma_1 (Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.Int.logand_lemma_1@tok () Term)

; </end encoding FStar.Int.logand_lemma_1>


; <Start encoding FStar.Int.logand_lemma_2>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.Int.logand_lemma_2 (Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.Int.logand_lemma_2@tok () Term)

; </end encoding FStar.Int.logand_lemma_2>


; <Start encoding FStar.Int.sign_bit_negative>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.Int.sign_bit_negative (Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.Int.sign_bit_negative@tok () Term)

; </end encoding FStar.Int.sign_bit_negative>


; <Start encoding FStar.Int.sign_bit_positive>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.Int.sign_bit_positive (Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.Int.sign_bit_positive@tok () Term)

; </end encoding FStar.Int.sign_bit_positive>


; <Start encoding FStar.Int.logand_pos_le>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.Int.logand_pos_le (Term Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.Int.logand_pos_le@tok () Term)

; </end encoding FStar.Int.logand_pos_le>


; <Start encoding FStar.Int.logand_pow2_minus_one>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.Int.logand_pow2_minus_one (Term Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.Int.logand_pow2_minus_one@tok () Term)

; </end encoding FStar.Int.logand_pow2_minus_one>


; <Skipped />


; <Skipped />


; <Start encoding FStar.Int.logand_max>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.Int.logand_max (Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.Int.logand_max@tok () Term)

; </end encoding FStar.Int.logand_max>


; <Skipped />


; <Start encoding FStar.Int.logxor_commutative>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.Int.logxor_commutative (Term Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.Int.logxor_commutative@tok () Term)

; </end encoding FStar.Int.logxor_commutative>


; <Start encoding FStar.Int.logxor_associative>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.Int.logxor_associative (Term Term Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.Int.logxor_associative@tok () Term)

; </end encoding FStar.Int.logxor_associative>


; <Start encoding FStar.Int.logxor_self>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.Int.logxor_self (Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.Int.logxor_self@tok () Term)

; </end encoding FStar.Int.logxor_self>


; <Start encoding FStar.Int.logxor_lemma_1>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.Int.logxor_lemma_1 (Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.Int.logxor_lemma_1@tok () Term)

; </end encoding FStar.Int.logxor_lemma_1>


; <Start encoding FStar.Int.logxor_lemma_2>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.Int.logxor_lemma_2 (Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.Int.logxor_lemma_2@tok () Term)

; </end encoding FStar.Int.logxor_lemma_2>


; <Start encoding FStar.Int.logxor_inv>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.Int.logxor_inv (Term Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.Int.logxor_inv@tok () Term)

; </end encoding FStar.Int.logxor_inv>


; <Start encoding FStar.Int.logxor_neq_nonzero>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.Int.logxor_neq_nonzero (Term Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.Int.logxor_neq_nonzero@tok () Term)

; </end encoding FStar.Int.logxor_neq_nonzero>


; <Start encoding FStar.Int.lognot_negative>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.Int.lognot_negative (Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.Int.lognot_negative@tok () Term)

; </end encoding FStar.Int.lognot_negative>


; <Start encoding FStar.Int.shift_left>

(declare-fun Tm_refine_f9945c9851ba67924155357268d171eb (Term) Term)
(declare-fun FStar.Int.shift_left (Term Term Term) Term)

(declare-fun Tm_arrow_855fa52a66bb6d9af33de248be8e1a9a () Term)
(declare-fun FStar.Int.shift_left@tok () Term)


; </end encoding FStar.Int.shift_left>


; <Start encoding FStar.Int.shift_right>


(declare-fun FStar.Int.shift_right (Term Term Term) Term)


(declare-fun FStar.Int.shift_right@tok () Term)


; </end encoding FStar.Int.shift_right>


; <Start encoding FStar.Int.shift_arithmetic_right>

(declare-fun FStar.Int.shift_arithmetic_right (Term Term Term) Term)
(declare-fun Tm_arrow_f565aa7121c91c2f8ce9f41727c7b7ca () Term)
(declare-fun FStar.Int.shift_arithmetic_right@tok () Term)

; </end encoding FStar.Int.shift_arithmetic_right>


; <Start encoding FStar.Int.shift_left_lemma_1>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.Int.shift_left_lemma_1 (Term Term Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.Int.shift_left_lemma_1@tok () Term)



; </end encoding FStar.Int.shift_left_lemma_1>


; <Start encoding FStar.Int.shift_left_lemma_2>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.Int.shift_left_lemma_2 (Term Term Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.Int.shift_left_lemma_2@tok () Term)



; </end encoding FStar.Int.shift_left_lemma_2>


; <Start encoding FStar.Int.shift_left_value_lemma>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.Int.shift_left_value_lemma (Term Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.Int.shift_left_value_lemma@tok () Term)


; </end encoding FStar.Int.shift_left_value_lemma>


; <Start encoding FStar.Int.shift_right_lemma_1>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.Int.shift_right_lemma_1 (Term Term Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.Int.shift_right_lemma_1@tok () Term)



; </end encoding FStar.Int.shift_right_lemma_1>


; <Start encoding FStar.Int.shift_right_lemma_2>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.Int.shift_right_lemma_2 (Term Term Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.Int.shift_right_lemma_2@tok () Term)



; </end encoding FStar.Int.shift_right_lemma_2>


; <Start encoding FStar.Int.shift_arithmetic_right_lemma_1>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.Int.shift_arithmetic_right_lemma_1 (Term Term Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.Int.shift_arithmetic_right_lemma_1@tok () Term)


; </end encoding FStar.Int.shift_arithmetic_right_lemma_1>


; <Start encoding FStar.Int.shift_arithmetic_right_lemma_2>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.Int.shift_arithmetic_right_lemma_2 (Term Term Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.Int.shift_arithmetic_right_lemma_2@tok () Term)


; </end encoding FStar.Int.shift_arithmetic_right_lemma_2>


; UNSAT CORE: @MaxFuel_assumption, @MaxIFuel_assumption, @fuel_correspondence_Prims.pow2.fuel_instrumented, @query, constructor_distinct_Lib.IntTypes.S16, constructor_distinct_Lib.IntTypes.S32, constructor_distinct_Lib.IntTypes.SEC, equality_tok_Lib.IntTypes.S16@tok, equality_tok_Lib.IntTypes.S32@tok, equality_tok_Lib.IntTypes.SEC@tok, equation_Lib.IntTypes.bits, equation_Lib.IntTypes.range, equation_Lib.IntTypes.signed, equation_Lib.IntTypes.unsigned, equation_Lib.IntTypes.v, equation_Prims.nat, equation_Prims.pos, equation_Spec.Kyber2.Params.params_q, int_inversion, int_typing, lemma_FStar.UInt.pow2_values, primitive_Prims.op_Addition, primitive_Prims.op_Division, primitive_Prims.op_LessThanOrEqual, primitive_Prims.op_Minus, primitive_Prims.op_Multiply, primitive_Prims.op_Subtraction, projection_inverse_BoxBool_proj_0, projection_inverse_BoxInt_proj_0, refinement_interpretation_Tm_refine_2b320913041b873fce938dd17eebb3e2, refinement_interpretation_Tm_refine_542f9d4f129664613f2483a6c88bc7c2, refinement_interpretation_Tm_refine_774ba3f728d91ead8ef40be66c9802e5, refinement_interpretation_Tm_refine_83845a86f2550cdf941eeb1d9b59602b, refinement_interpretation_Tm_refine_9d3fd79fd314167f1a9c213a188da3ec, refinement_interpretation_Tm_refine_b2401a8cabe2f9a01538f32548fa9f6c, typing_Lib.IntTypes.mk_int, typing_Prims.pow2, typing_tok_Lib.IntTypes.S32@tok, typing_tok_Lib.IntTypes.SEC@tok

;;; End module FStar.Int (560 decls; total size 30276)

;;; Start module FStar.UInt32

; <Start encoding FStar.UInt32.n>

(declare-fun FStar.UInt32.n (Dummy_sort) Term)

; </end encoding FStar.UInt32.n>


; <Skipped />


; <Start encoding FStar.UInt32.t>

(declare-fun FStar.UInt32.t () Term)

; </end encoding FStar.UInt32.t>


; <Start encoding FStar.UInt32.t__uu___haseq>


; </end encoding FStar.UInt32.t__uu___haseq>


; <Start encoding FStar.UInt32.v>

(declare-fun FStar.UInt32.v (Term) Term)
(declare-fun Tm_arrow_219d5e0e810e802cfa8e7d2fb16580c2 () Term)
(declare-fun FStar.UInt32.v@tok () Term)

; </end encoding FStar.UInt32.v>


; <Start encoding FStar.UInt32.uint_to_t>

(declare-fun FStar.UInt32.uint_to_t (Term) Term)
(declare-fun Tm_refine_c6c18a7ceb46d419c35ff8551117551e (Term) Term)
(declare-fun Tm_arrow_ec7cf9dff916b205e18518817f39e96d () Term)
(declare-fun FStar.UInt32.uint_to_t@tok () Term)


; </end encoding FStar.UInt32.uint_to_t>


; <Start encoding FStar.UInt32.uv_inv>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.UInt32.uv_inv (Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.UInt32.uv_inv@tok () Term)

; </end encoding FStar.UInt32.uv_inv>


; <Start encoding FStar.UInt32.vu_inv>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.UInt32.vu_inv (Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.UInt32.vu_inv@tok () Term)

; </end encoding FStar.UInt32.vu_inv>


; <Start encoding FStar.UInt32.v_inj>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.UInt32.v_inj (Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.UInt32.v_inj@tok () Term)

; </end encoding FStar.UInt32.v_inj>


; <Start encoding FStar.UInt32.add>

(declare-fun FStar.UInt32.add (Term Term) Term)
(declare-fun Tm_refine_096dcb399122345db27f37346c43e5dc (Term Term) Term)
(declare-fun Tm_arrow_040490d106ead2075bba6e5e3ed2e20a () Term)
(declare-fun FStar.UInt32.add@tok () Term)


; </end encoding FStar.UInt32.add>


; <Start encoding FStar.UInt32.add_underspec>

(declare-fun FStar.UInt32.add_underspec (Term Term) Term)
(declare-fun Tm_refine_0948310bc3bc5573bd426e513ac1cb96 (Term Term) Term)
(declare-fun Tm_arrow_3c55a6e3148d87247d503fae1495c170 () Term)
(declare-fun FStar.UInt32.add_underspec@tok () Term)


; </end encoding FStar.UInt32.add_underspec>


; <Start encoding FStar.UInt32.add_mod>

(declare-fun FStar.UInt32.add_mod (Term Term) Term)
(declare-fun Tm_refine_d60a0e9fdf52cedb444de54cc40036f8 (Term Term) Term)
(declare-fun Tm_arrow_cf72fc55ad9e1407e5894cde5ad8c9cd () Term)
(declare-fun FStar.UInt32.add_mod@tok () Term)


; </end encoding FStar.UInt32.add_mod>


; <Start encoding FStar.UInt32.sub>

(declare-fun FStar.UInt32.sub (Term Term) Term)
(declare-fun Tm_refine_ff3f214a1d72a8cdeaa968f7e92cedb4 (Term Term) Term)
(declare-fun Tm_arrow_cfdc2f66c08010ba75665e03ac3b27bc () Term)
(declare-fun FStar.UInt32.sub@tok () Term)


; </end encoding FStar.UInt32.sub>


; <Start encoding FStar.UInt32.sub_underspec>

(declare-fun FStar.UInt32.sub_underspec (Term Term) Term)
(declare-fun Tm_refine_ee2f0081b4e0356cdca6b63849127123 (Term Term) Term)
(declare-fun Tm_arrow_4787d92cfcb24a2c32d1f36796221e4e () Term)
(declare-fun FStar.UInt32.sub_underspec@tok () Term)


; </end encoding FStar.UInt32.sub_underspec>


; <Start encoding FStar.UInt32.sub_mod>

(declare-fun FStar.UInt32.sub_mod (Term Term) Term)
(declare-fun Tm_refine_2a3f39dfb4b954af155535c2a844d9ba (Term Term) Term)
(declare-fun Tm_arrow_14de785d22ca0e03881246090daa454d () Term)
(declare-fun FStar.UInt32.sub_mod@tok () Term)


; </end encoding FStar.UInt32.sub_mod>


; <Start encoding FStar.UInt32.mul>

(declare-fun FStar.UInt32.mul (Term Term) Term)
(declare-fun Tm_refine_6e61a5aae0540cf06a76daaa4d96339e (Term Term) Term)
(declare-fun Tm_arrow_fb5213fefc2e47f64471b9464149b808 () Term)
(declare-fun FStar.UInt32.mul@tok () Term)


; </end encoding FStar.UInt32.mul>


; <Start encoding FStar.UInt32.mul_underspec>

(declare-fun FStar.UInt32.mul_underspec (Term Term) Term)
(declare-fun Tm_refine_32e7f394e10ae3c5548067363c93ee28 (Term Term) Term)
(declare-fun Tm_arrow_27f1d957947d834468a6d3b10edc9171 () Term)
(declare-fun FStar.UInt32.mul_underspec@tok () Term)


; </end encoding FStar.UInt32.mul_underspec>


; <Start encoding FStar.UInt32.mul_mod>

(declare-fun FStar.UInt32.mul_mod (Term Term) Term)
(declare-fun Tm_refine_d5119ca5e7966f38ff77bad57945fbf2 (Term Term) Term)
(declare-fun Tm_arrow_9568fb967057008227f9ffd8f794844e () Term)
(declare-fun FStar.UInt32.mul_mod@tok () Term)


; </end encoding FStar.UInt32.mul_mod>


; <Start encoding FStar.UInt32.mul_div>

(declare-fun FStar.UInt32.mul_div (Term Term) Term)
(declare-fun Tm_refine_a4df7a251328ab1f2b2017dc220ac8cb (Term Term) Term)
(declare-fun Tm_arrow_9a8f03bbe7bfc9e48d69bc4d89e26eed () Term)
(declare-fun FStar.UInt32.mul_div@tok () Term)


; </end encoding FStar.UInt32.mul_div>


; <Start encoding FStar.UInt32.div>

(declare-fun Tm_refine_b02cf3d55abd63ea23bf833f942d6299 () Term)
(declare-fun FStar.UInt32.div (Term Term) Term)

(declare-fun Tm_refine_1018cc4a30bb4b3362dcecc401c070c5 (Term Term) Term)
(declare-fun Tm_arrow_43f0120fecc423169c6b28d9ad404662 () Term)
(declare-fun FStar.UInt32.div@tok () Term)


; </end encoding FStar.UInt32.div>


; <Start encoding FStar.UInt32.rem>


(declare-fun FStar.UInt32.rem (Term Term) Term)

(declare-fun Tm_refine_e40be42e98d01ee187ff0dfc002ad3da (Term Term) Term)
(declare-fun Tm_arrow_71a16560a0f81250f86712f168218e5d () Term)
(declare-fun FStar.UInt32.rem@tok () Term)


; </end encoding FStar.UInt32.rem>


; <Start encoding FStar.UInt32.logand>

(declare-fun FStar.UInt32.logand (Term Term) Term)
(declare-fun Tm_refine_a05ce860d46b15ee9038827af643923f (Term Term) Term)
(declare-fun Tm_arrow_746881170d68e053af8b855aa175bd59 () Term)
(declare-fun FStar.UInt32.logand@tok () Term)


; </end encoding FStar.UInt32.logand>


; <Start encoding FStar.UInt32.logxor>

(declare-fun FStar.UInt32.logxor (Term Term) Term)
(declare-fun Tm_refine_5832d6d16f396f7384e995f62e5de8fe (Term Term) Term)
(declare-fun Tm_arrow_a2056e2411df023777c3c1c8d85d27d3 () Term)
(declare-fun FStar.UInt32.logxor@tok () Term)


; </end encoding FStar.UInt32.logxor>


; <Start encoding FStar.UInt32.logor>

(declare-fun FStar.UInt32.logor (Term Term) Term)
(declare-fun Tm_refine_5d63bca2b179f7c8dafc73a641654218 (Term Term) Term)
(declare-fun Tm_arrow_d846db6f5cf16e09eccacdc929243f49 () Term)
(declare-fun FStar.UInt32.logor@tok () Term)


; </end encoding FStar.UInt32.logor>


; <Start encoding FStar.UInt32.lognot>

(declare-fun FStar.UInt32.lognot (Term) Term)
(declare-fun Tm_refine_a1bbfa63ab5b2731512874b4d2054ec7 (Term) Term)
(declare-fun Tm_arrow_f2ed57ee30f72f1f498fdcc5645ce419 () Term)
(declare-fun FStar.UInt32.lognot@tok () Term)


; </end encoding FStar.UInt32.lognot>


; <Start encoding FStar.UInt32.shift_right>

(declare-fun FStar.UInt32.shift_right (Term Term) Term)
(declare-fun Tm_refine_5889240f9f8d3c40d2814513fdc3fa57 (Term Term) Term)
(declare-fun Tm_arrow_3672e248b13705589d352a152751a93e () Term)
(declare-fun FStar.UInt32.shift_right@tok () Term)


; </end encoding FStar.UInt32.shift_right>


; <Start encoding FStar.UInt32.shift_left>

(declare-fun FStar.UInt32.shift_left (Term Term) Term)
(declare-fun Tm_refine_f2500b163dd1b8f868ae8b1a482713b2 (Term Term) Term)
(declare-fun Tm_arrow_4dc5343ea2db6551e560da99a84b9234 () Term)
(declare-fun FStar.UInt32.shift_left@tok () Term)


; </end encoding FStar.UInt32.shift_left>


; <Start encoding FStar.UInt32.eq>

(declare-fun FStar.UInt32.eq (Term Term) Term)
(declare-fun Tm_arrow_d139ed063ff47e81b14768e0d0c96acf () Term)
(declare-fun FStar.UInt32.eq@tok () Term)

; </end encoding FStar.UInt32.eq>


; <Start encoding FStar.UInt32.gt>

(declare-fun FStar.UInt32.gt (Term Term) Term)

(declare-fun FStar.UInt32.gt@tok () Term)

; </end encoding FStar.UInt32.gt>


; <Start encoding FStar.UInt32.gte>

(declare-fun FStar.UInt32.gte (Term Term) Term)

(declare-fun FStar.UInt32.gte@tok () Term)

; </end encoding FStar.UInt32.gte>


; <Start encoding FStar.UInt32.lt>

(declare-fun FStar.UInt32.lt (Term Term) Term)

(declare-fun FStar.UInt32.lt@tok () Term)

; </end encoding FStar.UInt32.lt>


; <Start encoding FStar.UInt32.lte>

(declare-fun FStar.UInt32.lte (Term Term) Term)

(declare-fun FStar.UInt32.lte@tok () Term)

; </end encoding FStar.UInt32.lte>


; <Start encoding FStar.UInt32.minus>

(declare-fun FStar.UInt32.minus (Term) Term)
(declare-fun Tm_arrow_bef642717d0305779f143055e945e0c3 () Term)
(declare-fun FStar.UInt32.minus@tok () Term)

; </end encoding FStar.UInt32.minus>


; <Start encoding FStar.UInt32.n_minus_one>

(declare-fun FStar.UInt32.n_minus_one (Dummy_sort) Term)

; </end encoding FStar.UInt32.n_minus_one>


; <Skipped />


; <Start encoding FStar.UInt32.eq_mask>

(declare-fun FStar.UInt32.eq_mask (Term Term) Term)
(declare-fun Tm_refine_15ac668aef507acaa7200ca30c7f5ade (Term Term) Term)
(declare-fun Tm_arrow_0b0c5e4aa1062d15c61b583843f060e3 () Term)
(declare-fun FStar.UInt32.eq_mask@tok () Term)


; </end encoding FStar.UInt32.eq_mask>


; <Start encoding FStar.UInt32.lemma_sub_msbs>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.UInt32.lemma_sub_msbs (Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.UInt32.lemma_sub_msbs@tok () Term)

; </end encoding FStar.UInt32.lemma_sub_msbs>


; <Start encoding FStar.UInt32.gte_mask>

(declare-fun FStar.UInt32.gte_mask (Term Term) Term)
(declare-fun Tm_refine_1e1ed4f35d387c4b7039c6ad866c76f9 (Term Term) Term)
(declare-fun Tm_arrow_e65e74c0e5c1b17b0a5e1601d146b873 () Term)
(declare-fun FStar.UInt32.gte_mask@tok () Term)


; </end encoding FStar.UInt32.gte_mask>


; <Skipped />


; <Start encoding FStar.UInt32.op_Plus_Hat>

(declare-fun FStar.UInt32.op_Plus_Hat (Term Term) Term)


(declare-fun FStar.UInt32.op_Plus_Hat@tok () Term)


; </end encoding FStar.UInt32.op_Plus_Hat>


; <Start encoding FStar.UInt32.op_Plus_Question_Hat>

(declare-fun FStar.UInt32.op_Plus_Question_Hat (Term Term) Term)


(declare-fun FStar.UInt32.op_Plus_Question_Hat@tok () Term)


; </end encoding FStar.UInt32.op_Plus_Question_Hat>


; <Start encoding FStar.UInt32.op_Plus_Percent_Hat>

(declare-fun FStar.UInt32.op_Plus_Percent_Hat (Term Term) Term)


(declare-fun FStar.UInt32.op_Plus_Percent_Hat@tok () Term)


; </end encoding FStar.UInt32.op_Plus_Percent_Hat>


; <Start encoding FStar.UInt32.op_Subtraction_Hat>

(declare-fun FStar.UInt32.op_Subtraction_Hat (Term Term) Term)


(declare-fun FStar.UInt32.op_Subtraction_Hat@tok () Term)


; </end encoding FStar.UInt32.op_Subtraction_Hat>


; <Start encoding FStar.UInt32.op_Subtraction_Question_Hat>

(declare-fun FStar.UInt32.op_Subtraction_Question_Hat (Term Term) Term)


(declare-fun FStar.UInt32.op_Subtraction_Question_Hat@tok () Term)


; </end encoding FStar.UInt32.op_Subtraction_Question_Hat>


; <Start encoding FStar.UInt32.op_Subtraction_Percent_Hat>

(declare-fun FStar.UInt32.op_Subtraction_Percent_Hat (Term Term) Term)


(declare-fun FStar.UInt32.op_Subtraction_Percent_Hat@tok () Term)


; </end encoding FStar.UInt32.op_Subtraction_Percent_Hat>


; <Start encoding FStar.UInt32.op_Star_Hat>

(declare-fun FStar.UInt32.op_Star_Hat (Term Term) Term)


(declare-fun FStar.UInt32.op_Star_Hat@tok () Term)


; </end encoding FStar.UInt32.op_Star_Hat>


; <Start encoding FStar.UInt32.op_Star_Question_Hat>

(declare-fun FStar.UInt32.op_Star_Question_Hat (Term Term) Term)


(declare-fun FStar.UInt32.op_Star_Question_Hat@tok () Term)


; </end encoding FStar.UInt32.op_Star_Question_Hat>


; <Start encoding FStar.UInt32.op_Star_Percent_Hat>

(declare-fun FStar.UInt32.op_Star_Percent_Hat (Term Term) Term)


(declare-fun FStar.UInt32.op_Star_Percent_Hat@tok () Term)


; </end encoding FStar.UInt32.op_Star_Percent_Hat>


; <Start encoding FStar.UInt32.op_Star_Slash_Hat>

(declare-fun FStar.UInt32.op_Star_Slash_Hat (Term Term) Term)


(declare-fun FStar.UInt32.op_Star_Slash_Hat@tok () Term)


; </end encoding FStar.UInt32.op_Star_Slash_Hat>


; <Start encoding FStar.UInt32.op_Slash_Hat>


(declare-fun FStar.UInt32.op_Slash_Hat (Term Term) Term)



(declare-fun FStar.UInt32.op_Slash_Hat@tok () Term)



; </end encoding FStar.UInt32.op_Slash_Hat>


; <Start encoding FStar.UInt32.op_Percent_Hat>


(declare-fun FStar.UInt32.op_Percent_Hat (Term Term) Term)



(declare-fun FStar.UInt32.op_Percent_Hat@tok () Term)



; </end encoding FStar.UInt32.op_Percent_Hat>


; <Start encoding FStar.UInt32.op_Hat_Hat>

(declare-fun FStar.UInt32.op_Hat_Hat (Term Term) Term)


(declare-fun FStar.UInt32.op_Hat_Hat@tok () Term)


; </end encoding FStar.UInt32.op_Hat_Hat>


; <Start encoding FStar.UInt32.op_Amp_Hat>

(declare-fun FStar.UInt32.op_Amp_Hat (Term Term) Term)


(declare-fun FStar.UInt32.op_Amp_Hat@tok () Term)


; </end encoding FStar.UInt32.op_Amp_Hat>


; <Start encoding FStar.UInt32.op_Bar_Hat>

(declare-fun FStar.UInt32.op_Bar_Hat (Term Term) Term)


(declare-fun FStar.UInt32.op_Bar_Hat@tok () Term)


; </end encoding FStar.UInt32.op_Bar_Hat>


; <Start encoding FStar.UInt32.op_Less_Less_Hat>

(declare-fun FStar.UInt32.op_Less_Less_Hat (Term Term) Term)


(declare-fun FStar.UInt32.op_Less_Less_Hat@tok () Term)


; </end encoding FStar.UInt32.op_Less_Less_Hat>


; <Start encoding FStar.UInt32.op_Greater_Greater_Hat>

(declare-fun FStar.UInt32.op_Greater_Greater_Hat (Term Term) Term)


(declare-fun FStar.UInt32.op_Greater_Greater_Hat@tok () Term)


; </end encoding FStar.UInt32.op_Greater_Greater_Hat>


; <Start encoding FStar.UInt32.op_Equals_Hat>

(declare-fun FStar.UInt32.op_Equals_Hat (Term Term) Term)

(declare-fun FStar.UInt32.op_Equals_Hat@tok () Term)

; </end encoding FStar.UInt32.op_Equals_Hat>


; <Start encoding FStar.UInt32.op_Greater_Hat>

(declare-fun FStar.UInt32.op_Greater_Hat (Term Term) Term)

(declare-fun FStar.UInt32.op_Greater_Hat@tok () Term)

; </end encoding FStar.UInt32.op_Greater_Hat>


; <Start encoding FStar.UInt32.op_Greater_Equals_Hat>

(declare-fun FStar.UInt32.op_Greater_Equals_Hat (Term Term) Term)

(declare-fun FStar.UInt32.op_Greater_Equals_Hat@tok () Term)

; </end encoding FStar.UInt32.op_Greater_Equals_Hat>


; <Start encoding FStar.UInt32.op_Less_Hat>

(declare-fun FStar.UInt32.op_Less_Hat (Term Term) Term)

(declare-fun FStar.UInt32.op_Less_Hat@tok () Term)

; </end encoding FStar.UInt32.op_Less_Hat>


; <Start encoding FStar.UInt32.op_Less_Equals_Hat>

(declare-fun FStar.UInt32.op_Less_Equals_Hat (Term Term) Term)

(declare-fun FStar.UInt32.op_Less_Equals_Hat@tok () Term)

; </end encoding FStar.UInt32.op_Less_Equals_Hat>


; <Start encoding FStar.UInt32.to_string>

(declare-fun FStar.UInt32.to_string (Term) Term)
(declare-fun Tm_arrow_f55251be2a5b7c14c15f08fca4ab0680 () Term)
(declare-fun FStar.UInt32.to_string@tok () Term)

; </end encoding FStar.UInt32.to_string>


; <Start encoding FStar.UInt32.of_string>

(declare-fun FStar.UInt32.of_string (Term) Term)
(declare-fun Tm_arrow_6de8d3358b41960ff524d2846484ac06 () Term)
(declare-fun FStar.UInt32.of_string@tok () Term)

; </end encoding FStar.UInt32.of_string>


; <Skipped />


; <Start encoding FStar.UInt32.__uint_to_t>

(declare-fun FStar.UInt32.__uint_to_t (Term) Term)
(declare-fun Tm_arrow_19947841a93fc097508ab70d5f4f5872 () Term)
(declare-fun FStar.UInt32.__uint_to_t@tok () Term)

; </end encoding FStar.UInt32.__uint_to_t>


; <Skipped />


; UNSAT CORE: @MaxFuel_assumption, @MaxIFuel_assumption, @fuel_correspondence_Prims.pow2.fuel_instrumented, @query, constructor_distinct_Lib.IntTypes.S16, constructor_distinct_Lib.IntTypes.S32, constructor_distinct_Lib.IntTypes.SEC, equality_tok_Lib.IntTypes.S16@tok, equality_tok_Lib.IntTypes.S32@tok, equality_tok_Lib.IntTypes.SEC@tok, equation_Lib.IntTypes.bits, equation_Lib.IntTypes.range, equation_Lib.IntTypes.signed, equation_Lib.IntTypes.unsigned, equation_Lib.IntTypes.v, equation_Prims.nat, equation_Prims.pos, equation_Spec.Kyber2.Params.params_q, int_inversion, int_typing, lemma_FStar.UInt.pow2_values, primitive_Prims.op_Addition, primitive_Prims.op_Division, primitive_Prims.op_LessThanOrEqual, primitive_Prims.op_Minus, primitive_Prims.op_Multiply, primitive_Prims.op_Subtraction, projection_inverse_BoxBool_proj_0, projection_inverse_BoxInt_proj_0, refinement_interpretation_Tm_refine_2b320913041b873fce938dd17eebb3e2, refinement_interpretation_Tm_refine_542f9d4f129664613f2483a6c88bc7c2, refinement_interpretation_Tm_refine_774ba3f728d91ead8ef40be66c9802e5, refinement_interpretation_Tm_refine_83845a86f2550cdf941eeb1d9b59602b, refinement_interpretation_Tm_refine_9d3fd79fd314167f1a9c213a188da3ec, refinement_interpretation_Tm_refine_b2401a8cabe2f9a01538f32548fa9f6c, typing_Lib.IntTypes.mk_int, typing_Prims.pow2, typing_tok_Lib.IntTypes.S32@tok, typing_tok_Lib.IntTypes.SEC@tok

;;; End module FStar.UInt32 (384 decls; total size 16941)

;;; Start module FStar.Int64

; <Start encoding FStar.Int64.n>

(declare-fun FStar.Int64.n (Dummy_sort) Term)

; </end encoding FStar.Int64.n>


; <Skipped />


; <Start encoding FStar.Int64.t>

(declare-fun FStar.Int64.t () Term)

; </end encoding FStar.Int64.t>


; <Start encoding FStar.Int64.t__uu___haseq>


; </end encoding FStar.Int64.t__uu___haseq>


; <Start encoding FStar.Int64.v>

(declare-fun FStar.Int64.v (Term) Term)
(declare-fun Tm_arrow_99ffa6f801d96e52b029955d85524582 () Term)
(declare-fun FStar.Int64.v@tok () Term)

; </end encoding FStar.Int64.v>


; <Start encoding FStar.Int64.int_to_t>

(declare-fun FStar.Int64.int_to_t (Term) Term)
(declare-fun Tm_refine_07d1d95240c432423a75b64d7bf03bac (Term) Term)
(declare-fun Tm_arrow_65de80b310ba49a91e99d12631918b62 () Term)
(declare-fun FStar.Int64.int_to_t@tok () Term)


; </end encoding FStar.Int64.int_to_t>


; <Start encoding FStar.Int64.uv_inv>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.Int64.uv_inv (Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.Int64.uv_inv@tok () Term)

; </end encoding FStar.Int64.uv_inv>


; <Start encoding FStar.Int64.vu_inv>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.Int64.vu_inv (Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.Int64.vu_inv@tok () Term)

; </end encoding FStar.Int64.vu_inv>


; <Start encoding FStar.Int64.v_inj>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.Int64.v_inj (Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.Int64.v_inj@tok () Term)

; </end encoding FStar.Int64.v_inj>


; <Start encoding FStar.Int64.add>

(declare-fun FStar.Int64.add (Term Term) Term)
(declare-fun Tm_refine_fe879916637a9365394f804132c6e7c5 (Term Term) Term)
(declare-fun Tm_arrow_ab808ef6ff8d4ffbbfd33d77c7118dd3 () Term)
(declare-fun FStar.Int64.add@tok () Term)


; </end encoding FStar.Int64.add>


; <Start encoding FStar.Int64.sub>

(declare-fun FStar.Int64.sub (Term Term) Term)
(declare-fun Tm_refine_86f843de1aa7faa442cbe17d43e88730 (Term Term) Term)
(declare-fun Tm_arrow_ec5b7a309eceb0604158920d3b4598dd () Term)
(declare-fun FStar.Int64.sub@tok () Term)


; </end encoding FStar.Int64.sub>


; <Start encoding FStar.Int64.mul>

(declare-fun FStar.Int64.mul (Term Term) Term)
(declare-fun Tm_refine_13d473b0edba072862fadd749639d79c (Term Term) Term)
(declare-fun Tm_arrow_bb055cef211ada4907b9b1a67f240414 () Term)
(declare-fun FStar.Int64.mul@tok () Term)


; </end encoding FStar.Int64.mul>


; <Start encoding FStar.Int64.div>

(declare-fun Tm_refine_75ea66a4c13dd935112a33955b38a921 () Term)
(declare-fun FStar.Int64.div (Term Term) Term)

(declare-fun Tm_refine_cfc7028e5beeeeab9bc67959c84e0985 (Term Term) Term)
(declare-fun Tm_arrow_dc665082987f183d2cc37ed3af084c97 () Term)
(declare-fun FStar.Int64.div@tok () Term)


; </end encoding FStar.Int64.div>


; <Start encoding FStar.Int64.rem>


(declare-fun FStar.Int64.rem (Term Term) Term)

(declare-fun Tm_refine_1fcb2ca0743eff2bfc4d1cf373fd0178 (Term Term) Term)
(declare-fun Tm_arrow_888fd449e3ab39046fdc887337012dfd () Term)
(declare-fun FStar.Int64.rem@tok () Term)


; </end encoding FStar.Int64.rem>


; <Start encoding FStar.Int64.logand>

(declare-fun FStar.Int64.logand (Term Term) Term)
(declare-fun Tm_refine_668d666188ba591f930e047419951069 (Term Term) Term)
(declare-fun Tm_arrow_6aaef2a998c6bdad2c0766cd7cd90242 () Term)
(declare-fun FStar.Int64.logand@tok () Term)


; </end encoding FStar.Int64.logand>


; <Start encoding FStar.Int64.logxor>

(declare-fun FStar.Int64.logxor (Term Term) Term)
(declare-fun Tm_refine_b33cdfc1dac4c7a5cd60701f04f7c86a (Term Term) Term)
(declare-fun Tm_arrow_f3db63f72bd6b300d3d9f16bcf4d3704 () Term)
(declare-fun FStar.Int64.logxor@tok () Term)


; </end encoding FStar.Int64.logxor>


; <Start encoding FStar.Int64.logor>

(declare-fun FStar.Int64.logor (Term Term) Term)
(declare-fun Tm_refine_c411639d0032b5372deeba1ba526ef5b (Term Term) Term)
(declare-fun Tm_arrow_79896b6e2984250273904bc9a9476de8 () Term)
(declare-fun FStar.Int64.logor@tok () Term)


; </end encoding FStar.Int64.logor>


; <Start encoding FStar.Int64.lognot>

(declare-fun FStar.Int64.lognot (Term) Term)
(declare-fun Tm_refine_cf5846dcd1540dac86c7b2185704d7b9 (Term) Term)
(declare-fun Tm_arrow_54b2804539b3024eadbd497bdfcab536 () Term)
(declare-fun FStar.Int64.lognot@tok () Term)


; </end encoding FStar.Int64.lognot>


; <Start encoding FStar.Int64.shift_right>

(declare-fun FStar.Int64.shift_right (Term Term) Term)
(declare-fun Tm_refine_6084e9428d88ecb71ce9c919c921c102 (Term Term) Term)
(declare-fun Tm_arrow_8c3d9a1d24ed970123ef96818226a211 () Term)
(declare-fun FStar.Int64.shift_right@tok () Term)


; </end encoding FStar.Int64.shift_right>


; <Start encoding FStar.Int64.shift_left>

(declare-fun FStar.Int64.shift_left (Term Term) Term)
(declare-fun Tm_refine_4e38db6b4d75bc46ff366c28b7136334 (Term Term) Term)
(declare-fun Tm_arrow_58d918d412dbfe9a2c6501179c5ee7bb () Term)
(declare-fun FStar.Int64.shift_left@tok () Term)


; </end encoding FStar.Int64.shift_left>


; <Start encoding FStar.Int64.shift_arithmetic_right>

(declare-fun FStar.Int64.shift_arithmetic_right (Term Term) Term)
(declare-fun Tm_refine_1a9c7d0d3bfda7c5600b8c99183ba043 (Term Term) Term)
(declare-fun Tm_arrow_3b82af9fea740d75be909e5f0ef1bade () Term)
(declare-fun FStar.Int64.shift_arithmetic_right@tok () Term)


; </end encoding FStar.Int64.shift_arithmetic_right>


; <Start encoding FStar.Int64.eq>

(declare-fun FStar.Int64.eq (Term Term) Term)
(declare-fun Tm_arrow_26633add8f221891ddf0e5ce52555c32 () Term)
(declare-fun FStar.Int64.eq@tok () Term)

; </end encoding FStar.Int64.eq>


; <Start encoding FStar.Int64.gt>

(declare-fun FStar.Int64.gt (Term Term) Term)

(declare-fun FStar.Int64.gt@tok () Term)

; </end encoding FStar.Int64.gt>


; <Start encoding FStar.Int64.gte>

(declare-fun FStar.Int64.gte (Term Term) Term)

(declare-fun FStar.Int64.gte@tok () Term)

; </end encoding FStar.Int64.gte>


; <Start encoding FStar.Int64.lt>

(declare-fun FStar.Int64.lt (Term Term) Term)

(declare-fun FStar.Int64.lt@tok () Term)

; </end encoding FStar.Int64.lt>


; <Start encoding FStar.Int64.lte>

(declare-fun FStar.Int64.lte (Term Term) Term)

(declare-fun FStar.Int64.lte@tok () Term)

; </end encoding FStar.Int64.lte>


; <Start encoding FStar.Int64.op_Plus_Hat>

(declare-fun FStar.Int64.op_Plus_Hat (Term Term) Term)


(declare-fun FStar.Int64.op_Plus_Hat@tok () Term)


; </end encoding FStar.Int64.op_Plus_Hat>


; <Start encoding FStar.Int64.op_Subtraction_Hat>

(declare-fun FStar.Int64.op_Subtraction_Hat (Term Term) Term)


(declare-fun FStar.Int64.op_Subtraction_Hat@tok () Term)


; </end encoding FStar.Int64.op_Subtraction_Hat>


; <Start encoding FStar.Int64.op_Star_Hat>

(declare-fun FStar.Int64.op_Star_Hat (Term Term) Term)


(declare-fun FStar.Int64.op_Star_Hat@tok () Term)


; </end encoding FStar.Int64.op_Star_Hat>


; <Start encoding FStar.Int64.op_Slash_Hat>


(declare-fun FStar.Int64.op_Slash_Hat (Term Term) Term)



(declare-fun FStar.Int64.op_Slash_Hat@tok () Term)



; </end encoding FStar.Int64.op_Slash_Hat>


; <Start encoding FStar.Int64.op_Percent_Hat>


(declare-fun FStar.Int64.op_Percent_Hat (Term Term) Term)



(declare-fun FStar.Int64.op_Percent_Hat@tok () Term)



; </end encoding FStar.Int64.op_Percent_Hat>


; <Start encoding FStar.Int64.op_Hat_Hat>

(declare-fun FStar.Int64.op_Hat_Hat (Term Term) Term)


(declare-fun FStar.Int64.op_Hat_Hat@tok () Term)


; </end encoding FStar.Int64.op_Hat_Hat>


; <Start encoding FStar.Int64.op_Amp_Hat>

(declare-fun FStar.Int64.op_Amp_Hat (Term Term) Term)


(declare-fun FStar.Int64.op_Amp_Hat@tok () Term)


; </end encoding FStar.Int64.op_Amp_Hat>


; <Start encoding FStar.Int64.op_Bar_Hat>

(declare-fun FStar.Int64.op_Bar_Hat (Term Term) Term)


(declare-fun FStar.Int64.op_Bar_Hat@tok () Term)


; </end encoding FStar.Int64.op_Bar_Hat>


; <Start encoding FStar.Int64.op_Less_Less_Hat>

(declare-fun FStar.Int64.op_Less_Less_Hat (Term Term) Term)


(declare-fun FStar.Int64.op_Less_Less_Hat@tok () Term)


; </end encoding FStar.Int64.op_Less_Less_Hat>


; <Start encoding FStar.Int64.op_Greater_Greater_Hat>

(declare-fun FStar.Int64.op_Greater_Greater_Hat (Term Term) Term)


(declare-fun FStar.Int64.op_Greater_Greater_Hat@tok () Term)


; </end encoding FStar.Int64.op_Greater_Greater_Hat>


; <Start encoding FStar.Int64.op_Greater_Greater_Greater_Hat>

(declare-fun FStar.Int64.op_Greater_Greater_Greater_Hat (Term Term) Term)


(declare-fun FStar.Int64.op_Greater_Greater_Greater_Hat@tok () Term)


; </end encoding FStar.Int64.op_Greater_Greater_Greater_Hat>


; <Start encoding FStar.Int64.op_Equals_Hat>

(declare-fun FStar.Int64.op_Equals_Hat (Term Term) Term)

(declare-fun FStar.Int64.op_Equals_Hat@tok () Term)

; </end encoding FStar.Int64.op_Equals_Hat>


; <Start encoding FStar.Int64.op_Greater_Hat>

(declare-fun FStar.Int64.op_Greater_Hat (Term Term) Term)

(declare-fun FStar.Int64.op_Greater_Hat@tok () Term)

; </end encoding FStar.Int64.op_Greater_Hat>


; <Start encoding FStar.Int64.op_Greater_Equals_Hat>

(declare-fun FStar.Int64.op_Greater_Equals_Hat (Term Term) Term)

(declare-fun FStar.Int64.op_Greater_Equals_Hat@tok () Term)

; </end encoding FStar.Int64.op_Greater_Equals_Hat>


; <Start encoding FStar.Int64.op_Less_Hat>

(declare-fun FStar.Int64.op_Less_Hat (Term Term) Term)

(declare-fun FStar.Int64.op_Less_Hat@tok () Term)

; </end encoding FStar.Int64.op_Less_Hat>


; <Start encoding FStar.Int64.op_Less_Equals_Hat>

(declare-fun FStar.Int64.op_Less_Equals_Hat (Term Term) Term)

(declare-fun FStar.Int64.op_Less_Equals_Hat@tok () Term)

; </end encoding FStar.Int64.op_Less_Equals_Hat>


; <Start encoding FStar.Int64.ct_abs>

(declare-fun Tm_refine_5678793836319ee26b16152f1eac0ca7 () Term)
(declare-fun FStar.Int64.ct_abs (Term) Term)

(declare-fun Tm_refine_fa246244243db4a2048d8db1827bec1d (Term) Term)
(declare-fun Tm_arrow_74937700ab43afea8cf7413e699a024a () Term)
(declare-fun FStar.Int64.ct_abs@tok () Term)



; </end encoding FStar.Int64.ct_abs>


; <Start encoding FStar.Int64.to_string>

(declare-fun FStar.Int64.to_string (Term) Term)
(declare-fun Tm_arrow_12e115acbb746e5a879100910c4a8c10 () Term)
(declare-fun FStar.Int64.to_string@tok () Term)

; </end encoding FStar.Int64.to_string>


; <Start encoding FStar.Int64.of_string>

(declare-fun FStar.Int64.of_string (Term) Term)
(declare-fun Tm_arrow_6710131d46f26d8c532544e216f8757c () Term)
(declare-fun FStar.Int64.of_string@tok () Term)

; </end encoding FStar.Int64.of_string>


; <Skipped />


; <Start encoding FStar.Int64.__int_to_t>

(declare-fun FStar.Int64.__int_to_t (Term) Term)
(declare-fun Tm_arrow_c93c4bb0af6de20b584d3a05faa17e72 () Term)
(declare-fun FStar.Int64.__int_to_t@tok () Term)

; </end encoding FStar.Int64.__int_to_t>


; <Skipped />


; UNSAT CORE: @MaxFuel_assumption, @MaxIFuel_assumption, @fuel_correspondence_Prims.pow2.fuel_instrumented, @query, constructor_distinct_Lib.IntTypes.S16, constructor_distinct_Lib.IntTypes.S32, constructor_distinct_Lib.IntTypes.SEC, equality_tok_Lib.IntTypes.S16@tok, equality_tok_Lib.IntTypes.S32@tok, equality_tok_Lib.IntTypes.SEC@tok, equation_Lib.IntTypes.bits, equation_Lib.IntTypes.range, equation_Lib.IntTypes.signed, equation_Lib.IntTypes.unsigned, equation_Lib.IntTypes.v, equation_Prims.nat, equation_Prims.pos, equation_Spec.Kyber2.Params.params_q, int_inversion, int_typing, lemma_FStar.UInt.pow2_values, primitive_Prims.op_Addition, primitive_Prims.op_Division, primitive_Prims.op_LessThanOrEqual, primitive_Prims.op_Minus, primitive_Prims.op_Multiply, primitive_Prims.op_Subtraction, projection_inverse_BoxBool_proj_0, projection_inverse_BoxInt_proj_0, refinement_interpretation_Tm_refine_2b320913041b873fce938dd17eebb3e2, refinement_interpretation_Tm_refine_542f9d4f129664613f2483a6c88bc7c2, refinement_interpretation_Tm_refine_774ba3f728d91ead8ef40be66c9802e5, refinement_interpretation_Tm_refine_83845a86f2550cdf941eeb1d9b59602b, refinement_interpretation_Tm_refine_9d3fd79fd314167f1a9c213a188da3ec, refinement_interpretation_Tm_refine_b2401a8cabe2f9a01538f32548fa9f6c, typing_Lib.IntTypes.mk_int, typing_Prims.pow2, typing_tok_Lib.IntTypes.S32@tok, typing_tok_Lib.IntTypes.SEC@tok

;;; End module FStar.Int64 (282 decls; total size 12389)

;;; Start module FStar.Int128

; <Start encoding FStar.Int128.n>

(declare-fun FStar.Int128.n (Dummy_sort) Term)

; </end encoding FStar.Int128.n>


; <Skipped />


; <Start encoding FStar.Int128.t>

(declare-fun FStar.Int128.t () Term)

; </end encoding FStar.Int128.t>


; <Start encoding FStar.Int128.t__uu___haseq>


; </end encoding FStar.Int128.t__uu___haseq>


; <Start encoding FStar.Int128.v>

(declare-fun FStar.Int128.v (Term) Term)
(declare-fun Tm_arrow_6b9b33ecb8595657b49310a66ef5c6c0 () Term)
(declare-fun FStar.Int128.v@tok () Term)

; </end encoding FStar.Int128.v>


; <Start encoding FStar.Int128.int_to_t>

(declare-fun FStar.Int128.int_to_t (Term) Term)
(declare-fun Tm_refine_45bc05678180f1d1ec5aae9695cd9049 (Term) Term)
(declare-fun Tm_arrow_d021228889e9a5504ee9a1974c566e69 () Term)
(declare-fun FStar.Int128.int_to_t@tok () Term)


; </end encoding FStar.Int128.int_to_t>


; <Start encoding FStar.Int128.uv_inv>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.Int128.uv_inv (Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.Int128.uv_inv@tok () Term)

; </end encoding FStar.Int128.uv_inv>


; <Start encoding FStar.Int128.vu_inv>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.Int128.vu_inv (Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.Int128.vu_inv@tok () Term)

; </end encoding FStar.Int128.vu_inv>


; <Start encoding FStar.Int128.v_inj>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.Int128.v_inj (Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.Int128.v_inj@tok () Term)

; </end encoding FStar.Int128.v_inj>


; <Start encoding FStar.Int128.add>

(declare-fun FStar.Int128.add (Term Term) Term)
(declare-fun Tm_refine_0a1d92e00c648f6794feea098f9116bb (Term Term) Term)
(declare-fun Tm_arrow_cc51dc80fda4c8b4216ed29189398a74 () Term)
(declare-fun FStar.Int128.add@tok () Term)


; </end encoding FStar.Int128.add>


; <Start encoding FStar.Int128.sub>

(declare-fun FStar.Int128.sub (Term Term) Term)
(declare-fun Tm_refine_659e55e38139824ea2eb3ddc3c5a545a (Term Term) Term)
(declare-fun Tm_arrow_202bc41121f0cca3b834c2133d960b07 () Term)
(declare-fun FStar.Int128.sub@tok () Term)


; </end encoding FStar.Int128.sub>


; <Start encoding FStar.Int128.mul>

(declare-fun FStar.Int128.mul (Term Term) Term)
(declare-fun Tm_refine_63d1e98c120c21b7ddfdf4324a046a4a (Term Term) Term)
(declare-fun Tm_arrow_117402bd140044793e085bca6252f2f4 () Term)
(declare-fun FStar.Int128.mul@tok () Term)


; </end encoding FStar.Int128.mul>


; <Start encoding FStar.Int128.div>

(declare-fun Tm_refine_6b9660f5bcae3394fca29b1c1dff77d5 () Term)
(declare-fun FStar.Int128.div (Term Term) Term)

(declare-fun Tm_refine_48e8d9a47843bf8b868199ce18b7bdf5 (Term Term) Term)
(declare-fun Tm_arrow_de98028e69896bb432dbb6b10faec3bb () Term)
(declare-fun FStar.Int128.div@tok () Term)


; </end encoding FStar.Int128.div>


; <Start encoding FStar.Int128.rem>


(declare-fun FStar.Int128.rem (Term Term) Term)

(declare-fun Tm_refine_cf667d298af7885b4e8dbf8b1a3f00a3 (Term Term) Term)
(declare-fun Tm_arrow_8c00e87cb51d54dbf61dbd227d40422e () Term)
(declare-fun FStar.Int128.rem@tok () Term)


; </end encoding FStar.Int128.rem>


; <Start encoding FStar.Int128.logand>

(declare-fun FStar.Int128.logand (Term Term) Term)
(declare-fun Tm_refine_55f285a61cb00e59dedb1f739f2a44bb (Term Term) Term)
(declare-fun Tm_arrow_edc0ecdab4e24dfc5a4680fd0b140ce6 () Term)
(declare-fun FStar.Int128.logand@tok () Term)


; </end encoding FStar.Int128.logand>


; <Start encoding FStar.Int128.logxor>

(declare-fun FStar.Int128.logxor (Term Term) Term)
(declare-fun Tm_refine_2190e73f08edb5e961ea99644a5f6aa6 (Term Term) Term)
(declare-fun Tm_arrow_b222b194a7570b68333d8d56de4dcb77 () Term)
(declare-fun FStar.Int128.logxor@tok () Term)


; </end encoding FStar.Int128.logxor>


; <Start encoding FStar.Int128.logor>

(declare-fun FStar.Int128.logor (Term Term) Term)
(declare-fun Tm_refine_9cc4daa0717e6e1e12e26ab405300d13 (Term Term) Term)
(declare-fun Tm_arrow_76cafe10e07d236d5028ffd9ddf3a9e4 () Term)
(declare-fun FStar.Int128.logor@tok () Term)


; </end encoding FStar.Int128.logor>


; <Start encoding FStar.Int128.lognot>

(declare-fun FStar.Int128.lognot (Term) Term)
(declare-fun Tm_refine_a5d8164fe24a87446f6577de773132d9 (Term) Term)
(declare-fun Tm_arrow_541a207cf22be9b8e0cff5d9b6f10f49 () Term)
(declare-fun FStar.Int128.lognot@tok () Term)


; </end encoding FStar.Int128.lognot>


; <Start encoding FStar.Int128.shift_right>

(declare-fun FStar.Int128.shift_right (Term Term) Term)
(declare-fun Tm_refine_be143cdf0bd5d8cc30e7736a5d3a873d (Term Term) Term)
(declare-fun Tm_arrow_ce6272783ce411471ec67c411ee383b0 () Term)
(declare-fun FStar.Int128.shift_right@tok () Term)


; </end encoding FStar.Int128.shift_right>


; <Start encoding FStar.Int128.shift_left>

(declare-fun FStar.Int128.shift_left (Term Term) Term)
(declare-fun Tm_refine_b4baf2f49a1342149d586a246b612c99 (Term Term) Term)
(declare-fun Tm_arrow_9a194e62764c8a074195c7c9aac69a5d () Term)
(declare-fun FStar.Int128.shift_left@tok () Term)


; </end encoding FStar.Int128.shift_left>


; <Start encoding FStar.Int128.shift_arithmetic_right>

(declare-fun FStar.Int128.shift_arithmetic_right (Term Term) Term)
(declare-fun Tm_refine_30b9049cb2adda82039acaac6c2ffa12 (Term Term) Term)
(declare-fun Tm_arrow_83d692dd1eabb75e813df56ec6e50c71 () Term)
(declare-fun FStar.Int128.shift_arithmetic_right@tok () Term)


; </end encoding FStar.Int128.shift_arithmetic_right>


; <Start encoding FStar.Int128.eq>

(declare-fun FStar.Int128.eq (Term Term) Term)
(declare-fun Tm_arrow_5f4ba772381c4c9ac0bdff212972c576 () Term)
(declare-fun FStar.Int128.eq@tok () Term)

; </end encoding FStar.Int128.eq>


; <Start encoding FStar.Int128.gt>

(declare-fun FStar.Int128.gt (Term Term) Term)

(declare-fun FStar.Int128.gt@tok () Term)

; </end encoding FStar.Int128.gt>


; <Start encoding FStar.Int128.gte>

(declare-fun FStar.Int128.gte (Term Term) Term)

(declare-fun FStar.Int128.gte@tok () Term)

; </end encoding FStar.Int128.gte>


; <Start encoding FStar.Int128.lt>

(declare-fun FStar.Int128.lt (Term Term) Term)

(declare-fun FStar.Int128.lt@tok () Term)

; </end encoding FStar.Int128.lt>


; <Start encoding FStar.Int128.lte>

(declare-fun FStar.Int128.lte (Term Term) Term)

(declare-fun FStar.Int128.lte@tok () Term)

; </end encoding FStar.Int128.lte>


; <Start encoding FStar.Int128.op_Plus_Hat>

(declare-fun FStar.Int128.op_Plus_Hat (Term Term) Term)


(declare-fun FStar.Int128.op_Plus_Hat@tok () Term)


; </end encoding FStar.Int128.op_Plus_Hat>


; <Start encoding FStar.Int128.op_Subtraction_Hat>

(declare-fun FStar.Int128.op_Subtraction_Hat (Term Term) Term)


(declare-fun FStar.Int128.op_Subtraction_Hat@tok () Term)


; </end encoding FStar.Int128.op_Subtraction_Hat>


; <Start encoding FStar.Int128.op_Star_Hat>

(declare-fun FStar.Int128.op_Star_Hat (Term Term) Term)


(declare-fun FStar.Int128.op_Star_Hat@tok () Term)


; </end encoding FStar.Int128.op_Star_Hat>


; <Start encoding FStar.Int128.op_Slash_Hat>


(declare-fun FStar.Int128.op_Slash_Hat (Term Term) Term)



(declare-fun FStar.Int128.op_Slash_Hat@tok () Term)



; </end encoding FStar.Int128.op_Slash_Hat>


; <Start encoding FStar.Int128.op_Percent_Hat>


(declare-fun FStar.Int128.op_Percent_Hat (Term Term) Term)



(declare-fun FStar.Int128.op_Percent_Hat@tok () Term)



; </end encoding FStar.Int128.op_Percent_Hat>


; <Start encoding FStar.Int128.op_Hat_Hat>

(declare-fun FStar.Int128.op_Hat_Hat (Term Term) Term)


(declare-fun FStar.Int128.op_Hat_Hat@tok () Term)


; </end encoding FStar.Int128.op_Hat_Hat>


; <Start encoding FStar.Int128.op_Amp_Hat>

(declare-fun FStar.Int128.op_Amp_Hat (Term Term) Term)


(declare-fun FStar.Int128.op_Amp_Hat@tok () Term)


; </end encoding FStar.Int128.op_Amp_Hat>


; <Start encoding FStar.Int128.op_Bar_Hat>

(declare-fun FStar.Int128.op_Bar_Hat (Term Term) Term)


(declare-fun FStar.Int128.op_Bar_Hat@tok () Term)


; </end encoding FStar.Int128.op_Bar_Hat>


; <Start encoding FStar.Int128.op_Less_Less_Hat>

(declare-fun FStar.Int128.op_Less_Less_Hat (Term Term) Term)


(declare-fun FStar.Int128.op_Less_Less_Hat@tok () Term)


; </end encoding FStar.Int128.op_Less_Less_Hat>


; <Start encoding FStar.Int128.op_Greater_Greater_Hat>

(declare-fun FStar.Int128.op_Greater_Greater_Hat (Term Term) Term)


(declare-fun FStar.Int128.op_Greater_Greater_Hat@tok () Term)


; </end encoding FStar.Int128.op_Greater_Greater_Hat>


; <Start encoding FStar.Int128.op_Greater_Greater_Greater_Hat>

(declare-fun FStar.Int128.op_Greater_Greater_Greater_Hat (Term Term) Term)


(declare-fun FStar.Int128.op_Greater_Greater_Greater_Hat@tok () Term)


; </end encoding FStar.Int128.op_Greater_Greater_Greater_Hat>


; <Start encoding FStar.Int128.op_Equals_Hat>

(declare-fun FStar.Int128.op_Equals_Hat (Term Term) Term)

(declare-fun FStar.Int128.op_Equals_Hat@tok () Term)

; </end encoding FStar.Int128.op_Equals_Hat>


; <Start encoding FStar.Int128.op_Greater_Hat>

(declare-fun FStar.Int128.op_Greater_Hat (Term Term) Term)

(declare-fun FStar.Int128.op_Greater_Hat@tok () Term)

; </end encoding FStar.Int128.op_Greater_Hat>


; <Start encoding FStar.Int128.op_Greater_Equals_Hat>

(declare-fun FStar.Int128.op_Greater_Equals_Hat (Term Term) Term)

(declare-fun FStar.Int128.op_Greater_Equals_Hat@tok () Term)

; </end encoding FStar.Int128.op_Greater_Equals_Hat>


; <Start encoding FStar.Int128.op_Less_Hat>

(declare-fun FStar.Int128.op_Less_Hat (Term Term) Term)

(declare-fun FStar.Int128.op_Less_Hat@tok () Term)

; </end encoding FStar.Int128.op_Less_Hat>


; <Start encoding FStar.Int128.op_Less_Equals_Hat>

(declare-fun FStar.Int128.op_Less_Equals_Hat (Term Term) Term)

(declare-fun FStar.Int128.op_Less_Equals_Hat@tok () Term)

; </end encoding FStar.Int128.op_Less_Equals_Hat>


; <Start encoding FStar.Int128.ct_abs>

(declare-fun Tm_refine_ca85c36eb10e9a2f43f93fc90550499d () Term)
(declare-fun FStar.Int128.ct_abs (Term) Term)

(declare-fun Tm_refine_2c24ef28e585872d4619a0aebb863ce9 (Term) Term)
(declare-fun Tm_arrow_9470672d33aa74a7f2d1d329c0be12ce () Term)
(declare-fun FStar.Int128.ct_abs@tok () Term)



; </end encoding FStar.Int128.ct_abs>


; <Start encoding FStar.Int128.to_string>

(declare-fun FStar.Int128.to_string (Term) Term)
(declare-fun Tm_arrow_af718d6c3778c7b49e27a037f7432a5c () Term)
(declare-fun FStar.Int128.to_string@tok () Term)

; </end encoding FStar.Int128.to_string>


; <Start encoding FStar.Int128.of_string>

(declare-fun FStar.Int128.of_string (Term) Term)
(declare-fun Tm_arrow_897054847014413bb8fcda810b57fe03 () Term)
(declare-fun FStar.Int128.of_string@tok () Term)

; </end encoding FStar.Int128.of_string>


; <Skipped />


; <Start encoding FStar.Int128.__int_to_t>

(declare-fun FStar.Int128.__int_to_t (Term) Term)
(declare-fun Tm_arrow_7cfba97cbd8c502a16a2fc231afb4bc4 () Term)
(declare-fun FStar.Int128.__int_to_t@tok () Term)

; </end encoding FStar.Int128.__int_to_t>


; <Skipped />


; <Start encoding FStar.Int128.mul_wide>

(declare-fun FStar.Int128.mul_wide (Term Term) Term)
(declare-fun Tm_refine_d9f46bd7f7278a97cf5dfd88f392c1f5 (Term Term) Term)
(declare-fun Tm_arrow_7350388ab40709dceab0c819ab93a300 () Term)
(declare-fun FStar.Int128.mul_wide@tok () Term)


; </end encoding FStar.Int128.mul_wide>


; UNSAT CORE: @MaxFuel_assumption, @MaxIFuel_assumption, @fuel_correspondence_Prims.pow2.fuel_instrumented, @query, constructor_distinct_Lib.IntTypes.S16, constructor_distinct_Lib.IntTypes.S32, constructor_distinct_Lib.IntTypes.SEC, equality_tok_Lib.IntTypes.S16@tok, equality_tok_Lib.IntTypes.S32@tok, equality_tok_Lib.IntTypes.SEC@tok, equation_Lib.IntTypes.bits, equation_Lib.IntTypes.range, equation_Lib.IntTypes.signed, equation_Lib.IntTypes.unsigned, equation_Lib.IntTypes.v, equation_Prims.nat, equation_Prims.pos, equation_Spec.Kyber2.Params.params_q, int_inversion, int_typing, lemma_FStar.UInt.pow2_values, primitive_Prims.op_Addition, primitive_Prims.op_Division, primitive_Prims.op_LessThanOrEqual, primitive_Prims.op_Minus, primitive_Prims.op_Multiply, primitive_Prims.op_Subtraction, projection_inverse_BoxBool_proj_0, projection_inverse_BoxInt_proj_0, refinement_interpretation_Tm_refine_2b320913041b873fce938dd17eebb3e2, refinement_interpretation_Tm_refine_542f9d4f129664613f2483a6c88bc7c2, refinement_interpretation_Tm_refine_774ba3f728d91ead8ef40be66c9802e5, refinement_interpretation_Tm_refine_83845a86f2550cdf941eeb1d9b59602b, refinement_interpretation_Tm_refine_9d3fd79fd314167f1a9c213a188da3ec, refinement_interpretation_Tm_refine_b2401a8cabe2f9a01538f32548fa9f6c, typing_Lib.IntTypes.mk_int, typing_Prims.pow2, typing_tok_Lib.IntTypes.S32@tok, typing_tok_Lib.IntTypes.SEC@tok

;;; End module FStar.Int128 (289 decls; total size 12890)

;;; Start module FStar.Int32

; <Start encoding FStar.Int32.n>

(declare-fun FStar.Int32.n (Dummy_sort) Term)

; </end encoding FStar.Int32.n>


; <Skipped />


; <Start encoding FStar.Int32.t>

(declare-fun FStar.Int32.t () Term)

; </end encoding FStar.Int32.t>


; <Start encoding FStar.Int32.t__uu___haseq>


; </end encoding FStar.Int32.t__uu___haseq>


; <Start encoding FStar.Int32.v>

(declare-fun FStar.Int32.v (Term) Term)
(declare-fun Tm_arrow_6ac7ef275f55ab679f78aa887c7709b4 () Term)
(declare-fun FStar.Int32.v@tok () Term)

; </end encoding FStar.Int32.v>


; <Start encoding FStar.Int32.int_to_t>

(declare-fun FStar.Int32.int_to_t (Term) Term)
(declare-fun Tm_refine_de03296927e755695593c3efc35c009e (Term) Term)
(declare-fun Tm_arrow_45ed431c7a9ff46f950d5828953d371e () Term)
(declare-fun FStar.Int32.int_to_t@tok () Term)


; </end encoding FStar.Int32.int_to_t>


; <Start encoding FStar.Int32.uv_inv>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.Int32.uv_inv (Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.Int32.uv_inv@tok () Term)

; </end encoding FStar.Int32.uv_inv>


; <Start encoding FStar.Int32.vu_inv>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.Int32.vu_inv (Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.Int32.vu_inv@tok () Term)

; </end encoding FStar.Int32.vu_inv>


; <Start encoding FStar.Int32.v_inj>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.Int32.v_inj (Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.Int32.v_inj@tok () Term)

; </end encoding FStar.Int32.v_inj>


; <Start encoding FStar.Int32.add>

(declare-fun FStar.Int32.add (Term Term) Term)
(declare-fun Tm_refine_1a59fc9612c859a6093eecd3ed5a0de6 (Term Term) Term)
(declare-fun Tm_arrow_7ab1c7c2d78b52acc1357ec695e622a8 () Term)
(declare-fun FStar.Int32.add@tok () Term)


; </end encoding FStar.Int32.add>


; <Start encoding FStar.Int32.sub>

(declare-fun FStar.Int32.sub (Term Term) Term)
(declare-fun Tm_refine_6f26696e0866dc892be2102019f8da24 (Term Term) Term)
(declare-fun Tm_arrow_cd6213b3a3faa2abc4b6d9b6965068b7 () Term)
(declare-fun FStar.Int32.sub@tok () Term)


; </end encoding FStar.Int32.sub>


; <Start encoding FStar.Int32.mul>

(declare-fun FStar.Int32.mul (Term Term) Term)
(declare-fun Tm_refine_5a3e15c900dbee1e4bf186924c47bd7f (Term Term) Term)
(declare-fun Tm_arrow_ab60430fc1d3e9dff80a5a201915b84e () Term)
(declare-fun FStar.Int32.mul@tok () Term)


; </end encoding FStar.Int32.mul>


; <Start encoding FStar.Int32.div>

(declare-fun Tm_refine_ebb5a3e35cc5b5152947a0f62e24676b () Term)
(declare-fun FStar.Int32.div (Term Term) Term)

(declare-fun Tm_refine_dc993b56db6169249168fa7f33457b1e (Term Term) Term)
(declare-fun Tm_arrow_ead240ef45d9630d0540e409482f3aa9 () Term)
(declare-fun FStar.Int32.div@tok () Term)


; </end encoding FStar.Int32.div>


; <Start encoding FStar.Int32.rem>


(declare-fun FStar.Int32.rem (Term Term) Term)

(declare-fun Tm_refine_092ccc25aff6c447d343343af2860af8 (Term Term) Term)
(declare-fun Tm_arrow_2f399d8482d1caea500a87c03b2807ce () Term)
(declare-fun FStar.Int32.rem@tok () Term)


; </end encoding FStar.Int32.rem>


; <Start encoding FStar.Int32.logand>

(declare-fun FStar.Int32.logand (Term Term) Term)
(declare-fun Tm_refine_59732383bfa1835a65f610cc898de30c (Term Term) Term)
(declare-fun Tm_arrow_32206f0c4f69cd41da7248d37ae47ae9 () Term)
(declare-fun FStar.Int32.logand@tok () Term)


; </end encoding FStar.Int32.logand>


; <Start encoding FStar.Int32.logxor>

(declare-fun FStar.Int32.logxor (Term Term) Term)
(declare-fun Tm_refine_cfc04815225fb057177ccba846e59202 (Term Term) Term)
(declare-fun Tm_arrow_df54306f42a33de966ccae6b50d35127 () Term)
(declare-fun FStar.Int32.logxor@tok () Term)


; </end encoding FStar.Int32.logxor>


; <Start encoding FStar.Int32.logor>

(declare-fun FStar.Int32.logor (Term Term) Term)
(declare-fun Tm_refine_610327e001ab23469cc9fd75155ba5bb (Term Term) Term)
(declare-fun Tm_arrow_872a52bb5eb9f7a0eb5088f8239814ae () Term)
(declare-fun FStar.Int32.logor@tok () Term)


; </end encoding FStar.Int32.logor>


; <Start encoding FStar.Int32.lognot>

(declare-fun FStar.Int32.lognot (Term) Term)
(declare-fun Tm_refine_8dab3eae5a8b7fdfccd323b7ee84970c (Term) Term)
(declare-fun Tm_arrow_498f8183a7be355f5c3a58e6bd47fec7 () Term)
(declare-fun FStar.Int32.lognot@tok () Term)


; </end encoding FStar.Int32.lognot>


; <Start encoding FStar.Int32.shift_right>

(declare-fun FStar.Int32.shift_right (Term Term) Term)
(declare-fun Tm_refine_de7c11ecbe06db1557b1d7ad7b4a5cb6 (Term Term) Term)
(declare-fun Tm_arrow_9fa9550c9a7bedae44bab76a445f0087 () Term)
(declare-fun FStar.Int32.shift_right@tok () Term)


; </end encoding FStar.Int32.shift_right>


; <Start encoding FStar.Int32.shift_left>

(declare-fun FStar.Int32.shift_left (Term Term) Term)
(declare-fun Tm_refine_0d33e586e4d6ff62d4def92b2157498f (Term Term) Term)
(declare-fun Tm_arrow_48d55ecff3cb5f6493c1c81fac5510c8 () Term)
(declare-fun FStar.Int32.shift_left@tok () Term)


; </end encoding FStar.Int32.shift_left>


; <Start encoding FStar.Int32.shift_arithmetic_right>

(declare-fun FStar.Int32.shift_arithmetic_right (Term Term) Term)
(declare-fun Tm_refine_8e9b3601222146e6c59890b3c936610f (Term Term) Term)
(declare-fun Tm_arrow_e5b5bc5765669c4126693e69af6d6b0a () Term)
(declare-fun FStar.Int32.shift_arithmetic_right@tok () Term)


; </end encoding FStar.Int32.shift_arithmetic_right>


; <Start encoding FStar.Int32.eq>

(declare-fun FStar.Int32.eq (Term Term) Term)
(declare-fun Tm_arrow_97c8762f8bf34c07a41d70decf96b961 () Term)
(declare-fun FStar.Int32.eq@tok () Term)

; </end encoding FStar.Int32.eq>


; <Start encoding FStar.Int32.gt>

(declare-fun FStar.Int32.gt (Term Term) Term)

(declare-fun FStar.Int32.gt@tok () Term)

; </end encoding FStar.Int32.gt>


; <Start encoding FStar.Int32.gte>

(declare-fun FStar.Int32.gte (Term Term) Term)

(declare-fun FStar.Int32.gte@tok () Term)

; </end encoding FStar.Int32.gte>


; <Start encoding FStar.Int32.lt>

(declare-fun FStar.Int32.lt (Term Term) Term)

(declare-fun FStar.Int32.lt@tok () Term)

; </end encoding FStar.Int32.lt>


; <Start encoding FStar.Int32.lte>

(declare-fun FStar.Int32.lte (Term Term) Term)

(declare-fun FStar.Int32.lte@tok () Term)

; </end encoding FStar.Int32.lte>


; <Start encoding FStar.Int32.op_Plus_Hat>

(declare-fun FStar.Int32.op_Plus_Hat (Term Term) Term)


(declare-fun FStar.Int32.op_Plus_Hat@tok () Term)


; </end encoding FStar.Int32.op_Plus_Hat>


; <Start encoding FStar.Int32.op_Subtraction_Hat>

(declare-fun FStar.Int32.op_Subtraction_Hat (Term Term) Term)


(declare-fun FStar.Int32.op_Subtraction_Hat@tok () Term)


; </end encoding FStar.Int32.op_Subtraction_Hat>


; <Start encoding FStar.Int32.op_Star_Hat>

(declare-fun FStar.Int32.op_Star_Hat (Term Term) Term)


(declare-fun FStar.Int32.op_Star_Hat@tok () Term)


; </end encoding FStar.Int32.op_Star_Hat>


; <Start encoding FStar.Int32.op_Slash_Hat>


(declare-fun FStar.Int32.op_Slash_Hat (Term Term) Term)



(declare-fun FStar.Int32.op_Slash_Hat@tok () Term)



; </end encoding FStar.Int32.op_Slash_Hat>


; <Start encoding FStar.Int32.op_Percent_Hat>


(declare-fun FStar.Int32.op_Percent_Hat (Term Term) Term)



(declare-fun FStar.Int32.op_Percent_Hat@tok () Term)



; </end encoding FStar.Int32.op_Percent_Hat>


; <Start encoding FStar.Int32.op_Hat_Hat>

(declare-fun FStar.Int32.op_Hat_Hat (Term Term) Term)


(declare-fun FStar.Int32.op_Hat_Hat@tok () Term)


; </end encoding FStar.Int32.op_Hat_Hat>


; <Start encoding FStar.Int32.op_Amp_Hat>

(declare-fun FStar.Int32.op_Amp_Hat (Term Term) Term)


(declare-fun FStar.Int32.op_Amp_Hat@tok () Term)


; </end encoding FStar.Int32.op_Amp_Hat>


; <Start encoding FStar.Int32.op_Bar_Hat>

(declare-fun FStar.Int32.op_Bar_Hat (Term Term) Term)


(declare-fun FStar.Int32.op_Bar_Hat@tok () Term)


; </end encoding FStar.Int32.op_Bar_Hat>


; <Start encoding FStar.Int32.op_Less_Less_Hat>

(declare-fun FStar.Int32.op_Less_Less_Hat (Term Term) Term)


(declare-fun FStar.Int32.op_Less_Less_Hat@tok () Term)


; </end encoding FStar.Int32.op_Less_Less_Hat>


; <Start encoding FStar.Int32.op_Greater_Greater_Hat>

(declare-fun FStar.Int32.op_Greater_Greater_Hat (Term Term) Term)


(declare-fun FStar.Int32.op_Greater_Greater_Hat@tok () Term)


; </end encoding FStar.Int32.op_Greater_Greater_Hat>


; <Start encoding FStar.Int32.op_Greater_Greater_Greater_Hat>

(declare-fun FStar.Int32.op_Greater_Greater_Greater_Hat (Term Term) Term)


(declare-fun FStar.Int32.op_Greater_Greater_Greater_Hat@tok () Term)


; </end encoding FStar.Int32.op_Greater_Greater_Greater_Hat>


; <Start encoding FStar.Int32.op_Equals_Hat>

(declare-fun FStar.Int32.op_Equals_Hat (Term Term) Term)

(declare-fun FStar.Int32.op_Equals_Hat@tok () Term)

; </end encoding FStar.Int32.op_Equals_Hat>


; <Start encoding FStar.Int32.op_Greater_Hat>

(declare-fun FStar.Int32.op_Greater_Hat (Term Term) Term)

(declare-fun FStar.Int32.op_Greater_Hat@tok () Term)

; </end encoding FStar.Int32.op_Greater_Hat>


; <Start encoding FStar.Int32.op_Greater_Equals_Hat>

(declare-fun FStar.Int32.op_Greater_Equals_Hat (Term Term) Term)

(declare-fun FStar.Int32.op_Greater_Equals_Hat@tok () Term)

; </end encoding FStar.Int32.op_Greater_Equals_Hat>


; <Start encoding FStar.Int32.op_Less_Hat>

(declare-fun FStar.Int32.op_Less_Hat (Term Term) Term)

(declare-fun FStar.Int32.op_Less_Hat@tok () Term)

; </end encoding FStar.Int32.op_Less_Hat>


; <Start encoding FStar.Int32.op_Less_Equals_Hat>

(declare-fun FStar.Int32.op_Less_Equals_Hat (Term Term) Term)

(declare-fun FStar.Int32.op_Less_Equals_Hat@tok () Term)

; </end encoding FStar.Int32.op_Less_Equals_Hat>


; <Start encoding FStar.Int32.ct_abs>

(declare-fun Tm_refine_7ebbe64b62d60feef45ced5325adbe87 () Term)
(declare-fun FStar.Int32.ct_abs (Term) Term)

(declare-fun Tm_refine_4d2308f4660adecb1fbe16f1324f9a1d (Term) Term)
(declare-fun Tm_arrow_bd407ddfecd5351c273a31a450f5f474 () Term)
(declare-fun FStar.Int32.ct_abs@tok () Term)



; </end encoding FStar.Int32.ct_abs>


; <Start encoding FStar.Int32.to_string>

(declare-fun FStar.Int32.to_string (Term) Term)
(declare-fun Tm_arrow_0c788e4c3e4a22a1b92aa7262a6999d7 () Term)
(declare-fun FStar.Int32.to_string@tok () Term)

; </end encoding FStar.Int32.to_string>


; <Start encoding FStar.Int32.of_string>

(declare-fun FStar.Int32.of_string (Term) Term)
(declare-fun Tm_arrow_37a58236a4d31e5c7ea1903fb153bc44 () Term)
(declare-fun FStar.Int32.of_string@tok () Term)

; </end encoding FStar.Int32.of_string>


; <Skipped />


; <Start encoding FStar.Int32.__int_to_t>

(declare-fun FStar.Int32.__int_to_t (Term) Term)
(declare-fun Tm_arrow_524d58760da7cd44300469b3aafe0fe8 () Term)
(declare-fun FStar.Int32.__int_to_t@tok () Term)

; </end encoding FStar.Int32.__int_to_t>


; <Skipped />


; UNSAT CORE: @MaxFuel_assumption, @MaxIFuel_assumption, @fuel_correspondence_Prims.pow2.fuel_instrumented, @query, constructor_distinct_Lib.IntTypes.S16, constructor_distinct_Lib.IntTypes.S32, constructor_distinct_Lib.IntTypes.SEC, equality_tok_Lib.IntTypes.S16@tok, equality_tok_Lib.IntTypes.S32@tok, equality_tok_Lib.IntTypes.SEC@tok, equation_Lib.IntTypes.bits, equation_Lib.IntTypes.range, equation_Lib.IntTypes.signed, equation_Lib.IntTypes.unsigned, equation_Lib.IntTypes.v, equation_Prims.nat, equation_Prims.pos, equation_Spec.Kyber2.Params.params_q, int_inversion, int_typing, lemma_FStar.UInt.pow2_values, primitive_Prims.op_Addition, primitive_Prims.op_Division, primitive_Prims.op_LessThanOrEqual, primitive_Prims.op_Minus, primitive_Prims.op_Multiply, primitive_Prims.op_Subtraction, projection_inverse_BoxBool_proj_0, projection_inverse_BoxInt_proj_0, refinement_interpretation_Tm_refine_2b320913041b873fce938dd17eebb3e2, refinement_interpretation_Tm_refine_542f9d4f129664613f2483a6c88bc7c2, refinement_interpretation_Tm_refine_774ba3f728d91ead8ef40be66c9802e5, refinement_interpretation_Tm_refine_83845a86f2550cdf941eeb1d9b59602b, refinement_interpretation_Tm_refine_9d3fd79fd314167f1a9c213a188da3ec, refinement_interpretation_Tm_refine_b2401a8cabe2f9a01538f32548fa9f6c, typing_Lib.IntTypes.mk_int, typing_Prims.pow2, typing_tok_Lib.IntTypes.S32@tok, typing_tok_Lib.IntTypes.SEC@tok

;;; End module FStar.Int32 (282 decls; total size 12389)

;;; Start module FStar.Int16

; <Start encoding FStar.Int16.n>

(declare-fun FStar.Int16.n (Dummy_sort) Term)

; </end encoding FStar.Int16.n>


; <Skipped />


; <Start encoding FStar.Int16.t>

(declare-fun FStar.Int16.t () Term)

; </end encoding FStar.Int16.t>


; <Start encoding FStar.Int16.t__uu___haseq>


; </end encoding FStar.Int16.t__uu___haseq>


; <Start encoding FStar.Int16.v>

(declare-fun FStar.Int16.v (Term) Term)
(declare-fun Tm_arrow_0fa295607b0fc969db274fdadf1d7515 () Term)
(declare-fun FStar.Int16.v@tok () Term)

; </end encoding FStar.Int16.v>


; <Start encoding FStar.Int16.int_to_t>

(declare-fun FStar.Int16.int_to_t (Term) Term)
(declare-fun Tm_refine_23286ea88a7a3790e551bc019ec2120d (Term) Term)
(declare-fun Tm_arrow_8d21b7df85ceec27ed0cd7885ecff8fb () Term)
(declare-fun FStar.Int16.int_to_t@tok () Term)


; </end encoding FStar.Int16.int_to_t>


; <Start encoding FStar.Int16.uv_inv>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.Int16.uv_inv (Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.Int16.uv_inv@tok () Term)

; </end encoding FStar.Int16.uv_inv>


; <Start encoding FStar.Int16.vu_inv>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.Int16.vu_inv (Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.Int16.vu_inv@tok () Term)

; </end encoding FStar.Int16.vu_inv>


; <Start encoding FStar.Int16.v_inj>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.Int16.v_inj (Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.Int16.v_inj@tok () Term)

; </end encoding FStar.Int16.v_inj>


; <Start encoding FStar.Int16.add>

(declare-fun FStar.Int16.add (Term Term) Term)
(declare-fun Tm_refine_fb9510157cb6b62d131c55bba7a4d70b (Term Term) Term)
(declare-fun Tm_arrow_0934ba8377c5cae68e7b3dd557b7118e () Term)
(declare-fun FStar.Int16.add@tok () Term)


; </end encoding FStar.Int16.add>


; <Start encoding FStar.Int16.sub>

(declare-fun FStar.Int16.sub (Term Term) Term)
(declare-fun Tm_refine_15e641d4c3253f2274acbc3ea50486da (Term Term) Term)
(declare-fun Tm_arrow_21635bec91feb223ed344387175b3054 () Term)
(declare-fun FStar.Int16.sub@tok () Term)


; </end encoding FStar.Int16.sub>


; <Start encoding FStar.Int16.mul>

(declare-fun FStar.Int16.mul (Term Term) Term)
(declare-fun Tm_refine_700c7f5f4e58af37fbb38c0b5fc4bddd (Term Term) Term)
(declare-fun Tm_arrow_7ee218138d72a6587b8dd81115a53a10 () Term)
(declare-fun FStar.Int16.mul@tok () Term)


; </end encoding FStar.Int16.mul>


; <Start encoding FStar.Int16.div>

(declare-fun Tm_refine_ea65a038e3ff144d643fa0488efde007 () Term)
(declare-fun FStar.Int16.div (Term Term) Term)

(declare-fun Tm_refine_f112a5fe168b56973d9730c0b83d412e (Term Term) Term)
(declare-fun Tm_arrow_f8a0e7ee4475d4fe1b8917c00c0dcdd1 () Term)
(declare-fun FStar.Int16.div@tok () Term)


; </end encoding FStar.Int16.div>


; <Start encoding FStar.Int16.rem>


(declare-fun FStar.Int16.rem (Term Term) Term)

(declare-fun Tm_refine_245d1c8094b17c4b29d897cd0e899835 (Term Term) Term)
(declare-fun Tm_arrow_e0302621b8559d599c837cacb1c1692e () Term)
(declare-fun FStar.Int16.rem@tok () Term)


; </end encoding FStar.Int16.rem>


; <Start encoding FStar.Int16.logand>

(declare-fun FStar.Int16.logand (Term Term) Term)
(declare-fun Tm_refine_1554a74b043532b79a1ed4602d7d208a (Term Term) Term)
(declare-fun Tm_arrow_11d87311050852e1491efc9bd74de896 () Term)
(declare-fun FStar.Int16.logand@tok () Term)


; </end encoding FStar.Int16.logand>


; <Start encoding FStar.Int16.logxor>

(declare-fun FStar.Int16.logxor (Term Term) Term)
(declare-fun Tm_refine_73d6a67474af40e4e88b020e029714fe (Term Term) Term)
(declare-fun Tm_arrow_f0f1e6f50efe5ce003731eb380f9ef47 () Term)
(declare-fun FStar.Int16.logxor@tok () Term)


; </end encoding FStar.Int16.logxor>


; <Start encoding FStar.Int16.logor>

(declare-fun FStar.Int16.logor (Term Term) Term)
(declare-fun Tm_refine_dadf313786aa7190ddb7ef4f2d497cc5 (Term Term) Term)
(declare-fun Tm_arrow_e90a11a91a32ccc3d124ab1e2262c813 () Term)
(declare-fun FStar.Int16.logor@tok () Term)


; </end encoding FStar.Int16.logor>


; <Start encoding FStar.Int16.lognot>

(declare-fun FStar.Int16.lognot (Term) Term)
(declare-fun Tm_refine_ae3f238744520b1f3acdca33c4938ef3 (Term) Term)
(declare-fun Tm_arrow_4d03cd9635080e8e9ad2bef444110b23 () Term)
(declare-fun FStar.Int16.lognot@tok () Term)


; </end encoding FStar.Int16.lognot>


; <Start encoding FStar.Int16.shift_right>

(declare-fun FStar.Int16.shift_right (Term Term) Term)
(declare-fun Tm_refine_4baaf0faf56342192724a33bdb0810a2 (Term Term) Term)
(declare-fun Tm_arrow_6c4589d8eff65d1f5afe1177ea1607dd () Term)
(declare-fun FStar.Int16.shift_right@tok () Term)


; </end encoding FStar.Int16.shift_right>


; <Start encoding FStar.Int16.shift_left>

(declare-fun FStar.Int16.shift_left (Term Term) Term)
(declare-fun Tm_refine_4c3630cc08d6b89849ecb30c365aa106 (Term Term) Term)
(declare-fun Tm_arrow_f529273381547b3de08febb31ae0fcad () Term)
(declare-fun FStar.Int16.shift_left@tok () Term)


; </end encoding FStar.Int16.shift_left>


; <Start encoding FStar.Int16.shift_arithmetic_right>

(declare-fun FStar.Int16.shift_arithmetic_right (Term Term) Term)
(declare-fun Tm_refine_f5c2adada3e7fc43f5a27c0a90323d68 (Term Term) Term)
(declare-fun Tm_arrow_5cce2883a0c4b490e05bfe58e5d46e9d () Term)
(declare-fun FStar.Int16.shift_arithmetic_right@tok () Term)


; </end encoding FStar.Int16.shift_arithmetic_right>


; <Start encoding FStar.Int16.eq>

(declare-fun FStar.Int16.eq (Term Term) Term)
(declare-fun Tm_arrow_e88eb9ebff945ed220573988f8468851 () Term)
(declare-fun FStar.Int16.eq@tok () Term)

; </end encoding FStar.Int16.eq>


; <Start encoding FStar.Int16.gt>

(declare-fun FStar.Int16.gt (Term Term) Term)

(declare-fun FStar.Int16.gt@tok () Term)

; </end encoding FStar.Int16.gt>


; <Start encoding FStar.Int16.gte>

(declare-fun FStar.Int16.gte (Term Term) Term)

(declare-fun FStar.Int16.gte@tok () Term)

; </end encoding FStar.Int16.gte>


; <Start encoding FStar.Int16.lt>

(declare-fun FStar.Int16.lt (Term Term) Term)

(declare-fun FStar.Int16.lt@tok () Term)

; </end encoding FStar.Int16.lt>


; <Start encoding FStar.Int16.lte>

(declare-fun FStar.Int16.lte (Term Term) Term)

(declare-fun FStar.Int16.lte@tok () Term)

; </end encoding FStar.Int16.lte>


; <Start encoding FStar.Int16.op_Plus_Hat>

(declare-fun FStar.Int16.op_Plus_Hat (Term Term) Term)


(declare-fun FStar.Int16.op_Plus_Hat@tok () Term)


; </end encoding FStar.Int16.op_Plus_Hat>


; <Start encoding FStar.Int16.op_Subtraction_Hat>

(declare-fun FStar.Int16.op_Subtraction_Hat (Term Term) Term)


(declare-fun FStar.Int16.op_Subtraction_Hat@tok () Term)


; </end encoding FStar.Int16.op_Subtraction_Hat>


; <Start encoding FStar.Int16.op_Star_Hat>

(declare-fun FStar.Int16.op_Star_Hat (Term Term) Term)


(declare-fun FStar.Int16.op_Star_Hat@tok () Term)


; </end encoding FStar.Int16.op_Star_Hat>


; <Start encoding FStar.Int16.op_Slash_Hat>


(declare-fun FStar.Int16.op_Slash_Hat (Term Term) Term)



(declare-fun FStar.Int16.op_Slash_Hat@tok () Term)



; </end encoding FStar.Int16.op_Slash_Hat>


; <Start encoding FStar.Int16.op_Percent_Hat>


(declare-fun FStar.Int16.op_Percent_Hat (Term Term) Term)



(declare-fun FStar.Int16.op_Percent_Hat@tok () Term)



; </end encoding FStar.Int16.op_Percent_Hat>


; <Start encoding FStar.Int16.op_Hat_Hat>

(declare-fun FStar.Int16.op_Hat_Hat (Term Term) Term)


(declare-fun FStar.Int16.op_Hat_Hat@tok () Term)


; </end encoding FStar.Int16.op_Hat_Hat>


; <Start encoding FStar.Int16.op_Amp_Hat>

(declare-fun FStar.Int16.op_Amp_Hat (Term Term) Term)


(declare-fun FStar.Int16.op_Amp_Hat@tok () Term)


; </end encoding FStar.Int16.op_Amp_Hat>


; <Start encoding FStar.Int16.op_Bar_Hat>

(declare-fun FStar.Int16.op_Bar_Hat (Term Term) Term)


(declare-fun FStar.Int16.op_Bar_Hat@tok () Term)


; </end encoding FStar.Int16.op_Bar_Hat>


; <Start encoding FStar.Int16.op_Less_Less_Hat>

(declare-fun FStar.Int16.op_Less_Less_Hat (Term Term) Term)


(declare-fun FStar.Int16.op_Less_Less_Hat@tok () Term)


; </end encoding FStar.Int16.op_Less_Less_Hat>


; <Start encoding FStar.Int16.op_Greater_Greater_Hat>

(declare-fun FStar.Int16.op_Greater_Greater_Hat (Term Term) Term)


(declare-fun FStar.Int16.op_Greater_Greater_Hat@tok () Term)


; </end encoding FStar.Int16.op_Greater_Greater_Hat>


; <Start encoding FStar.Int16.op_Greater_Greater_Greater_Hat>

(declare-fun FStar.Int16.op_Greater_Greater_Greater_Hat (Term Term) Term)


(declare-fun FStar.Int16.op_Greater_Greater_Greater_Hat@tok () Term)


; </end encoding FStar.Int16.op_Greater_Greater_Greater_Hat>


; <Start encoding FStar.Int16.op_Equals_Hat>

(declare-fun FStar.Int16.op_Equals_Hat (Term Term) Term)

(declare-fun FStar.Int16.op_Equals_Hat@tok () Term)

; </end encoding FStar.Int16.op_Equals_Hat>


; <Start encoding FStar.Int16.op_Greater_Hat>

(declare-fun FStar.Int16.op_Greater_Hat (Term Term) Term)

(declare-fun FStar.Int16.op_Greater_Hat@tok () Term)

; </end encoding FStar.Int16.op_Greater_Hat>


; <Start encoding FStar.Int16.op_Greater_Equals_Hat>

(declare-fun FStar.Int16.op_Greater_Equals_Hat (Term Term) Term)

(declare-fun FStar.Int16.op_Greater_Equals_Hat@tok () Term)

; </end encoding FStar.Int16.op_Greater_Equals_Hat>


; <Start encoding FStar.Int16.op_Less_Hat>

(declare-fun FStar.Int16.op_Less_Hat (Term Term) Term)

(declare-fun FStar.Int16.op_Less_Hat@tok () Term)

; </end encoding FStar.Int16.op_Less_Hat>


; <Start encoding FStar.Int16.op_Less_Equals_Hat>

(declare-fun FStar.Int16.op_Less_Equals_Hat (Term Term) Term)

(declare-fun FStar.Int16.op_Less_Equals_Hat@tok () Term)

; </end encoding FStar.Int16.op_Less_Equals_Hat>


; <Start encoding FStar.Int16.ct_abs>

(declare-fun Tm_refine_bf5555126581fbecb556df8ab0a05eef () Term)
(declare-fun FStar.Int16.ct_abs (Term) Term)

(declare-fun Tm_refine_c45ab34a5716456732d20bcf7ffaec5e (Term) Term)
(declare-fun Tm_arrow_b49cbe9039c72bedb35334112a647851 () Term)
(declare-fun FStar.Int16.ct_abs@tok () Term)



; </end encoding FStar.Int16.ct_abs>


; <Start encoding FStar.Int16.to_string>

(declare-fun FStar.Int16.to_string (Term) Term)
(declare-fun Tm_arrow_b79d4f54e35e823402b6ea060f6d4e59 () Term)
(declare-fun FStar.Int16.to_string@tok () Term)

; </end encoding FStar.Int16.to_string>


; <Start encoding FStar.Int16.of_string>

(declare-fun FStar.Int16.of_string (Term) Term)
(declare-fun Tm_arrow_e8011cf47c39277f09fdc13e1fb6ea29 () Term)
(declare-fun FStar.Int16.of_string@tok () Term)

; </end encoding FStar.Int16.of_string>


; <Skipped />


; <Start encoding FStar.Int16.__int_to_t>

(declare-fun FStar.Int16.__int_to_t (Term) Term)
(declare-fun Tm_arrow_15c86b42f565747893d23b8c62ede2ef () Term)
(declare-fun FStar.Int16.__int_to_t@tok () Term)

; </end encoding FStar.Int16.__int_to_t>


; <Skipped />


; UNSAT CORE: @MaxFuel_assumption, @MaxIFuel_assumption, @fuel_correspondence_Prims.pow2.fuel_instrumented, @query, constructor_distinct_Lib.IntTypes.S16, constructor_distinct_Lib.IntTypes.S32, constructor_distinct_Lib.IntTypes.SEC, equality_tok_Lib.IntTypes.S16@tok, equality_tok_Lib.IntTypes.S32@tok, equality_tok_Lib.IntTypes.SEC@tok, equation_Lib.IntTypes.bits, equation_Lib.IntTypes.range, equation_Lib.IntTypes.signed, equation_Lib.IntTypes.unsigned, equation_Lib.IntTypes.v, equation_Prims.nat, equation_Prims.pos, equation_Spec.Kyber2.Params.params_q, int_inversion, int_typing, lemma_FStar.UInt.pow2_values, primitive_Prims.op_Addition, primitive_Prims.op_Division, primitive_Prims.op_LessThanOrEqual, primitive_Prims.op_Minus, primitive_Prims.op_Multiply, primitive_Prims.op_Subtraction, projection_inverse_BoxBool_proj_0, projection_inverse_BoxInt_proj_0, refinement_interpretation_Tm_refine_2b320913041b873fce938dd17eebb3e2, refinement_interpretation_Tm_refine_542f9d4f129664613f2483a6c88bc7c2, refinement_interpretation_Tm_refine_774ba3f728d91ead8ef40be66c9802e5, refinement_interpretation_Tm_refine_83845a86f2550cdf941eeb1d9b59602b, refinement_interpretation_Tm_refine_9d3fd79fd314167f1a9c213a188da3ec, refinement_interpretation_Tm_refine_b2401a8cabe2f9a01538f32548fa9f6c, typing_Lib.IntTypes.mk_int, typing_Prims.pow2, typing_tok_Lib.IntTypes.S32@tok, typing_tok_Lib.IntTypes.SEC@tok

;;; End module FStar.Int16 (282 decls; total size 12389)

;;; Start module FStar.Int8

; <Start encoding FStar.Int8.n>

(declare-fun FStar.Int8.n (Dummy_sort) Term)

; </end encoding FStar.Int8.n>


; <Skipped />


; <Start encoding FStar.Int8.t>

(declare-fun FStar.Int8.t () Term)

; </end encoding FStar.Int8.t>


; <Start encoding FStar.Int8.t__uu___haseq>


; </end encoding FStar.Int8.t__uu___haseq>


; <Start encoding FStar.Int8.v>

(declare-fun FStar.Int8.v (Term) Term)
(declare-fun Tm_arrow_43f6603813c73ab1ca4373e96a80ebb3 () Term)
(declare-fun FStar.Int8.v@tok () Term)

; </end encoding FStar.Int8.v>


; <Start encoding FStar.Int8.int_to_t>

(declare-fun FStar.Int8.int_to_t (Term) Term)
(declare-fun Tm_refine_9c18c3ce38588df16c04dd7bb2735919 (Term) Term)
(declare-fun Tm_arrow_9c8e9a076ed5b18c49d5bd9f40ce09a9 () Term)
(declare-fun FStar.Int8.int_to_t@tok () Term)


; </end encoding FStar.Int8.int_to_t>


; <Start encoding FStar.Int8.uv_inv>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.Int8.uv_inv (Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.Int8.uv_inv@tok () Term)

; </end encoding FStar.Int8.uv_inv>


; <Start encoding FStar.Int8.vu_inv>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.Int8.vu_inv (Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.Int8.vu_inv@tok () Term)

; </end encoding FStar.Int8.vu_inv>


; <Start encoding FStar.Int8.v_inj>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.Int8.v_inj (Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.Int8.v_inj@tok () Term)

; </end encoding FStar.Int8.v_inj>


; <Start encoding FStar.Int8.add>

(declare-fun FStar.Int8.add (Term Term) Term)
(declare-fun Tm_refine_6fc6a31ab47b4bdbaebd6950053e5613 (Term Term) Term)
(declare-fun Tm_arrow_8218b87681ff167446f43943649df62f () Term)
(declare-fun FStar.Int8.add@tok () Term)


; </end encoding FStar.Int8.add>


; <Start encoding FStar.Int8.sub>

(declare-fun FStar.Int8.sub (Term Term) Term)
(declare-fun Tm_refine_862d457231c360f6649ae6d8ba5b541b (Term Term) Term)
(declare-fun Tm_arrow_5a21817bbbea98e4cd8552311d34979b () Term)
(declare-fun FStar.Int8.sub@tok () Term)


; </end encoding FStar.Int8.sub>


; <Start encoding FStar.Int8.mul>

(declare-fun FStar.Int8.mul (Term Term) Term)
(declare-fun Tm_refine_43f73b7d72993020418b205a0999eb04 (Term Term) Term)
(declare-fun Tm_arrow_302b0a8650e00006ded35923e58daed2 () Term)
(declare-fun FStar.Int8.mul@tok () Term)


; </end encoding FStar.Int8.mul>


; <Start encoding FStar.Int8.div>

(declare-fun Tm_refine_bcfada7fe24cdb2217294983169b91ee () Term)
(declare-fun FStar.Int8.div (Term Term) Term)

(declare-fun Tm_refine_6b42f81b5b4a0efe3f207760fd11908c (Term Term) Term)
(declare-fun Tm_arrow_8caaf192d6ae747d5e56fb3bd55a009d () Term)
(declare-fun FStar.Int8.div@tok () Term)


; </end encoding FStar.Int8.div>


; <Start encoding FStar.Int8.rem>


(declare-fun FStar.Int8.rem (Term Term) Term)

(declare-fun Tm_refine_fba2a21e6626a3b679cbef8056e37abb (Term Term) Term)
(declare-fun Tm_arrow_efef6c9fb13d2e2757b34ff1994e9bfa () Term)
(declare-fun FStar.Int8.rem@tok () Term)


; </end encoding FStar.Int8.rem>


; <Start encoding FStar.Int8.logand>

(declare-fun FStar.Int8.logand (Term Term) Term)
(declare-fun Tm_refine_5e12831cb9116bd70112d93d2d6c6807 (Term Term) Term)
(declare-fun Tm_arrow_75ab2b3b13a4015130766e4a20124a55 () Term)
(declare-fun FStar.Int8.logand@tok () Term)


; </end encoding FStar.Int8.logand>


; <Start encoding FStar.Int8.logxor>

(declare-fun FStar.Int8.logxor (Term Term) Term)
(declare-fun Tm_refine_584f00a866e490bb4bae2638fd9c79b0 (Term Term) Term)
(declare-fun Tm_arrow_64275246f5477d5f5f1ef1727093e778 () Term)
(declare-fun FStar.Int8.logxor@tok () Term)


; </end encoding FStar.Int8.logxor>


; <Start encoding FStar.Int8.logor>

(declare-fun FStar.Int8.logor (Term Term) Term)
(declare-fun Tm_refine_134164bdbad0a3e994dac33142d3681e (Term Term) Term)
(declare-fun Tm_arrow_5f232a5f8bbec94f1666a600efa599e2 () Term)
(declare-fun FStar.Int8.logor@tok () Term)


; </end encoding FStar.Int8.logor>


; <Start encoding FStar.Int8.lognot>

(declare-fun FStar.Int8.lognot (Term) Term)
(declare-fun Tm_refine_f18dd090dac60beaad71a15678e07e5e (Term) Term)
(declare-fun Tm_arrow_3452d7ef4ad28364d608b221260c1861 () Term)
(declare-fun FStar.Int8.lognot@tok () Term)


; </end encoding FStar.Int8.lognot>


; <Start encoding FStar.Int8.shift_right>

(declare-fun FStar.Int8.shift_right (Term Term) Term)
(declare-fun Tm_refine_27089deb56d9d9a75564ebd98fb2e533 (Term Term) Term)
(declare-fun Tm_arrow_fa7abc2c1eab61a012b1ff2777553858 () Term)
(declare-fun FStar.Int8.shift_right@tok () Term)


; </end encoding FStar.Int8.shift_right>


; <Start encoding FStar.Int8.shift_left>

(declare-fun FStar.Int8.shift_left (Term Term) Term)
(declare-fun Tm_refine_815e3c430ad669a0fa5b3a3b325da391 (Term Term) Term)
(declare-fun Tm_arrow_dcf4a032008174e4f302c20063d74c41 () Term)
(declare-fun FStar.Int8.shift_left@tok () Term)


; </end encoding FStar.Int8.shift_left>


; <Start encoding FStar.Int8.shift_arithmetic_right>

(declare-fun FStar.Int8.shift_arithmetic_right (Term Term) Term)
(declare-fun Tm_refine_2459069c94e2a3c73821eea13d1e9736 (Term Term) Term)
(declare-fun Tm_arrow_d04ac139400a80fe78a1b646e09d1330 () Term)
(declare-fun FStar.Int8.shift_arithmetic_right@tok () Term)


; </end encoding FStar.Int8.shift_arithmetic_right>


; <Start encoding FStar.Int8.eq>

(declare-fun FStar.Int8.eq (Term Term) Term)
(declare-fun Tm_arrow_5260d2ae2d48387a16b7a94cf04acbd1 () Term)
(declare-fun FStar.Int8.eq@tok () Term)

; </end encoding FStar.Int8.eq>


; <Start encoding FStar.Int8.gt>

(declare-fun FStar.Int8.gt (Term Term) Term)

(declare-fun FStar.Int8.gt@tok () Term)

; </end encoding FStar.Int8.gt>


; <Start encoding FStar.Int8.gte>

(declare-fun FStar.Int8.gte (Term Term) Term)

(declare-fun FStar.Int8.gte@tok () Term)

; </end encoding FStar.Int8.gte>


; <Start encoding FStar.Int8.lt>

(declare-fun FStar.Int8.lt (Term Term) Term)

(declare-fun FStar.Int8.lt@tok () Term)

; </end encoding FStar.Int8.lt>


; <Start encoding FStar.Int8.lte>

(declare-fun FStar.Int8.lte (Term Term) Term)

(declare-fun FStar.Int8.lte@tok () Term)

; </end encoding FStar.Int8.lte>


; <Start encoding FStar.Int8.op_Plus_Hat>

(declare-fun FStar.Int8.op_Plus_Hat (Term Term) Term)


(declare-fun FStar.Int8.op_Plus_Hat@tok () Term)


; </end encoding FStar.Int8.op_Plus_Hat>


; <Start encoding FStar.Int8.op_Subtraction_Hat>

(declare-fun FStar.Int8.op_Subtraction_Hat (Term Term) Term)


(declare-fun FStar.Int8.op_Subtraction_Hat@tok () Term)


; </end encoding FStar.Int8.op_Subtraction_Hat>


; <Start encoding FStar.Int8.op_Star_Hat>

(declare-fun FStar.Int8.op_Star_Hat (Term Term) Term)


(declare-fun FStar.Int8.op_Star_Hat@tok () Term)


; </end encoding FStar.Int8.op_Star_Hat>


; <Start encoding FStar.Int8.op_Slash_Hat>


(declare-fun FStar.Int8.op_Slash_Hat (Term Term) Term)



(declare-fun FStar.Int8.op_Slash_Hat@tok () Term)



; </end encoding FStar.Int8.op_Slash_Hat>


; <Start encoding FStar.Int8.op_Percent_Hat>


(declare-fun FStar.Int8.op_Percent_Hat (Term Term) Term)



(declare-fun FStar.Int8.op_Percent_Hat@tok () Term)



; </end encoding FStar.Int8.op_Percent_Hat>


; <Start encoding FStar.Int8.op_Hat_Hat>

(declare-fun FStar.Int8.op_Hat_Hat (Term Term) Term)


(declare-fun FStar.Int8.op_Hat_Hat@tok () Term)


; </end encoding FStar.Int8.op_Hat_Hat>


; <Start encoding FStar.Int8.op_Amp_Hat>

(declare-fun FStar.Int8.op_Amp_Hat (Term Term) Term)


(declare-fun FStar.Int8.op_Amp_Hat@tok () Term)


; </end encoding FStar.Int8.op_Amp_Hat>


; <Start encoding FStar.Int8.op_Bar_Hat>

(declare-fun FStar.Int8.op_Bar_Hat (Term Term) Term)


(declare-fun FStar.Int8.op_Bar_Hat@tok () Term)


; </end encoding FStar.Int8.op_Bar_Hat>


; <Start encoding FStar.Int8.op_Less_Less_Hat>

(declare-fun FStar.Int8.op_Less_Less_Hat (Term Term) Term)


(declare-fun FStar.Int8.op_Less_Less_Hat@tok () Term)


; </end encoding FStar.Int8.op_Less_Less_Hat>


; <Start encoding FStar.Int8.op_Greater_Greater_Hat>

(declare-fun FStar.Int8.op_Greater_Greater_Hat (Term Term) Term)


(declare-fun FStar.Int8.op_Greater_Greater_Hat@tok () Term)


; </end encoding FStar.Int8.op_Greater_Greater_Hat>


; <Start encoding FStar.Int8.op_Greater_Greater_Greater_Hat>

(declare-fun FStar.Int8.op_Greater_Greater_Greater_Hat (Term Term) Term)


(declare-fun FStar.Int8.op_Greater_Greater_Greater_Hat@tok () Term)


; </end encoding FStar.Int8.op_Greater_Greater_Greater_Hat>


; <Start encoding FStar.Int8.op_Equals_Hat>

(declare-fun FStar.Int8.op_Equals_Hat (Term Term) Term)

(declare-fun FStar.Int8.op_Equals_Hat@tok () Term)

; </end encoding FStar.Int8.op_Equals_Hat>


; <Start encoding FStar.Int8.op_Greater_Hat>

(declare-fun FStar.Int8.op_Greater_Hat (Term Term) Term)

(declare-fun FStar.Int8.op_Greater_Hat@tok () Term)

; </end encoding FStar.Int8.op_Greater_Hat>


; <Start encoding FStar.Int8.op_Greater_Equals_Hat>

(declare-fun FStar.Int8.op_Greater_Equals_Hat (Term Term) Term)

(declare-fun FStar.Int8.op_Greater_Equals_Hat@tok () Term)

; </end encoding FStar.Int8.op_Greater_Equals_Hat>


; <Start encoding FStar.Int8.op_Less_Hat>

(declare-fun FStar.Int8.op_Less_Hat (Term Term) Term)

(declare-fun FStar.Int8.op_Less_Hat@tok () Term)

; </end encoding FStar.Int8.op_Less_Hat>


; <Start encoding FStar.Int8.op_Less_Equals_Hat>

(declare-fun FStar.Int8.op_Less_Equals_Hat (Term Term) Term)

(declare-fun FStar.Int8.op_Less_Equals_Hat@tok () Term)

; </end encoding FStar.Int8.op_Less_Equals_Hat>


; <Start encoding FStar.Int8.ct_abs>

(declare-fun Tm_refine_3c6fe23ae90da367aa6a92961d06aaec () Term)
(declare-fun FStar.Int8.ct_abs (Term) Term)

(declare-fun Tm_refine_bde8d01c5fdfb8b8c4e3dd1ab9675afc (Term) Term)
(declare-fun Tm_arrow_052ebf4a77dde51c89b306577df4f4c9 () Term)
(declare-fun FStar.Int8.ct_abs@tok () Term)



; </end encoding FStar.Int8.ct_abs>


; <Start encoding FStar.Int8.to_string>

(declare-fun FStar.Int8.to_string (Term) Term)
(declare-fun Tm_arrow_400358d26faabbce1309072303a3a22b () Term)
(declare-fun FStar.Int8.to_string@tok () Term)

; </end encoding FStar.Int8.to_string>


; <Start encoding FStar.Int8.of_string>

(declare-fun FStar.Int8.of_string (Term) Term)
(declare-fun Tm_arrow_9ca2e4fddc8bc761a6b938f65756e158 () Term)
(declare-fun FStar.Int8.of_string@tok () Term)

; </end encoding FStar.Int8.of_string>


; <Skipped />


; <Start encoding FStar.Int8.__int_to_t>

(declare-fun FStar.Int8.__int_to_t (Term) Term)
(declare-fun Tm_arrow_66eefc0df0e57e313fcd45f9558c6a17 () Term)
(declare-fun FStar.Int8.__int_to_t@tok () Term)

; </end encoding FStar.Int8.__int_to_t>


; <Skipped />


; UNSAT CORE: @MaxFuel_assumption, @MaxIFuel_assumption, @fuel_correspondence_Prims.pow2.fuel_instrumented, @query, constructor_distinct_Lib.IntTypes.S16, constructor_distinct_Lib.IntTypes.S32, constructor_distinct_Lib.IntTypes.SEC, equality_tok_Lib.IntTypes.S16@tok, equality_tok_Lib.IntTypes.S32@tok, equality_tok_Lib.IntTypes.SEC@tok, equation_Lib.IntTypes.bits, equation_Lib.IntTypes.range, equation_Lib.IntTypes.signed, equation_Lib.IntTypes.unsigned, equation_Lib.IntTypes.v, equation_Prims.nat, equation_Prims.pos, equation_Spec.Kyber2.Params.params_q, int_inversion, int_typing, lemma_FStar.UInt.pow2_values, primitive_Prims.op_Addition, primitive_Prims.op_Division, primitive_Prims.op_LessThanOrEqual, primitive_Prims.op_Minus, primitive_Prims.op_Multiply, primitive_Prims.op_Subtraction, projection_inverse_BoxBool_proj_0, projection_inverse_BoxInt_proj_0, refinement_interpretation_Tm_refine_2b320913041b873fce938dd17eebb3e2, refinement_interpretation_Tm_refine_542f9d4f129664613f2483a6c88bc7c2, refinement_interpretation_Tm_refine_774ba3f728d91ead8ef40be66c9802e5, refinement_interpretation_Tm_refine_83845a86f2550cdf941eeb1d9b59602b, refinement_interpretation_Tm_refine_9d3fd79fd314167f1a9c213a188da3ec, refinement_interpretation_Tm_refine_b2401a8cabe2f9a01538f32548fa9f6c, typing_Lib.IntTypes.mk_int, typing_Prims.pow2, typing_tok_Lib.IntTypes.S32@tok, typing_tok_Lib.IntTypes.SEC@tok

;;; End module FStar.Int8 (282 decls; total size 12213)

;;; Start module FStar.UInt64

; <Start encoding FStar.UInt64.n>

(declare-fun FStar.UInt64.n (Dummy_sort) Term)

; </end encoding FStar.UInt64.n>


; <Skipped />


; <Start encoding FStar.UInt64.t>

(declare-fun FStar.UInt64.t () Term)

; </end encoding FStar.UInt64.t>


; <Start encoding FStar.UInt64.t__uu___haseq>


; </end encoding FStar.UInt64.t__uu___haseq>


; <Start encoding FStar.UInt64.v>

(declare-fun FStar.UInt64.v (Term) Term)
(declare-fun Tm_arrow_a2f4da9ddeae24db4804189f83f1b8cc () Term)
(declare-fun FStar.UInt64.v@tok () Term)

; </end encoding FStar.UInt64.v>


; <Start encoding FStar.UInt64.uint_to_t>

(declare-fun FStar.UInt64.uint_to_t (Term) Term)
(declare-fun Tm_refine_689af9466f50f143e51c7e8270f2cee2 (Term) Term)
(declare-fun Tm_arrow_1a701e71412fa688b6705ca6a164cf00 () Term)
(declare-fun FStar.UInt64.uint_to_t@tok () Term)


; </end encoding FStar.UInt64.uint_to_t>


; <Start encoding FStar.UInt64.uv_inv>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.UInt64.uv_inv (Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.UInt64.uv_inv@tok () Term)

; </end encoding FStar.UInt64.uv_inv>


; <Start encoding FStar.UInt64.vu_inv>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.UInt64.vu_inv (Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.UInt64.vu_inv@tok () Term)

; </end encoding FStar.UInt64.vu_inv>


; <Start encoding FStar.UInt64.v_inj>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.UInt64.v_inj (Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.UInt64.v_inj@tok () Term)

; </end encoding FStar.UInt64.v_inj>


; <Start encoding FStar.UInt64.add>

(declare-fun FStar.UInt64.add (Term Term) Term)
(declare-fun Tm_refine_8db5bc3e058ba8660f1d29f550410f79 (Term Term) Term)
(declare-fun Tm_arrow_eac887a9479138bbea8be8c74ae66a6a () Term)
(declare-fun FStar.UInt64.add@tok () Term)


; </end encoding FStar.UInt64.add>


; <Start encoding FStar.UInt64.add_underspec>

(declare-fun FStar.UInt64.add_underspec (Term Term) Term)
(declare-fun Tm_refine_30520f4aa1db6a708962f02a92706a29 (Term Term) Term)
(declare-fun Tm_arrow_3ecb2dd7854525dffb2850fcebe91a8b () Term)
(declare-fun FStar.UInt64.add_underspec@tok () Term)


; </end encoding FStar.UInt64.add_underspec>


; <Start encoding FStar.UInt64.add_mod>

(declare-fun FStar.UInt64.add_mod (Term Term) Term)
(declare-fun Tm_refine_6f711a8125ef1fb553efffd1586844b8 (Term Term) Term)
(declare-fun Tm_arrow_8575722d6bd84fe086882b51510e573d () Term)
(declare-fun FStar.UInt64.add_mod@tok () Term)


; </end encoding FStar.UInt64.add_mod>


; <Start encoding FStar.UInt64.sub>

(declare-fun FStar.UInt64.sub (Term Term) Term)
(declare-fun Tm_refine_0259ae7f711bbf5250aad23eaff14623 (Term Term) Term)
(declare-fun Tm_arrow_694c28c0ec41ea788096358e2e3a2d57 () Term)
(declare-fun FStar.UInt64.sub@tok () Term)


; </end encoding FStar.UInt64.sub>


; <Start encoding FStar.UInt64.sub_underspec>

(declare-fun FStar.UInt64.sub_underspec (Term Term) Term)
(declare-fun Tm_refine_cec805d05e315e9ebc15835b8c937cec (Term Term) Term)
(declare-fun Tm_arrow_b664f86b76aea14c2040aaa5b781d325 () Term)
(declare-fun FStar.UInt64.sub_underspec@tok () Term)


; </end encoding FStar.UInt64.sub_underspec>


; <Start encoding FStar.UInt64.sub_mod>

(declare-fun FStar.UInt64.sub_mod (Term Term) Term)
(declare-fun Tm_refine_cce5569ce2fdd586ce3d0cdbed37c360 (Term Term) Term)
(declare-fun Tm_arrow_ae6576cb12ae206e4ae62605e07d5521 () Term)
(declare-fun FStar.UInt64.sub_mod@tok () Term)


; </end encoding FStar.UInt64.sub_mod>


; <Start encoding FStar.UInt64.mul>

(declare-fun FStar.UInt64.mul (Term Term) Term)
(declare-fun Tm_refine_f53dbabf36543e6603d3884a7abe5c9d (Term Term) Term)
(declare-fun Tm_arrow_f7ece7ff3ff754975697c1120e5e1dfd () Term)
(declare-fun FStar.UInt64.mul@tok () Term)


; </end encoding FStar.UInt64.mul>


; <Start encoding FStar.UInt64.mul_underspec>

(declare-fun FStar.UInt64.mul_underspec (Term Term) Term)
(declare-fun Tm_refine_f819583bd425fbc4ed9986e721e32b5c (Term Term) Term)
(declare-fun Tm_arrow_854bc72472517d18139e5653ff3e092d () Term)
(declare-fun FStar.UInt64.mul_underspec@tok () Term)


; </end encoding FStar.UInt64.mul_underspec>


; <Start encoding FStar.UInt64.mul_mod>

(declare-fun FStar.UInt64.mul_mod (Term Term) Term)
(declare-fun Tm_refine_353967525d91fe7285f7764921186a68 (Term Term) Term)
(declare-fun Tm_arrow_947e057ab406dc1a7e2e2b35b1257d2c () Term)
(declare-fun FStar.UInt64.mul_mod@tok () Term)


; </end encoding FStar.UInt64.mul_mod>


; <Start encoding FStar.UInt64.mul_div>

(declare-fun FStar.UInt64.mul_div (Term Term) Term)
(declare-fun Tm_refine_cdb44c86f58d0e20c8b3519d3cb14e7c (Term Term) Term)
(declare-fun Tm_arrow_ca9e6066cdda4bd7e12ce189dc2c98a9 () Term)
(declare-fun FStar.UInt64.mul_div@tok () Term)


; </end encoding FStar.UInt64.mul_div>


; <Start encoding FStar.UInt64.div>

(declare-fun Tm_refine_79d30f0bd2097427fe8d96697e20df0f () Term)
(declare-fun FStar.UInt64.div (Term Term) Term)

(declare-fun Tm_refine_cea82fdb2c3c307d773cae3c18ebf2b8 (Term Term) Term)
(declare-fun Tm_arrow_03651bc23d02cbd21b45681db45ca681 () Term)
(declare-fun FStar.UInt64.div@tok () Term)


; </end encoding FStar.UInt64.div>


; <Start encoding FStar.UInt64.rem>


(declare-fun FStar.UInt64.rem (Term Term) Term)

(declare-fun Tm_refine_40913005fcdb02d3c1a9de40e3088fb6 (Term Term) Term)
(declare-fun Tm_arrow_f6daf6070d48109b887896781d8d7028 () Term)
(declare-fun FStar.UInt64.rem@tok () Term)


; </end encoding FStar.UInt64.rem>


; <Start encoding FStar.UInt64.logand>

(declare-fun FStar.UInt64.logand (Term Term) Term)
(declare-fun Tm_refine_fc8b02edd6d4507c20589e697568337f (Term Term) Term)
(declare-fun Tm_arrow_a922e8a00e3054757d55985e67bcd94c () Term)
(declare-fun FStar.UInt64.logand@tok () Term)


; </end encoding FStar.UInt64.logand>


; <Start encoding FStar.UInt64.logxor>

(declare-fun FStar.UInt64.logxor (Term Term) Term)
(declare-fun Tm_refine_75ef378c01efa37f4dfff3ea9efb36a5 (Term Term) Term)
(declare-fun Tm_arrow_bb9545ce70e83100010f56f84c3a6ecf () Term)
(declare-fun FStar.UInt64.logxor@tok () Term)


; </end encoding FStar.UInt64.logxor>


; <Start encoding FStar.UInt64.logor>

(declare-fun FStar.UInt64.logor (Term Term) Term)
(declare-fun Tm_refine_310e35e7b50334cd45a94554dfa7956f (Term Term) Term)
(declare-fun Tm_arrow_9e844b7d1af974e9810866c41d982883 () Term)
(declare-fun FStar.UInt64.logor@tok () Term)


; </end encoding FStar.UInt64.logor>


; <Start encoding FStar.UInt64.lognot>

(declare-fun FStar.UInt64.lognot (Term) Term)
(declare-fun Tm_refine_97db105b62009a1e332be0ecdebf5887 (Term) Term)
(declare-fun Tm_arrow_9dc0f8ae6a99884263e3eb4bee3d254d () Term)
(declare-fun FStar.UInt64.lognot@tok () Term)


; </end encoding FStar.UInt64.lognot>


; <Start encoding FStar.UInt64.shift_right>

(declare-fun FStar.UInt64.shift_right (Term Term) Term)
(declare-fun Tm_refine_88040590729e0cf7c1fa8ff71ceb6d9e (Term Term) Term)
(declare-fun Tm_arrow_e4cf5f3f51ab7cdef8ea6672e9dd9c57 () Term)
(declare-fun FStar.UInt64.shift_right@tok () Term)


; </end encoding FStar.UInt64.shift_right>


; <Start encoding FStar.UInt64.shift_left>

(declare-fun FStar.UInt64.shift_left (Term Term) Term)
(declare-fun Tm_refine_4aba674d4d89fd88af8e58e26a200053 (Term Term) Term)
(declare-fun Tm_arrow_2404bf62117b936ff915c06f2d21bc7e () Term)
(declare-fun FStar.UInt64.shift_left@tok () Term)


; </end encoding FStar.UInt64.shift_left>


; <Start encoding FStar.UInt64.eq>

(declare-fun FStar.UInt64.eq (Term Term) Term)
(declare-fun Tm_arrow_0ffcf39b8a32f025d2561257331795d6 () Term)
(declare-fun FStar.UInt64.eq@tok () Term)

; </end encoding FStar.UInt64.eq>


; <Start encoding FStar.UInt64.gt>

(declare-fun FStar.UInt64.gt (Term Term) Term)

(declare-fun FStar.UInt64.gt@tok () Term)

; </end encoding FStar.UInt64.gt>


; <Start encoding FStar.UInt64.gte>

(declare-fun FStar.UInt64.gte (Term Term) Term)

(declare-fun FStar.UInt64.gte@tok () Term)

; </end encoding FStar.UInt64.gte>


; <Start encoding FStar.UInt64.lt>

(declare-fun FStar.UInt64.lt (Term Term) Term)

(declare-fun FStar.UInt64.lt@tok () Term)

; </end encoding FStar.UInt64.lt>


; <Start encoding FStar.UInt64.lte>

(declare-fun FStar.UInt64.lte (Term Term) Term)

(declare-fun FStar.UInt64.lte@tok () Term)

; </end encoding FStar.UInt64.lte>


; <Start encoding FStar.UInt64.minus>

(declare-fun FStar.UInt64.minus (Term) Term)
(declare-fun Tm_arrow_fecc3e3818c38bd44799597ebc955c6f () Term)
(declare-fun FStar.UInt64.minus@tok () Term)

; </end encoding FStar.UInt64.minus>


; <Start encoding FStar.UInt64.n_minus_one>

(declare-fun FStar.UInt64.n_minus_one (Dummy_sort) Term)

; </end encoding FStar.UInt64.n_minus_one>


; <Skipped />


; <Start encoding FStar.UInt64.eq_mask>

(declare-fun FStar.UInt64.eq_mask (Term Term) Term)
(declare-fun Tm_refine_0ee1d29a79e71092cd60594854f680fa (Term Term) Term)
(declare-fun Tm_arrow_9ee842d2eb7e30d8166a7dfc64b92b86 () Term)
(declare-fun FStar.UInt64.eq_mask@tok () Term)


; </end encoding FStar.UInt64.eq_mask>


; <Start encoding FStar.UInt64.lemma_sub_msbs>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.UInt64.lemma_sub_msbs (Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.UInt64.lemma_sub_msbs@tok () Term)

; </end encoding FStar.UInt64.lemma_sub_msbs>


; <Start encoding FStar.UInt64.gte_mask>

(declare-fun FStar.UInt64.gte_mask (Term Term) Term)
(declare-fun Tm_refine_fccf05cdab966d5da487c6a7646b30e6 (Term Term) Term)
(declare-fun Tm_arrow_f5e3442361edcf7519b966526c30c289 () Term)
(declare-fun FStar.UInt64.gte_mask@tok () Term)


; </end encoding FStar.UInt64.gte_mask>


; <Skipped />


; <Start encoding FStar.UInt64.op_Plus_Hat>

(declare-fun FStar.UInt64.op_Plus_Hat (Term Term) Term)


(declare-fun FStar.UInt64.op_Plus_Hat@tok () Term)


; </end encoding FStar.UInt64.op_Plus_Hat>


; <Start encoding FStar.UInt64.op_Plus_Question_Hat>

(declare-fun FStar.UInt64.op_Plus_Question_Hat (Term Term) Term)


(declare-fun FStar.UInt64.op_Plus_Question_Hat@tok () Term)


; </end encoding FStar.UInt64.op_Plus_Question_Hat>


; <Start encoding FStar.UInt64.op_Plus_Percent_Hat>

(declare-fun FStar.UInt64.op_Plus_Percent_Hat (Term Term) Term)


(declare-fun FStar.UInt64.op_Plus_Percent_Hat@tok () Term)


; </end encoding FStar.UInt64.op_Plus_Percent_Hat>


; <Start encoding FStar.UInt64.op_Subtraction_Hat>

(declare-fun FStar.UInt64.op_Subtraction_Hat (Term Term) Term)


(declare-fun FStar.UInt64.op_Subtraction_Hat@tok () Term)


; </end encoding FStar.UInt64.op_Subtraction_Hat>


; <Start encoding FStar.UInt64.op_Subtraction_Question_Hat>

(declare-fun FStar.UInt64.op_Subtraction_Question_Hat (Term Term) Term)


(declare-fun FStar.UInt64.op_Subtraction_Question_Hat@tok () Term)


; </end encoding FStar.UInt64.op_Subtraction_Question_Hat>


; <Start encoding FStar.UInt64.op_Subtraction_Percent_Hat>

(declare-fun FStar.UInt64.op_Subtraction_Percent_Hat (Term Term) Term)


(declare-fun FStar.UInt64.op_Subtraction_Percent_Hat@tok () Term)


; </end encoding FStar.UInt64.op_Subtraction_Percent_Hat>


; <Start encoding FStar.UInt64.op_Star_Hat>

(declare-fun FStar.UInt64.op_Star_Hat (Term Term) Term)


(declare-fun FStar.UInt64.op_Star_Hat@tok () Term)


; </end encoding FStar.UInt64.op_Star_Hat>


; <Start encoding FStar.UInt64.op_Star_Question_Hat>

(declare-fun FStar.UInt64.op_Star_Question_Hat (Term Term) Term)


(declare-fun FStar.UInt64.op_Star_Question_Hat@tok () Term)


; </end encoding FStar.UInt64.op_Star_Question_Hat>


; <Start encoding FStar.UInt64.op_Star_Percent_Hat>

(declare-fun FStar.UInt64.op_Star_Percent_Hat (Term Term) Term)


(declare-fun FStar.UInt64.op_Star_Percent_Hat@tok () Term)


; </end encoding FStar.UInt64.op_Star_Percent_Hat>


; <Start encoding FStar.UInt64.op_Star_Slash_Hat>

(declare-fun FStar.UInt64.op_Star_Slash_Hat (Term Term) Term)


(declare-fun FStar.UInt64.op_Star_Slash_Hat@tok () Term)


; </end encoding FStar.UInt64.op_Star_Slash_Hat>


; <Start encoding FStar.UInt64.op_Slash_Hat>


(declare-fun FStar.UInt64.op_Slash_Hat (Term Term) Term)



(declare-fun FStar.UInt64.op_Slash_Hat@tok () Term)



; </end encoding FStar.UInt64.op_Slash_Hat>


; <Start encoding FStar.UInt64.op_Percent_Hat>


(declare-fun FStar.UInt64.op_Percent_Hat (Term Term) Term)



(declare-fun FStar.UInt64.op_Percent_Hat@tok () Term)



; </end encoding FStar.UInt64.op_Percent_Hat>


; <Start encoding FStar.UInt64.op_Hat_Hat>

(declare-fun FStar.UInt64.op_Hat_Hat (Term Term) Term)


(declare-fun FStar.UInt64.op_Hat_Hat@tok () Term)


; </end encoding FStar.UInt64.op_Hat_Hat>


; <Start encoding FStar.UInt64.op_Amp_Hat>

(declare-fun FStar.UInt64.op_Amp_Hat (Term Term) Term)


(declare-fun FStar.UInt64.op_Amp_Hat@tok () Term)


; </end encoding FStar.UInt64.op_Amp_Hat>


; <Start encoding FStar.UInt64.op_Bar_Hat>

(declare-fun FStar.UInt64.op_Bar_Hat (Term Term) Term)


(declare-fun FStar.UInt64.op_Bar_Hat@tok () Term)


; </end encoding FStar.UInt64.op_Bar_Hat>


; <Start encoding FStar.UInt64.op_Less_Less_Hat>

(declare-fun FStar.UInt64.op_Less_Less_Hat (Term Term) Term)


(declare-fun FStar.UInt64.op_Less_Less_Hat@tok () Term)


; </end encoding FStar.UInt64.op_Less_Less_Hat>


; <Start encoding FStar.UInt64.op_Greater_Greater_Hat>

(declare-fun FStar.UInt64.op_Greater_Greater_Hat (Term Term) Term)


(declare-fun FStar.UInt64.op_Greater_Greater_Hat@tok () Term)


; </end encoding FStar.UInt64.op_Greater_Greater_Hat>


; <Start encoding FStar.UInt64.op_Equals_Hat>

(declare-fun FStar.UInt64.op_Equals_Hat (Term Term) Term)

(declare-fun FStar.UInt64.op_Equals_Hat@tok () Term)

; </end encoding FStar.UInt64.op_Equals_Hat>


; <Start encoding FStar.UInt64.op_Greater_Hat>

(declare-fun FStar.UInt64.op_Greater_Hat (Term Term) Term)

(declare-fun FStar.UInt64.op_Greater_Hat@tok () Term)

; </end encoding FStar.UInt64.op_Greater_Hat>


; <Start encoding FStar.UInt64.op_Greater_Equals_Hat>

(declare-fun FStar.UInt64.op_Greater_Equals_Hat (Term Term) Term)

(declare-fun FStar.UInt64.op_Greater_Equals_Hat@tok () Term)

; </end encoding FStar.UInt64.op_Greater_Equals_Hat>


; <Start encoding FStar.UInt64.op_Less_Hat>

(declare-fun FStar.UInt64.op_Less_Hat (Term Term) Term)

(declare-fun FStar.UInt64.op_Less_Hat@tok () Term)

; </end encoding FStar.UInt64.op_Less_Hat>


; <Start encoding FStar.UInt64.op_Less_Equals_Hat>

(declare-fun FStar.UInt64.op_Less_Equals_Hat (Term Term) Term)

(declare-fun FStar.UInt64.op_Less_Equals_Hat@tok () Term)

; </end encoding FStar.UInt64.op_Less_Equals_Hat>


; <Start encoding FStar.UInt64.to_string>

(declare-fun FStar.UInt64.to_string (Term) Term)
(declare-fun Tm_arrow_eadaf45fbe43a52bd1e81e6277ec1e5d () Term)
(declare-fun FStar.UInt64.to_string@tok () Term)

; </end encoding FStar.UInt64.to_string>


; <Start encoding FStar.UInt64.of_string>

(declare-fun FStar.UInt64.of_string (Term) Term)
(declare-fun Tm_arrow_62958bdcc2cfcc0e190321112b871f4a () Term)
(declare-fun FStar.UInt64.of_string@tok () Term)

; </end encoding FStar.UInt64.of_string>


; <Skipped />


; <Start encoding FStar.UInt64.__uint_to_t>

(declare-fun FStar.UInt64.__uint_to_t (Term) Term)
(declare-fun Tm_arrow_07df0a4b62f40f4b63a6f4429c4d256a () Term)
(declare-fun FStar.UInt64.__uint_to_t@tok () Term)

; </end encoding FStar.UInt64.__uint_to_t>


; <Skipped />


; UNSAT CORE: @MaxFuel_assumption, @MaxIFuel_assumption, @fuel_correspondence_Prims.pow2.fuel_instrumented, @query, constructor_distinct_Lib.IntTypes.S16, constructor_distinct_Lib.IntTypes.S32, constructor_distinct_Lib.IntTypes.SEC, equality_tok_Lib.IntTypes.S16@tok, equality_tok_Lib.IntTypes.S32@tok, equality_tok_Lib.IntTypes.SEC@tok, equation_Lib.IntTypes.bits, equation_Lib.IntTypes.range, equation_Lib.IntTypes.signed, equation_Lib.IntTypes.unsigned, equation_Lib.IntTypes.v, equation_Prims.nat, equation_Prims.pos, equation_Spec.Kyber2.Params.params_q, int_inversion, int_typing, lemma_FStar.UInt.pow2_values, primitive_Prims.op_Addition, primitive_Prims.op_Division, primitive_Prims.op_LessThanOrEqual, primitive_Prims.op_Minus, primitive_Prims.op_Multiply, primitive_Prims.op_Subtraction, projection_inverse_BoxBool_proj_0, projection_inverse_BoxInt_proj_0, refinement_interpretation_Tm_refine_2b320913041b873fce938dd17eebb3e2, refinement_interpretation_Tm_refine_542f9d4f129664613f2483a6c88bc7c2, refinement_interpretation_Tm_refine_774ba3f728d91ead8ef40be66c9802e5, refinement_interpretation_Tm_refine_83845a86f2550cdf941eeb1d9b59602b, refinement_interpretation_Tm_refine_9d3fd79fd314167f1a9c213a188da3ec, refinement_interpretation_Tm_refine_b2401a8cabe2f9a01538f32548fa9f6c, typing_Lib.IntTypes.mk_int, typing_Prims.pow2, typing_tok_Lib.IntTypes.S32@tok, typing_tok_Lib.IntTypes.SEC@tok

;;; End module FStar.UInt64 (384 decls; total size 16941)

;;; Start module FStar.UInt128

; <Start encoding FStar.UInt128.n>

(declare-fun FStar.UInt128.n (Dummy_sort) Term)

; </end encoding FStar.UInt128.n>


; <Start encoding FStar.UInt128.t>

(declare-fun FStar.UInt128.t (Dummy_sort) Term)



; </end encoding FStar.UInt128.t>


; <Start encoding FStar.UInt128.v>

(declare-fun FStar.UInt128.v (Term) Term)
(declare-fun Tm_arrow_1e0f5f336a391e0e3f222969a4e20082 () Term)
(declare-fun FStar.UInt128.v@tok () Term)

; </end encoding FStar.UInt128.v>


; <Start encoding FStar.UInt128.uint_to_t>

(declare-fun FStar.UInt128.uint_to_t (Term) Term)
(declare-fun Tm_refine_5e8afe5488805949b2c6333b5c9e0e16 (Term) Term)
(declare-fun Tm_arrow_6add220f3aefee51a2a01f25e88b3a4d () Term)
(declare-fun FStar.UInt128.uint_to_t@tok () Term)


; </end encoding FStar.UInt128.uint_to_t>


; <Start encoding FStar.UInt128.v_inj>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.UInt128.v_inj (Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.UInt128.v_inj@tok () Term)

; </end encoding FStar.UInt128.v_inj>


; <Start encoding FStar.UInt128.add>

(declare-fun FStar.UInt128.add (Term Term) Term)
(declare-fun Tm_refine_200045f8615f23a9b7995d72ac63d949 (Term Term) Term)
(declare-fun Tm_arrow_fb9425641edccbf43d8d0ff9038e9a40 () Term)
(declare-fun FStar.UInt128.add@tok () Term)


; </end encoding FStar.UInt128.add>


; <Start encoding FStar.UInt128.add_underspec>

(declare-fun FStar.UInt128.add_underspec (Term Term) Term)
(declare-fun Tm_refine_f0a188da54db4dcbcbfe1dd04a17a348 (Term Term) Term)
(declare-fun Tm_arrow_a6d7d16b168014a515741d53de84e0e9 () Term)
(declare-fun FStar.UInt128.add_underspec@tok () Term)


; </end encoding FStar.UInt128.add_underspec>


; <Start encoding FStar.UInt128.add_mod>

(declare-fun FStar.UInt128.add_mod (Term Term) Term)
(declare-fun Tm_refine_0b9eeff4a539d64421bc9cdf6ccef56c (Term Term) Term)
(declare-fun Tm_arrow_7a8c80680009cc49cfc9cd9ec75a4263 () Term)
(declare-fun FStar.UInt128.add_mod@tok () Term)


; </end encoding FStar.UInt128.add_mod>


; <Start encoding FStar.UInt128.sub>

(declare-fun FStar.UInt128.sub (Term Term) Term)
(declare-fun Tm_refine_f570d27ada9e8b417d745c2ba97c9454 (Term Term) Term)
(declare-fun Tm_arrow_66edeed80e2b43fa22b95ab3137c9c4c () Term)
(declare-fun FStar.UInt128.sub@tok () Term)


; </end encoding FStar.UInt128.sub>


; <Start encoding FStar.UInt128.sub_underspec>

(declare-fun FStar.UInt128.sub_underspec (Term Term) Term)
(declare-fun Tm_refine_783bc70be359dac929d8f93ad2fd48cf (Term Term) Term)
(declare-fun Tm_arrow_1649416594e0f923a0b8de592081403d () Term)
(declare-fun FStar.UInt128.sub_underspec@tok () Term)


; </end encoding FStar.UInt128.sub_underspec>


; <Start encoding FStar.UInt128.sub_mod>

(declare-fun FStar.UInt128.sub_mod (Term Term) Term)
(declare-fun Tm_refine_95b2f31bb163e95302627d5143c54d2a (Term Term) Term)
(declare-fun Tm_arrow_5f5301d7f0dab1d6008a26736df4cf49 () Term)
(declare-fun FStar.UInt128.sub_mod@tok () Term)


; </end encoding FStar.UInt128.sub_mod>


; <Start encoding FStar.UInt128.logand>

(declare-fun FStar.UInt128.logand (Term Term) Term)
(declare-fun Tm_refine_6377d26335dc60c35078980c34caecb6 (Term Term) Term)
(declare-fun Tm_arrow_77ff2c671bb0c2c1fcc14fbf10eeb65b () Term)
(declare-fun FStar.UInt128.logand@tok () Term)


; </end encoding FStar.UInt128.logand>


; <Start encoding FStar.UInt128.logxor>

(declare-fun FStar.UInt128.logxor (Term Term) Term)
(declare-fun Tm_refine_1e2a54f659380dff04459b91e600441e (Term Term) Term)
(declare-fun Tm_arrow_7f84de3be03d468fa2ad17457d9f4a18 () Term)
(declare-fun FStar.UInt128.logxor@tok () Term)


; </end encoding FStar.UInt128.logxor>


; <Start encoding FStar.UInt128.logor>

(declare-fun FStar.UInt128.logor (Term Term) Term)
(declare-fun Tm_refine_be6bb0b9b6f3f07f3a5bb3ae3b56ec6a (Term Term) Term)
(declare-fun Tm_arrow_98d3158ebc9bf0ad30b0a1e6ea069757 () Term)
(declare-fun FStar.UInt128.logor@tok () Term)


; </end encoding FStar.UInt128.logor>


; <Start encoding FStar.UInt128.lognot>

(declare-fun FStar.UInt128.lognot (Term) Term)
(declare-fun Tm_refine_1512b534c5a3f7ce35a7cbe610648d54 (Term) Term)
(declare-fun Tm_arrow_a392c4cff94318eebb1d118180d500d5 () Term)
(declare-fun FStar.UInt128.lognot@tok () Term)


; </end encoding FStar.UInt128.lognot>


; <Start encoding FStar.UInt128.__uint_to_t>

(declare-fun FStar.UInt128.__uint_to_t (Term) Term)
(declare-fun Tm_arrow_631f4d97ec7ab749f44ac6b2cdfdd773 () Term)
(declare-fun FStar.UInt128.__uint_to_t@tok () Term)

; </end encoding FStar.UInt128.__uint_to_t>


; <Start encoding FStar.UInt128.shift_left>

(declare-fun FStar.UInt128.shift_left (Term Term) Term)
(declare-fun Tm_refine_a1ecca9ac49058a08f58aac038646add (Term Term) Term)
(declare-fun Tm_arrow_135da308b0ac98c589fc9b4ff42b12b3 () Term)
(declare-fun FStar.UInt128.shift_left@tok () Term)


; </end encoding FStar.UInt128.shift_left>


; <Start encoding FStar.UInt128.shift_right>

(declare-fun FStar.UInt128.shift_right (Term Term) Term)
(declare-fun Tm_refine_ae880c61bd89ebe8bd4cc06ccf657330 (Term Term) Term)
(declare-fun Tm_arrow_c7a29220b1a4f641c5091a7ead6c9e4e () Term)
(declare-fun FStar.UInt128.shift_right@tok () Term)


; </end encoding FStar.UInt128.shift_right>


; <Start encoding FStar.UInt128.eq>

(declare-fun FStar.UInt128.eq (Term Term) Term)
(declare-fun Tm_refine_17bdce673f0f99167643711ae2c8398d (Term Term) Term)
(declare-fun Tm_arrow_6a8308c5b55a94e42f409204b68a39fe () Term)
(declare-fun FStar.UInt128.eq@tok () Term)


; </end encoding FStar.UInt128.eq>


; <Start encoding FStar.UInt128.gt>

(declare-fun FStar.UInt128.gt (Term Term) Term)
(declare-fun Tm_refine_ad71613c7c18e4200ebe056ffd50c6bd (Term Term) Term)
(declare-fun Tm_arrow_879ba229f4716600b8dd7fd9a02a56b0 () Term)
(declare-fun FStar.UInt128.gt@tok () Term)


; </end encoding FStar.UInt128.gt>


; <Start encoding FStar.UInt128.lt>

(declare-fun FStar.UInt128.lt (Term Term) Term)
(declare-fun Tm_refine_d92cd57a31527a4277019659be7180b3 (Term Term) Term)
(declare-fun Tm_arrow_342ba56e15643014ec03fa8309d60fd3 () Term)
(declare-fun FStar.UInt128.lt@tok () Term)


; </end encoding FStar.UInt128.lt>


; <Start encoding FStar.UInt128.gte>

(declare-fun FStar.UInt128.gte (Term Term) Term)
(declare-fun Tm_refine_af3877cdc4e82890dc596c9b9a18e702 (Term Term) Term)
(declare-fun Tm_arrow_7722b191f0154868206c9aed80fbb3bc () Term)
(declare-fun FStar.UInt128.gte@tok () Term)


; </end encoding FStar.UInt128.gte>


; <Start encoding FStar.UInt128.lte>

(declare-fun FStar.UInt128.lte (Term Term) Term)
(declare-fun Tm_refine_054034522c859ee7a09294edf08a7add (Term Term) Term)
(declare-fun Tm_arrow_cfe624425159e4a3707dc9302bca8b3d () Term)
(declare-fun FStar.UInt128.lte@tok () Term)


; </end encoding FStar.UInt128.lte>


; <Start encoding FStar.UInt128.eq_mask>

(declare-fun FStar.UInt128.eq_mask (Term Term) Term)
(declare-fun Tm_refine_68ab6aeda386ed241196c1cf02a3355f (Term Term) Term)
(declare-fun Tm_arrow_8744aced183e131fdcd8a3d0b5b481db () Term)
(declare-fun FStar.UInt128.eq_mask@tok () Term)


; </end encoding FStar.UInt128.eq_mask>


; <Start encoding FStar.UInt128.gte_mask>

(declare-fun FStar.UInt128.gte_mask (Term Term) Term)
(declare-fun Tm_refine_c14dd0a1e5e977af38870e46b185d9f2 (Term Term) Term)
(declare-fun Tm_arrow_e86638e904e458749403b2b51347361f () Term)
(declare-fun FStar.UInt128.gte_mask@tok () Term)


; </end encoding FStar.UInt128.gte_mask>


; <Start encoding FStar.UInt128.uint64_to_uint128>

(declare-fun FStar.UInt128.uint64_to_uint128 (Term) Term)
(declare-fun Tm_refine_89263c8dd7df5c497acdada0682b1aab (Term) Term)
(declare-fun Tm_arrow_ed21e069ecb28f59c416a7b67f15246c () Term)
(declare-fun FStar.UInt128.uint64_to_uint128@tok () Term)


; </end encoding FStar.UInt128.uint64_to_uint128>


; <Start encoding FStar.UInt128.uint128_to_uint64>

(declare-fun FStar.UInt128.uint128_to_uint64 (Term) Term)
(declare-fun Tm_refine_338a102944bc2ef4f4b05c7ace7637ea (Term) Term)
(declare-fun Tm_arrow_1968c0cb4b8383b2e166a34131275d79 () Term)
(declare-fun FStar.UInt128.uint128_to_uint64@tok () Term)


; </end encoding FStar.UInt128.uint128_to_uint64>


; <Start encoding FStar.UInt128.op_Plus_Hat>

(declare-fun FStar.UInt128.op_Plus_Hat (Term Term) Term)


(declare-fun FStar.UInt128.op_Plus_Hat@tok () Term)


; </end encoding FStar.UInt128.op_Plus_Hat>


; <Start encoding FStar.UInt128.op_Plus_Question_Hat>

(declare-fun FStar.UInt128.op_Plus_Question_Hat (Term Term) Term)


(declare-fun FStar.UInt128.op_Plus_Question_Hat@tok () Term)


; </end encoding FStar.UInt128.op_Plus_Question_Hat>


; <Start encoding FStar.UInt128.op_Plus_Percent_Hat>

(declare-fun FStar.UInt128.op_Plus_Percent_Hat (Term Term) Term)


(declare-fun FStar.UInt128.op_Plus_Percent_Hat@tok () Term)


; </end encoding FStar.UInt128.op_Plus_Percent_Hat>


; <Start encoding FStar.UInt128.op_Subtraction_Hat>

(declare-fun FStar.UInt128.op_Subtraction_Hat (Term Term) Term)


(declare-fun FStar.UInt128.op_Subtraction_Hat@tok () Term)


; </end encoding FStar.UInt128.op_Subtraction_Hat>


; <Start encoding FStar.UInt128.op_Subtraction_Question_Hat>

(declare-fun FStar.UInt128.op_Subtraction_Question_Hat (Term Term) Term)


(declare-fun FStar.UInt128.op_Subtraction_Question_Hat@tok () Term)


; </end encoding FStar.UInt128.op_Subtraction_Question_Hat>


; <Start encoding FStar.UInt128.op_Subtraction_Percent_Hat>

(declare-fun FStar.UInt128.op_Subtraction_Percent_Hat (Term Term) Term)


(declare-fun FStar.UInt128.op_Subtraction_Percent_Hat@tok () Term)


; </end encoding FStar.UInt128.op_Subtraction_Percent_Hat>


; <Start encoding FStar.UInt128.op_Amp_Hat>

(declare-fun FStar.UInt128.op_Amp_Hat (Term Term) Term)


(declare-fun FStar.UInt128.op_Amp_Hat@tok () Term)


; </end encoding FStar.UInt128.op_Amp_Hat>


; <Start encoding FStar.UInt128.op_Hat_Hat>

(declare-fun FStar.UInt128.op_Hat_Hat (Term Term) Term)


(declare-fun FStar.UInt128.op_Hat_Hat@tok () Term)


; </end encoding FStar.UInt128.op_Hat_Hat>


; <Start encoding FStar.UInt128.op_Bar_Hat>

(declare-fun FStar.UInt128.op_Bar_Hat (Term Term) Term)


(declare-fun FStar.UInt128.op_Bar_Hat@tok () Term)


; </end encoding FStar.UInt128.op_Bar_Hat>


; <Start encoding FStar.UInt128.op_Less_Less_Hat>

(declare-fun FStar.UInt128.op_Less_Less_Hat (Term Term) Term)


(declare-fun FStar.UInt128.op_Less_Less_Hat@tok () Term)


; </end encoding FStar.UInt128.op_Less_Less_Hat>


; <Start encoding FStar.UInt128.op_Greater_Greater_Hat>

(declare-fun FStar.UInt128.op_Greater_Greater_Hat (Term Term) Term)


(declare-fun FStar.UInt128.op_Greater_Greater_Hat@tok () Term)


; </end encoding FStar.UInt128.op_Greater_Greater_Hat>


; <Start encoding FStar.UInt128.op_Equals_Hat>

(declare-fun FStar.UInt128.op_Equals_Hat (Term Term) Term)


(declare-fun FStar.UInt128.op_Equals_Hat@tok () Term)


; </end encoding FStar.UInt128.op_Equals_Hat>


; <Start encoding FStar.UInt128.op_Greater_Hat>

(declare-fun FStar.UInt128.op_Greater_Hat (Term Term) Term)


(declare-fun FStar.UInt128.op_Greater_Hat@tok () Term)


; </end encoding FStar.UInt128.op_Greater_Hat>


; <Start encoding FStar.UInt128.op_Less_Hat>

(declare-fun FStar.UInt128.op_Less_Hat (Term Term) Term)


(declare-fun FStar.UInt128.op_Less_Hat@tok () Term)


; </end encoding FStar.UInt128.op_Less_Hat>


; <Start encoding FStar.UInt128.op_Greater_Equals_Hat>

(declare-fun FStar.UInt128.op_Greater_Equals_Hat (Term Term) Term)


(declare-fun FStar.UInt128.op_Greater_Equals_Hat@tok () Term)


; </end encoding FStar.UInt128.op_Greater_Equals_Hat>


; <Start encoding FStar.UInt128.op_Less_Equals_Hat>

(declare-fun FStar.UInt128.op_Less_Equals_Hat (Term Term) Term)


(declare-fun FStar.UInt128.op_Less_Equals_Hat@tok () Term)


; </end encoding FStar.UInt128.op_Less_Equals_Hat>


; <Start encoding FStar.UInt128.mul32>

(declare-fun FStar.UInt128.mul32 (Term Term) Term)
(declare-fun Tm_refine_6cd4abb57f0a59d82dc8ad7d5d61011b (Term Term) Term)
(declare-fun Tm_arrow_5fb2add5c46e9416df24f5cc29e4b2a3 () Term)
(declare-fun FStar.UInt128.mul32@tok () Term)


; </end encoding FStar.UInt128.mul32>


; <Start encoding FStar.UInt128.mul_wide>

(declare-fun FStar.UInt128.mul_wide (Term Term) Term)
(declare-fun Tm_refine_3f8bbe5c36b8972a6ce0499e59ec5fe3 (Term Term) Term)
(declare-fun Tm_arrow_c463badca2a453f880a39f1972a873d7 () Term)
(declare-fun FStar.UInt128.mul_wide@tok () Term)


; </end encoding FStar.UInt128.mul_wide>


; UNSAT CORE: @MaxFuel_assumption, @MaxIFuel_assumption, @fuel_correspondence_Prims.pow2.fuel_instrumented, @query, constructor_distinct_Lib.IntTypes.S16, constructor_distinct_Lib.IntTypes.S32, constructor_distinct_Lib.IntTypes.SEC, equality_tok_Lib.IntTypes.S16@tok, equality_tok_Lib.IntTypes.S32@tok, equality_tok_Lib.IntTypes.SEC@tok, equation_Lib.IntTypes.bits, equation_Lib.IntTypes.range, equation_Lib.IntTypes.signed, equation_Lib.IntTypes.unsigned, equation_Lib.IntTypes.v, equation_Prims.nat, equation_Prims.pos, equation_Spec.Kyber2.Params.params_q, int_inversion, int_typing, lemma_FStar.UInt.pow2_values, primitive_Prims.op_Addition, primitive_Prims.op_Division, primitive_Prims.op_LessThanOrEqual, primitive_Prims.op_Minus, primitive_Prims.op_Multiply, primitive_Prims.op_Subtraction, projection_inverse_BoxBool_proj_0, projection_inverse_BoxInt_proj_0, refinement_interpretation_Tm_refine_2b320913041b873fce938dd17eebb3e2, refinement_interpretation_Tm_refine_542f9d4f129664613f2483a6c88bc7c2, refinement_interpretation_Tm_refine_774ba3f728d91ead8ef40be66c9802e5, refinement_interpretation_Tm_refine_83845a86f2550cdf941eeb1d9b59602b, refinement_interpretation_Tm_refine_9d3fd79fd314167f1a9c213a188da3ec, refinement_interpretation_Tm_refine_b2401a8cabe2f9a01538f32548fa9f6c, typing_Lib.IntTypes.mk_int, typing_Prims.pow2, typing_tok_Lib.IntTypes.S32@tok, typing_tok_Lib.IntTypes.SEC@tok

;;; End module FStar.UInt128 (303 decls; total size 13845)

;;; Start module FStar.UInt16

; <Start encoding FStar.UInt16.n>

(declare-fun FStar.UInt16.n (Dummy_sort) Term)

; </end encoding FStar.UInt16.n>


; <Skipped />


; <Start encoding FStar.UInt16.t>

(declare-fun FStar.UInt16.t () Term)

; </end encoding FStar.UInt16.t>


; <Start encoding FStar.UInt16.t__uu___haseq>


; </end encoding FStar.UInt16.t__uu___haseq>


; <Start encoding FStar.UInt16.v>

(declare-fun FStar.UInt16.v (Term) Term)
(declare-fun Tm_arrow_320deeeac0f5bd97eb73d7155ff07f9c () Term)
(declare-fun FStar.UInt16.v@tok () Term)

; </end encoding FStar.UInt16.v>


; <Start encoding FStar.UInt16.uint_to_t>

(declare-fun FStar.UInt16.uint_to_t (Term) Term)
(declare-fun Tm_refine_9c36b8f5a7a9b8fb80adbe9309fb4f4a (Term) Term)
(declare-fun Tm_arrow_7a51cae43ce25be7a51405bb86a4e951 () Term)
(declare-fun FStar.UInt16.uint_to_t@tok () Term)


; </end encoding FStar.UInt16.uint_to_t>


; <Start encoding FStar.UInt16.uv_inv>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.UInt16.uv_inv (Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.UInt16.uv_inv@tok () Term)

; </end encoding FStar.UInt16.uv_inv>


; <Start encoding FStar.UInt16.vu_inv>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.UInt16.vu_inv (Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.UInt16.vu_inv@tok () Term)

; </end encoding FStar.UInt16.vu_inv>


; <Start encoding FStar.UInt16.v_inj>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.UInt16.v_inj (Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.UInt16.v_inj@tok () Term)

; </end encoding FStar.UInt16.v_inj>


; <Start encoding FStar.UInt16.add>

(declare-fun FStar.UInt16.add (Term Term) Term)
(declare-fun Tm_refine_2e33cd83d3c91966aa0ce7a0a5c2d3a2 (Term Term) Term)
(declare-fun Tm_arrow_6550ae8dcb8f2b1d75a0633fd7873a0e () Term)
(declare-fun FStar.UInt16.add@tok () Term)


; </end encoding FStar.UInt16.add>


; <Start encoding FStar.UInt16.add_underspec>

(declare-fun FStar.UInt16.add_underspec (Term Term) Term)
(declare-fun Tm_refine_657db395af35c536aedc2dbae5397382 (Term Term) Term)
(declare-fun Tm_arrow_13cab4b148d750996b553a6ed2f43d1e () Term)
(declare-fun FStar.UInt16.add_underspec@tok () Term)


; </end encoding FStar.UInt16.add_underspec>


; <Start encoding FStar.UInt16.add_mod>

(declare-fun FStar.UInt16.add_mod (Term Term) Term)
(declare-fun Tm_refine_aac89d186eb67617493682246aa5fb12 (Term Term) Term)
(declare-fun Tm_arrow_097a6518b2b33747ec252b013af6761a () Term)
(declare-fun FStar.UInt16.add_mod@tok () Term)


; </end encoding FStar.UInt16.add_mod>


; <Start encoding FStar.UInt16.sub>

(declare-fun FStar.UInt16.sub (Term Term) Term)
(declare-fun Tm_refine_ea06d755fefbc5fe88a9cfffafc2687c (Term Term) Term)
(declare-fun Tm_arrow_d94354912d5cb61d94990fa1e0eefff8 () Term)
(declare-fun FStar.UInt16.sub@tok () Term)


; </end encoding FStar.UInt16.sub>


; <Start encoding FStar.UInt16.sub_underspec>

(declare-fun FStar.UInt16.sub_underspec (Term Term) Term)
(declare-fun Tm_refine_5a02b3181e9cbd3a53938cb29bd8bdda (Term Term) Term)
(declare-fun Tm_arrow_57feeb2ae5411370df42ddc8058dc82a () Term)
(declare-fun FStar.UInt16.sub_underspec@tok () Term)


; </end encoding FStar.UInt16.sub_underspec>


; <Start encoding FStar.UInt16.sub_mod>

(declare-fun FStar.UInt16.sub_mod (Term Term) Term)
(declare-fun Tm_refine_836d8da982ea37134b32d641fb9ba7ad (Term Term) Term)
(declare-fun Tm_arrow_b6386c218b54692724824339b9aebeb5 () Term)
(declare-fun FStar.UInt16.sub_mod@tok () Term)


; </end encoding FStar.UInt16.sub_mod>


; <Start encoding FStar.UInt16.mul>

(declare-fun FStar.UInt16.mul (Term Term) Term)
(declare-fun Tm_refine_2d13984d764b4d9bf25fd676af9ca788 (Term Term) Term)
(declare-fun Tm_arrow_cc09a68f1bc3f63a2fe61d382849c069 () Term)
(declare-fun FStar.UInt16.mul@tok () Term)


; </end encoding FStar.UInt16.mul>


; <Start encoding FStar.UInt16.mul_underspec>

(declare-fun FStar.UInt16.mul_underspec (Term Term) Term)
(declare-fun Tm_refine_158579aaf8fa19d5c3cfead9e3e74364 (Term Term) Term)
(declare-fun Tm_arrow_897c61165a6d89945028f8c7eb47bc82 () Term)
(declare-fun FStar.UInt16.mul_underspec@tok () Term)


; </end encoding FStar.UInt16.mul_underspec>


; <Start encoding FStar.UInt16.mul_mod>

(declare-fun FStar.UInt16.mul_mod (Term Term) Term)
(declare-fun Tm_refine_77e48fee6522b2b73c6719ccf217ce95 (Term Term) Term)
(declare-fun Tm_arrow_9ea5c57034ebdb98fad6275c07be2d0c () Term)
(declare-fun FStar.UInt16.mul_mod@tok () Term)


; </end encoding FStar.UInt16.mul_mod>


; <Start encoding FStar.UInt16.mul_div>

(declare-fun FStar.UInt16.mul_div (Term Term) Term)
(declare-fun Tm_refine_bec23dfa1a6c0334bdbb7af57fcee0ef (Term Term) Term)
(declare-fun Tm_arrow_f2cd0021033e3705139ddfc7ab07f651 () Term)
(declare-fun FStar.UInt16.mul_div@tok () Term)


; </end encoding FStar.UInt16.mul_div>


; <Start encoding FStar.UInt16.div>

(declare-fun Tm_refine_9b1cb58e4cc7db7d20c9b1b635e9d4c5 () Term)
(declare-fun FStar.UInt16.div (Term Term) Term)

(declare-fun Tm_refine_b8ca54cbb92aab1d06093921cb1b79d4 (Term Term) Term)
(declare-fun Tm_arrow_c64009d7193c95c5c8f3b783e64b62db () Term)
(declare-fun FStar.UInt16.div@tok () Term)


; </end encoding FStar.UInt16.div>


; <Start encoding FStar.UInt16.rem>


(declare-fun FStar.UInt16.rem (Term Term) Term)

(declare-fun Tm_refine_662be2f812ca5e088bf27dce90d1c9dc (Term Term) Term)
(declare-fun Tm_arrow_26f2084b0a289feb52b28d08fdd7e962 () Term)
(declare-fun FStar.UInt16.rem@tok () Term)


; </end encoding FStar.UInt16.rem>


; <Start encoding FStar.UInt16.logand>

(declare-fun FStar.UInt16.logand (Term Term) Term)
(declare-fun Tm_refine_f0571771024375b2825b24bd709dd6cf (Term Term) Term)
(declare-fun Tm_arrow_26120bed67fed79b931747d58e3553e1 () Term)
(declare-fun FStar.UInt16.logand@tok () Term)


; </end encoding FStar.UInt16.logand>


; <Start encoding FStar.UInt16.logxor>

(declare-fun FStar.UInt16.logxor (Term Term) Term)
(declare-fun Tm_refine_d5949f9fb78e07352f5a6e7cf15930bd (Term Term) Term)
(declare-fun Tm_arrow_b9617eb8fe4cd222bdae95b6c9a18cac () Term)
(declare-fun FStar.UInt16.logxor@tok () Term)


; </end encoding FStar.UInt16.logxor>


; <Start encoding FStar.UInt16.logor>

(declare-fun FStar.UInt16.logor (Term Term) Term)
(declare-fun Tm_refine_ce789af7b92629261cc98372dabf4709 (Term Term) Term)
(declare-fun Tm_arrow_d47d13e24ad18213b651812a45923884 () Term)
(declare-fun FStar.UInt16.logor@tok () Term)


; </end encoding FStar.UInt16.logor>


; <Start encoding FStar.UInt16.lognot>

(declare-fun FStar.UInt16.lognot (Term) Term)
(declare-fun Tm_refine_f7d2623a4d67bd61ba576e6505531fb6 (Term) Term)
(declare-fun Tm_arrow_cba08f3b4af2b28a3c225d42626ccb25 () Term)
(declare-fun FStar.UInt16.lognot@tok () Term)


; </end encoding FStar.UInt16.lognot>


; <Start encoding FStar.UInt16.shift_right>

(declare-fun FStar.UInt16.shift_right (Term Term) Term)
(declare-fun Tm_refine_cfd7aab10b16968433aa1153c133ed88 (Term Term) Term)
(declare-fun Tm_arrow_015d474dda9f49d6eda2f141ba3cd833 () Term)
(declare-fun FStar.UInt16.shift_right@tok () Term)


; </end encoding FStar.UInt16.shift_right>


; <Start encoding FStar.UInt16.shift_left>

(declare-fun FStar.UInt16.shift_left (Term Term) Term)
(declare-fun Tm_refine_5e48638bf7dc9b0bc32fac4648086573 (Term Term) Term)
(declare-fun Tm_arrow_4b0624936cbe68635bdcbbac62ff8106 () Term)
(declare-fun FStar.UInt16.shift_left@tok () Term)


; </end encoding FStar.UInt16.shift_left>


; <Start encoding FStar.UInt16.eq>

(declare-fun FStar.UInt16.eq (Term Term) Term)
(declare-fun Tm_arrow_64e0451c7051eeac4f77ce8e360ff473 () Term)
(declare-fun FStar.UInt16.eq@tok () Term)

; </end encoding FStar.UInt16.eq>


; <Start encoding FStar.UInt16.gt>

(declare-fun FStar.UInt16.gt (Term Term) Term)

(declare-fun FStar.UInt16.gt@tok () Term)

; </end encoding FStar.UInt16.gt>


; <Start encoding FStar.UInt16.gte>

(declare-fun FStar.UInt16.gte (Term Term) Term)

(declare-fun FStar.UInt16.gte@tok () Term)

; </end encoding FStar.UInt16.gte>


; <Start encoding FStar.UInt16.lt>

(declare-fun FStar.UInt16.lt (Term Term) Term)

(declare-fun FStar.UInt16.lt@tok () Term)

; </end encoding FStar.UInt16.lt>


; <Start encoding FStar.UInt16.lte>

(declare-fun FStar.UInt16.lte (Term Term) Term)

(declare-fun FStar.UInt16.lte@tok () Term)

; </end encoding FStar.UInt16.lte>


; <Start encoding FStar.UInt16.minus>

(declare-fun FStar.UInt16.minus (Term) Term)
(declare-fun Tm_arrow_4791db3f4441272f9ac3dfb5f408128c () Term)
(declare-fun FStar.UInt16.minus@tok () Term)

; </end encoding FStar.UInt16.minus>


; <Start encoding FStar.UInt16.n_minus_one>

(declare-fun FStar.UInt16.n_minus_one (Dummy_sort) Term)

; </end encoding FStar.UInt16.n_minus_one>


; <Skipped />


; <Start encoding FStar.UInt16.eq_mask>

(declare-fun FStar.UInt16.eq_mask (Term Term) Term)
(declare-fun Tm_refine_c95bf7502a6a130806ddeeac9db3fad3 (Term Term) Term)
(declare-fun Tm_arrow_00441bf796d2eb09de4496490939020c () Term)
(declare-fun FStar.UInt16.eq_mask@tok () Term)


; </end encoding FStar.UInt16.eq_mask>


; <Start encoding FStar.UInt16.lemma_sub_msbs>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.UInt16.lemma_sub_msbs (Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.UInt16.lemma_sub_msbs@tok () Term)

; </end encoding FStar.UInt16.lemma_sub_msbs>


; <Start encoding FStar.UInt16.gte_mask>

(declare-fun FStar.UInt16.gte_mask (Term Term) Term)
(declare-fun Tm_refine_5bc62249204f52a190a8bd49ef608b8e (Term Term) Term)
(declare-fun Tm_arrow_39d028727e0870b4f87ed710ce4d0e65 () Term)
(declare-fun FStar.UInt16.gte_mask@tok () Term)


; </end encoding FStar.UInt16.gte_mask>


; <Skipped />


; <Start encoding FStar.UInt16.op_Plus_Hat>

(declare-fun FStar.UInt16.op_Plus_Hat (Term Term) Term)


(declare-fun FStar.UInt16.op_Plus_Hat@tok () Term)


; </end encoding FStar.UInt16.op_Plus_Hat>


; <Start encoding FStar.UInt16.op_Plus_Question_Hat>

(declare-fun FStar.UInt16.op_Plus_Question_Hat (Term Term) Term)


(declare-fun FStar.UInt16.op_Plus_Question_Hat@tok () Term)


; </end encoding FStar.UInt16.op_Plus_Question_Hat>


; <Start encoding FStar.UInt16.op_Plus_Percent_Hat>

(declare-fun FStar.UInt16.op_Plus_Percent_Hat (Term Term) Term)


(declare-fun FStar.UInt16.op_Plus_Percent_Hat@tok () Term)


; </end encoding FStar.UInt16.op_Plus_Percent_Hat>


; <Start encoding FStar.UInt16.op_Subtraction_Hat>

(declare-fun FStar.UInt16.op_Subtraction_Hat (Term Term) Term)


(declare-fun FStar.UInt16.op_Subtraction_Hat@tok () Term)


; </end encoding FStar.UInt16.op_Subtraction_Hat>


; <Start encoding FStar.UInt16.op_Subtraction_Question_Hat>

(declare-fun FStar.UInt16.op_Subtraction_Question_Hat (Term Term) Term)


(declare-fun FStar.UInt16.op_Subtraction_Question_Hat@tok () Term)


; </end encoding FStar.UInt16.op_Subtraction_Question_Hat>


; <Start encoding FStar.UInt16.op_Subtraction_Percent_Hat>

(declare-fun FStar.UInt16.op_Subtraction_Percent_Hat (Term Term) Term)


(declare-fun FStar.UInt16.op_Subtraction_Percent_Hat@tok () Term)


; </end encoding FStar.UInt16.op_Subtraction_Percent_Hat>


; <Start encoding FStar.UInt16.op_Star_Hat>

(declare-fun FStar.UInt16.op_Star_Hat (Term Term) Term)


(declare-fun FStar.UInt16.op_Star_Hat@tok () Term)


; </end encoding FStar.UInt16.op_Star_Hat>


; <Start encoding FStar.UInt16.op_Star_Question_Hat>

(declare-fun FStar.UInt16.op_Star_Question_Hat (Term Term) Term)


(declare-fun FStar.UInt16.op_Star_Question_Hat@tok () Term)


; </end encoding FStar.UInt16.op_Star_Question_Hat>


; <Start encoding FStar.UInt16.op_Star_Percent_Hat>

(declare-fun FStar.UInt16.op_Star_Percent_Hat (Term Term) Term)


(declare-fun FStar.UInt16.op_Star_Percent_Hat@tok () Term)


; </end encoding FStar.UInt16.op_Star_Percent_Hat>


; <Start encoding FStar.UInt16.op_Star_Slash_Hat>

(declare-fun FStar.UInt16.op_Star_Slash_Hat (Term Term) Term)


(declare-fun FStar.UInt16.op_Star_Slash_Hat@tok () Term)


; </end encoding FStar.UInt16.op_Star_Slash_Hat>


; <Start encoding FStar.UInt16.op_Slash_Hat>


(declare-fun FStar.UInt16.op_Slash_Hat (Term Term) Term)



(declare-fun FStar.UInt16.op_Slash_Hat@tok () Term)



; </end encoding FStar.UInt16.op_Slash_Hat>


; <Start encoding FStar.UInt16.op_Percent_Hat>


(declare-fun FStar.UInt16.op_Percent_Hat (Term Term) Term)



(declare-fun FStar.UInt16.op_Percent_Hat@tok () Term)



; </end encoding FStar.UInt16.op_Percent_Hat>


; <Start encoding FStar.UInt16.op_Hat_Hat>

(declare-fun FStar.UInt16.op_Hat_Hat (Term Term) Term)


(declare-fun FStar.UInt16.op_Hat_Hat@tok () Term)


; </end encoding FStar.UInt16.op_Hat_Hat>


; <Start encoding FStar.UInt16.op_Amp_Hat>

(declare-fun FStar.UInt16.op_Amp_Hat (Term Term) Term)


(declare-fun FStar.UInt16.op_Amp_Hat@tok () Term)


; </end encoding FStar.UInt16.op_Amp_Hat>


; <Start encoding FStar.UInt16.op_Bar_Hat>

(declare-fun FStar.UInt16.op_Bar_Hat (Term Term) Term)


(declare-fun FStar.UInt16.op_Bar_Hat@tok () Term)


; </end encoding FStar.UInt16.op_Bar_Hat>


; <Start encoding FStar.UInt16.op_Less_Less_Hat>

(declare-fun FStar.UInt16.op_Less_Less_Hat (Term Term) Term)


(declare-fun FStar.UInt16.op_Less_Less_Hat@tok () Term)


; </end encoding FStar.UInt16.op_Less_Less_Hat>


; <Start encoding FStar.UInt16.op_Greater_Greater_Hat>

(declare-fun FStar.UInt16.op_Greater_Greater_Hat (Term Term) Term)


(declare-fun FStar.UInt16.op_Greater_Greater_Hat@tok () Term)


; </end encoding FStar.UInt16.op_Greater_Greater_Hat>


; <Start encoding FStar.UInt16.op_Equals_Hat>

(declare-fun FStar.UInt16.op_Equals_Hat (Term Term) Term)

(declare-fun FStar.UInt16.op_Equals_Hat@tok () Term)

; </end encoding FStar.UInt16.op_Equals_Hat>


; <Start encoding FStar.UInt16.op_Greater_Hat>

(declare-fun FStar.UInt16.op_Greater_Hat (Term Term) Term)

(declare-fun FStar.UInt16.op_Greater_Hat@tok () Term)

; </end encoding FStar.UInt16.op_Greater_Hat>


; <Start encoding FStar.UInt16.op_Greater_Equals_Hat>

(declare-fun FStar.UInt16.op_Greater_Equals_Hat (Term Term) Term)

(declare-fun FStar.UInt16.op_Greater_Equals_Hat@tok () Term)

; </end encoding FStar.UInt16.op_Greater_Equals_Hat>


; <Start encoding FStar.UInt16.op_Less_Hat>

(declare-fun FStar.UInt16.op_Less_Hat (Term Term) Term)

(declare-fun FStar.UInt16.op_Less_Hat@tok () Term)

; </end encoding FStar.UInt16.op_Less_Hat>


; <Start encoding FStar.UInt16.op_Less_Equals_Hat>

(declare-fun FStar.UInt16.op_Less_Equals_Hat (Term Term) Term)

(declare-fun FStar.UInt16.op_Less_Equals_Hat@tok () Term)

; </end encoding FStar.UInt16.op_Less_Equals_Hat>


; <Start encoding FStar.UInt16.to_string>

(declare-fun FStar.UInt16.to_string (Term) Term)
(declare-fun Tm_arrow_ca17693c38febf5a69748eba309d6cb9 () Term)
(declare-fun FStar.UInt16.to_string@tok () Term)

; </end encoding FStar.UInt16.to_string>


; <Start encoding FStar.UInt16.of_string>

(declare-fun FStar.UInt16.of_string (Term) Term)
(declare-fun Tm_arrow_bc7c7f3d75321d651fefeed212556f8a () Term)
(declare-fun FStar.UInt16.of_string@tok () Term)

; </end encoding FStar.UInt16.of_string>


; <Skipped />


; <Start encoding FStar.UInt16.__uint_to_t>

(declare-fun FStar.UInt16.__uint_to_t (Term) Term)
(declare-fun Tm_arrow_8768f9720ff4df9c04e8b385e7b09ec7 () Term)
(declare-fun FStar.UInt16.__uint_to_t@tok () Term)

; </end encoding FStar.UInt16.__uint_to_t>


; <Skipped />


; UNSAT CORE: @MaxFuel_assumption, @MaxIFuel_assumption, @fuel_correspondence_Prims.pow2.fuel_instrumented, @query, constructor_distinct_Lib.IntTypes.S16, constructor_distinct_Lib.IntTypes.S32, constructor_distinct_Lib.IntTypes.SEC, equality_tok_Lib.IntTypes.S16@tok, equality_tok_Lib.IntTypes.S32@tok, equality_tok_Lib.IntTypes.SEC@tok, equation_Lib.IntTypes.bits, equation_Lib.IntTypes.range, equation_Lib.IntTypes.signed, equation_Lib.IntTypes.unsigned, equation_Lib.IntTypes.v, equation_Prims.nat, equation_Prims.pos, equation_Spec.Kyber2.Params.params_q, int_inversion, int_typing, lemma_FStar.UInt.pow2_values, primitive_Prims.op_Addition, primitive_Prims.op_Division, primitive_Prims.op_LessThanOrEqual, primitive_Prims.op_Minus, primitive_Prims.op_Multiply, primitive_Prims.op_Subtraction, projection_inverse_BoxBool_proj_0, projection_inverse_BoxInt_proj_0, refinement_interpretation_Tm_refine_2b320913041b873fce938dd17eebb3e2, refinement_interpretation_Tm_refine_542f9d4f129664613f2483a6c88bc7c2, refinement_interpretation_Tm_refine_774ba3f728d91ead8ef40be66c9802e5, refinement_interpretation_Tm_refine_83845a86f2550cdf941eeb1d9b59602b, refinement_interpretation_Tm_refine_9d3fd79fd314167f1a9c213a188da3ec, refinement_interpretation_Tm_refine_b2401a8cabe2f9a01538f32548fa9f6c, typing_Lib.IntTypes.mk_int, typing_Prims.pow2, typing_tok_Lib.IntTypes.S32@tok, typing_tok_Lib.IntTypes.SEC@tok

;;; End module FStar.UInt16 (384 decls; total size 16941)

;;; Start module FStar.UInt8

; <Start encoding FStar.UInt8.n>

(declare-fun FStar.UInt8.n (Dummy_sort) Term)

; </end encoding FStar.UInt8.n>


; <Skipped />


; <Start encoding FStar.UInt8.t>

(declare-fun FStar.UInt8.t () Term)

; </end encoding FStar.UInt8.t>


; <Start encoding FStar.UInt8.t__uu___haseq>


; </end encoding FStar.UInt8.t__uu___haseq>


; <Start encoding FStar.UInt8.v>

(declare-fun FStar.UInt8.v (Term) Term)
(declare-fun Tm_arrow_903d0d5833f56e664141f1d33877b9f4 () Term)
(declare-fun FStar.UInt8.v@tok () Term)

; </end encoding FStar.UInt8.v>


; <Start encoding FStar.UInt8.uint_to_t>

(declare-fun FStar.UInt8.uint_to_t (Term) Term)
(declare-fun Tm_refine_80b9fa1848cd4b08f626f8a84eef7f15 (Term) Term)
(declare-fun Tm_arrow_486ad8d474e5fa20bac6d82023dbbf49 () Term)
(declare-fun FStar.UInt8.uint_to_t@tok () Term)


; </end encoding FStar.UInt8.uint_to_t>


; <Start encoding FStar.UInt8.uv_inv>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.UInt8.uv_inv (Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.UInt8.uv_inv@tok () Term)

; </end encoding FStar.UInt8.uv_inv>


; <Start encoding FStar.UInt8.vu_inv>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.UInt8.vu_inv (Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.UInt8.vu_inv@tok () Term)

; </end encoding FStar.UInt8.vu_inv>


; <Start encoding FStar.UInt8.v_inj>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.UInt8.v_inj (Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.UInt8.v_inj@tok () Term)

; </end encoding FStar.UInt8.v_inj>


; <Start encoding FStar.UInt8.add>

(declare-fun FStar.UInt8.add (Term Term) Term)
(declare-fun Tm_refine_14ad3c506eec743fd9df82958be4a121 (Term Term) Term)
(declare-fun Tm_arrow_b585555da81d143c3666bd4396ba0711 () Term)
(declare-fun FStar.UInt8.add@tok () Term)


; </end encoding FStar.UInt8.add>


; <Start encoding FStar.UInt8.add_underspec>

(declare-fun FStar.UInt8.add_underspec (Term Term) Term)
(declare-fun Tm_refine_bebbd69699f71a72f9230a2dda14f6e1 (Term Term) Term)
(declare-fun Tm_arrow_dc5c3bc62ce727cbf32757be4c6cd0fe () Term)
(declare-fun FStar.UInt8.add_underspec@tok () Term)


; </end encoding FStar.UInt8.add_underspec>


; <Start encoding FStar.UInt8.add_mod>

(declare-fun FStar.UInt8.add_mod (Term Term) Term)
(declare-fun Tm_refine_89db1ed82b9e858c7009b223abadce75 (Term Term) Term)
(declare-fun Tm_arrow_1c13691eb4935eebc70ac9646c744737 () Term)
(declare-fun FStar.UInt8.add_mod@tok () Term)


; </end encoding FStar.UInt8.add_mod>


; <Start encoding FStar.UInt8.sub>

(declare-fun FStar.UInt8.sub (Term Term) Term)
(declare-fun Tm_refine_5c2df25247feb3ea0c2bf506292c4edb (Term Term) Term)
(declare-fun Tm_arrow_80e60e5d94a3f061ff1f493c72acb8e0 () Term)
(declare-fun FStar.UInt8.sub@tok () Term)


; </end encoding FStar.UInt8.sub>


; <Start encoding FStar.UInt8.sub_underspec>

(declare-fun FStar.UInt8.sub_underspec (Term Term) Term)
(declare-fun Tm_refine_430396136335ee778d937372962d98b3 (Term Term) Term)
(declare-fun Tm_arrow_bcc5d9ebcde1ad1f3be83bdef2f4c1e3 () Term)
(declare-fun FStar.UInt8.sub_underspec@tok () Term)


; </end encoding FStar.UInt8.sub_underspec>


; <Start encoding FStar.UInt8.sub_mod>

(declare-fun FStar.UInt8.sub_mod (Term Term) Term)
(declare-fun Tm_refine_7dcdbb404ee976d87938afd934761fc3 (Term Term) Term)
(declare-fun Tm_arrow_9346a06829c15fa35f9d44f878a82c7d () Term)
(declare-fun FStar.UInt8.sub_mod@tok () Term)


; </end encoding FStar.UInt8.sub_mod>


; <Start encoding FStar.UInt8.mul>

(declare-fun FStar.UInt8.mul (Term Term) Term)
(declare-fun Tm_refine_2db4257ee753d30f5896de88896e0bee (Term Term) Term)
(declare-fun Tm_arrow_275b3c969d5e5ac0339949affb985202 () Term)
(declare-fun FStar.UInt8.mul@tok () Term)


; </end encoding FStar.UInt8.mul>


; <Start encoding FStar.UInt8.mul_underspec>

(declare-fun FStar.UInt8.mul_underspec (Term Term) Term)
(declare-fun Tm_refine_41eead9d2ff06211a4c052ac6c46ef7b (Term Term) Term)
(declare-fun Tm_arrow_518f9fd166f6f3af864c609bcefae247 () Term)
(declare-fun FStar.UInt8.mul_underspec@tok () Term)


; </end encoding FStar.UInt8.mul_underspec>


; <Start encoding FStar.UInt8.mul_mod>

(declare-fun FStar.UInt8.mul_mod (Term Term) Term)
(declare-fun Tm_refine_c051bab90ae189d4c08877f17789c2dd (Term Term) Term)
(declare-fun Tm_arrow_066adcb4d5eb4eb67920d6bbccfee97e () Term)
(declare-fun FStar.UInt8.mul_mod@tok () Term)


; </end encoding FStar.UInt8.mul_mod>


; <Start encoding FStar.UInt8.mul_div>

(declare-fun FStar.UInt8.mul_div (Term Term) Term)
(declare-fun Tm_refine_14cc94541ea8d844145c532975ae23a0 (Term Term) Term)
(declare-fun Tm_arrow_feed76f11e42be7baea96fb8918fb55f () Term)
(declare-fun FStar.UInt8.mul_div@tok () Term)


; </end encoding FStar.UInt8.mul_div>


; <Start encoding FStar.UInt8.div>

(declare-fun Tm_refine_de9e56261c4c3e3a03968ac6adac1747 () Term)
(declare-fun FStar.UInt8.div (Term Term) Term)

(declare-fun Tm_refine_9977b95ba5af0b9e4a4ba59aeee4998f (Term Term) Term)
(declare-fun Tm_arrow_723915356405dcedf2342efdd7ae4f9e () Term)
(declare-fun FStar.UInt8.div@tok () Term)


; </end encoding FStar.UInt8.div>


; <Start encoding FStar.UInt8.rem>


(declare-fun FStar.UInt8.rem (Term Term) Term)

(declare-fun Tm_refine_ca08a9f46b195a78117c3f90f863870f (Term Term) Term)
(declare-fun Tm_arrow_ebbef099aa8c148b0d5d3fcdc0987181 () Term)
(declare-fun FStar.UInt8.rem@tok () Term)


; </end encoding FStar.UInt8.rem>


; <Start encoding FStar.UInt8.logand>

(declare-fun FStar.UInt8.logand (Term Term) Term)
(declare-fun Tm_refine_1a1f114a01fda1d6d60467e846f0e43a (Term Term) Term)
(declare-fun Tm_arrow_0418dda5e979d2cbe994efed6241c940 () Term)
(declare-fun FStar.UInt8.logand@tok () Term)


; </end encoding FStar.UInt8.logand>


; <Start encoding FStar.UInt8.logxor>

(declare-fun FStar.UInt8.logxor (Term Term) Term)
(declare-fun Tm_refine_60aad1143b201ec1328875c4bde8f1c7 (Term Term) Term)
(declare-fun Tm_arrow_0ff578d4d90c0a0bdf53f8f10852a4ce () Term)
(declare-fun FStar.UInt8.logxor@tok () Term)


; </end encoding FStar.UInt8.logxor>


; <Start encoding FStar.UInt8.logor>

(declare-fun FStar.UInt8.logor (Term Term) Term)
(declare-fun Tm_refine_90f3e88ac21bdb91e42538f99dc76067 (Term Term) Term)
(declare-fun Tm_arrow_cbda115d0c3ff49f73fe77512af57bab () Term)
(declare-fun FStar.UInt8.logor@tok () Term)


; </end encoding FStar.UInt8.logor>


; <Start encoding FStar.UInt8.lognot>

(declare-fun FStar.UInt8.lognot (Term) Term)
(declare-fun Tm_refine_2eb9e74c99165870eb01e3cebb8052d2 (Term) Term)
(declare-fun Tm_arrow_a3cb607f1eab00eb629342aa43fa9911 () Term)
(declare-fun FStar.UInt8.lognot@tok () Term)


; </end encoding FStar.UInt8.lognot>


; <Start encoding FStar.UInt8.shift_right>

(declare-fun FStar.UInt8.shift_right (Term Term) Term)
(declare-fun Tm_refine_148ca1afd1c53121c26ec352bca6b6ca (Term Term) Term)
(declare-fun Tm_arrow_d489cc6e6d7a72161c3bafbe3b0e45c8 () Term)
(declare-fun FStar.UInt8.shift_right@tok () Term)


; </end encoding FStar.UInt8.shift_right>


; <Start encoding FStar.UInt8.shift_left>

(declare-fun FStar.UInt8.shift_left (Term Term) Term)
(declare-fun Tm_refine_c5b8e62e00df539941482c7841cd5e2e (Term Term) Term)
(declare-fun Tm_arrow_3f675b11156ee489ecf6491f25870e1f () Term)
(declare-fun FStar.UInt8.shift_left@tok () Term)


; </end encoding FStar.UInt8.shift_left>


; <Start encoding FStar.UInt8.eq>

(declare-fun FStar.UInt8.eq (Term Term) Term)
(declare-fun Tm_arrow_3969f45b61ef13bb657d1539eb6b3677 () Term)
(declare-fun FStar.UInt8.eq@tok () Term)

; </end encoding FStar.UInt8.eq>


; <Start encoding FStar.UInt8.gt>

(declare-fun FStar.UInt8.gt (Term Term) Term)

(declare-fun FStar.UInt8.gt@tok () Term)

; </end encoding FStar.UInt8.gt>


; <Start encoding FStar.UInt8.gte>

(declare-fun FStar.UInt8.gte (Term Term) Term)

(declare-fun FStar.UInt8.gte@tok () Term)

; </end encoding FStar.UInt8.gte>


; <Start encoding FStar.UInt8.lt>

(declare-fun FStar.UInt8.lt (Term Term) Term)

(declare-fun FStar.UInt8.lt@tok () Term)

; </end encoding FStar.UInt8.lt>


; <Start encoding FStar.UInt8.lte>

(declare-fun FStar.UInt8.lte (Term Term) Term)

(declare-fun FStar.UInt8.lte@tok () Term)

; </end encoding FStar.UInt8.lte>


; <Start encoding FStar.UInt8.minus>

(declare-fun FStar.UInt8.minus (Term) Term)
(declare-fun Tm_arrow_ac45876449cdbb69007be8e5fe63fd10 () Term)
(declare-fun FStar.UInt8.minus@tok () Term)

; </end encoding FStar.UInt8.minus>


; <Start encoding FStar.UInt8.n_minus_one>

(declare-fun FStar.UInt8.n_minus_one (Dummy_sort) Term)

; </end encoding FStar.UInt8.n_minus_one>


; <Skipped />


; <Start encoding FStar.UInt8.eq_mask>

(declare-fun FStar.UInt8.eq_mask (Term Term) Term)
(declare-fun Tm_refine_37561c6787399cd7f8bd58720d95b571 (Term Term) Term)
(declare-fun Tm_arrow_b23685d6950a6478c69f3694047e0676 () Term)
(declare-fun FStar.UInt8.eq_mask@tok () Term)


; </end encoding FStar.UInt8.eq_mask>


; <Start encoding FStar.UInt8.lemma_sub_msbs>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.UInt8.lemma_sub_msbs (Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.UInt8.lemma_sub_msbs@tok () Term)

; </end encoding FStar.UInt8.lemma_sub_msbs>


; <Start encoding FStar.UInt8.gte_mask>

(declare-fun FStar.UInt8.gte_mask (Term Term) Term)
(declare-fun Tm_refine_d67c4a277ba15407844764d7876a77ca (Term Term) Term)
(declare-fun Tm_arrow_cb502315b1513b99482f6793463bf4d8 () Term)
(declare-fun FStar.UInt8.gte_mask@tok () Term)


; </end encoding FStar.UInt8.gte_mask>


; <Skipped />


; <Start encoding FStar.UInt8.op_Plus_Hat>

(declare-fun FStar.UInt8.op_Plus_Hat (Term Term) Term)


(declare-fun FStar.UInt8.op_Plus_Hat@tok () Term)


; </end encoding FStar.UInt8.op_Plus_Hat>


; <Start encoding FStar.UInt8.op_Plus_Question_Hat>

(declare-fun FStar.UInt8.op_Plus_Question_Hat (Term Term) Term)


(declare-fun FStar.UInt8.op_Plus_Question_Hat@tok () Term)


; </end encoding FStar.UInt8.op_Plus_Question_Hat>


; <Start encoding FStar.UInt8.op_Plus_Percent_Hat>

(declare-fun FStar.UInt8.op_Plus_Percent_Hat (Term Term) Term)


(declare-fun FStar.UInt8.op_Plus_Percent_Hat@tok () Term)


; </end encoding FStar.UInt8.op_Plus_Percent_Hat>


; <Start encoding FStar.UInt8.op_Subtraction_Hat>

(declare-fun FStar.UInt8.op_Subtraction_Hat (Term Term) Term)


(declare-fun FStar.UInt8.op_Subtraction_Hat@tok () Term)


; </end encoding FStar.UInt8.op_Subtraction_Hat>


; <Start encoding FStar.UInt8.op_Subtraction_Question_Hat>

(declare-fun FStar.UInt8.op_Subtraction_Question_Hat (Term Term) Term)


(declare-fun FStar.UInt8.op_Subtraction_Question_Hat@tok () Term)


; </end encoding FStar.UInt8.op_Subtraction_Question_Hat>


; <Start encoding FStar.UInt8.op_Subtraction_Percent_Hat>

(declare-fun FStar.UInt8.op_Subtraction_Percent_Hat (Term Term) Term)


(declare-fun FStar.UInt8.op_Subtraction_Percent_Hat@tok () Term)


; </end encoding FStar.UInt8.op_Subtraction_Percent_Hat>


; <Start encoding FStar.UInt8.op_Star_Hat>

(declare-fun FStar.UInt8.op_Star_Hat (Term Term) Term)


(declare-fun FStar.UInt8.op_Star_Hat@tok () Term)


; </end encoding FStar.UInt8.op_Star_Hat>


; <Start encoding FStar.UInt8.op_Star_Question_Hat>

(declare-fun FStar.UInt8.op_Star_Question_Hat (Term Term) Term)


(declare-fun FStar.UInt8.op_Star_Question_Hat@tok () Term)


; </end encoding FStar.UInt8.op_Star_Question_Hat>


; <Start encoding FStar.UInt8.op_Star_Percent_Hat>

(declare-fun FStar.UInt8.op_Star_Percent_Hat (Term Term) Term)


(declare-fun FStar.UInt8.op_Star_Percent_Hat@tok () Term)


; </end encoding FStar.UInt8.op_Star_Percent_Hat>


; <Start encoding FStar.UInt8.op_Star_Slash_Hat>

(declare-fun FStar.UInt8.op_Star_Slash_Hat (Term Term) Term)


(declare-fun FStar.UInt8.op_Star_Slash_Hat@tok () Term)


; </end encoding FStar.UInt8.op_Star_Slash_Hat>


; <Start encoding FStar.UInt8.op_Slash_Hat>


(declare-fun FStar.UInt8.op_Slash_Hat (Term Term) Term)



(declare-fun FStar.UInt8.op_Slash_Hat@tok () Term)



; </end encoding FStar.UInt8.op_Slash_Hat>


; <Start encoding FStar.UInt8.op_Percent_Hat>


(declare-fun FStar.UInt8.op_Percent_Hat (Term Term) Term)



(declare-fun FStar.UInt8.op_Percent_Hat@tok () Term)



; </end encoding FStar.UInt8.op_Percent_Hat>


; <Start encoding FStar.UInt8.op_Hat_Hat>

(declare-fun FStar.UInt8.op_Hat_Hat (Term Term) Term)


(declare-fun FStar.UInt8.op_Hat_Hat@tok () Term)


; </end encoding FStar.UInt8.op_Hat_Hat>


; <Start encoding FStar.UInt8.op_Amp_Hat>

(declare-fun FStar.UInt8.op_Amp_Hat (Term Term) Term)


(declare-fun FStar.UInt8.op_Amp_Hat@tok () Term)


; </end encoding FStar.UInt8.op_Amp_Hat>


; <Start encoding FStar.UInt8.op_Bar_Hat>

(declare-fun FStar.UInt8.op_Bar_Hat (Term Term) Term)


(declare-fun FStar.UInt8.op_Bar_Hat@tok () Term)


; </end encoding FStar.UInt8.op_Bar_Hat>


; <Start encoding FStar.UInt8.op_Less_Less_Hat>

(declare-fun FStar.UInt8.op_Less_Less_Hat (Term Term) Term)


(declare-fun FStar.UInt8.op_Less_Less_Hat@tok () Term)


; </end encoding FStar.UInt8.op_Less_Less_Hat>


; <Start encoding FStar.UInt8.op_Greater_Greater_Hat>

(declare-fun FStar.UInt8.op_Greater_Greater_Hat (Term Term) Term)


(declare-fun FStar.UInt8.op_Greater_Greater_Hat@tok () Term)


; </end encoding FStar.UInt8.op_Greater_Greater_Hat>


; <Start encoding FStar.UInt8.op_Equals_Hat>

(declare-fun FStar.UInt8.op_Equals_Hat (Term Term) Term)

(declare-fun FStar.UInt8.op_Equals_Hat@tok () Term)

; </end encoding FStar.UInt8.op_Equals_Hat>


; <Start encoding FStar.UInt8.op_Greater_Hat>

(declare-fun FStar.UInt8.op_Greater_Hat (Term Term) Term)

(declare-fun FStar.UInt8.op_Greater_Hat@tok () Term)

; </end encoding FStar.UInt8.op_Greater_Hat>


; <Start encoding FStar.UInt8.op_Greater_Equals_Hat>

(declare-fun FStar.UInt8.op_Greater_Equals_Hat (Term Term) Term)

(declare-fun FStar.UInt8.op_Greater_Equals_Hat@tok () Term)

; </end encoding FStar.UInt8.op_Greater_Equals_Hat>


; <Start encoding FStar.UInt8.op_Less_Hat>

(declare-fun FStar.UInt8.op_Less_Hat (Term Term) Term)

(declare-fun FStar.UInt8.op_Less_Hat@tok () Term)

; </end encoding FStar.UInt8.op_Less_Hat>


; <Start encoding FStar.UInt8.op_Less_Equals_Hat>

(declare-fun FStar.UInt8.op_Less_Equals_Hat (Term Term) Term)

(declare-fun FStar.UInt8.op_Less_Equals_Hat@tok () Term)

; </end encoding FStar.UInt8.op_Less_Equals_Hat>


; <Start encoding FStar.UInt8.to_string>

(declare-fun FStar.UInt8.to_string (Term) Term)
(declare-fun Tm_arrow_69d97142496ce01acc01a48fea19707a () Term)
(declare-fun FStar.UInt8.to_string@tok () Term)

; </end encoding FStar.UInt8.to_string>


; <Start encoding FStar.UInt8.of_string>

(declare-fun FStar.UInt8.of_string (Term) Term)
(declare-fun Tm_arrow_0c51a4ef32654b7402b2b4fb3f9c4803 () Term)
(declare-fun FStar.UInt8.of_string@tok () Term)

; </end encoding FStar.UInt8.of_string>


; <Skipped />


; <Start encoding FStar.UInt8.__uint_to_t>

(declare-fun FStar.UInt8.__uint_to_t (Term) Term)
(declare-fun Tm_arrow_0cd5e3d818b1df17855bcc116acd2bd7 () Term)
(declare-fun FStar.UInt8.__uint_to_t@tok () Term)

; </end encoding FStar.UInt8.__uint_to_t>


; <Skipped />


; <Start encoding FStar.UInt8.byte>

(declare-fun FStar.UInt8.byte () Term)

; </end encoding FStar.UInt8.byte>


; UNSAT CORE: @MaxFuel_assumption, @MaxIFuel_assumption, @fuel_correspondence_Prims.pow2.fuel_instrumented, @query, constructor_distinct_Lib.IntTypes.S16, constructor_distinct_Lib.IntTypes.S32, constructor_distinct_Lib.IntTypes.SEC, equality_tok_Lib.IntTypes.S16@tok, equality_tok_Lib.IntTypes.S32@tok, equality_tok_Lib.IntTypes.SEC@tok, equation_Lib.IntTypes.bits, equation_Lib.IntTypes.range, equation_Lib.IntTypes.signed, equation_Lib.IntTypes.unsigned, equation_Lib.IntTypes.v, equation_Prims.nat, equation_Prims.pos, equation_Spec.Kyber2.Params.params_q, int_inversion, int_typing, lemma_FStar.UInt.pow2_values, primitive_Prims.op_Addition, primitive_Prims.op_Division, primitive_Prims.op_LessThanOrEqual, primitive_Prims.op_Minus, primitive_Prims.op_Multiply, primitive_Prims.op_Subtraction, projection_inverse_BoxBool_proj_0, projection_inverse_BoxInt_proj_0, refinement_interpretation_Tm_refine_2b320913041b873fce938dd17eebb3e2, refinement_interpretation_Tm_refine_542f9d4f129664613f2483a6c88bc7c2, refinement_interpretation_Tm_refine_774ba3f728d91ead8ef40be66c9802e5, refinement_interpretation_Tm_refine_83845a86f2550cdf941eeb1d9b59602b, refinement_interpretation_Tm_refine_9d3fd79fd314167f1a9c213a188da3ec, refinement_interpretation_Tm_refine_b2401a8cabe2f9a01538f32548fa9f6c, typing_Lib.IntTypes.mk_int, typing_Prims.pow2, typing_tok_Lib.IntTypes.S32@tok, typing_tok_Lib.IntTypes.SEC@tok

;;; End module FStar.UInt8 (387 decls; total size 16816)

;;; Start module Lib.IntTypes

; <Start encoding Lib.IntTypes.pow2_2>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun Lib.IntTypes.pow2_2 (Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun Lib.IntTypes.pow2_2@tok () Term)

; </end encoding Lib.IntTypes.pow2_2>


; <Start encoding Lib.IntTypes.pow2_3>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun Lib.IntTypes.pow2_3 (Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun Lib.IntTypes.pow2_3@tok () Term)

; </end encoding Lib.IntTypes.pow2_3>


; <Start encoding Lib.IntTypes.pow2_4>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun Lib.IntTypes.pow2_4 (Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun Lib.IntTypes.pow2_4@tok () Term)

; </end encoding Lib.IntTypes.pow2_4>


; <Start encoding Lib.IntTypes.pow2_127>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun Lib.IntTypes.pow2_127 (Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun Lib.IntTypes.pow2_127@tok () Term)

; </end encoding Lib.IntTypes.pow2_127>


; <Start encoding >

;;;;;;;;;;;;;;;;Constructor
(declare-fun Lib.IntTypes.inttype () Term)
;;;;;;;;;;;;;;;;Constructor
(declare-fun Lib.IntTypes.U1 () Term)
;;;;;;;;;;;;;;;;data constructor proxy: U1
(declare-fun Lib.IntTypes.U1@tok () Term)
;;;;;;;;;;;;;;;;Constructor
(declare-fun Lib.IntTypes.U8 () Term)
;;;;;;;;;;;;;;;;data constructor proxy: U8
(declare-fun Lib.IntTypes.U8@tok () Term)
;;;;;;;;;;;;;;;;Constructor
(declare-fun Lib.IntTypes.U16 () Term)
;;;;;;;;;;;;;;;;data constructor proxy: U16
(declare-fun Lib.IntTypes.U16@tok () Term)
;;;;;;;;;;;;;;;;Constructor
(declare-fun Lib.IntTypes.U32 () Term)
;;;;;;;;;;;;;;;;data constructor proxy: U32
(declare-fun Lib.IntTypes.U32@tok () Term)
;;;;;;;;;;;;;;;;Constructor
(declare-fun Lib.IntTypes.U64 () Term)
;;;;;;;;;;;;;;;;data constructor proxy: U64
(declare-fun Lib.IntTypes.U64@tok () Term)
;;;;;;;;;;;;;;;;Constructor
(declare-fun Lib.IntTypes.U128 () Term)
;;;;;;;;;;;;;;;;data constructor proxy: U128
(declare-fun Lib.IntTypes.U128@tok () Term)
;;;;;;;;;;;;;;;;Constructor
(declare-fun Lib.IntTypes.S8 () Term)
;;;;;;;;;;;;;;;;data constructor proxy: S8
(declare-fun Lib.IntTypes.S8@tok () Term)
;;;;;;;;;;;;;;;;Constructor
(declare-fun Lib.IntTypes.S16 () Term)
;;;;;;;;;;;;;;;;data constructor proxy: S16
(declare-fun Lib.IntTypes.S16@tok () Term)
;;;;;;;;;;;;;;;;Constructor
(declare-fun Lib.IntTypes.S32 () Term)
;;;;;;;;;;;;;;;;data constructor proxy: S32
(declare-fun Lib.IntTypes.S32@tok () Term)
;;;;;;;;;;;;;;;;Constructor
(declare-fun Lib.IntTypes.S64 () Term)
;;;;;;;;;;;;;;;;data constructor proxy: S64
(declare-fun Lib.IntTypes.S64@tok () Term)
;;;;;;;;;;;;;;;;Constructor
(declare-fun Lib.IntTypes.S128 () Term)
;;;;;;;;;;;;;;;;data constructor proxy: S128
(declare-fun Lib.IntTypes.S128@tok () Term)

; <Start encoding Lib.IntTypes.inttype>


; <start constructor Lib.IntTypes.inttype>

;;;;;;;;;;;;;;;;Discriminator definition
(define-fun is-Lib.IntTypes.inttype ((__@x0 Term)) Bool
 (and (= (Term_constr_id __@x0)
101)
(= __@x0
Lib.IntTypes.inttype)))

; </end constructor Lib.IntTypes.inttype>


; </end encoding Lib.IntTypes.inttype>


; <Start encoding Lib.IntTypes.U1>


; <start constructor Lib.IntTypes.U1>

;;;;;;;;;;;;;;;;Discriminator definition
(define-fun is-Lib.IntTypes.U1 ((__@x0 Term)) Bool
 (and (= (Term_constr_id __@x0)
107)
(= __@x0
Lib.IntTypes.U1)))

; </end constructor Lib.IntTypes.U1>


; </end encoding Lib.IntTypes.U1>


; <Start encoding Lib.IntTypes.U8>


; <start constructor Lib.IntTypes.U8>

;;;;;;;;;;;;;;;;Discriminator definition
(define-fun is-Lib.IntTypes.U8 ((__@x0 Term)) Bool
 (and (= (Term_constr_id __@x0)
109)
(= __@x0
Lib.IntTypes.U8)))

; </end constructor Lib.IntTypes.U8>


; </end encoding Lib.IntTypes.U8>


; <Start encoding Lib.IntTypes.U16>


; <start constructor Lib.IntTypes.U16>

;;;;;;;;;;;;;;;;Discriminator definition
(define-fun is-Lib.IntTypes.U16 ((__@x0 Term)) Bool
 (and (= (Term_constr_id __@x0)
111)
(= __@x0
Lib.IntTypes.U16)))

; </end constructor Lib.IntTypes.U16>


; </end encoding Lib.IntTypes.U16>


; <Start encoding Lib.IntTypes.U32>


; <start constructor Lib.IntTypes.U32>

;;;;;;;;;;;;;;;;Discriminator definition
(define-fun is-Lib.IntTypes.U32 ((__@x0 Term)) Bool
 (and (= (Term_constr_id __@x0)
113)
(= __@x0
Lib.IntTypes.U32)))

; </end constructor Lib.IntTypes.U32>


; </end encoding Lib.IntTypes.U32>


; <Start encoding Lib.IntTypes.U64>


; <start constructor Lib.IntTypes.U64>

;;;;;;;;;;;;;;;;Discriminator definition
(define-fun is-Lib.IntTypes.U64 ((__@x0 Term)) Bool
 (and (= (Term_constr_id __@x0)
115)
(= __@x0
Lib.IntTypes.U64)))

; </end constructor Lib.IntTypes.U64>


; </end encoding Lib.IntTypes.U64>


; <Start encoding Lib.IntTypes.U128>


; <start constructor Lib.IntTypes.U128>

;;;;;;;;;;;;;;;;Discriminator definition
(define-fun is-Lib.IntTypes.U128 ((__@x0 Term)) Bool
 (and (= (Term_constr_id __@x0)
117)
(= __@x0
Lib.IntTypes.U128)))

; </end constructor Lib.IntTypes.U128>


; </end encoding Lib.IntTypes.U128>


; <Start encoding Lib.IntTypes.S8>


; <start constructor Lib.IntTypes.S8>

;;;;;;;;;;;;;;;;Discriminator definition
(define-fun is-Lib.IntTypes.S8 ((__@x0 Term)) Bool
 (and (= (Term_constr_id __@x0)
119)
(= __@x0
Lib.IntTypes.S8)))

; </end constructor Lib.IntTypes.S8>


; </end encoding Lib.IntTypes.S8>


; <Start encoding Lib.IntTypes.S16>


; <start constructor Lib.IntTypes.S16>

;;;;;;;;;;;;;;;;Constructor distinct
;;; Fact-ids: Name Lib.IntTypes.inttype; Namespace Lib.IntTypes; Name Lib.IntTypes.U1; Namespace Lib.IntTypes; Name Lib.IntTypes.U8; Namespace Lib.IntTypes; Name Lib.IntTypes.U16; Namespace Lib.IntTypes; Name Lib.IntTypes.U32; Namespace Lib.IntTypes; Name Lib.IntTypes.U64; Namespace Lib.IntTypes; Name Lib.IntTypes.U128; Namespace Lib.IntTypes; Name Lib.IntTypes.S8; Namespace Lib.IntTypes; Name Lib.IntTypes.S16; Namespace Lib.IntTypes; Name Lib.IntTypes.S32; Namespace Lib.IntTypes; Name Lib.IntTypes.S64; Namespace Lib.IntTypes; Name Lib.IntTypes.S128; Namespace Lib.IntTypes
(assert (! (= 121
(Term_constr_id Lib.IntTypes.S16))
:named constructor_distinct_Lib.IntTypes.S16))
;;;;;;;;;;;;;;;;Discriminator definition
(define-fun is-Lib.IntTypes.S16 ((__@x0 Term)) Bool
 (and (= (Term_constr_id __@x0)
121)
(= __@x0
Lib.IntTypes.S16)))

; </end constructor Lib.IntTypes.S16>

;;;;;;;;;;;;;;;;equality for proxy
;;; Fact-ids: Name Lib.IntTypes.inttype; Namespace Lib.IntTypes; Name Lib.IntTypes.U1; Namespace Lib.IntTypes; Name Lib.IntTypes.U8; Namespace Lib.IntTypes; Name Lib.IntTypes.U16; Namespace Lib.IntTypes; Name Lib.IntTypes.U32; Namespace Lib.IntTypes; Name Lib.IntTypes.U64; Namespace Lib.IntTypes; Name Lib.IntTypes.U128; Namespace Lib.IntTypes; Name Lib.IntTypes.S8; Namespace Lib.IntTypes; Name Lib.IntTypes.S16; Namespace Lib.IntTypes; Name Lib.IntTypes.S32; Namespace Lib.IntTypes; Name Lib.IntTypes.S64; Namespace Lib.IntTypes; Name Lib.IntTypes.S128; Namespace Lib.IntTypes
(assert (! (= Lib.IntTypes.S16@tok
Lib.IntTypes.S16)
:named equality_tok_Lib.IntTypes.S16@tok))

; </end encoding Lib.IntTypes.S16>


; <Start encoding Lib.IntTypes.S32>


; <start constructor Lib.IntTypes.S32>

;;;;;;;;;;;;;;;;Constructor distinct
;;; Fact-ids: Name Lib.IntTypes.inttype; Namespace Lib.IntTypes; Name Lib.IntTypes.U1; Namespace Lib.IntTypes; Name Lib.IntTypes.U8; Namespace Lib.IntTypes; Name Lib.IntTypes.U16; Namespace Lib.IntTypes; Name Lib.IntTypes.U32; Namespace Lib.IntTypes; Name Lib.IntTypes.U64; Namespace Lib.IntTypes; Name Lib.IntTypes.U128; Namespace Lib.IntTypes; Name Lib.IntTypes.S8; Namespace Lib.IntTypes; Name Lib.IntTypes.S16; Namespace Lib.IntTypes; Name Lib.IntTypes.S32; Namespace Lib.IntTypes; Name Lib.IntTypes.S64; Namespace Lib.IntTypes; Name Lib.IntTypes.S128; Namespace Lib.IntTypes
(assert (! (= 123
(Term_constr_id Lib.IntTypes.S32))
:named constructor_distinct_Lib.IntTypes.S32))
;;;;;;;;;;;;;;;;Discriminator definition
(define-fun is-Lib.IntTypes.S32 ((__@x0 Term)) Bool
 (and (= (Term_constr_id __@x0)
123)
(= __@x0
Lib.IntTypes.S32)))

; </end constructor Lib.IntTypes.S32>

;;;;;;;;;;;;;;;;typing for data constructor proxy
;;; Fact-ids: Name Lib.IntTypes.inttype; Namespace Lib.IntTypes; Name Lib.IntTypes.U1; Namespace Lib.IntTypes; Name Lib.IntTypes.U8; Namespace Lib.IntTypes; Name Lib.IntTypes.U16; Namespace Lib.IntTypes; Name Lib.IntTypes.U32; Namespace Lib.IntTypes; Name Lib.IntTypes.U64; Namespace Lib.IntTypes; Name Lib.IntTypes.U128; Namespace Lib.IntTypes; Name Lib.IntTypes.S8; Namespace Lib.IntTypes; Name Lib.IntTypes.S16; Namespace Lib.IntTypes; Name Lib.IntTypes.S32; Namespace Lib.IntTypes; Name Lib.IntTypes.S64; Namespace Lib.IntTypes; Name Lib.IntTypes.S128; Namespace Lib.IntTypes
(assert (! (HasType Lib.IntTypes.S32@tok
Lib.IntTypes.inttype)
:named typing_tok_Lib.IntTypes.S32@tok))
;;;;;;;;;;;;;;;;equality for proxy
;;; Fact-ids: Name Lib.IntTypes.inttype; Namespace Lib.IntTypes; Name Lib.IntTypes.U1; Namespace Lib.IntTypes; Name Lib.IntTypes.U8; Namespace Lib.IntTypes; Name Lib.IntTypes.U16; Namespace Lib.IntTypes; Name Lib.IntTypes.U32; Namespace Lib.IntTypes; Name Lib.IntTypes.U64; Namespace Lib.IntTypes; Name Lib.IntTypes.U128; Namespace Lib.IntTypes; Name Lib.IntTypes.S8; Namespace Lib.IntTypes; Name Lib.IntTypes.S16; Namespace Lib.IntTypes; Name Lib.IntTypes.S32; Namespace Lib.IntTypes; Name Lib.IntTypes.S64; Namespace Lib.IntTypes; Name Lib.IntTypes.S128; Namespace Lib.IntTypes
(assert (! (= Lib.IntTypes.S32@tok
Lib.IntTypes.S32)
:named equality_tok_Lib.IntTypes.S32@tok))

; </end encoding Lib.IntTypes.S32>


; <Start encoding Lib.IntTypes.S64>


; <start constructor Lib.IntTypes.S64>

;;;;;;;;;;;;;;;;Discriminator definition
(define-fun is-Lib.IntTypes.S64 ((__@x0 Term)) Bool
 (and (= (Term_constr_id __@x0)
125)
(= __@x0
Lib.IntTypes.S64)))

; </end constructor Lib.IntTypes.S64>


; </end encoding Lib.IntTypes.S64>


; <Start encoding Lib.IntTypes.S128>


; <start constructor Lib.IntTypes.S128>

;;;;;;;;;;;;;;;;Discriminator definition
(define-fun is-Lib.IntTypes.S128 ((__@x0 Term)) Bool
 (and (= (Term_constr_id __@x0)
127)
(= __@x0
Lib.IntTypes.S128)))

; </end constructor Lib.IntTypes.S128>


; </end encoding Lib.IntTypes.S128>


; </end encoding >


; <Start encoding Lib.IntTypes.inttype__uu___haseq>


; </end encoding Lib.IntTypes.inttype__uu___haseq>


; <Start encoding Lib.IntTypes.uu___is_U1>

(declare-fun Lib.IntTypes.uu___is_U1 (Term) Term)
(declare-fun Tm_arrow_7a5cad3cdb73aef16572f096971b1835 () Term)
(declare-fun Lib.IntTypes.uu___is_U1@tok () Term)

; </end encoding Lib.IntTypes.uu___is_U1>


; <Skipped Lib.IntTypes.uu___is_U1/>


; <Start encoding Lib.IntTypes.uu___is_U8>

(declare-fun Lib.IntTypes.uu___is_U8 (Term) Term)

(declare-fun Lib.IntTypes.uu___is_U8@tok () Term)

; </end encoding Lib.IntTypes.uu___is_U8>


; <Skipped Lib.IntTypes.uu___is_U8/>


; <Start encoding Lib.IntTypes.uu___is_U16>

(declare-fun Lib.IntTypes.uu___is_U16 (Term) Term)

(declare-fun Lib.IntTypes.uu___is_U16@tok () Term)

; </end encoding Lib.IntTypes.uu___is_U16>


; <Skipped Lib.IntTypes.uu___is_U16/>


; <Start encoding Lib.IntTypes.uu___is_U32>

(declare-fun Lib.IntTypes.uu___is_U32 (Term) Term)

(declare-fun Lib.IntTypes.uu___is_U32@tok () Term)

; </end encoding Lib.IntTypes.uu___is_U32>


; <Skipped Lib.IntTypes.uu___is_U32/>


; <Start encoding Lib.IntTypes.uu___is_U64>

(declare-fun Lib.IntTypes.uu___is_U64 (Term) Term)

(declare-fun Lib.IntTypes.uu___is_U64@tok () Term)

; </end encoding Lib.IntTypes.uu___is_U64>


; <Skipped Lib.IntTypes.uu___is_U64/>


; <Start encoding Lib.IntTypes.uu___is_U128>

(declare-fun Lib.IntTypes.uu___is_U128 (Term) Term)

(declare-fun Lib.IntTypes.uu___is_U128@tok () Term)

; </end encoding Lib.IntTypes.uu___is_U128>


; <Skipped Lib.IntTypes.uu___is_U128/>


; <Start encoding Lib.IntTypes.uu___is_S8>

(declare-fun Lib.IntTypes.uu___is_S8 (Term) Term)

(declare-fun Lib.IntTypes.uu___is_S8@tok () Term)

; </end encoding Lib.IntTypes.uu___is_S8>


; <Skipped Lib.IntTypes.uu___is_S8/>


; <Start encoding Lib.IntTypes.uu___is_S16>

(declare-fun Lib.IntTypes.uu___is_S16 (Term) Term)

(declare-fun Lib.IntTypes.uu___is_S16@tok () Term)

; </end encoding Lib.IntTypes.uu___is_S16>


; <Skipped Lib.IntTypes.uu___is_S16/>


; <Start encoding Lib.IntTypes.uu___is_S32>

(declare-fun Lib.IntTypes.uu___is_S32 (Term) Term)

(declare-fun Lib.IntTypes.uu___is_S32@tok () Term)

; </end encoding Lib.IntTypes.uu___is_S32>


; <Skipped Lib.IntTypes.uu___is_S32/>


; <Start encoding Lib.IntTypes.uu___is_S64>

(declare-fun Lib.IntTypes.uu___is_S64 (Term) Term)

(declare-fun Lib.IntTypes.uu___is_S64@tok () Term)

; </end encoding Lib.IntTypes.uu___is_S64>


; <Skipped Lib.IntTypes.uu___is_S64/>


; <Start encoding Lib.IntTypes.uu___is_S128>

(declare-fun Lib.IntTypes.uu___is_S128 (Term) Term)

(declare-fun Lib.IntTypes.uu___is_S128@tok () Term)

; </end encoding Lib.IntTypes.uu___is_S128>


; <Skipped Lib.IntTypes.uu___is_S128/>


; <Start encoding Lib.IntTypes.unsigned>

(declare-fun Lib.IntTypes.unsigned (Term) Term)

(declare-fun Lib.IntTypes.unsigned@tok () Term)
;;;;;;;;;;;;;;;;Equation for Lib.IntTypes.unsigned
;;; Fact-ids: Name Lib.IntTypes.unsigned; Namespace Lib.IntTypes
(assert (! 
;; def=/home/caerbannog/dev/hacl-star/lib/Lib.IntTypes.fsti(21,4-21,12); use=/home/caerbannog/dev/hacl-star/lib/Lib.IntTypes.fsti(21,4-21,12)
(forall ((@x0 Term))
 (! (= (Lib.IntTypes.unsigned @x0)
(let ((@lb1 @x0))
(ite (is-Lib.IntTypes.U1 @lb1)
(BoxBool true)
(ite (is-Lib.IntTypes.U8 @lb1)
(BoxBool true)
(ite (is-Lib.IntTypes.U16 @lb1)
(BoxBool true)
(ite (is-Lib.IntTypes.U32 @lb1)
(BoxBool true)
(ite (is-Lib.IntTypes.U64 @lb1)
(BoxBool true)
(ite (is-Lib.IntTypes.U128 @lb1)
(BoxBool true)
(BoxBool false)))))))))
 

:pattern ((Lib.IntTypes.unsigned @x0))
:qid equation_Lib.IntTypes.unsigned))

:named equation_Lib.IntTypes.unsigned))

; </end encoding Lib.IntTypes.unsigned>


; <Start encoding Lib.IntTypes.signed>

(declare-fun Lib.IntTypes.signed (Term) Term)

(declare-fun Lib.IntTypes.signed@tok () Term)
;;;;;;;;;;;;;;;;Equation for Lib.IntTypes.signed
;;; Fact-ids: Name Lib.IntTypes.signed; Namespace Lib.IntTypes
(assert (! 
;; def=/home/caerbannog/dev/hacl-star/lib/Lib.IntTypes.fsti(25,4-25,10); use=/home/caerbannog/dev/hacl-star/lib/Lib.IntTypes.fsti(25,4-25,10)
(forall ((@x0 Term))
 (! (= (Lib.IntTypes.signed @x0)
(let ((@lb1 @x0))
(ite (is-Lib.IntTypes.S8 @lb1)
(BoxBool true)
(ite (is-Lib.IntTypes.S16 @lb1)
(BoxBool true)
(ite (is-Lib.IntTypes.S32 @lb1)
(BoxBool true)
(ite (is-Lib.IntTypes.S64 @lb1)
(BoxBool true)
(ite (is-Lib.IntTypes.S128 @lb1)
(BoxBool true)
(BoxBool false))))))))
 

:pattern ((Lib.IntTypes.signed @x0))
:qid equation_Lib.IntTypes.signed))

:named equation_Lib.IntTypes.signed))

; </end encoding Lib.IntTypes.signed>


; <Start encoding Lib.IntTypes.numbytes>

(declare-fun Lib.IntTypes.numbytes (Term) Term)
(declare-fun Tm_arrow_23b5b42911a552aed95d29aa9a521ba0 () Term)
(declare-fun Lib.IntTypes.numbytes@tok () Term)

; </end encoding Lib.IntTypes.numbytes>


; <Start encoding Lib.IntTypes.bits>

(declare-fun Lib.IntTypes.bits (Term) Term)

(declare-fun Lib.IntTypes.bits@tok () Term)
;;;;;;;;;;;;;;;;Equation for Lib.IntTypes.bits
;;; Fact-ids: Name Lib.IntTypes.bits; Namespace Lib.IntTypes
(assert (! 
;; def=/home/caerbannog/dev/hacl-star/lib/Lib.IntTypes.fsti(48,4-48,8); use=/home/caerbannog/dev/hacl-star/lib/Lib.IntTypes.fsti(48,4-48,8)
(forall ((@x0 Term))
 (! (= (Lib.IntTypes.bits @x0)
(let ((@lb1 @x0))
(ite (is-Lib.IntTypes.U1 @lb1)
(BoxInt 1)
(ite (is-Lib.IntTypes.U8 @lb1)
(BoxInt 8)
(ite (is-Lib.IntTypes.S8 @lb1)
(BoxInt 8)
(ite (is-Lib.IntTypes.U16 @lb1)
(BoxInt 16)
(ite (is-Lib.IntTypes.S16 @lb1)
(BoxInt 16)
(ite (is-Lib.IntTypes.U32 @lb1)
(BoxInt 32)
(ite (is-Lib.IntTypes.S32 @lb1)
(BoxInt 32)
(ite (is-Lib.IntTypes.U64 @lb1)
(BoxInt 64)
(ite (is-Lib.IntTypes.S64 @lb1)
(BoxInt 64)
(ite (is-Lib.IntTypes.U128 @lb1)
(BoxInt 128)
(ite (is-Lib.IntTypes.S128 @lb1)
(BoxInt 128)
Tm_unit)))))))))))))
 

:pattern ((Lib.IntTypes.bits @x0))
:qid equation_Lib.IntTypes.bits))

:named equation_Lib.IntTypes.bits))

; </end encoding Lib.IntTypes.bits>


; <Start encoding Lib.IntTypes.bits_numbytes>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun Lib.IntTypes.bits_numbytes (Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun Lib.IntTypes.bits_numbytes@tok () Term)

; </end encoding Lib.IntTypes.bits_numbytes>


; <Start encoding Lib.IntTypes.modulus>

(declare-fun Lib.IntTypes.modulus (Term) Term)
(declare-fun Tm_arrow_c7315dd5e048ac109580a6bcdeadb822 () Term)
(declare-fun Lib.IntTypes.modulus@tok () Term)

; </end encoding Lib.IntTypes.modulus>


; <Start encoding Lib.IntTypes.maxint>

(declare-fun Lib.IntTypes.maxint (Term) Term)

(declare-fun Lib.IntTypes.maxint@tok () Term)

; </end encoding Lib.IntTypes.maxint>


; <Start encoding Lib.IntTypes.minint>

(declare-fun Lib.IntTypes.minint (Term) Term)

(declare-fun Lib.IntTypes.minint@tok () Term)

; </end encoding Lib.IntTypes.minint>


; <Start encoding Lib.IntTypes.range>

(declare-fun Lib.IntTypes.range (Term Term) Term)
(declare-fun Tm_arrow_67e78a4d5f570fde2d51248a9fb88dde () Term)
(declare-fun Lib.IntTypes.range@tok () Term)
;;;;;;;;;;;;;;;;Equation for Lib.IntTypes.range
;;; Fact-ids: Name Lib.IntTypes.range; Namespace Lib.IntTypes
(assert (! 
;; def=/home/caerbannog/dev/hacl-star/lib/Lib.IntTypes.fsti(75,4-75,9); use=/home/caerbannog/dev/hacl-star/lib/Lib.IntTypes.fsti(75,4-75,9)
(forall ((@x0 Term) (@x1 Term))
 (! (= (Valid (Lib.IntTypes.range @x0
@x1))

;; def=/home/caerbannog/dev/hacl-star/lib/Lib.IntTypes.fsti(76,2-76,32); use=/home/caerbannog/dev/hacl-star/lib/Lib.IntTypes.fsti(76,2-76,32)
(and 
;; def=/home/caerbannog/dev/hacl-star/lib/Lib.IntTypes.fsti(76,2-76,15); use=/home/caerbannog/dev/hacl-star/lib/Lib.IntTypes.fsti(76,2-76,15)
(<= (BoxInt_proj_0 (let ((@lb2 (Lib.IntTypes.unsigned @x1)))
(ite (= @lb2
(BoxBool true))
(BoxInt 0)
(Prims.op_Minus (Prims.pow2 (Prims.op_Subtraction (Lib.IntTypes.bits @x1)
(BoxInt 1)))))))
(BoxInt_proj_0 @x0))


;; def=/home/caerbannog/dev/hacl-star/lib/Lib.IntTypes.fsti(76,19-76,32); use=/home/caerbannog/dev/hacl-star/lib/Lib.IntTypes.fsti(76,19-76,32)
(<= (BoxInt_proj_0 @x0)
(BoxInt_proj_0 (let ((@lb2 (Lib.IntTypes.unsigned @x1)))
(ite (= @lb2
(BoxBool true))
(Prims.op_Subtraction (Prims.pow2 (Lib.IntTypes.bits @x1))
(BoxInt 1))
(Prims.op_Subtraction (Prims.pow2 (Prims.op_Subtraction (Lib.IntTypes.bits @x1)
(BoxInt 1)))
(BoxInt 1))))))
)
)
 

:pattern ((Lib.IntTypes.range @x0
@x1))
:qid equation_Lib.IntTypes.range))

:named equation_Lib.IntTypes.range))

; </end encoding Lib.IntTypes.range>


; <Start encoding Lib.IntTypes.range_t>

(declare-fun Lib.IntTypes.range_t (Term) Term)
(declare-fun Tm_arrow_4df4f60888efe6330802a6511a1b88e7 () Term)
(declare-fun Lib.IntTypes.range_t@tok () Term)
(declare-fun Tm_refine_83845a86f2550cdf941eeb1d9b59602b (Term) Term)
;;;;;;;;;;;;;;;;refinement_interpretation
;;; Fact-ids: Name Lib.IntTypes.range_t; Namespace Lib.IntTypes
(assert (! 
;; def=/home/caerbannog/dev/hacl-star/lib/Lib.IntTypes.fsti(79,27-79,43); use=/home/caerbannog/dev/hacl-star/lib/Lib.IntTypes.fsti(79,27-79,43)
(forall ((@u0 Fuel) (@x1 Term) (@x2 Term))
 (! (iff (HasTypeFuel @u0
@x1
(Tm_refine_83845a86f2550cdf941eeb1d9b59602b @x2))
(and (HasTypeFuel @u0
@x1
Prims.int)

;; def=/home/caerbannog/dev/hacl-star/lib/Lib.IntTypes.fsti(79,33-79,42); use=/home/caerbannog/dev/hacl-star/lib/Lib.IntTypes.fsti(79,33-79,42)
(Valid 
;; def=/home/caerbannog/dev/hacl-star/lib/Lib.IntTypes.fsti(79,33-79,42); use=/home/caerbannog/dev/hacl-star/lib/Lib.IntTypes.fsti(79,33-79,42)
(Lib.IntTypes.range @x1
@x2)
)
))
 

:pattern ((HasTypeFuel @u0
@x1
(Tm_refine_83845a86f2550cdf941eeb1d9b59602b @x2)))
:qid refinement_interpretation_Tm_refine_83845a86f2550cdf941eeb1d9b59602b))

:named refinement_interpretation_Tm_refine_83845a86f2550cdf941eeb1d9b59602b))

; </end encoding Lib.IntTypes.range_t>


; <Start encoding Lib.IntTypes.pub_int_t>

(declare-fun Lib.IntTypes.pub_int_t (Term) Term)

(declare-fun Lib.IntTypes.pub_int_t@tok () Term)
(declare-fun Tm_refine_15e0fa5b1a593e81b2c5f5ce75454fde () Term)

; </end encoding Lib.IntTypes.pub_int_t>


; <Start encoding Lib.IntTypes.pub_int_v>

(declare-fun Lib.IntTypes.pub_int_v (Term Term) Term)

(declare-fun Tm_arrow_46133954d0d05b7bfa7b8471d863ce2c () Term)
(declare-fun Lib.IntTypes.pub_int_v@tok () Term)


; </end encoding Lib.IntTypes.pub_int_v>


; <Start encoding >

;;;;;;;;;;;;;;;;Constructor
(declare-fun Lib.IntTypes.secrecy_level () Term)
;;;;;;;;;;;;;;;;Constructor
(declare-fun Lib.IntTypes.SEC () Term)
;;;;;;;;;;;;;;;;data constructor proxy: SEC
(declare-fun Lib.IntTypes.SEC@tok () Term)
;;;;;;;;;;;;;;;;Constructor
(declare-fun Lib.IntTypes.PUB () Term)
;;;;;;;;;;;;;;;;data constructor proxy: PUB
(declare-fun Lib.IntTypes.PUB@tok () Term)

; <Start encoding Lib.IntTypes.secrecy_level>


; <start constructor Lib.IntTypes.secrecy_level>

;;;;;;;;;;;;;;;;Discriminator definition
(define-fun is-Lib.IntTypes.secrecy_level ((__@x0 Term)) Bool
 (and (= (Term_constr_id __@x0)
176)
(= __@x0
Lib.IntTypes.secrecy_level)))

; </end constructor Lib.IntTypes.secrecy_level>


; </end encoding Lib.IntTypes.secrecy_level>


; <Start encoding Lib.IntTypes.SEC>


; <start constructor Lib.IntTypes.SEC>

;;;;;;;;;;;;;;;;Constructor distinct
;;; Fact-ids: Name Lib.IntTypes.secrecy_level; Namespace Lib.IntTypes; Name Lib.IntTypes.SEC; Namespace Lib.IntTypes; Name Lib.IntTypes.PUB; Namespace Lib.IntTypes
(assert (! (= 182
(Term_constr_id Lib.IntTypes.SEC))
:named constructor_distinct_Lib.IntTypes.SEC))
;;;;;;;;;;;;;;;;Discriminator definition
(define-fun is-Lib.IntTypes.SEC ((__@x0 Term)) Bool
 (and (= (Term_constr_id __@x0)
182)
(= __@x0
Lib.IntTypes.SEC)))

; </end constructor Lib.IntTypes.SEC>

;;;;;;;;;;;;;;;;typing for data constructor proxy
;;; Fact-ids: Name Lib.IntTypes.secrecy_level; Namespace Lib.IntTypes; Name Lib.IntTypes.SEC; Namespace Lib.IntTypes; Name Lib.IntTypes.PUB; Namespace Lib.IntTypes
(assert (! (HasType Lib.IntTypes.SEC@tok
Lib.IntTypes.secrecy_level)
:named typing_tok_Lib.IntTypes.SEC@tok))
;;;;;;;;;;;;;;;;equality for proxy
;;; Fact-ids: Name Lib.IntTypes.secrecy_level; Namespace Lib.IntTypes; Name Lib.IntTypes.SEC; Namespace Lib.IntTypes; Name Lib.IntTypes.PUB; Namespace Lib.IntTypes
(assert (! (= Lib.IntTypes.SEC@tok
Lib.IntTypes.SEC)
:named equality_tok_Lib.IntTypes.SEC@tok))

; </end encoding Lib.IntTypes.SEC>


; <Start encoding Lib.IntTypes.PUB>


; <start constructor Lib.IntTypes.PUB>

;;;;;;;;;;;;;;;;Discriminator definition
(define-fun is-Lib.IntTypes.PUB ((__@x0 Term)) Bool
 (and (= (Term_constr_id __@x0)
184)
(= __@x0
Lib.IntTypes.PUB)))

; </end constructor Lib.IntTypes.PUB>


; </end encoding Lib.IntTypes.PUB>


; </end encoding >


; <Start encoding Lib.IntTypes.secrecy_level__uu___haseq>


; </end encoding Lib.IntTypes.secrecy_level__uu___haseq>


; <Start encoding Lib.IntTypes.uu___is_SEC>

(declare-fun Lib.IntTypes.uu___is_SEC (Term) Term)
(declare-fun Tm_arrow_9e2c93fb3bb6bcb9b4d5840395c6fda4 () Term)
(declare-fun Lib.IntTypes.uu___is_SEC@tok () Term)

; </end encoding Lib.IntTypes.uu___is_SEC>


; <Skipped Lib.IntTypes.uu___is_SEC/>


; <Start encoding Lib.IntTypes.uu___is_PUB>

(declare-fun Lib.IntTypes.uu___is_PUB (Term) Term)

(declare-fun Lib.IntTypes.uu___is_PUB@tok () Term)

; </end encoding Lib.IntTypes.uu___is_PUB>


; <Skipped Lib.IntTypes.uu___is_PUB/>


; <Start encoding Lib.IntTypes.sec_int_t>

(declare-fun Lib.IntTypes.sec_int_t (Term) Term)

(declare-fun Lib.IntTypes.sec_int_t@tok () Term)

; </end encoding Lib.IntTypes.sec_int_t>


; <Start encoding Lib.IntTypes.sec_int_v>

(declare-fun Lib.IntTypes.sec_int_v (Term Term) Term)

(declare-fun Tm_arrow_deb09b76ab55f7f0334d3df98d506b02 () Term)
(declare-fun Lib.IntTypes.sec_int_v@tok () Term)


; </end encoding Lib.IntTypes.sec_int_v>


; <Start encoding Lib.IntTypes.int_t>

(declare-fun Lib.IntTypes.int_t (Term Term) Term)
(declare-fun Tm_arrow_e7d94b39f18cb7383e1e954e1935767d () Term)
(declare-fun Lib.IntTypes.int_t@tok () Term)

; </end encoding Lib.IntTypes.int_t>


; <Start encoding Lib.IntTypes.v>

(declare-fun Lib.IntTypes.v (Term Term Term) Term)

(declare-fun Tm_arrow_40440245ccf70a9a985209c507b76328 () Term)
(declare-fun Lib.IntTypes.v@tok () Term)

;;;;;;;;;;;;;;;;Equation for Lib.IntTypes.v
;;; Fact-ids: Name Lib.IntTypes.v; Namespace Lib.IntTypes
(assert (! 
;; def=/home/caerbannog/dev/hacl-star/lib/Lib.IntTypes.fsti(136,4-136,5); use=/home/caerbannog/dev/hacl-star/lib/Lib.IntTypes.fsti(136,4-136,5)
(forall ((@x0 Term) (@x1 Term) (@x2 Term))
 (! (= (Lib.IntTypes.v @x0
@x1
@x2)
(let ((@lb3 @x1))
(ite (is-Lib.IntTypes.PUB @lb3)
(Lib.IntTypes.pub_int_v @x0
@x2)
(ite (is-Lib.IntTypes.SEC @lb3)
(Lib.IntTypes.sec_int_v @x0
@x2)
Tm_unit))))
 

:pattern ((Lib.IntTypes.v @x0
@x1
@x2))
:qid equation_Lib.IntTypes.v))

:named equation_Lib.IntTypes.v))

; </end encoding Lib.IntTypes.v>


; <Start encoding Lib.IntTypes.uint_t>

(declare-fun Tm_refine_387e6d282145573240ab7b8a4b94cce5 () Term)
(declare-fun Lib.IntTypes.uint_t (Term Term) Term)

(declare-fun Tm_arrow_165597a1da7fd7253bb782734839f857 () Term)
(declare-fun Lib.IntTypes.uint_t@tok () Term)


; </end encoding Lib.IntTypes.uint_t>


; <Start encoding Lib.IntTypes.sint_t>

(declare-fun Tm_refine_499d370c56448bf714eb7f1fd73227a1 () Term)
(declare-fun Lib.IntTypes.sint_t (Term Term) Term)

(declare-fun Tm_arrow_70ff23e061ea5135fc6de56c1cadb46a () Term)
(declare-fun Lib.IntTypes.sint_t@tok () Term)


; </end encoding Lib.IntTypes.sint_t>


; <Start encoding Lib.IntTypes.uint_v>


(declare-fun Lib.IntTypes.uint_v (Term Term Term) Term)


(declare-fun Tm_arrow_243b70db1ef7bc61b19dc128f2f31704 () Term)
(declare-fun Lib.IntTypes.uint_v@tok () Term)



; </end encoding Lib.IntTypes.uint_v>


; <Start encoding Lib.IntTypes.sint_v>


(declare-fun Lib.IntTypes.sint_v (Term Term Term) Term)


(declare-fun Tm_arrow_e8f9a89fba56b944fd558cf4607d24af () Term)
(declare-fun Lib.IntTypes.sint_v@tok () Term)



; </end encoding Lib.IntTypes.sint_v>


; <Start encoding Lib.IntTypes.uint1>

(declare-fun Lib.IntTypes.uint1 () Term)

; </end encoding Lib.IntTypes.uint1>


; <Start encoding Lib.IntTypes.uint8>

(declare-fun Lib.IntTypes.uint8 () Term)

; </end encoding Lib.IntTypes.uint8>


; <Start encoding Lib.IntTypes.int8>

(declare-fun Lib.IntTypes.int8 () Term)

; </end encoding Lib.IntTypes.int8>


; <Start encoding Lib.IntTypes.uint16>

(declare-fun Lib.IntTypes.uint16 () Term)

; </end encoding Lib.IntTypes.uint16>


; <Start encoding Lib.IntTypes.int16>

(declare-fun Lib.IntTypes.int16 () Term)

; </end encoding Lib.IntTypes.int16>


; <Start encoding Lib.IntTypes.uint32>

(declare-fun Lib.IntTypes.uint32 () Term)

; </end encoding Lib.IntTypes.uint32>


; <Start encoding Lib.IntTypes.int32>

(declare-fun Lib.IntTypes.int32 () Term)

; </end encoding Lib.IntTypes.int32>


; <Start encoding Lib.IntTypes.uint64>

(declare-fun Lib.IntTypes.uint64 () Term)

; </end encoding Lib.IntTypes.uint64>


; <Start encoding Lib.IntTypes.int64>

(declare-fun Lib.IntTypes.int64 () Term)

; </end encoding Lib.IntTypes.int64>


; <Start encoding Lib.IntTypes.uint128>

(declare-fun Lib.IntTypes.uint128 () Term)

; </end encoding Lib.IntTypes.uint128>


; <Start encoding Lib.IntTypes.int128>

(declare-fun Lib.IntTypes.int128 () Term)

; </end encoding Lib.IntTypes.int128>


; <Start encoding Lib.IntTypes.bit_t>

(declare-fun Lib.IntTypes.bit_t () Term)

; </end encoding Lib.IntTypes.bit_t>


; <Start encoding Lib.IntTypes.byte_t>

(declare-fun Lib.IntTypes.byte_t () Term)

; </end encoding Lib.IntTypes.byte_t>


; <Start encoding Lib.IntTypes.size_t>

(declare-fun Lib.IntTypes.size_t () Term)

; </end encoding Lib.IntTypes.size_t>


; <Start encoding Lib.IntTypes.pub_uint8>

(declare-fun Lib.IntTypes.pub_uint8 () Term)

; </end encoding Lib.IntTypes.pub_uint8>


; <Start encoding Lib.IntTypes.pub_int8>

(declare-fun Lib.IntTypes.pub_int8 () Term)

; </end encoding Lib.IntTypes.pub_int8>


; <Start encoding Lib.IntTypes.pub_uint16>

(declare-fun Lib.IntTypes.pub_uint16 () Term)

; </end encoding Lib.IntTypes.pub_uint16>


; <Start encoding Lib.IntTypes.pub_int16>

(declare-fun Lib.IntTypes.pub_int16 () Term)

; </end encoding Lib.IntTypes.pub_int16>


; <Start encoding Lib.IntTypes.pub_uint32>

(declare-fun Lib.IntTypes.pub_uint32 () Term)

; </end encoding Lib.IntTypes.pub_uint32>


; <Start encoding Lib.IntTypes.pub_int32>

(declare-fun Lib.IntTypes.pub_int32 () Term)

; </end encoding Lib.IntTypes.pub_int32>


; <Start encoding Lib.IntTypes.pub_uint64>

(declare-fun Lib.IntTypes.pub_uint64 () Term)

; </end encoding Lib.IntTypes.pub_uint64>


; <Start encoding Lib.IntTypes.pub_int64>

(declare-fun Lib.IntTypes.pub_int64 () Term)

; </end encoding Lib.IntTypes.pub_int64>


; <Start encoding Lib.IntTypes.pub_uint128>

(declare-fun Lib.IntTypes.pub_uint128 () Term)

; </end encoding Lib.IntTypes.pub_uint128>


; <Start encoding Lib.IntTypes.pub_int128>

(declare-fun Lib.IntTypes.pub_int128 () Term)

; </end encoding Lib.IntTypes.pub_int128>


; <Start encoding Lib.IntTypes.secret>

(declare-fun Lib.IntTypes.secret (Term Term) Term)
(declare-fun Tm_refine_576183a4f8267f6296f94f4827351efd (Term Term) Term)
(declare-fun Tm_arrow_feb4494e55abb95bc979559ccab03ad0 () Term)
(declare-fun Lib.IntTypes.secret@tok () Term)


; </end encoding Lib.IntTypes.secret>


; <Start encoding Lib.IntTypes.mk_int>


(declare-fun Lib.IntTypes.mk_int (Term Term Term) Term)

(declare-fun Tm_refine_9d3fd79fd314167f1a9c213a188da3ec (Term Term Term) Term)
;;;;;;;;;;;;;;;;refinement_interpretation
;;; Fact-ids: Name Lib.IntTypes.mk_int; Namespace Lib.IntTypes
(assert (! 
;; def=/home/caerbannog/dev/hacl-star/lib/Lib.IntTypes.fsti(233,61-233,82); use=/home/caerbannog/dev/hacl-star/lib/Lib.IntTypes.fsti(233,61-233,82)
(forall ((@u0 Fuel) (@x1 Term) (@x2 Term) (@x3 Term) (@x4 Term))
 (! (iff (HasTypeFuel @u0
@x1
(Tm_refine_9d3fd79fd314167f1a9c213a188da3ec @x2
@x3
@x4))
(and (HasTypeFuel @u0
@x1
(Lib.IntTypes.int_t @x2
@x3))

;; def=/home/caerbannog/dev/hacl-star/lib/Lib.IntTypes.fsti(233,73-233,81); use=/home/caerbannog/dev/hacl-star/lib/Lib.IntTypes.fsti(233,73-233,81)
(= (Lib.IntTypes.v @x2
@x3
@x1)
@x4)
))
 

:pattern ((HasTypeFuel @u0
@x1
(Tm_refine_9d3fd79fd314167f1a9c213a188da3ec @x2
@x3
@x4)))
:qid refinement_interpretation_Tm_refine_9d3fd79fd314167f1a9c213a188da3ec))

:named refinement_interpretation_Tm_refine_9d3fd79fd314167f1a9c213a188da3ec))
(declare-fun Tm_arrow_2b601ac3b6dd5023f5acf9aca946a2fa () Term)
(declare-fun Lib.IntTypes.mk_int@tok () Term)

;;;;;;;;;;;;;;;;free var typing
;;; Fact-ids: Name Lib.IntTypes.mk_int; Namespace Lib.IntTypes
(assert (! 
;; def=/home/caerbannog/dev/hacl-star/lib/Lib.IntTypes.fsti(233,4-233,10); use=/home/caerbannog/dev/hacl-star/lib/Lib.IntTypes.fsti(233,4-233,10)
(forall ((@x0 Term) (@x1 Term) (@x2 Term))
 (! (implies (and (HasType @x0
Lib.IntTypes.inttype)
(HasType @x1
Lib.IntTypes.secrecy_level)
(HasType @x2
(Tm_refine_83845a86f2550cdf941eeb1d9b59602b @x0)))
(HasType (Lib.IntTypes.mk_int @x0
@x1
@x2)
(Tm_refine_9d3fd79fd314167f1a9c213a188da3ec @x0
@x1
@x2)))
 

:pattern ((Lib.IntTypes.mk_int @x0
@x1
@x2))
:qid typing_Lib.IntTypes.mk_int))

:named typing_Lib.IntTypes.mk_int))

; </end encoding Lib.IntTypes.mk_int>


; <Start encoding Lib.IntTypes.uint>



(declare-fun Lib.IntTypes.uint (Term Term Term) Term)



(declare-fun Tm_arrow_be50b03d4c9e27836938014e403fde09 () Term)
(declare-fun Lib.IntTypes.uint@tok () Term)




; </end encoding Lib.IntTypes.uint>


; <Start encoding Lib.IntTypes.sint>



(declare-fun Lib.IntTypes.sint (Term Term Term) Term)



(declare-fun Tm_arrow_6c0c51aee864a5060b051166d85dd8d1 () Term)
(declare-fun Lib.IntTypes.sint@tok () Term)




; </end encoding Lib.IntTypes.sint>


; <Start encoding Lib.IntTypes.v_injective>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun Lib.IntTypes.v_injective (Term Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun Lib.IntTypes.v_injective@tok () Term)

; </end encoding Lib.IntTypes.v_injective>


; <Start encoding Lib.IntTypes.v_mk_int>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun Lib.IntTypes.v_mk_int (Term Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun Lib.IntTypes.v_mk_int@tok () Term)


; </end encoding Lib.IntTypes.v_mk_int>


; <Start encoding Lib.IntTypes.u1>

(declare-fun Tm_refine_b4b08e995afca2a1ea2a545fa1dd44cc () Term)
(declare-fun Lib.IntTypes.u1 (Term) Term)

(declare-fun Tm_refine_c178be26ecd23c8e6026ec38d882bc65 (Term) Term)
(declare-fun Tm_arrow_2245d3e5d01af4b1f3534b29a7a77d5a () Term)
(declare-fun Lib.IntTypes.u1@tok () Term)



; </end encoding Lib.IntTypes.u1>


; <Start encoding Lib.IntTypes.u8>

(declare-fun Tm_refine_ac361b132c26d906d5997e1372d2a888 () Term)
(declare-fun Lib.IntTypes.u8 (Term) Term)

(declare-fun Tm_refine_d32749f2772b0847957005b759926d60 (Term) Term)
(declare-fun Tm_arrow_141242f5cf351ff84207bb5a809ef1dc () Term)
(declare-fun Lib.IntTypes.u8@tok () Term)



; </end encoding Lib.IntTypes.u8>


; <Start encoding Lib.IntTypes.i8>

(declare-fun Tm_refine_117824c94bb8fa4b5424e2a89ad3129a () Term)
(declare-fun Lib.IntTypes.i8 (Term) Term)

(declare-fun Tm_refine_8af992e69a3ca1855e7c9e939877ac20 (Term) Term)
(declare-fun Tm_arrow_d8465485add1d5ee7930872f346323ef () Term)
(declare-fun Lib.IntTypes.i8@tok () Term)



; </end encoding Lib.IntTypes.i8>


; <Start encoding Lib.IntTypes.u16>

(declare-fun Tm_refine_a636b6491af501737c1eb06142217342 () Term)
(declare-fun Lib.IntTypes.u16 (Term) Term)

(declare-fun Tm_refine_cfdb4594af8e17b0b5af724541abf53f (Term) Term)
(declare-fun Tm_arrow_8e474a9207d1b09769a3f2f09a90520a () Term)
(declare-fun Lib.IntTypes.u16@tok () Term)



; </end encoding Lib.IntTypes.u16>


; <Start encoding Lib.IntTypes.i16>

(declare-fun Tm_refine_b2401a8cabe2f9a01538f32548fa9f6c () Term)
;;;;;;;;;;;;;;;;refinement_interpretation
;;; Fact-ids: Name Lib.IntTypes.i16; Namespace Lib.IntTypes
(assert (! 
;; def=/home/caerbannog/dev/hacl-star/lib/Lib.IntTypes.fsti(79,27-79,43); use=/home/caerbannog/dev/hacl-star/lib/Lib.IntTypes.fsti(262,11-262,18)
(forall ((@u0 Fuel) (@x1 Term))
 (! (iff (HasTypeFuel @u0
@x1
Tm_refine_b2401a8cabe2f9a01538f32548fa9f6c)
(and (HasTypeFuel @u0
@x1
Prims.int)

;; def=/home/caerbannog/dev/hacl-star/lib/Lib.IntTypes.fsti(79,33-79,42); use=/home/caerbannog/dev/hacl-star/lib/Lib.IntTypes.fsti(262,11-262,18)
(Valid 
;; def=/home/caerbannog/dev/hacl-star/lib/Lib.IntTypes.fsti(79,33-79,42); use=/home/caerbannog/dev/hacl-star/lib/Lib.IntTypes.fsti(262,11-262,18)
(Lib.IntTypes.range @x1
Lib.IntTypes.S16@tok)
)
))
 

:pattern ((HasTypeFuel @u0
@x1
Tm_refine_b2401a8cabe2f9a01538f32548fa9f6c))
:qid refinement_interpretation_Tm_refine_b2401a8cabe2f9a01538f32548fa9f6c))

:named refinement_interpretation_Tm_refine_b2401a8cabe2f9a01538f32548fa9f6c))
(declare-fun Lib.IntTypes.i16 (Term) Term)

(declare-fun Tm_refine_c3b8ee23953c5e0e5fe9a52bd7b8ce36 (Term) Term)
(declare-fun Tm_arrow_26c52b915008c7c4e6d3470bfeee33e6 () Term)
(declare-fun Lib.IntTypes.i16@tok () Term)



; </end encoding Lib.IntTypes.i16>


; <Start encoding Lib.IntTypes.u32>

(declare-fun Tm_refine_68ee6d2c8678eb431259a3d4f412550b () Term)
(declare-fun Lib.IntTypes.u32 (Term) Term)

(declare-fun Tm_refine_27680283e93f30a8d9ac7d3b22ec31bf (Term) Term)
(declare-fun Tm_arrow_f897e4c26470162336b1533e0ee2bef6 () Term)
(declare-fun Lib.IntTypes.u32@tok () Term)



; </end encoding Lib.IntTypes.u32>


; <Start encoding Lib.IntTypes.i32>

(declare-fun Tm_refine_ee21347fbca1d214410772ef0425736c () Term)
(declare-fun Lib.IntTypes.i32 (Term) Term)

(declare-fun Tm_refine_ca0cbdcca473f23237c4cff4fd7db154 (Term) Term)
(declare-fun Tm_arrow_f356d18ee1ebd06426f315f7f02deeda () Term)
(declare-fun Lib.IntTypes.i32@tok () Term)



; </end encoding Lib.IntTypes.i32>


; <Start encoding Lib.IntTypes.u64>

(declare-fun Tm_refine_4ae12848fac0601da6605bac9d6872f1 () Term)
(declare-fun Lib.IntTypes.u64 (Term) Term)

(declare-fun Tm_refine_59c6c389f7d2ec9ac28044f709e4c7d6 (Term) Term)
(declare-fun Tm_arrow_cd9c4321e04ad58d1f8f5a6d59ebef77 () Term)
(declare-fun Lib.IntTypes.u64@tok () Term)



; </end encoding Lib.IntTypes.u64>


; <Start encoding Lib.IntTypes.i64>

(declare-fun Tm_refine_360500544b85bc92abd73f53c89e0565 () Term)
(declare-fun Lib.IntTypes.i64 (Term) Term)

(declare-fun Tm_refine_643f451a283be66fd11c916f069b072a (Term) Term)
(declare-fun Tm_arrow_007ea375a93301309e598769cd3bf8d2 () Term)
(declare-fun Lib.IntTypes.i64@tok () Term)



; </end encoding Lib.IntTypes.i64>


; <Start encoding Lib.IntTypes.u128>


(declare-fun Lib.IntTypes.u128 (Term) Term)

(declare-fun Tm_refine_17b5c82e827d21e595c1a46cf8137822 (Term) Term)
(declare-fun Tm_arrow_6e1982efde74d230328c94c7157048b3 () Term)
(declare-fun Lib.IntTypes.u128@tok () Term)



; </end encoding Lib.IntTypes.u128>


; <Start encoding Lib.IntTypes.i128>


(declare-fun Lib.IntTypes.i128 (Term) Term)

(declare-fun Tm_refine_7cece939a5cd7fe40399019c25128476 (Term) Term)
(declare-fun Tm_arrow_40c949d66098a87c48a9513e2c177e03 () Term)
(declare-fun Lib.IntTypes.i128@tok () Term)



; </end encoding Lib.IntTypes.i128>


; <Start encoding Lib.IntTypes.max_size_t>

(declare-fun Lib.IntTypes.max_size_t (Dummy_sort) Term)

; </end encoding Lib.IntTypes.max_size_t>


; <Start encoding Lib.IntTypes.size_nat>

(declare-fun Lib.IntTypes.size_nat () Term)
(declare-fun Tm_refine_0ec011aea9f93256a3547ad9f0c667f1 () Term)

; </end encoding Lib.IntTypes.size_nat>


; <Start encoding Lib.IntTypes.size_pos>

(declare-fun Lib.IntTypes.size_pos () Term)
(declare-fun Tm_refine_44540322a5aeeac77ad2eb12638c2b4f () Term)

; </end encoding Lib.IntTypes.size_pos>


; <Start encoding Lib.IntTypes.size>


(declare-fun Lib.IntTypes.size (Term) Term)

(declare-fun Tm_arrow_550b7962f8ca5f0b5341f4dbe1326e3b () Term)
(declare-fun Lib.IntTypes.size@tok () Term)


; </end encoding Lib.IntTypes.size>


; <Start encoding Lib.IntTypes.size_v>

(declare-fun Lib.IntTypes.size_v (Term) Term)

(declare-fun Tm_arrow_9e32e400e693a15c6164cbca39a40ed3 () Term)
(declare-fun Lib.IntTypes.size_v@tok () Term)


; </end encoding Lib.IntTypes.size_v>


; <Start encoding Lib.IntTypes.byte>

(declare-fun Tm_refine_31c7d3d85d92cb942c95a78642e657c7 () Term)
(declare-fun Lib.IntTypes.byte (Term) Term)

(declare-fun Tm_refine_feb7ca629b12462e536ece5390fccfcd (Term) Term)
(declare-fun Tm_arrow_2b5535fcbbddba9a91583448a0f7cd5a () Term)
(declare-fun Lib.IntTypes.byte@tok () Term)



; </end encoding Lib.IntTypes.byte>


; <Start encoding Lib.IntTypes.byte_v>

(declare-fun Lib.IntTypes.byte_v (Term) Term)
(declare-fun Tm_refine_3b07284e627a7902ae6d028541e34cbc (Term) Term)
(declare-fun Tm_arrow_fc643a4c11baf9cff9a52f6de72ec0d6 () Term)
(declare-fun Lib.IntTypes.byte_v@tok () Term)


; </end encoding Lib.IntTypes.byte_v>


; <Start encoding Lib.IntTypes.size_to_uint32>

(declare-fun Lib.IntTypes.size_to_uint32 (Term) Term)
(declare-fun Tm_refine_0c6907d271a3f37ff8fbfce1f7abda4e (Term) Term)
(declare-fun Tm_arrow_bae393d09677ef1a6c05971ad302a4a6 () Term)
(declare-fun Lib.IntTypes.size_to_uint32@tok () Term)


; </end encoding Lib.IntTypes.size_to_uint32>


; <Start encoding Lib.IntTypes.size_to_uint64>

(declare-fun Lib.IntTypes.size_to_uint64 (Term) Term)
(declare-fun Tm_refine_24a7b28458ba679bb56000984769c285 (Term) Term)
(declare-fun Tm_arrow_a2876930604c8d174ab88ad31b80c10f () Term)
(declare-fun Lib.IntTypes.size_to_uint64@tok () Term)


; </end encoding Lib.IntTypes.size_to_uint64>


; <Start encoding Lib.IntTypes.byte_to_uint8>

(declare-fun Lib.IntTypes.byte_to_uint8 (Term) Term)
(declare-fun Tm_refine_85c9fcd4432001be726c03d4644abe93 (Term) Term)
(declare-fun Tm_arrow_ec0c223d77b92c103755cfb1804969d7 () Term)
(declare-fun Lib.IntTypes.byte_to_uint8@tok () Term)


; </end encoding Lib.IntTypes.byte_to_uint8>


; <Start encoding Lib.IntTypes.op_At_Percent_Dot>

(declare-fun Lib.IntTypes.op_At_Percent_Dot (Term Term) Term)
(declare-fun Tm_arrow_2f76166844837503dc378578a4b4f747 () Term)
(declare-fun Lib.IntTypes.op_At_Percent_Dot@tok () Term)

; </end encoding Lib.IntTypes.op_At_Percent_Dot>


; <Start encoding Lib.IntTypes.cast>

(declare-fun Tm_refine_4c82af8a46684f75d7fe12f75a0fb1a7 (Term) Term)
(declare-fun Tm_refine_55ad6dde98f777fb8caf2adfada0d12e (Term Term Term) Term)
(declare-fun Lib.IntTypes.cast (Term Term Term Term Term) Term)


(declare-fun Tm_refine_4f1cffa40412af126565457cc49b8cca (Term Term Term Term Term) Term)
(declare-fun Tm_arrow_34fd433514ffefe549e10fa9df8d2ada () Term)
(declare-fun Lib.IntTypes.cast@tok () Term)


; </end encoding Lib.IntTypes.cast>


; <Start encoding Lib.IntTypes.to_u1>

(declare-fun Tm_refine_b98107d696cf7d315a15113cd76a74c4 (Term Term) Term)
(declare-fun Lib.IntTypes.to_u1 (Term Term Term) Term)

(declare-fun Tm_arrow_afc048f01c4f6515a705a38288e26630 () Term)
(declare-fun Lib.IntTypes.to_u1@tok () Term)


; </end encoding Lib.IntTypes.to_u1>


; <Start encoding Lib.IntTypes.to_u8>

(declare-fun Tm_refine_6084f6cde9161b0fc14125a161d11802 (Term Term) Term)
(declare-fun Lib.IntTypes.to_u8 (Term Term Term) Term)

(declare-fun Tm_arrow_8cb3b625c51e9b92b672a3b9123a81bf () Term)
(declare-fun Lib.IntTypes.to_u8@tok () Term)


; </end encoding Lib.IntTypes.to_u8>


; <Start encoding Lib.IntTypes.to_i8>

(declare-fun Tm_refine_73e68a650b4ec471aafd1d5636c1d41d (Term Term) Term)
(declare-fun Lib.IntTypes.to_i8 (Term Term Term) Term)

(declare-fun Tm_arrow_266e8f683bc7fd97bf618833177d3be2 () Term)
(declare-fun Lib.IntTypes.to_i8@tok () Term)


; </end encoding Lib.IntTypes.to_i8>


; <Start encoding Lib.IntTypes.to_u16>

(declare-fun Tm_refine_42c61fc2f4b17d29637f887490c756ab (Term Term) Term)
(declare-fun Lib.IntTypes.to_u16 (Term Term Term) Term)

(declare-fun Tm_arrow_73396c649d0f67390420898904df2c04 () Term)
(declare-fun Lib.IntTypes.to_u16@tok () Term)


; </end encoding Lib.IntTypes.to_u16>


; <Start encoding Lib.IntTypes.to_i16>

(declare-fun Tm_refine_e9d99d1d28ded57a90ac7f64bc89c207 (Term Term) Term)
(declare-fun Lib.IntTypes.to_i16 (Term Term Term) Term)

(declare-fun Tm_arrow_75935f9f6dbe645907f8bd87dc0af08c () Term)
(declare-fun Lib.IntTypes.to_i16@tok () Term)


; </end encoding Lib.IntTypes.to_i16>


; <Start encoding Lib.IntTypes.to_u32>

(declare-fun Tm_refine_3ae9d71cfebf196370b730f09544db38 (Term Term) Term)
(declare-fun Lib.IntTypes.to_u32 (Term Term Term) Term)

(declare-fun Tm_arrow_c373043f1940a59bdfc7ba82cfac45e5 () Term)
(declare-fun Lib.IntTypes.to_u32@tok () Term)


; </end encoding Lib.IntTypes.to_u32>


; <Start encoding Lib.IntTypes.to_i32>

(declare-fun Tm_refine_98a7d49788f76e21c9724fdc0714636c (Term Term) Term)
(declare-fun Lib.IntTypes.to_i32 (Term Term Term) Term)

(declare-fun Tm_arrow_47a177813f55463f3c99624fc3446352 () Term)
(declare-fun Lib.IntTypes.to_i32@tok () Term)


; </end encoding Lib.IntTypes.to_i32>


; <Start encoding Lib.IntTypes.to_u64>

(declare-fun Tm_refine_5d8c61e01ead47d91f96119687c63a63 (Term Term) Term)
(declare-fun Lib.IntTypes.to_u64 (Term Term Term) Term)

(declare-fun Tm_arrow_8a1a2d01d36403e8042c35f73161308f () Term)
(declare-fun Lib.IntTypes.to_u64@tok () Term)


; </end encoding Lib.IntTypes.to_u64>


; <Start encoding Lib.IntTypes.to_i64>

(declare-fun Tm_refine_f3563e9cf1d25b85173335f920f4c410 (Term Term) Term)
(declare-fun Lib.IntTypes.to_i64 (Term Term Term) Term)

(declare-fun Tm_arrow_dd65515cf761f666c6a4239c2e079512 () Term)
(declare-fun Lib.IntTypes.to_i64@tok () Term)


; </end encoding Lib.IntTypes.to_i64>


; <Start encoding Lib.IntTypes.to_u128>

(declare-fun Tm_refine_3e073210117584b7835d28b3eb426595 (Term Term) Term)
(declare-fun Lib.IntTypes.to_u128 (Term Term Term) Term)

(declare-fun Tm_arrow_4cd657904f4ad4d4f83b8e2ca5aedde8 () Term)
(declare-fun Lib.IntTypes.to_u128@tok () Term)


; </end encoding Lib.IntTypes.to_u128>


; <Start encoding Lib.IntTypes.to_i128>

(declare-fun Tm_refine_2b8af226883ad80f41a1659fc7a5b3f3 (Term Term) Term)
(declare-fun Lib.IntTypes.to_i128 (Term Term Term) Term)

(declare-fun Tm_arrow_8419982793bbc86076075f31445a3b6b () Term)
(declare-fun Lib.IntTypes.to_i128@tok () Term)


; </end encoding Lib.IntTypes.to_i128>


; <Start encoding Lib.IntTypes.ones_v>

(declare-fun Lib.IntTypes.ones_v (Term) Term)

(declare-fun Lib.IntTypes.ones_v@tok () Term)

; </end encoding Lib.IntTypes.ones_v>


; <Start encoding Lib.IntTypes.ones>

(declare-fun Lib.IntTypes.ones (Term Term) Term)
(declare-fun Tm_refine_032bf6a48f5060ca879f2d84d403b4fa (Term Term) Term)
(declare-fun Tm_arrow_daf1518c6b573ba48bac31e30eb83569 () Term)
(declare-fun Lib.IntTypes.ones@tok () Term)


; </end encoding Lib.IntTypes.ones>


; <Start encoding Lib.IntTypes.zeros>

(declare-fun Lib.IntTypes.zeros (Term Term) Term)
(declare-fun Tm_refine_1f338ca89b14fdf09b67051d08dca8db (Term Term) Term)
(declare-fun Tm_arrow_182f005a7ab482dd6af56c8ecb6b3d61 () Term)
(declare-fun Lib.IntTypes.zeros@tok () Term)


; </end encoding Lib.IntTypes.zeros>


; <Start encoding Lib.IntTypes.add_mod>


(declare-fun Lib.IntTypes.add_mod (Term Term Term Term) Term)

(declare-fun Tm_arrow_b6c7b131dcab59a8eb8f50c70226d5b9 () Term)
(declare-fun Lib.IntTypes.add_mod@tok () Term)

; </end encoding Lib.IntTypes.add_mod>


; <Start encoding Lib.IntTypes.add_mod_lemma>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun Lib.IntTypes.add_mod_lemma (Term Term Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun Lib.IntTypes.add_mod_lemma@tok () Term)


; </end encoding Lib.IntTypes.add_mod_lemma>


; <Start encoding Lib.IntTypes.add>

(declare-fun Tm_refine_feb9bb9f35b4e580b5c2b388310d192a (Term Term Term) Term)
(declare-fun Lib.IntTypes.add (Term Term Term Term) Term)

(declare-fun Tm_arrow_6103473ce2c53f304835922d5ba5654d () Term)
(declare-fun Lib.IntTypes.add@tok () Term)

; </end encoding Lib.IntTypes.add>


; <Start encoding Lib.IntTypes.add_lemma>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun Lib.IntTypes.add_lemma (Term Term Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun Lib.IntTypes.add_lemma@tok () Term)


; </end encoding Lib.IntTypes.add_lemma>


; <Start encoding Lib.IntTypes.incr>

(declare-fun Tm_refine_afa0526f38dbf9e3a3d62e51b33489ef (Term Term) Term)
(declare-fun Lib.IntTypes.incr (Term Term Term) Term)

(declare-fun Tm_arrow_60cdd0ac07812c70fd450a21604f0e6f () Term)
(declare-fun Lib.IntTypes.incr@tok () Term)

; </end encoding Lib.IntTypes.incr>


; <Start encoding Lib.IntTypes.incr_lemma>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun Lib.IntTypes.incr_lemma (Term Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun Lib.IntTypes.incr_lemma@tok () Term)

; </end encoding Lib.IntTypes.incr_lemma>


; <Start encoding Lib.IntTypes.mul_mod>

(declare-fun Tm_refine_4e3bbd8eec0c3ef82902d2336c68c242 () Term)
(declare-fun Lib.IntTypes.mul_mod (Term Term Term Term) Term)

(declare-fun Tm_arrow_cd6e2af2c720a97ef71723e3dc123b88 () Term)
(declare-fun Lib.IntTypes.mul_mod@tok () Term)

; </end encoding Lib.IntTypes.mul_mod>


; <Start encoding Lib.IntTypes.mul_mod_lemma>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun Lib.IntTypes.mul_mod_lemma (Term Term Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun Lib.IntTypes.mul_mod_lemma@tok () Term)


; </end encoding Lib.IntTypes.mul_mod_lemma>


; <Start encoding Lib.IntTypes.mul>

(declare-fun Tm_refine_b550ca9347e0645a53715102a08d8fa1 () Term)
(declare-fun Tm_refine_9ff150f589411d5a40376aa0c5e1ca86 (Term Term Term) Term)
(declare-fun Lib.IntTypes.mul (Term Term Term Term) Term)


(declare-fun Tm_arrow_68edef36a5de76ca466d8fdf5f31efa2 () Term)
(declare-fun Lib.IntTypes.mul@tok () Term)

; </end encoding Lib.IntTypes.mul>


; <Start encoding Lib.IntTypes.mul_lemma>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun Lib.IntTypes.mul_lemma (Term Term Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun Lib.IntTypes.mul_lemma@tok () Term)



; </end encoding Lib.IntTypes.mul_lemma>


; <Start encoding Lib.IntTypes.mul64_wide>

(declare-fun Lib.IntTypes.mul64_wide (Term Term) Term)
(declare-fun Tm_arrow_5f6ec659f8f6409b2aa64286bd56fc42 () Term)
(declare-fun Lib.IntTypes.mul64_wide@tok () Term)

; </end encoding Lib.IntTypes.mul64_wide>


; <Start encoding Lib.IntTypes.mul64_wide_lemma>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun Lib.IntTypes.mul64_wide_lemma (Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun Lib.IntTypes.mul64_wide_lemma@tok () Term)

; </end encoding Lib.IntTypes.mul64_wide_lemma>


; <Start encoding Lib.IntTypes.mul_s64_wide>

(declare-fun Lib.IntTypes.mul_s64_wide (Term Term) Term)
(declare-fun Tm_arrow_8c0921275def679dc45195a422550c71 () Term)
(declare-fun Lib.IntTypes.mul_s64_wide@tok () Term)

; </end encoding Lib.IntTypes.mul_s64_wide>


; <Start encoding Lib.IntTypes.mul_s64_wide_lemma>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun Lib.IntTypes.mul_s64_wide_lemma (Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun Lib.IntTypes.mul_s64_wide_lemma@tok () Term)

; </end encoding Lib.IntTypes.mul_s64_wide_lemma>


; <Start encoding Lib.IntTypes.sub_mod>


(declare-fun Lib.IntTypes.sub_mod (Term Term Term Term) Term)


(declare-fun Lib.IntTypes.sub_mod@tok () Term)

; </end encoding Lib.IntTypes.sub_mod>


; <Start encoding Lib.IntTypes.sub_mod_lemma>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun Lib.IntTypes.sub_mod_lemma (Term Term Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun Lib.IntTypes.sub_mod_lemma@tok () Term)


; </end encoding Lib.IntTypes.sub_mod_lemma>


; <Start encoding Lib.IntTypes.sub>

(declare-fun Tm_refine_1cc58e901e83e96dff5b4d1682343605 (Term Term Term) Term)
(declare-fun Lib.IntTypes.sub (Term Term Term Term) Term)

(declare-fun Tm_arrow_a202f55208631a180575cba61fdf76c0 () Term)
(declare-fun Lib.IntTypes.sub@tok () Term)

; </end encoding Lib.IntTypes.sub>


; <Start encoding Lib.IntTypes.sub_lemma>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun Lib.IntTypes.sub_lemma (Term Term Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun Lib.IntTypes.sub_lemma@tok () Term)


; </end encoding Lib.IntTypes.sub_lemma>


; <Start encoding Lib.IntTypes.decr>

(declare-fun Tm_refine_e078a351fb9a9df6f9eb32a09e98e8aa (Term Term) Term)
(declare-fun Lib.IntTypes.decr (Term Term Term) Term)

(declare-fun Tm_arrow_a59fac5c6ad8c2cb5a3a0bbdf8c501e0 () Term)
(declare-fun Lib.IntTypes.decr@tok () Term)

; </end encoding Lib.IntTypes.decr>


; <Start encoding Lib.IntTypes.decr_lemma>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun Lib.IntTypes.decr_lemma (Term Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun Lib.IntTypes.decr_lemma@tok () Term)

; </end encoding Lib.IntTypes.decr_lemma>


; <Start encoding Lib.IntTypes.logxor>

(declare-fun Lib.IntTypes.logxor (Term Term Term Term) Term)
(declare-fun Tm_arrow_f4a9562bad893d799188b75efefcbe4b () Term)
(declare-fun Lib.IntTypes.logxor@tok () Term)

; </end encoding Lib.IntTypes.logxor>


; <Start encoding Lib.IntTypes.logxor_lemma>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun Lib.IntTypes.logxor_lemma (Term Term Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun Lib.IntTypes.logxor_lemma@tok () Term)

; </end encoding Lib.IntTypes.logxor_lemma>


; <Start encoding Lib.IntTypes.logxor_lemma1>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun Lib.IntTypes.logxor_lemma1 (Term Term Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun Lib.IntTypes.logxor_lemma1@tok () Term)

; </end encoding Lib.IntTypes.logxor_lemma1>


; <Start encoding Lib.IntTypes.logand>

(declare-fun Lib.IntTypes.logand (Term Term Term Term) Term)

(declare-fun Lib.IntTypes.logand@tok () Term)

; </end encoding Lib.IntTypes.logand>


; <Start encoding Lib.IntTypes.logand_zeros>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun Lib.IntTypes.logand_zeros (Term Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun Lib.IntTypes.logand_zeros@tok () Term)

; </end encoding Lib.IntTypes.logand_zeros>


; <Start encoding Lib.IntTypes.logand_ones>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun Lib.IntTypes.logand_ones (Term Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun Lib.IntTypes.logand_ones@tok () Term)

; </end encoding Lib.IntTypes.logand_ones>


; <Start encoding Lib.IntTypes.logand_lemma>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun Lib.IntTypes.logand_lemma (Term Term Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun Lib.IntTypes.logand_lemma@tok () Term)

; </end encoding Lib.IntTypes.logand_lemma>


; <Start encoding Lib.IntTypes.logand_v>



(declare-fun Lib.IntTypes.logand_v (Term Term Term) Term)



(declare-fun Tm_arrow_a57bfdacab615fe929798b9c423e828b () Term)
(declare-fun Lib.IntTypes.logand_v@tok () Term)




; </end encoding Lib.IntTypes.logand_v>


; <Start encoding Lib.IntTypes.logand_spec>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun Lib.IntTypes.logand_spec (Term Term Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun Lib.IntTypes.logand_spec@tok () Term)

; </end encoding Lib.IntTypes.logand_spec>


; <Start encoding Lib.IntTypes.logor>

(declare-fun Lib.IntTypes.logor (Term Term Term Term) Term)

(declare-fun Lib.IntTypes.logor@tok () Term)

; </end encoding Lib.IntTypes.logor>


; <Start encoding Lib.IntTypes.logor_disjoint>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun Lib.IntTypes.logor_disjoint (Term Term Term Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun Lib.IntTypes.logor_disjoint@tok () Term)

; </end encoding Lib.IntTypes.logor_disjoint>


; <Start encoding Lib.IntTypes.lognot>

(declare-fun Lib.IntTypes.lognot (Term Term Term) Term)
(declare-fun Tm_arrow_1908442cbcab18a03680e5d4e4bd7d5c () Term)
(declare-fun Lib.IntTypes.lognot@tok () Term)

; </end encoding Lib.IntTypes.lognot>


; <Start encoding Lib.IntTypes.shiftval>

(declare-fun Lib.IntTypes.shiftval (Term) Term)

(declare-fun Lib.IntTypes.shiftval@tok () Term)
(declare-fun Tm_refine_e40dba697735a60216c598c2a27841b5 (Term) Term)

; </end encoding Lib.IntTypes.shiftval>


; <Start encoding Lib.IntTypes.rotval>

(declare-fun Lib.IntTypes.rotval (Term) Term)

(declare-fun Lib.IntTypes.rotval@tok () Term)
(declare-fun Tm_refine_0da46ef8643a6f8ea97a3358bc923338 (Term) Term)

; </end encoding Lib.IntTypes.rotval>


; <Start encoding Lib.IntTypes.shift_right>

(declare-fun Lib.IntTypes.shift_right (Term Term Term Term) Term)
(declare-fun Tm_arrow_cb85578b810e2f37b16ac494a6aa674f () Term)
(declare-fun Lib.IntTypes.shift_right@tok () Term)

; </end encoding Lib.IntTypes.shift_right>


; <Start encoding Lib.IntTypes.shift_right_lemma>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun Lib.IntTypes.shift_right_lemma (Term Term Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun Lib.IntTypes.shift_right_lemma@tok () Term)

; </end encoding Lib.IntTypes.shift_right_lemma>


; <Start encoding Lib.IntTypes.shift_left>

(declare-fun Tm_refine_fffc918f3ac13711d39fee794fcdce53 (Term Term) Term)
(declare-fun Lib.IntTypes.shift_left (Term Term Term Term) Term)

(declare-fun Tm_arrow_4558013623bb3073d082b2bcf71fe665 () Term)
(declare-fun Lib.IntTypes.shift_left@tok () Term)

; </end encoding Lib.IntTypes.shift_left>


; <Start encoding Lib.IntTypes.shift_left_lemma>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun Lib.IntTypes.shift_left_lemma (Term Term Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun Lib.IntTypes.shift_left_lemma@tok () Term)


; </end encoding Lib.IntTypes.shift_left_lemma>


; <Start encoding Lib.IntTypes.rotate_right>


(declare-fun Lib.IntTypes.rotate_right (Term Term Term Term) Term)

(declare-fun Tm_arrow_b26527517c2fc0b25fb27d1f6c420de4 () Term)
(declare-fun Lib.IntTypes.rotate_right@tok () Term)

; </end encoding Lib.IntTypes.rotate_right>


; <Start encoding Lib.IntTypes.rotate_left>


(declare-fun Lib.IntTypes.rotate_left (Term Term Term Term) Term)


(declare-fun Lib.IntTypes.rotate_left@tok () Term)

; </end encoding Lib.IntTypes.rotate_left>


; <Start encoding Lib.IntTypes.ct_abs>

(declare-fun Tm_refine_de547f196c5d80d3c8c7650b475a5db4 () Term)

(declare-fun Lib.IntTypes.ct_abs (Term Term Term) Term)


(declare-fun Tm_refine_ab4042114500dff1eaea14b4488f3107 (Term Term Term) Term)
(declare-fun Tm_arrow_a57acdfc002ce99685830751964396bb () Term)
(declare-fun Lib.IntTypes.ct_abs@tok () Term)


; </end encoding Lib.IntTypes.ct_abs>


; <Start encoding Lib.IntTypes.eq_mask>

(declare-fun Tm_refine_d13c5132af51f62dfb7018a438f66ab7 () Term)
(declare-fun Lib.IntTypes.eq_mask (Term Term Term) Term)

(declare-fun Tm_arrow_ddf90b607a103b2a2807495669efe916 () Term)
(declare-fun Lib.IntTypes.eq_mask@tok () Term)

; </end encoding Lib.IntTypes.eq_mask>


; <Start encoding Lib.IntTypes.eq_mask_lemma>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun Lib.IntTypes.eq_mask_lemma (Term Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun Lib.IntTypes.eq_mask_lemma@tok () Term)



; </end encoding Lib.IntTypes.eq_mask_lemma>


; <Start encoding Lib.IntTypes.eq_mask_logand_lemma>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun Lib.IntTypes.eq_mask_logand_lemma (Term Term Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun Lib.IntTypes.eq_mask_logand_lemma@tok () Term)



; </end encoding Lib.IntTypes.eq_mask_logand_lemma>


; <Start encoding Lib.IntTypes.neq_mask>


(declare-fun Lib.IntTypes.neq_mask (Term Term Term) Term)


(declare-fun Lib.IntTypes.neq_mask@tok () Term)

; </end encoding Lib.IntTypes.neq_mask>


; <Start encoding Lib.IntTypes.neq_mask_lemma>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun Lib.IntTypes.neq_mask_lemma (Term Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun Lib.IntTypes.neq_mask_lemma@tok () Term)



; </end encoding Lib.IntTypes.neq_mask_lemma>


; <Start encoding Lib.IntTypes.gte_mask>


(declare-fun Lib.IntTypes.gte_mask (Term Term Term) Term)

(declare-fun Tm_arrow_f4afff6b394bf99658a087b1e50597af () Term)
(declare-fun Lib.IntTypes.gte_mask@tok () Term)

; </end encoding Lib.IntTypes.gte_mask>


; <Start encoding Lib.IntTypes.gte_mask_lemma>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun Lib.IntTypes.gte_mask_lemma (Term Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun Lib.IntTypes.gte_mask_lemma@tok () Term)


; </end encoding Lib.IntTypes.gte_mask_lemma>


; <Start encoding Lib.IntTypes.gte_mask_logand_lemma>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun Lib.IntTypes.gte_mask_logand_lemma (Term Term Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun Lib.IntTypes.gte_mask_logand_lemma@tok () Term)


; </end encoding Lib.IntTypes.gte_mask_logand_lemma>


; <Start encoding Lib.IntTypes.lt_mask>


(declare-fun Lib.IntTypes.lt_mask (Term Term Term) Term)


(declare-fun Lib.IntTypes.lt_mask@tok () Term)

; </end encoding Lib.IntTypes.lt_mask>


; <Start encoding Lib.IntTypes.lt_mask_lemma>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun Lib.IntTypes.lt_mask_lemma (Term Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun Lib.IntTypes.lt_mask_lemma@tok () Term)


; </end encoding Lib.IntTypes.lt_mask_lemma>


; <Start encoding Lib.IntTypes.gt_mask>


(declare-fun Lib.IntTypes.gt_mask (Term Term Term) Term)


(declare-fun Lib.IntTypes.gt_mask@tok () Term)

; </end encoding Lib.IntTypes.gt_mask>


; <Start encoding Lib.IntTypes.gt_mask_lemma>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun Lib.IntTypes.gt_mask_lemma (Term Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun Lib.IntTypes.gt_mask_lemma@tok () Term)


; </end encoding Lib.IntTypes.gt_mask_lemma>


; <Start encoding Lib.IntTypes.lte_mask>


(declare-fun Lib.IntTypes.lte_mask (Term Term Term) Term)


(declare-fun Lib.IntTypes.lte_mask@tok () Term)

; </end encoding Lib.IntTypes.lte_mask>


; <Start encoding Lib.IntTypes.lte_mask_lemma>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun Lib.IntTypes.lte_mask_lemma (Term Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun Lib.IntTypes.lte_mask_lemma@tok () Term)


; </end encoding Lib.IntTypes.lte_mask_lemma>


; <Start encoding Lib.IntTypes.mod_mask>


(declare-fun Lib.IntTypes.mod_mask (Term Term Term) Term)

(declare-fun Tm_arrow_dde77df78b990c6640d980cd6fe1d191 () Term)
(declare-fun Lib.IntTypes.mod_mask@tok () Term)


; </end encoding Lib.IntTypes.mod_mask>


; <Start encoding Lib.IntTypes.mod_mask_lemma>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun Lib.IntTypes.mod_mask_lemma (Term Term Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun Lib.IntTypes.mod_mask_lemma@tok () Term)


; </end encoding Lib.IntTypes.mod_mask_lemma>


; <Start encoding Lib.IntTypes.op_Plus_Bang>

(declare-fun Lib.IntTypes.op_Plus_Bang (Term Term) Term)

(declare-fun Tm_arrow_4748061ecbd4912a48b6da82af3774a4 (Term Term) Term)
(declare-fun Tm_arrow_27f910cf3d6a7631b9ff421de5d4d192 () Term)
(declare-fun Lib.IntTypes.op_Plus_Bang@tok () Term)


;;;;;;;;;;;;;;;;kick_partial_app
;;; Fact-ids: Name Lib.IntTypes.op_Plus_Bang; Namespace Lib.IntTypes
(assert (! (Valid (ApplyTT __uu__PartialApp
Lib.IntTypes.add@tok))
:named @kick_partial_app_ba79cac500b4e22faa742b45615bf647))

; </end encoding Lib.IntTypes.op_Plus_Bang>


; <Start encoding Lib.IntTypes.op_Plus_Dot>


(declare-fun Lib.IntTypes.op_Plus_Dot (Term Term) Term)

(declare-fun Tm_arrow_26e1564cd439c7a51d9fb0abd624cd07 (Term Term) Term)
(declare-fun Tm_arrow_c0fea3f793b80ab8f3a9d6f15a203cfc () Term)
(declare-fun Lib.IntTypes.op_Plus_Dot@tok () Term)


;;;;;;;;;;;;;;;;kick_partial_app
;;; Fact-ids: Name Lib.IntTypes.op_Plus_Dot; Namespace Lib.IntTypes
(assert (! (Valid (ApplyTT __uu__PartialApp
Lib.IntTypes.add_mod@tok))
:named @kick_partial_app_ad446ac11653950d7e6d791b1283108b))

; </end encoding Lib.IntTypes.op_Plus_Dot>


; <Start encoding Lib.IntTypes.op_Star_Bang>


(declare-fun Lib.IntTypes.op_Star_Bang (Term Term) Term)


(declare-fun Tm_arrow_8d9b837067a652cd46cbe330b5a57ae8 (Term Term) Term)
(declare-fun Tm_arrow_b123053daf9a361af825b854f405b211 () Term)
(declare-fun Lib.IntTypes.op_Star_Bang@tok () Term)



;;;;;;;;;;;;;;;;kick_partial_app
;;; Fact-ids: Name Lib.IntTypes.op_Star_Bang; Namespace Lib.IntTypes
(assert (! (Valid (ApplyTT __uu__PartialApp
Lib.IntTypes.mul@tok))
:named @kick_partial_app_58f2e8c711f17f836faaad7ffef33a7e))

; </end encoding Lib.IntTypes.op_Star_Bang>


; <Start encoding Lib.IntTypes.op_Star_Dot>


(declare-fun Lib.IntTypes.op_Star_Dot (Term Term) Term)


(declare-fun Tm_arrow_82d7b669c6fcb8647d58e1305f409fdd () Term)
(declare-fun Lib.IntTypes.op_Star_Dot@tok () Term)


;;;;;;;;;;;;;;;;kick_partial_app
;;; Fact-ids: Name Lib.IntTypes.op_Star_Dot; Namespace Lib.IntTypes
(assert (! (Valid (ApplyTT __uu__PartialApp
Lib.IntTypes.mul_mod@tok))
:named @kick_partial_app_cf84f124c81b2a3b75085fc2fe575549))

; </end encoding Lib.IntTypes.op_Star_Dot>


; <Start encoding Lib.IntTypes.op_Subtraction_Bang>

(declare-fun Lib.IntTypes.op_Subtraction_Bang (Term Term) Term)

(declare-fun Tm_arrow_cf0576d9b83132b1c4b2d704c1820e74 (Term Term) Term)
(declare-fun Tm_arrow_3abf4cc2b13e332a0d31f351bff3a903 () Term)
(declare-fun Lib.IntTypes.op_Subtraction_Bang@tok () Term)


;;;;;;;;;;;;;;;;kick_partial_app
;;; Fact-ids: Name Lib.IntTypes.op_Subtraction_Bang; Namespace Lib.IntTypes
(assert (! (Valid (ApplyTT __uu__PartialApp
Lib.IntTypes.sub@tok))
:named @kick_partial_app_3a53997354ed354516f904966f3f2d6f))

; </end encoding Lib.IntTypes.op_Subtraction_Bang>


; <Start encoding Lib.IntTypes.op_Subtraction_Dot>


(declare-fun Lib.IntTypes.op_Subtraction_Dot (Term Term) Term)



(declare-fun Lib.IntTypes.op_Subtraction_Dot@tok () Term)


;;;;;;;;;;;;;;;;kick_partial_app
;;; Fact-ids: Name Lib.IntTypes.op_Subtraction_Dot; Namespace Lib.IntTypes
(assert (! (Valid (ApplyTT __uu__PartialApp
Lib.IntTypes.sub_mod@tok))
:named @kick_partial_app_b64f93a5beb561157c1951c1c1fcbb7d))

; </end encoding Lib.IntTypes.op_Subtraction_Dot>


; <Start encoding Lib.IntTypes.op_Greater_Greater_Dot>

(declare-fun Lib.IntTypes.op_Greater_Greater_Dot (Term Term) Term)
(declare-fun Tm_arrow_69077372bac495d5eb2b3177362e29d2 (Term Term) Term)
(declare-fun Tm_arrow_dbca19db741b233e4ae08e8783dc8fb4 () Term)
(declare-fun Lib.IntTypes.op_Greater_Greater_Dot@tok () Term)

;;;;;;;;;;;;;;;;kick_partial_app
;;; Fact-ids: Name Lib.IntTypes.op_Greater_Greater_Dot; Namespace Lib.IntTypes
(assert (! (Valid (ApplyTT __uu__PartialApp
Lib.IntTypes.shift_right@tok))
:named @kick_partial_app_a70eab15fa615882f896c3d521dcaff2))

; </end encoding Lib.IntTypes.op_Greater_Greater_Dot>


; <Start encoding Lib.IntTypes.op_Less_Less_Dot>

(declare-fun Lib.IntTypes.op_Less_Less_Dot (Term Term) Term)

(declare-fun Tm_arrow_c971193cbcf499f0ed2b7a2acf7a1609 (Term Term) Term)
(declare-fun Tm_arrow_3c77712e82fc06acd8752f36b0232b4e () Term)
(declare-fun Lib.IntTypes.op_Less_Less_Dot@tok () Term)


;;;;;;;;;;;;;;;;kick_partial_app
;;; Fact-ids: Name Lib.IntTypes.op_Less_Less_Dot; Namespace Lib.IntTypes
(assert (! (Valid (ApplyTT __uu__PartialApp
Lib.IntTypes.shift_left@tok))
:named @kick_partial_app_b58abb751ac24b06edcb69cb8723eecd))

; </end encoding Lib.IntTypes.op_Less_Less_Dot>


; <Start encoding Lib.IntTypes.op_Greater_Greater_Greater_Dot>

(declare-fun Lib.IntTypes.op_Greater_Greater_Greater_Dot (Term Term) Term)

(declare-fun Tm_arrow_b35df878355e54b5a1b49b803e7ef043 (Term Term) Term)
(declare-fun Tm_arrow_65614e05c05b86cecdd5df39816991d7 () Term)
(declare-fun Lib.IntTypes.op_Greater_Greater_Greater_Dot@tok () Term)


;;;;;;;;;;;;;;;;kick_partial_app
;;; Fact-ids: Name Lib.IntTypes.op_Greater_Greater_Greater_Dot; Namespace Lib.IntTypes
(assert (! (Valid (ApplyTT __uu__PartialApp
Lib.IntTypes.rotate_right@tok))
:named @kick_partial_app_5536e36f9e11538f425401d4f0d0680b))

; </end encoding Lib.IntTypes.op_Greater_Greater_Greater_Dot>


; <Start encoding Lib.IntTypes.op_Less_Less_Less_Dot>

(declare-fun Lib.IntTypes.op_Less_Less_Less_Dot (Term Term) Term)



(declare-fun Lib.IntTypes.op_Less_Less_Less_Dot@tok () Term)


;;;;;;;;;;;;;;;;kick_partial_app
;;; Fact-ids: Name Lib.IntTypes.op_Less_Less_Less_Dot; Namespace Lib.IntTypes
(assert (! (Valid (ApplyTT __uu__PartialApp
Lib.IntTypes.rotate_left@tok))
:named @kick_partial_app_d083db66f7da9021bdc10206f2553c06))

; </end encoding Lib.IntTypes.op_Less_Less_Less_Dot>


; <Start encoding Lib.IntTypes.op_Hat_Dot>

(declare-fun Lib.IntTypes.op_Hat_Dot (Term Term) Term)

(declare-fun Tm_arrow_d29fc23e6a30c0c4a0a1275a88868b8e () Term)
(declare-fun Lib.IntTypes.op_Hat_Dot@tok () Term)

;;;;;;;;;;;;;;;;kick_partial_app
;;; Fact-ids: Name Lib.IntTypes.op_Hat_Dot; Namespace Lib.IntTypes
(assert (! (Valid (ApplyTT __uu__PartialApp
Lib.IntTypes.logxor@tok))
:named @kick_partial_app_8fa9c89b2a609f5543a3376538ef7f24))

; </end encoding Lib.IntTypes.op_Hat_Dot>


; <Start encoding Lib.IntTypes.op_Bar_Dot>

(declare-fun Lib.IntTypes.op_Bar_Dot (Term Term) Term)


(declare-fun Lib.IntTypes.op_Bar_Dot@tok () Term)

;;;;;;;;;;;;;;;;kick_partial_app
;;; Fact-ids: Name Lib.IntTypes.op_Bar_Dot; Namespace Lib.IntTypes
(assert (! (Valid (ApplyTT __uu__PartialApp
Lib.IntTypes.logor@tok))
:named @kick_partial_app_4023eb217999264d683e0fb21d03212f))

; </end encoding Lib.IntTypes.op_Bar_Dot>


; <Start encoding Lib.IntTypes.op_Amp_Dot>

(declare-fun Lib.IntTypes.op_Amp_Dot (Term Term) Term)


(declare-fun Lib.IntTypes.op_Amp_Dot@tok () Term)

;;;;;;;;;;;;;;;;kick_partial_app
;;; Fact-ids: Name Lib.IntTypes.op_Amp_Dot; Namespace Lib.IntTypes
(assert (! (Valid (ApplyTT __uu__PartialApp
Lib.IntTypes.logand@tok))
:named @kick_partial_app_958d4357c25babd2430335b823a327f0))

; </end encoding Lib.IntTypes.op_Amp_Dot>


; <Start encoding Lib.IntTypes.op_Tilde_Dot>

(declare-fun Lib.IntTypes.op_Tilde_Dot (Term Term) Term)
(declare-fun Tm_arrow_049b1b0f12668169ec345ed911fc709a (Term Term) Term)
(declare-fun Tm_arrow_0f6885253189468e65338d1c5252543b () Term)
(declare-fun Lib.IntTypes.op_Tilde_Dot@tok () Term)

;;;;;;;;;;;;;;;;kick_partial_app
;;; Fact-ids: Name Lib.IntTypes.op_Tilde_Dot; Namespace Lib.IntTypes
(assert (! (Valid (ApplyTT __uu__PartialApp
Lib.IntTypes.lognot@tok))
:named @kick_partial_app_b549b61570d50f74e1a303bcfa1785fb))

; </end encoding Lib.IntTypes.op_Tilde_Dot>


; <Start encoding Lib.IntTypes.div>


(declare-fun Tm_refine_e450d0eda8ec6ce5c9eff42d01f0e81a (Term Term) Term)
(declare-fun Lib.IntTypes.div (Term Term Term) Term)


(declare-fun Tm_arrow_75c9d8cffd77af696d9868df0ceb9cf9 () Term)
(declare-fun Lib.IntTypes.div@tok () Term)

; </end encoding Lib.IntTypes.div>


; <Start encoding Lib.IntTypes.div_lemma>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun Lib.IntTypes.div_lemma (Term Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun Lib.IntTypes.div_lemma@tok () Term)



; </end encoding Lib.IntTypes.div_lemma>


; <Start encoding Lib.IntTypes.mod>



(declare-fun Lib.IntTypes.mod (Term Term Term) Term)



(declare-fun Lib.IntTypes.mod@tok () Term)

; </end encoding Lib.IntTypes.mod>


; <Start encoding Lib.IntTypes.mod_lemma>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun Lib.IntTypes.mod_lemma (Term Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun Lib.IntTypes.mod_lemma@tok () Term)



; </end encoding Lib.IntTypes.mod_lemma>


; <Start encoding Lib.IntTypes.eq>

(declare-fun Lib.IntTypes.eq (Term Term Term) Term)
(declare-fun Tm_arrow_0659d9623134a9bcc70d6289b6fd28bf () Term)
(declare-fun Lib.IntTypes.eq@tok () Term)

; </end encoding Lib.IntTypes.eq>


; <Start encoding Lib.IntTypes.eq_lemma>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun Lib.IntTypes.eq_lemma (Term Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun Lib.IntTypes.eq_lemma@tok () Term)


; </end encoding Lib.IntTypes.eq_lemma>


; <Start encoding Lib.IntTypes.ne>

(declare-fun Lib.IntTypes.ne (Term Term Term) Term)

(declare-fun Lib.IntTypes.ne@tok () Term)

; </end encoding Lib.IntTypes.ne>


; <Start encoding Lib.IntTypes.ne_lemma>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun Lib.IntTypes.ne_lemma (Term Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun Lib.IntTypes.ne_lemma@tok () Term)


; </end encoding Lib.IntTypes.ne_lemma>


; <Start encoding Lib.IntTypes.lt>

(declare-fun Lib.IntTypes.lt (Term Term Term) Term)

(declare-fun Lib.IntTypes.lt@tok () Term)

; </end encoding Lib.IntTypes.lt>


; <Start encoding Lib.IntTypes.lt_lemma>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun Lib.IntTypes.lt_lemma (Term Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun Lib.IntTypes.lt_lemma@tok () Term)

; </end encoding Lib.IntTypes.lt_lemma>


; <Start encoding Lib.IntTypes.lte>

(declare-fun Lib.IntTypes.lte (Term Term Term) Term)

(declare-fun Lib.IntTypes.lte@tok () Term)

; </end encoding Lib.IntTypes.lte>


; <Start encoding Lib.IntTypes.lte_lemma>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun Lib.IntTypes.lte_lemma (Term Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun Lib.IntTypes.lte_lemma@tok () Term)

; </end encoding Lib.IntTypes.lte_lemma>


; <Start encoding Lib.IntTypes.gt>

(declare-fun Lib.IntTypes.gt (Term Term Term) Term)

(declare-fun Lib.IntTypes.gt@tok () Term)

; </end encoding Lib.IntTypes.gt>


; <Start encoding Lib.IntTypes.gt_lemma>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun Lib.IntTypes.gt_lemma (Term Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun Lib.IntTypes.gt_lemma@tok () Term)

; </end encoding Lib.IntTypes.gt_lemma>


; <Start encoding Lib.IntTypes.gte>

(declare-fun Lib.IntTypes.gte (Term Term Term) Term)

(declare-fun Lib.IntTypes.gte@tok () Term)

; </end encoding Lib.IntTypes.gte>


; <Start encoding Lib.IntTypes.gte_lemma>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun Lib.IntTypes.gte_lemma (Term Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun Lib.IntTypes.gte_lemma@tok () Term)

; </end encoding Lib.IntTypes.gte_lemma>


; <Start encoding Lib.IntTypes.op_Slash_Dot>


(declare-fun Lib.IntTypes.op_Slash_Dot (Term) Term)


(declare-fun Tm_arrow_6a3e920b5265e08755ab0451be7385d0 (Term) Term)
(declare-fun Tm_arrow_ac512cb9ff42efd177fb9527bdceefaa () Term)
(declare-fun Lib.IntTypes.op_Slash_Dot@tok () Term)



;;;;;;;;;;;;;;;;kick_partial_app
;;; Fact-ids: Name Lib.IntTypes.op_Slash_Dot; Namespace Lib.IntTypes
(assert (! (Valid (ApplyTT __uu__PartialApp
Lib.IntTypes.div@tok))
:named @kick_partial_app_83470e4eb482c1afb76802a98ddacde4))

; </end encoding Lib.IntTypes.op_Slash_Dot>


; <Start encoding Lib.IntTypes.op_Percent_Dot>


(declare-fun Lib.IntTypes.op_Percent_Dot (Term) Term)




(declare-fun Lib.IntTypes.op_Percent_Dot@tok () Term)



;;;;;;;;;;;;;;;;kick_partial_app
;;; Fact-ids: Name Lib.IntTypes.op_Percent_Dot; Namespace Lib.IntTypes
(assert (! (Valid (ApplyTT __uu__PartialApp
Lib.IntTypes.mod@tok))
:named @kick_partial_app_9d2efaa1000c8d55ed0f8dd453f3c9ed))

; </end encoding Lib.IntTypes.op_Percent_Dot>


; <Start encoding Lib.IntTypes.op_Equals_Dot>

(declare-fun Lib.IntTypes.op_Equals_Dot (Term) Term)
(declare-fun Tm_arrow_cc646d4915292a473ee835f7737d9776 (Term) Term)
(declare-fun Tm_arrow_a9fadd2033f434155d72b2bcc7d0f9a6 () Term)
(declare-fun Lib.IntTypes.op_Equals_Dot@tok () Term)

;;;;;;;;;;;;;;;;kick_partial_app
;;; Fact-ids: Name Lib.IntTypes.op_Equals_Dot; Namespace Lib.IntTypes
(assert (! (Valid (ApplyTT __uu__PartialApp
Lib.IntTypes.eq@tok))
:named @kick_partial_app_6fea289ed65cc266cb4bc4e6fdfc443a))

; </end encoding Lib.IntTypes.op_Equals_Dot>


; <Start encoding Lib.IntTypes.op_Less_Greater_Dot>

(declare-fun Lib.IntTypes.op_Less_Greater_Dot (Term) Term)


(declare-fun Lib.IntTypes.op_Less_Greater_Dot@tok () Term)

;;;;;;;;;;;;;;;;kick_partial_app
;;; Fact-ids: Name Lib.IntTypes.op_Less_Greater_Dot; Namespace Lib.IntTypes
(assert (! (Valid (ApplyTT __uu__PartialApp
Lib.IntTypes.ne@tok))
:named @kick_partial_app_9843dc105d5b6b3c8c59924d38c0e228))

; </end encoding Lib.IntTypes.op_Less_Greater_Dot>


; <Start encoding Lib.IntTypes.op_Less_Dot>

(declare-fun Lib.IntTypes.op_Less_Dot (Term) Term)


(declare-fun Lib.IntTypes.op_Less_Dot@tok () Term)

;;;;;;;;;;;;;;;;kick_partial_app
;;; Fact-ids: Name Lib.IntTypes.op_Less_Dot; Namespace Lib.IntTypes
(assert (! (Valid (ApplyTT __uu__PartialApp
Lib.IntTypes.lt@tok))
:named @kick_partial_app_a72a8245daf92ff2fc3d6db0fa50a6ec))

; </end encoding Lib.IntTypes.op_Less_Dot>


; <Start encoding Lib.IntTypes.op_Less_Equals_Dot>

(declare-fun Lib.IntTypes.op_Less_Equals_Dot (Term) Term)


(declare-fun Lib.IntTypes.op_Less_Equals_Dot@tok () Term)

;;;;;;;;;;;;;;;;kick_partial_app
;;; Fact-ids: Name Lib.IntTypes.op_Less_Equals_Dot; Namespace Lib.IntTypes
(assert (! (Valid (ApplyTT __uu__PartialApp
Lib.IntTypes.lte@tok))
:named @kick_partial_app_d50d1867de774d0c7a508c3cdea4200b))

; </end encoding Lib.IntTypes.op_Less_Equals_Dot>


; <Start encoding Lib.IntTypes.op_Greater_Dot>

(declare-fun Lib.IntTypes.op_Greater_Dot (Term) Term)


(declare-fun Lib.IntTypes.op_Greater_Dot@tok () Term)

;;;;;;;;;;;;;;;;kick_partial_app
;;; Fact-ids: Name Lib.IntTypes.op_Greater_Dot; Namespace Lib.IntTypes
(assert (! (Valid (ApplyTT __uu__PartialApp
Lib.IntTypes.gt@tok))
:named @kick_partial_app_dd6fa8a5c121fe6429c409e3cd3115fa))

; </end encoding Lib.IntTypes.op_Greater_Dot>


; <Start encoding Lib.IntTypes.op_Greater_Equals_Dot>

(declare-fun Lib.IntTypes.op_Greater_Equals_Dot (Term) Term)


(declare-fun Lib.IntTypes.op_Greater_Equals_Dot@tok () Term)

;;;;;;;;;;;;;;;;kick_partial_app
;;; Fact-ids: Name Lib.IntTypes.op_Greater_Equals_Dot; Namespace Lib.IntTypes
(assert (! (Valid (ApplyTT __uu__PartialApp
Lib.IntTypes.gte@tok))
:named @kick_partial_app_4e04573fbf4f422d85bba1dcc685ea5c))

; </end encoding Lib.IntTypes.op_Greater_Equals_Dot>


; UNSAT CORE: @MaxFuel_assumption, @MaxIFuel_assumption, @fuel_correspondence_Prims.pow2.fuel_instrumented, @query, constructor_distinct_Lib.IntTypes.S16, constructor_distinct_Lib.IntTypes.S32, constructor_distinct_Lib.IntTypes.SEC, equality_tok_Lib.IntTypes.S16@tok, equality_tok_Lib.IntTypes.S32@tok, equality_tok_Lib.IntTypes.SEC@tok, equation_Lib.IntTypes.bits, equation_Lib.IntTypes.range, equation_Lib.IntTypes.signed, equation_Lib.IntTypes.unsigned, equation_Lib.IntTypes.v, equation_Prims.nat, equation_Prims.pos, equation_Spec.Kyber2.Params.params_q, int_inversion, int_typing, lemma_FStar.UInt.pow2_values, primitive_Prims.op_Addition, primitive_Prims.op_Division, primitive_Prims.op_LessThanOrEqual, primitive_Prims.op_Minus, primitive_Prims.op_Multiply, primitive_Prims.op_Subtraction, projection_inverse_BoxBool_proj_0, projection_inverse_BoxInt_proj_0, refinement_interpretation_Tm_refine_2b320913041b873fce938dd17eebb3e2, refinement_interpretation_Tm_refine_542f9d4f129664613f2483a6c88bc7c2, refinement_interpretation_Tm_refine_774ba3f728d91ead8ef40be66c9802e5, refinement_interpretation_Tm_refine_83845a86f2550cdf941eeb1d9b59602b, refinement_interpretation_Tm_refine_9d3fd79fd314167f1a9c213a188da3ec, refinement_interpretation_Tm_refine_b2401a8cabe2f9a01538f32548fa9f6c, typing_Lib.IntTypes.mk_int, typing_Prims.pow2, typing_tok_Lib.IntTypes.S32@tok, typing_tok_Lib.IntTypes.SEC@tok

;;; End module Lib.IntTypes (1394 decls; total size 79367)

;;; Start module Spec.Unsafe

; <Start encoding Spec.Unsafe.unsafe_int64_to_int16>

(declare-fun Spec.Unsafe.unsafe_int64_to_int16 (Term) Term)
(declare-fun Tm_refine_94dc30b33c02c88626a7c4fcb2880287 (Term) Term)
(declare-fun Tm_arrow_01955f0d4df8503d1866dd00f75b92e1 () Term)
(declare-fun Spec.Unsafe.unsafe_int64_to_int16@tok () Term)


; </end encoding Spec.Unsafe.unsafe_int64_to_int16>


; UNSAT CORE: @MaxFuel_assumption, @MaxIFuel_assumption, @fuel_correspondence_Prims.pow2.fuel_instrumented, @query, constructor_distinct_Lib.IntTypes.S16, constructor_distinct_Lib.IntTypes.S32, constructor_distinct_Lib.IntTypes.SEC, equality_tok_Lib.IntTypes.S16@tok, equality_tok_Lib.IntTypes.S32@tok, equality_tok_Lib.IntTypes.SEC@tok, equation_Lib.IntTypes.bits, equation_Lib.IntTypes.range, equation_Lib.IntTypes.signed, equation_Lib.IntTypes.unsigned, equation_Lib.IntTypes.v, equation_Prims.nat, equation_Prims.pos, equation_Spec.Kyber2.Params.params_q, int_inversion, int_typing, lemma_FStar.UInt.pow2_values, primitive_Prims.op_Addition, primitive_Prims.op_Division, primitive_Prims.op_LessThanOrEqual, primitive_Prims.op_Minus, primitive_Prims.op_Multiply, primitive_Prims.op_Subtraction, projection_inverse_BoxBool_proj_0, projection_inverse_BoxInt_proj_0, refinement_interpretation_Tm_refine_2b320913041b873fce938dd17eebb3e2, refinement_interpretation_Tm_refine_542f9d4f129664613f2483a6c88bc7c2, refinement_interpretation_Tm_refine_774ba3f728d91ead8ef40be66c9802e5, refinement_interpretation_Tm_refine_83845a86f2550cdf941eeb1d9b59602b, refinement_interpretation_Tm_refine_9d3fd79fd314167f1a9c213a188da3ec, refinement_interpretation_Tm_refine_b2401a8cabe2f9a01538f32548fa9f6c, typing_Lib.IntTypes.mk_int, typing_Prims.pow2, typing_tok_Lib.IntTypes.S32@tok, typing_tok_Lib.IntTypes.SEC@tok

;;; End module Spec.Unsafe (8 decls; total size 1763)

;;; Start module Kyber2.Params

; <Start encoding Kyber2.Params.params_n>

(declare-fun Kyber2.Params.params_n (Dummy_sort) Term)

; </end encoding Kyber2.Params.params_n>


; <Start encoding Kyber2.Params.params_halfninv>

(declare-fun Kyber2.Params.params_halfninv (Dummy_sort) Term)

; </end encoding Kyber2.Params.params_halfninv>


; <Start encoding Kyber2.Params.params_k>

(declare-fun Kyber2.Params.params_k (Dummy_sort) Term)

; </end encoding Kyber2.Params.params_k>


; <Start encoding Kyber2.Params.params_q>

(declare-fun Kyber2.Params.params_q (Dummy_sort) Term)

; </end encoding Kyber2.Params.params_q>


; <Start encoding Kyber2.Params.params_eta>

(declare-fun Kyber2.Params.params_eta (Dummy_sort) Term)

; </end encoding Kyber2.Params.params_eta>


; <Start encoding Kyber2.Params.params_du>

(declare-fun Kyber2.Params.params_du (Dummy_sort) Term)

; </end encoding Kyber2.Params.params_du>


; <Start encoding Kyber2.Params.params_dv>

(declare-fun Kyber2.Params.params_dv (Dummy_sort) Term)

; </end encoding Kyber2.Params.params_dv>


; <Start encoding Kyber2.Params.params_minus_log_delta>

(declare-fun Kyber2.Params.params_minus_log_delta (Dummy_sort) Term)

; </end encoding Kyber2.Params.params_minus_log_delta>


; <Start encoding Kyber2.Params.params_logr>

(declare-fun Kyber2.Params.params_logr (Dummy_sort) Term)

; </end encoding Kyber2.Params.params_logr>


; <Start encoding Kyber2.Params.params_qinv>

(declare-fun Kyber2.Params.params_qinv (Dummy_sort) Term)

; </end encoding Kyber2.Params.params_qinv>


; <Start encoding Kyber2.Params.params_zeta>

(declare-fun Kyber2.Params.params_zeta (Dummy_sort) Term)

; </end encoding Kyber2.Params.params_zeta>


; <Start encoding Kyber2.Params.params_zetainv>

(declare-fun Kyber2.Params.params_zetainv (Dummy_sort) Term)

; </end encoding Kyber2.Params.params_zetainv>


; <Start encoding Kyber2.Params.params_mont>

(declare-fun Kyber2.Params.params_mont (Dummy_sort) Term)

; </end encoding Kyber2.Params.params_mont>


; <Start encoding Kyber2.Params.params_mont2>

(declare-fun Kyber2.Params.params_mont2 (Dummy_sort) Term)

; </end encoding Kyber2.Params.params_mont2>


; <Start encoding Kyber2.Params.params_rinv>

(declare-fun Kyber2.Params.params_rinv (Dummy_sort) Term)

; </end encoding Kyber2.Params.params_rinv>


; UNSAT CORE: @MaxFuel_assumption, @MaxIFuel_assumption, @fuel_correspondence_Prims.pow2.fuel_instrumented, @query, constructor_distinct_Lib.IntTypes.S16, constructor_distinct_Lib.IntTypes.S32, constructor_distinct_Lib.IntTypes.SEC, equality_tok_Lib.IntTypes.S16@tok, equality_tok_Lib.IntTypes.S32@tok, equality_tok_Lib.IntTypes.SEC@tok, equation_Lib.IntTypes.bits, equation_Lib.IntTypes.range, equation_Lib.IntTypes.signed, equation_Lib.IntTypes.unsigned, equation_Lib.IntTypes.v, equation_Prims.nat, equation_Prims.pos, equation_Spec.Kyber2.Params.params_q, int_inversion, int_typing, lemma_FStar.UInt.pow2_values, primitive_Prims.op_Addition, primitive_Prims.op_Division, primitive_Prims.op_LessThanOrEqual, primitive_Prims.op_Minus, primitive_Prims.op_Multiply, primitive_Prims.op_Subtraction, projection_inverse_BoxBool_proj_0, projection_inverse_BoxInt_proj_0, refinement_interpretation_Tm_refine_2b320913041b873fce938dd17eebb3e2, refinement_interpretation_Tm_refine_542f9d4f129664613f2483a6c88bc7c2, refinement_interpretation_Tm_refine_774ba3f728d91ead8ef40be66c9802e5, refinement_interpretation_Tm_refine_83845a86f2550cdf941eeb1d9b59602b, refinement_interpretation_Tm_refine_9d3fd79fd314167f1a9c213a188da3ec, refinement_interpretation_Tm_refine_b2401a8cabe2f9a01538f32548fa9f6c, typing_Lib.IntTypes.mk_int, typing_Prims.pow2, typing_tok_Lib.IntTypes.S32@tok, typing_tok_Lib.IntTypes.SEC@tok

;;; End module Kyber2.Params (46 decls; total size 3680)

;;; Start module Spec.Kyber2.Params

; <Start encoding Spec.Kyber2.Params.v>

(declare-fun Spec.Kyber2.Params.v (Term) Term)


(declare-fun Spec.Kyber2.Params.v@tok () Term)


; </end encoding Spec.Kyber2.Params.v>


; <Start encoding Spec.Kyber2.Params.params_n>

(declare-fun Spec.Kyber2.Params.params_n (Dummy_sort) Term)

; </end encoding Spec.Kyber2.Params.params_n>


; <Start encoding Spec.Kyber2.Params.params_halfninv>

(declare-fun Spec.Kyber2.Params.params_halfninv (Dummy_sort) Term)

; </end encoding Spec.Kyber2.Params.params_halfninv>


; <Start encoding Spec.Kyber2.Params.params_k>

(declare-fun Spec.Kyber2.Params.params_k (Dummy_sort) Term)

; </end encoding Spec.Kyber2.Params.params_k>


; <Start encoding Spec.Kyber2.Params.params_q>

(declare-fun Spec.Kyber2.Params.params_q (Dummy_sort) Term)
;;;;;;;;;;;;;;;;Equation for Spec.Kyber2.Params.params_q
;;; Fact-ids: Name Spec.Kyber2.Params.params_q; Namespace Spec.Kyber2.Params
(assert (! 
;; def=Spec.Kyber2.Params.fst(14,11-14,19); use=Spec.Kyber2.Params.fst(14,11-14,19)
(forall ((@u0 Dummy_sort))
 (! (= 
;; def=Spec.Kyber2.Params.fst(14,11-14,19); use=Spec.Kyber2.Params.fst(14,11-14,19)
(Spec.Kyber2.Params.params_q @u0)

(BoxInt 3329))
 

:pattern (
;; def=Spec.Kyber2.Params.fst(14,11-14,19); use=Spec.Kyber2.Params.fst(14,11-14,19)
(Spec.Kyber2.Params.params_q @u0)
)
:qid equation_Spec.Kyber2.Params.params_q))

:named equation_Spec.Kyber2.Params.params_q))

; </end encoding Spec.Kyber2.Params.params_q>


; <Start encoding Spec.Kyber2.Params.params_eta>

(declare-fun Spec.Kyber2.Params.params_eta (Dummy_sort) Term)

; </end encoding Spec.Kyber2.Params.params_eta>


; <Start encoding Spec.Kyber2.Params.params_du>

(declare-fun Spec.Kyber2.Params.params_du (Dummy_sort) Term)

; </end encoding Spec.Kyber2.Params.params_du>


; <Start encoding Spec.Kyber2.Params.params_dv>

(declare-fun Spec.Kyber2.Params.params_dv (Dummy_sort) Term)

; </end encoding Spec.Kyber2.Params.params_dv>


; <Start encoding Spec.Kyber2.Params.params_minus_log_delta>

(declare-fun Spec.Kyber2.Params.params_minus_log_delta (Dummy_sort) Term)

; </end encoding Spec.Kyber2.Params.params_minus_log_delta>


; <Start encoding Spec.Kyber2.Params.params_logr>

(declare-fun Spec.Kyber2.Params.params_logr (Dummy_sort) Term)



; </end encoding Spec.Kyber2.Params.params_logr>


; <Start encoding Spec.Kyber2.Params.params_qinv>

(declare-fun Spec.Kyber2.Params.params_qinv (Dummy_sort) Term)

; </end encoding Spec.Kyber2.Params.params_qinv>


; <Start encoding Spec.Kyber2.Params.params_zeta>

(declare-fun Spec.Kyber2.Params.params_zeta (Dummy_sort) Term)

; </end encoding Spec.Kyber2.Params.params_zeta>


; <Start encoding Spec.Kyber2.Params.params_zetainv>

(declare-fun Spec.Kyber2.Params.params_zetainv (Dummy_sort) Term)

; </end encoding Spec.Kyber2.Params.params_zetainv>


; <Start encoding Spec.Kyber2.Params.params_mont>

(declare-fun Spec.Kyber2.Params.params_mont (Dummy_sort) Term)

; </end encoding Spec.Kyber2.Params.params_mont>


; <Start encoding Spec.Kyber2.Params.params_mont2>

(declare-fun Spec.Kyber2.Params.params_mont2 (Dummy_sort) Term)

; </end encoding Spec.Kyber2.Params.params_mont2>


; <Start encoding Spec.Kyber2.Params.params_rinv>

(declare-fun Spec.Kyber2.Params.params_rinv (Dummy_sort) Term)

; </end encoding Spec.Kyber2.Params.params_rinv>


; UNSAT CORE: @MaxFuel_assumption, @MaxIFuel_assumption, @fuel_correspondence_Prims.pow2.fuel_instrumented, @query, constructor_distinct_Lib.IntTypes.S16, constructor_distinct_Lib.IntTypes.S32, constructor_distinct_Lib.IntTypes.SEC, equality_tok_Lib.IntTypes.S16@tok, equality_tok_Lib.IntTypes.S32@tok, equality_tok_Lib.IntTypes.SEC@tok, equation_Lib.IntTypes.bits, equation_Lib.IntTypes.range, equation_Lib.IntTypes.signed, equation_Lib.IntTypes.unsigned, equation_Lib.IntTypes.v, equation_Prims.nat, equation_Prims.pos, equation_Spec.Kyber2.Params.params_q, int_inversion, int_typing, lemma_FStar.UInt.pow2_values, primitive_Prims.op_Addition, primitive_Prims.op_Division, primitive_Prims.op_LessThanOrEqual, primitive_Prims.op_Minus, primitive_Prims.op_Multiply, primitive_Prims.op_Subtraction, projection_inverse_BoxBool_proj_0, projection_inverse_BoxInt_proj_0, refinement_interpretation_Tm_refine_2b320913041b873fce938dd17eebb3e2, refinement_interpretation_Tm_refine_542f9d4f129664613f2483a6c88bc7c2, refinement_interpretation_Tm_refine_774ba3f728d91ead8ef40be66c9802e5, refinement_interpretation_Tm_refine_83845a86f2550cdf941eeb1d9b59602b, refinement_interpretation_Tm_refine_9d3fd79fd314167f1a9c213a188da3ec, refinement_interpretation_Tm_refine_b2401a8cabe2f9a01538f32548fa9f6c, typing_Lib.IntTypes.mk_int, typing_Prims.pow2, typing_tok_Lib.IntTypes.S32@tok, typing_tok_Lib.IntTypes.SEC@tok

;;; End module Spec.Kyber2.Params (56 decls; total size 4711)

; Internals for Spec.Kyber2.Reduce

(push)

; <Skipped />


; <Start encoding Spec.Kyber2.Reduce.lemma_div_le>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun Spec.Kyber2.Reduce.lemma_div_le (Term Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun Spec.Kyber2.Reduce.lemma_div_le@tok () Term)

; </end encoding Spec.Kyber2.Reduce.lemma_div_le>


; <Skipped Spec.Kyber2.Reduce.montgomery_reduce_int32/>


; <Start encoding Spec.Kyber2.Reduce.lemma_montgomery2>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun Spec.Kyber2.Reduce.lemma_montgomery2 (Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun Spec.Kyber2.Reduce.lemma_montgomery2@tok () Term)

; </end encoding Spec.Kyber2.Reduce.lemma_montgomery2>


; <Start encoding Spec.Kyber2.Reduce.montgomery_reduce_int32>

(declare-fun Spec.Kyber2.Reduce.montgomery_reduce_int32 (Term) Term)
(declare-fun Tm_refine_8887dbf77aff255e427aaf910878c487 (Term) Term)
(declare-fun Tm_arrow_05b4c09ca3033eaf82fc91def710d589 () Term)
(declare-fun Spec.Kyber2.Reduce.montgomery_reduce_int32@tok () Term)


; </end encoding Spec.Kyber2.Reduce.montgomery_reduce_int32>


; encoding sigelt 


; <Skipped />


; encoding sigelt barrett_reduce_int16


; <Skipped Spec.Kyber2.Reduce.barrett_reduce_int16/>


; encoding sigelt barrett_range_v


; <Start encoding Spec.Kyber2.Reduce.barrett_range_v>

;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun Spec.Kyber2.Reduce.barrett_range_v (Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun Spec.Kyber2.Reduce.barrett_range_v@tok () Term)

; </end encoding Spec.Kyber2.Reduce.barrett_range_v>


; Starting query at Spec.Kyber2.Reduce.fst(187,2-194,46)

(push)
(declare-fun label_244 () Bool)
(declare-fun label_243 () Bool)
(declare-fun label_242 () Bool)
(declare-fun label_241 () Bool)
(declare-fun label_240 () Bool)
(declare-fun label_239 () Bool)
(declare-fun label_238 () Bool)
(declare-fun label_237 () Bool)
(declare-fun label_236 () Bool)
(declare-fun label_235 () Bool)
(declare-fun label_234 () Bool)
(declare-fun label_233 () Bool)
(declare-fun label_232 () Bool)
(declare-fun label_231 () Bool)
(declare-fun label_230 () Bool)
(declare-fun label_229 () Bool)
(declare-fun label_228 () Bool)
(declare-fun label_227 () Bool)

(declare-fun Tm_refine_d4f40346fd210882fa1d130410be0df7 () Term)

(declare-fun Tm_refine_b051696d4fc171d15833b61798f0e7af () Term)











; Encoding query formula: forall (a: Lib.IntTypes.int_t (Lib.IntTypes.S16) (Lib.IntTypes.SEC)).
;   (forall (_: Prims.squash Prims.l_True).
;       (*could not prove post-condition*) Lib.IntTypes.signed (Lib.IntTypes.S16)) /\
;   (forall (p: Prims.pure_post Prims.unit).
;       (forall (pure_result: Prims.unit).
;           Lib.IntTypes.range ((Prims.pow2 26 / 3329 + 1) * Lib.IntTypes.v a) (Lib.IntTypes.S32) ==>
;           p pure_result) ==>
;       (forall (pure_result: Prims.unit).
;           Lib.IntTypes.range (Prims.pow2 26 / 3329 + 1) (Lib.IntTypes.S16) /\
;           Lib.IntTypes.range (Prims.pow2 26 / 3329 + 1) (Lib.IntTypes.S32) ==>
;           (forall (u36475: Lib.IntTypes.int_t (Lib.IntTypes.S32) (Lib.IntTypes.SEC)).
;               (*Subtyping check failed; expected type Lib.IntTypes.range_t (Lib.IntTypes.S32); got type Prims.int*)
;               Prims.auto_squash (Lib.IntTypes.range (Prims.pow2 26 / 3329 + 1) (Lib.IntTypes.S32))) /\
;           Prims.auto_squash (Lib.IntTypes.range (Prims.pow2 26 / 3329 + 1) (Lib.IntTypes.S32)) /\
;           (forall (return_val: x: Prims.int{Lib.IntTypes.range x (Lib.IntTypes.S32)}).
;               return_val == Prims.pow2 26 / 3329 + 1 ==>
;               (forall (any_result:
;                   u36479:
;                   Lib.IntTypes.int_t (Lib.IntTypes.S32) (Lib.IntTypes.SEC)
;                     {Lib.IntTypes.v u36479 == Prims.pow2 26 / 3329 + 1}).
;                   Lib.IntTypes.mk_int (Prims.pow2 26 / 3329 + 1) == any_result ==>
;                   (forall (return_val:
;                       u36481:
;                       Lib.IntTypes.int_t (Lib.IntTypes.S32) (Lib.IntTypes.SEC)
;                         {Lib.IntTypes.v u36481 == Prims.pow2 26 / 3329 + 1}).
;                       return_val == Lib.IntTypes.mk_int (Prims.pow2 26 / 3329 + 1) ==>
;                       Lib.IntTypes.mk_int (Prims.pow2 26 / 3329 + 1) == return_val ==>
;                       (forall (u36482: Lib.IntTypes.int_t (Lib.IntTypes.S32) (Lib.IntTypes.SEC)).
;                           (*Subtyping check failed; expected type Lib.IntTypes.range_t (Lib.IntTypes.S32); got type Prims.int*)
;                           Prims.auto_squash (Lib.IntTypes.range 3329 (Lib.IntTypes.S32))) /\
;                       Prims.auto_squash (Lib.IntTypes.range 3329 (Lib.IntTypes.S32)) /\
;                       (forall (return_val: Prims.int).
;                           return_val == 3329 ==>
;                           (forall (any_result:
;                               u36485:
;                               Lib.IntTypes.int_t (Lib.IntTypes.S32) (Lib.IntTypes.SEC)
;                                 {Lib.IntTypes.v u36485 == 3329}).
;                               Lib.IntTypes.mk_int 3329 == any_result ==>
;                               (forall (return_val:
;                                   u36487:
;                                   Lib.IntTypes.int_t (Lib.IntTypes.S32) (Lib.IntTypes.SEC)
;                                     {Lib.IntTypes.v u36487 == 3329}).
;                                   return_val == Lib.IntTypes.mk_int 3329 ==>
;                                   Lib.IntTypes.mk_int 3329 == return_val ==>
;                                   (forall (pure_result: Prims.unit).
;                                       Prims.pow2 15 * Prims.pow2 15 = Prims.pow2 30 ==>
;                                       (forall (pure_result: Prims.unit).
;                                           Prims.pow2 30 < Prims.pow2 31 ==>
;                                           Lib.IntTypes.signed (Lib.IntTypes.S32) /\
;                                           (forall (return_val: Lib.IntTypes.inttype).
;                                               return_val == Lib.IntTypes.S32 ==>
;                                               (forall (any_result:
;                                                   x:
;                                                   Prims.int{Lib.IntTypes.range x (Lib.IntTypes.S32)})
;                                                 .
;                                                   Lib.IntTypes.v (Lib.IntTypes.mk_int (Prims.pow2 26 /
;                                                           3329 +
;                                                           1)) ==
;                                                   any_result ==>
;                                                   Lib.IntTypes.range (Lib.IntTypes.v (Lib.IntTypes.mk_int 
;                                                             (Prims.pow2 26 / 3329 + 1)))
;                                                     (Lib.IntTypes.S32) ==>
;                                                   (Lib.IntTypes.v (Lib.IntTypes.mk_int (Prims.pow2 26
;                                                            /
;                                                           3329 +
;                                                           1)) >=
;                                                   0) /\
;                                                   (forall (return_val: Prims.nat).
;                                                       return_val ==
;                                                       Lib.IntTypes.v (Lib.IntTypes.mk_int (Prims.pow2 
;                                                                 26 /
;                                                               3329 +
;                                                               1)) ==>
;                                                       Lib.IntTypes.v (Lib.IntTypes.mk_int (Prims.pow2 
;                                                                 26 /
;                                                               3329 +
;                                                               1)) ==
;                                                       return_val ==>
;                                                       Lib.IntTypes.signed (Lib.IntTypes.S16) /\
;                                                       (forall (return_val: Lib.IntTypes.inttype).
;                                                           return_val == Lib.IntTypes.S16 ==>
;                                                           (forall (any_result:
;                                                               x:
;                                                               Prims.int
;                                                                 { Lib.IntTypes.range x
;                                                                     (Lib.IntTypes.S16) }).
;                                                               Lib.IntTypes.v a == any_result ==>
;                                                               (forall (return_val:
;                                                                   x:
;                                                                   Prims.int
;                                                                     { Lib.IntTypes.range x
;                                                                         (Lib.IntTypes.S16) }).
;                                                                   return_val == Lib.IntTypes.v a ==>
;                                                                   Lib.IntTypes.v a == return_val ==>
;                                                                   Lib.IntTypes.v a <= Prims.pow2 15 /\
;                                                                   (forall (pure_result: Prims.unit).
;                                                                       Lib.IntTypes.v (Lib.IntTypes.mk_int 
;                                                                             (Prims.pow2 26 / 3329 +
;                                                                               1)) *
;                                                                       Lib.IntTypes.v a <=
;                                                                       Lib.IntTypes.v (Lib.IntTypes.mk_int 
;                                                                             (Prims.pow2 26 / 3329 +
;                                                                               1)) *
;                                                                       Prims.pow2 15 ==>
;                                                                       Prims.pow2 15 > 0 ==>
;                                                                       (Prims.pow2 15 >= 0) /\
;                                                                       (forall (return_val:
;                                                                           Prims.nat).
;                                                                           return_val ==
;                                                                           Prims.pow2 15 ==>
;                                                                           Lib.IntTypes.signed (Lib.IntTypes.S32
;                                                                             ) /\
;                                                                           (forall (return_val:
;                                                                               Lib.IntTypes.inttype).
;                                                                               return_val ==
;                                                                               Lib.IntTypes.S32 ==>
;                                                                               (forall (any_result:
;                                                                                   x:
;                                                                                   Prims.int
;                                                                                     { Lib.IntTypes.range 
;                                                                                         x
;                                                                                         (Lib.IntTypes.S32
;                                                                                         ) }).
;                                                                                   Lib.IntTypes.v (Lib.IntTypes.mk_int 
;                                                                                         (Prims.pow2 26
;                                                                                            /
;                                                                                           3329 +
;                                                                                           1)) ==
;                                                                                   any_result ==>
;                                                                                   (forall (return_val:
;                                                                                       x:
;                                                                                       Prims.int
;                                                                                         { Lib.IntTypes.range 
;                                                                                             x
;                                                                                             (Lib.IntTypes.S32
;                                                                                             ) }).
;                                                                                       return_val ==
;                                                                                       Lib.IntTypes.v 
;                                                                                         (Lib.IntTypes.mk_int 
;                                                                                             (Prims.pow2 
;                                                                                                 26 /
;                                                                                               3329 +
;                                                                                               1)) ==>
;                                                                                       Lib.IntTypes.v 
;                                                                                         (Lib.IntTypes.mk_int 
;                                                                                             (Prims.pow2 
;                                                                                                 26 /
;                                                                                               3329 +
;                                                                                               1)) ==
;                                                                                       return_val ==>
;                                                                                       Lib.IntTypes.v 
;                                                                                         (Lib.IntTypes.mk_int 
;                                                                                             (Prims.pow2 
;                                                                                                 26 /
;                                                                                               3329 +
;                                                                                               1)) <=
;                                                                                       Prims.pow2 15 -
;                                                                                       1 /\
;                                                                                       (forall (pure_result:
;                                                                                           Prims.unit)
;                                                                                         .
;                                                                                           Lib.IntTypes.v 
;                                                                                             (Lib.IntTypes.mk_int 
;                                                                                                 (Prims.pow2 
;                                                                                                     26
;                                                                                                    /
;                                                                                                   3329 +
;                                                                                                   1)
;                                                                                             ) *
;                                                                                           Prims.pow2 
;                                                                                             15 <=
;                                                                                           (Prims.pow2 
;                                                                                               15 -
;                                                                                             1) *
;                                                                                           Prims.pow2 
;                                                                                             15 ==>
;                                                                                           Lib.IntTypes.signed 
;                                                                                             (Lib.IntTypes.S32
;                                                                                             ) /\
;                                                                                           (forall (return_val:
;                                                                                               Lib.IntTypes.inttype)
;                                                                                             .
;                                                                                               return_val ==
;                                                                                               Lib.IntTypes.S32 ==>
;                                                                                               (forall 
;                                                                                                   (any_result:
;                                                                                                   x:
;                                                                                                   Prims.int
;                                                                                                     {
;                                                                                                       Lib.IntTypes.range 
;                                                                                                         x
;                                                                                                         (
;                                                                                                           Lib.IntTypes.S32
;                                                                                                         )
;                                                                                                       
;                                                                                                     })
;                                                                                                 .
;                                                                                                   Lib.IntTypes.v 
;                                                                                                     (
;                                                                                                       Lib.IntTypes.mk_int 
;                                                                                                         (
;                                                                                                           Prims.pow2 
;                                                                                                             26
;                                                                                                            /
;                                                                                                           3329 +
;                                                                                                           1
;                                                                                                         )
;                                                                                                       
;                                                                                                     )
;                                                                                                    ==
;                                                                                                   any_result ==>
;                                                                                                   (forall 
;                                                                                                       (return_val:
;                                                                                                       x:
;                                                                                                       Prims.int
;                                                                                                         {
;                                                                                                           Lib.IntTypes.range 
;                                                                                                             x
;                                                                                                             (
;                                                                                                               Lib.IntTypes.S32
;                                                                                                             )
;                                                                                                           
;                                                                                                         })
;                                                                                                     .
;                                                                                                       return_val ==
;                                                                                                       Lib.IntTypes.v 
;                                                                                                         (
;                                                                                                           Lib.IntTypes.mk_int 
;                                                                                                             (
;                                                                                                               Prims.pow2 
;                                                                                                                 26
;                                                                                                                /
;                                                                                                               3329 +
;                                                                                                               1
;                                                                                                             )
;                                                                                                           
;                                                                                                         )
;                                                                                                        ==>
;                                                                                                       Lib.IntTypes.v 
;                                                                                                         (
;                                                                                                           Lib.IntTypes.mk_int 
;                                                                                                             (
;                                                                                                               Prims.pow2 
;                                                                                                                 26
;                                                                                                                /
;                                                                                                               3329 +
;                                                                                                               1
;                                                                                                             )
;                                                                                                           
;                                                                                                         )
;                                                                                                        ==
;                                                                                                       return_val ==>
;                                                                                                       Lib.IntTypes.signed 
;                                                                                                         (
;                                                                                                           Lib.IntTypes.S16
;                                                                                                         )
;                                                                                                        /\
;                                                                                                       (
;                                                                                                         forall 
;                                                                                                           (return_val:
;                                                                                                           Lib.IntTypes.inttype)
;                                                                                                         .
;                                                                                                           return_val ==
;                                                                                                           Lib.IntTypes.S16 ==>
;                                                                                                           (
;                                                                                                             forall 
;                                                                                                               (any_result:
;                                                                                                               x:
;                                                                                                               Prims.int
;                                                                                                                 {
;                                                                                                                   Lib.IntTypes.range 
;                                                                                                                     x
;                                                                                                                     (
;                                                                                                                       Lib.IntTypes.S16
;                                                                                                                     )
;                                                                                                                   
;                                                                                                                 })
;                                                                                                             .
;                                                                                                               Lib.IntTypes.v 
;                                                                                                                 a
;                                                                                                                ==
;                                                                                                               any_result ==>
;                                                                                                               (
;                                                                                                                 forall 
;                                                                                                                   (return_val:
;                                                                                                                   x:
;                                                                                                                   Prims.int
;                                                                                                                     {
;                                                                                                                       Lib.IntTypes.range 
;                                                                                                                         x
;                                                                                                                         (
;                                                                                                                           Lib.IntTypes.S16
;                                                                                                                         )
;                                                                                                                       
;                                                                                                                     })
;                                                                                                                 .
;                                                                                                                   return_val ==
;                                                                                                                   Lib.IntTypes.v 
;                                                                                                                     a
;                                                                                                                    ==>
;                                                                                                                   Lib.IntTypes.v 
;                                                                                                                     a
;                                                                                                                    ==
;                                                                                                                   return_val ==>
;                                                                                                                   (
;                                                                                                                     forall 
;                                                                                                                       (any_result:
;                                                                                                                       Prims.int)
;                                                                                                                     .
;                                                                                                                       Lib.IntTypes.v 
;                                                                                                                         (
;                                                                                                                           Lib.IntTypes.mk_int 
;                                                                                                                             (
;                                                                                                                               Prims.pow2 
;                                                                                                                                 26
;                                                                                                                                /
;                                                                                                                               3329 +
;                                                                                                                               1
;                                                                                                                             )
;                                                                                                                           
;                                                                                                                         )
;                                                                                                                        *
;                                                                                                                       Lib.IntTypes.v 
;                                                                                                                         a
;                                                                                                                        ==
;                                                                                                                       any_result ==>
;                                                                                                                       (
;                                                                                                                         forall 
;                                                                                                                           (any_result:
;                                                                                                                           Type0)
;                                                                                                                         .
;                                                                                                                           Lib.IntTypes.range 
;                                                                                                                             (
;                                                                                                                               Lib.IntTypes.v 
;                                                                                                                                 (
;                                                                                                                                   Lib.IntTypes.mk_int 
;                                                                                                                                     (
;                                                                                                                                       Prims.pow2 
;                                                                                                                                         26
;                                                                                                                                        /
;                                                                                                                                       3329 +
;                                                                                                                                       1
;                                                                                                                                     )
;                                                                                                                                   
;                                                                                                                                 )
;                                                                                                                                *
;                                                                                                                               Lib.IntTypes.v 
;                                                                                                                                 a
;                                                                                                                               
;                                                                                                                             )
;                                                                                                                             (
;                                                                                                                               Lib.IntTypes.S32
;                                                                                                                             )
;                                                                                                                            ==
;                                                                                                                           any_result ==>
;                                                                                                                           x:
;                                                                                                                           Prims.unit
;                                                                                                                             {
;                                                                                                                               Prims.c_and 
;                                                                                                                                 (
;                                                                                                                                   x:
;                                                                                                                                   Prims.unit
;                                                                                                                                     {
;                                                                                                                                       Prims.equals 
;                                                                                                                                         (
;                                                                                                                                           -2147483648 <=
;                                                                                                                                           Lib.IntTypes.sec_int_v 
;                                                                                                                                             (
;                                                                                                                                               Lib.IntTypes.mk_int 
;                                                                                                                                                 20159
;                                                                                                                                               
;                                                                                                                                             )
;                                                                                                                                            *
;                                                                                                                                           Lib.IntTypes.sec_int_v 
;                                                                                                                                             a
;                                                                                                                                           
;                                                                                                                                         )
;                                                                                                                                         true
;                                                                                                                                       
;                                                                                                                                     }
;                                                                                                                                 )
;                                                                                                                                 (
;                                                                                                                                   x:
;                                                                                                                                   Prims.unit
;                                                                                                                                     {
;                                                                                                                                       Prims.equals 
;                                                                                                                                         (
;                                                                                                                                           Lib.IntTypes.sec_int_v 
;                                                                                                                                             (
;                                                                                                                                               Lib.IntTypes.mk_int 
;                                                                                                                                                 20159
;                                                                                                                                               
;                                                                                                                                             )
;                                                                                                                                            *
;                                                                                                                                           Lib.IntTypes.sec_int_v 
;                                                                                                                                             a
;                                                                                                                                            <=
;                                                                                                                                           2147483647
;                                                                                                                                         )
;                                                                                                                                         true
;                                                                                                                                       
;                                                                                                                                     }
;                                                                                                                                 )
;                                                                                                                               
;                                                                                                                             } /\
;                                                                                                                           (
;                                                                                                                             forall 
;                                                                                                                               (pure_result:
;                                                                                                                               Prims.unit)
;                                                                                                                             .
;                                                                                                                               Lib.IntTypes.range 
;                                                                                                                                 (
;                                                                                                                                   Lib.IntTypes.v 
;                                                                                                                                     (
;                                                                                                                                       Lib.IntTypes.mk_int 
;                                                                                                                                         (
;                                                                                                                                           Prims.pow2 
;                                                                                                                                             26
;                                                                                                                                            /
;                                                                                                                                           3329 +
;                                                                                                                                           1
;                                                                                                                                         )
;                                                                                                                                       
;                                                                                                                                     )
;                                                                                                                                    *
;                                                                                                                                   Lib.IntTypes.v 
;                                                                                                                                     a
;                                                                                                                                   
;                                                                                                                                 )
;                                                                                                                                 (
;                                                                                                                                   Lib.IntTypes.S32
;                                                                                                                                 )
;                                                                                                                                ==>
;                                                                                                                               p 
;                                                                                                                                 pure_result
;                                                                                                                               
;                                                                                                                           )
;                                                                                                                       )
;                                                                                                                   )
;                                                                                                               )
;                                                                                                           )
;                                                                                                       )
;                                                                                                   ))
;                                                                                           ))))))))))
;                                                   )))))))))))))

(push)

; <fuel='0' ifuel='0'>

;;; Fact-ids: 
(assert (! (= MaxFuel
ZFuel)
:named @MaxFuel_assumption))
;;; Fact-ids: 
(assert (! (= MaxIFuel
ZFuel)
:named @MaxIFuel_assumption))
;;;;;;;;;;;;;;;;query
;;; Fact-ids: 
(assert (! (not (forall ((@x0 Term))
 (! (implies (HasType @x0
(Lib.IntTypes.int_t Lib.IntTypes.S16@tok
Lib.IntTypes.SEC@tok))

;; def=prims.fst(202,5-202,44); use=prims.fst(226,22-226,35)
(and 
;; def=<dummy>(0,0-0,0); use=Spec.Kyber2.Reduce.fst(187,2-194,46)
(forall ((@x1 Term))
 (! (implies (HasType @x1
(Prims.squash Prims.l_True))

;; def=/home/caerbannog/dev/hacl-star/lib/Lib.IntTypes.fsti(145,22-145,30); use=Spec.Kyber2.Reduce.fst(186,103-186,104)
(or label_227

;; def=/home/caerbannog/dev/hacl-star/lib/Lib.IntTypes.fsti(145,22-145,30); use=Spec.Kyber2.Reduce.fst(187,2-194,46)
(BoxBool_proj_0 (Lib.IntTypes.signed Lib.IntTypes.S16@tok))
)
)
 
;;no pats
:qid @query.1))


;; def=prims.fst(202,5-202,44); use=prims.fst(226,22-226,35)
(forall ((@x1 Term))
 (! (implies (and (HasType @x1
(Prims.pure_post Prims.unit))

;; def=prims.fst(237,46-237,106); use=Spec.Kyber2.Reduce.fst(187,2-194,46)
(forall ((@x2 Term))
 (! (implies (and (or label_228
(HasType @x2
Prims.unit))

;; def=Spec.Kyber2.Reduce.fst(186,63-186,110); use=Spec.Kyber2.Reduce.fst(187,2-194,46)
(or label_229

;; def=Spec.Kyber2.Reduce.fst(186,63-186,110); use=Spec.Kyber2.Reduce.fst(187,2-194,46)
(Valid 
;; def=Spec.Kyber2.Reduce.fst(186,63-186,110); use=Spec.Kyber2.Reduce.fst(187,2-194,46)
(Lib.IntTypes.range (Prims.op_Multiply (Prims.op_Addition (Prims.op_Division (Prims.pow2 (BoxInt 26))
(BoxInt 3329))
(BoxInt 1))
(Lib.IntTypes.v Lib.IntTypes.S16@tok
Lib.IntTypes.SEC@tok
@x0))
Lib.IntTypes.S32@tok)
)
)
)

;; def=prims.fst(237,92-237,105); use=Spec.Kyber2.Reduce.fst(187,2-194,46)
(Valid 
;; def=prims.fst(237,92-237,105); use=Spec.Kyber2.Reduce.fst(187,2-194,46)
(ApplyTT @x1
@x2)
)
)
 

:pattern (
;; def=prims.fst(237,92-237,105); use=Spec.Kyber2.Reduce.fst(187,2-194,46)
(Valid 
;; def=prims.fst(237,92-237,105); use=Spec.Kyber2.Reduce.fst(187,2-194,46)
(ApplyTT @x1
@x2)
)
)
:qid @query.3))
)

;; def=prims.fst(237,46-237,106); use=Spec.Kyber2.Reduce.fst(187,2-187,17)
(forall ((@x2 Term))
 (! (implies (and (HasType @x2
Prims.unit)

;; def=Spec.Kyber2.Reduce.fst(182,57-182,91); use=Spec.Kyber2.Reduce.fst(187,2-187,17)
(Valid 
;; def=Spec.Kyber2.Reduce.fst(182,57-182,91); use=Spec.Kyber2.Reduce.fst(187,2-187,17)
(Lib.IntTypes.range (Prims.op_Addition (Prims.op_Division (Prims.pow2 (BoxInt 26))
(BoxInt 3329))
(BoxInt 1))
Lib.IntTypes.S16@tok)
)


;; def=Spec.Kyber2.Reduce.fst(182,95-182,129); use=Spec.Kyber2.Reduce.fst(187,2-187,17)
(Valid 
;; def=Spec.Kyber2.Reduce.fst(182,95-182,129); use=Spec.Kyber2.Reduce.fst(187,2-187,17)
(Lib.IntTypes.range (Prims.op_Addition (Prims.op_Division (Prims.pow2 (BoxInt 26))
(BoxInt 3329))
(BoxInt 1))
Lib.IntTypes.S32@tok)
)
)

;; def=prims.fst(208,69-208,78); use=Spec.Kyber2.Reduce.fst(187,2-194,46)
(and 
;; def=<dummy>(0,0-0,0); use=Spec.Kyber2.Reduce.fst(188,2-194,46)
(forall ((@x3 Term))
 (! (implies (HasType @x3
(Lib.IntTypes.int_t Lib.IntTypes.S32@tok
Lib.IntTypes.SEC@tok))

;; def=/home/caerbannog/dev/hacl-star/lib/Lib.IntTypes.fsti(79,33-79,42); use=Spec.Kyber2.Reduce.fst(188,10-188,13)
(or label_230

;; def=/home/caerbannog/dev/hacl-star/lib/Lib.IntTypes.fsti(79,33-79,42); use=Spec.Kyber2.Reduce.fst(188,10-188,13)
(Valid 
;; def=/home/caerbannog/dev/hacl-star/lib/Lib.IntTypes.fsti(79,33-79,42); use=Spec.Kyber2.Reduce.fst(188,10-188,13)
(Lib.IntTypes.range (Prims.op_Addition (Prims.op_Division (Prims.pow2 (BoxInt 26))
(BoxInt 3329))
(BoxInt 1))
Lib.IntTypes.S32@tok)
)
)
)
 
;;no pats
:qid @query.5))


;; def=/home/caerbannog/dev/hacl-star/lib/Lib.IntTypes.fsti(79,33-79,42); use=Spec.Kyber2.Reduce.fst(188,14-188,38)
(or label_231

;; def=/home/caerbannog/dev/hacl-star/lib/Lib.IntTypes.fsti(79,33-79,42); use=Spec.Kyber2.Reduce.fst(188,14-188,38)
(Valid 
;; def=/home/caerbannog/dev/hacl-star/lib/Lib.IntTypes.fsti(79,33-79,42); use=Spec.Kyber2.Reduce.fst(188,14-188,38)
(Lib.IntTypes.range (Prims.op_Addition (Prims.op_Division (Prims.pow2 (BoxInt 26))
(BoxInt 3329))
(BoxInt 1))
Lib.IntTypes.S32@tok)
)
)


;; def=prims.fst(182,5-182,58); use=Spec.Kyber2.Reduce.fst(187,2-194,46)
(forall ((@x3 Term))
 (! (implies (and (HasType @x3
Tm_refine_ee21347fbca1d214410772ef0425736c)

;; def=prims.fst(182,28-182,41); use=Spec.Kyber2.Reduce.fst(187,2-194,46)
(= @x3
(Prims.op_Addition (Prims.op_Division (Prims.pow2 (BoxInt 26))
(BoxInt 3329))
(BoxInt 1)))
)

;; def=prims.fst(214,45-214,80); use=Spec.Kyber2.Reduce.fst(187,2-194,46)
(forall ((@x4 Term))
 (! (implies (and (HasType @x4
Tm_refine_d4f40346fd210882fa1d130410be0df7)

;; def=/home/caerbannog/dev/hacl-star/lib/Lib.IntTypes.fsti(268,26-268,43); use=Spec.Kyber2.Reduce.fst(188,10-188,38)
(= (Lib.IntTypes.mk_int Lib.IntTypes.S32@tok
Lib.IntTypes.SEC@tok
(Prims.op_Addition (Prims.op_Division (Prims.pow2 (BoxInt 26))
(BoxInt 3329))
(BoxInt 1)))
@x4)
)

;; def=prims.fst(182,5-182,58); use=Spec.Kyber2.Reduce.fst(187,2-194,46)
(forall ((@x5 Term))
 (! (implies (and (HasType @x5
Tm_refine_d4f40346fd210882fa1d130410be0df7)

;; def=prims.fst(182,28-182,41); use=Spec.Kyber2.Reduce.fst(187,2-194,46)
(= @x5
(Lib.IntTypes.mk_int Lib.IntTypes.S32@tok
Lib.IntTypes.SEC@tok
(Prims.op_Addition (Prims.op_Division (Prims.pow2 (BoxInt 26))
(BoxInt 3329))
(BoxInt 1))))


;; def=Spec.Kyber2.Reduce.fst(188,6-188,38); use=Spec.Kyber2.Reduce.fst(188,6-188,38)
(= (Lib.IntTypes.mk_int Lib.IntTypes.S32@tok
Lib.IntTypes.SEC@tok
(Prims.op_Addition (Prims.op_Division (Prims.pow2 (BoxInt 26))
(BoxInt 3329))
(BoxInt 1)))
@x5)
)

;; def=prims.fst(208,69-208,78); use=Spec.Kyber2.Reduce.fst(187,2-194,46)
(and 
;; def=<dummy>(0,0-0,0); use=Spec.Kyber2.Reduce.fst(189,2-194,46)
(forall ((@x6 Term))
 (! (implies (HasType @x6
(Lib.IntTypes.int_t Lib.IntTypes.S32@tok
Lib.IntTypes.SEC@tok))

;; def=/home/caerbannog/dev/hacl-star/lib/Lib.IntTypes.fsti(79,33-79,42); use=Spec.Kyber2.Reduce.fst(189,10-189,13)
(or label_232

;; def=/home/caerbannog/dev/hacl-star/lib/Lib.IntTypes.fsti(79,33-79,42); use=Spec.Kyber2.Reduce.fst(189,10-189,13)
(Valid 
;; def=/home/caerbannog/dev/hacl-star/lib/Lib.IntTypes.fsti(79,33-79,42); use=Spec.Kyber2.Reduce.fst(189,10-189,13)
(Lib.IntTypes.range (BoxInt 3329)
Lib.IntTypes.S32@tok)
)
)
)
 
;;no pats
:qid @query.9))


;; def=/home/caerbannog/dev/hacl-star/lib/Lib.IntTypes.fsti(79,33-79,42); use=Spec.Kyber2.Reduce.fst(189,14-189,22)
(or label_233

;; def=/home/caerbannog/dev/hacl-star/lib/Lib.IntTypes.fsti(79,33-79,42); use=Spec.Kyber2.Reduce.fst(189,14-189,22)
(Valid 
;; def=/home/caerbannog/dev/hacl-star/lib/Lib.IntTypes.fsti(79,33-79,42); use=Spec.Kyber2.Reduce.fst(189,14-189,22)
(Lib.IntTypes.range (BoxInt 3329)
Lib.IntTypes.S32@tok)
)
)


;; def=prims.fst(182,5-182,58); use=Spec.Kyber2.Reduce.fst(187,2-194,46)
(forall ((@x6 Term))
 (! (implies (and (HasType @x6
Prims.int)

;; def=prims.fst(182,28-182,41); use=Spec.Kyber2.Reduce.fst(187,2-194,46)
(= @x6
(BoxInt 3329))
)

;; def=prims.fst(214,45-214,80); use=Spec.Kyber2.Reduce.fst(187,2-194,46)
(forall ((@x7 Term))
 (! (implies (and (HasType @x7
Tm_refine_b051696d4fc171d15833b61798f0e7af)

;; def=/home/caerbannog/dev/hacl-star/lib/Lib.IntTypes.fsti(268,26-268,43); use=Spec.Kyber2.Reduce.fst(189,10-189,22)
(= (Lib.IntTypes.mk_int Lib.IntTypes.S32@tok
Lib.IntTypes.SEC@tok
(BoxInt 3329))
@x7)
)

;; def=prims.fst(182,5-182,58); use=Spec.Kyber2.Reduce.fst(187,2-194,46)
(forall ((@x8 Term))
 (! (implies (and (HasType @x8
Tm_refine_b051696d4fc171d15833b61798f0e7af)

;; def=prims.fst(182,28-182,41); use=Spec.Kyber2.Reduce.fst(187,2-194,46)
(= @x8
(Lib.IntTypes.mk_int Lib.IntTypes.S32@tok
Lib.IntTypes.SEC@tok
(BoxInt 3329)))


;; def=Spec.Kyber2.Reduce.fst(189,6-189,22); use=Spec.Kyber2.Reduce.fst(189,6-189,22)
(= (Lib.IntTypes.mk_int Lib.IntTypes.S32@tok
Lib.IntTypes.SEC@tok
(BoxInt 3329))
@x8)
)

;; def=prims.fst(237,46-237,106); use=Spec.Kyber2.Reduce.fst(190,2-190,11)
(forall ((@x9 Term))
 (! (implies (and (HasType @x9
Prims.unit)

;; def=FStar.Math.Lemmas.fst(182,11-182,43); use=Spec.Kyber2.Reduce.fst(190,2-190,11)
(= (Prims.op_Multiply (Prims.pow2 (BoxInt 15))
(Prims.pow2 (BoxInt 15)))
(Prims.pow2 (BoxInt 30)))
)

;; def=prims.fst(237,46-237,106); use=Spec.Kyber2.Reduce.fst(191,2-191,16)
(forall ((@x10 Term))
 (! (implies (and (HasType @x10
Prims.unit)

;; def=FStar.Math.Lemmas.fst(165,12-165,29); use=Spec.Kyber2.Reduce.fst(191,2-191,16)
(< (BoxInt_proj_0 (Prims.pow2 (BoxInt 30)))
(BoxInt_proj_0 (Prims.pow2 (BoxInt 31))))
)

;; def=prims.fst(208,69-208,78); use=Spec.Kyber2.Reduce.fst(187,2-194,46)
(and 
;; def=/home/caerbannog/dev/hacl-star/lib/Lib.IntTypes.fsti(145,22-145,30); use=Spec.Kyber2.Reduce.fst(192,29-192,30)
(or label_234

;; def=/home/caerbannog/dev/hacl-star/lib/Lib.IntTypes.fsti(145,22-145,30); use=Spec.Kyber2.Reduce.fst(192,29-192,30)
(BoxBool_proj_0 (Lib.IntTypes.signed Lib.IntTypes.S32@tok))
)


;; def=prims.fst(182,5-182,58); use=Spec.Kyber2.Reduce.fst(187,2-194,46)
(forall ((@x11 Term))
 (! (implies (and (HasType @x11
Lib.IntTypes.inttype)

;; def=prims.fst(182,28-182,41); use=Spec.Kyber2.Reduce.fst(187,2-194,46)
(= @x11
Lib.IntTypes.S32@tok)
)

;; def=prims.fst(214,45-214,80); use=Spec.Kyber2.Reduce.fst(187,2-194,46)
(forall ((@x12 Term))
 (! (implies (and (HasType @x12
Tm_refine_ee21347fbca1d214410772ef0425736c)

;; def=FStar.Math.Lemmas.fst(33,26-33,29); use=Spec.Kyber2.Reduce.fst(192,2-192,31)
(= (Lib.IntTypes.v Lib.IntTypes.S32@tok
Lib.IntTypes.SEC@tok
(Lib.IntTypes.mk_int Lib.IntTypes.S32@tok
Lib.IntTypes.SEC@tok
(Prims.op_Addition (Prims.op_Division (Prims.pow2 (BoxInt 26))
(BoxInt 3329))
(BoxInt 1))))
@x12)
)

;; def=prims.fst(208,69-208,78); use=Spec.Kyber2.Reduce.fst(187,2-194,46)
(and (implies 
;; def=/home/caerbannog/dev/hacl-star/lib/Lib.IntTypes.fsti(79,33-79,42); use=Spec.Kyber2.Reduce.fst(192,22-192,28)
(Valid 
;; def=/home/caerbannog/dev/hacl-star/lib/Lib.IntTypes.fsti(79,33-79,42); use=Spec.Kyber2.Reduce.fst(192,22-192,28)
(Lib.IntTypes.range (Lib.IntTypes.v Lib.IntTypes.S32@tok
Lib.IntTypes.SEC@tok
(Lib.IntTypes.mk_int Lib.IntTypes.S32@tok
Lib.IntTypes.SEC@tok
(Prims.op_Addition (Prims.op_Division (Prims.pow2 (BoxInt 26))
(BoxInt 3329))
(BoxInt 1))))
Lib.IntTypes.S32@tok)
)


;; def=prims.fst(441,17-441,23); use=Spec.Kyber2.Reduce.fst(192,21-192,31)
(or label_235

;; def=prims.fst(441,17-441,23); use=Spec.Kyber2.Reduce.fst(192,21-192,31)
(>= (BoxInt_proj_0 (Lib.IntTypes.v Lib.IntTypes.S32@tok
Lib.IntTypes.SEC@tok
(Lib.IntTypes.mk_int Lib.IntTypes.S32@tok
Lib.IntTypes.SEC@tok
(Prims.op_Addition (Prims.op_Division (Prims.pow2 (BoxInt 26))
(BoxInt 3329))
(BoxInt 1)))))
(BoxInt_proj_0 (BoxInt 0)))
)
)

;; def=prims.fst(182,5-182,58); use=Spec.Kyber2.Reduce.fst(187,2-194,46)
(forall ((@x13 Term))
 (! (implies (and (HasType @x13
Prims.nat)

;; def=prims.fst(182,28-182,41); use=Spec.Kyber2.Reduce.fst(187,2-194,46)
(= @x13
(Lib.IntTypes.v Lib.IntTypes.S32@tok
Lib.IntTypes.SEC@tok
(Lib.IntTypes.mk_int Lib.IntTypes.S32@tok
Lib.IntTypes.SEC@tok
(Prims.op_Addition (Prims.op_Division (Prims.pow2 (BoxInt 26))
(BoxInt 3329))
(BoxInt 1)))))


;; def=FStar.Math.Lemmas.fst(33,24-33,25); use=Spec.Kyber2.Reduce.fst(187,2-194,46)
(= (Lib.IntTypes.v Lib.IntTypes.S32@tok
Lib.IntTypes.SEC@tok
(Lib.IntTypes.mk_int Lib.IntTypes.S32@tok
Lib.IntTypes.SEC@tok
(Prims.op_Addition (Prims.op_Division (Prims.pow2 (BoxInt 26))
(BoxInt 3329))
(BoxInt 1))))
@x13)
)

;; def=prims.fst(208,69-208,78); use=Spec.Kyber2.Reduce.fst(187,2-194,46)
(and 
;; def=/home/caerbannog/dev/hacl-star/lib/Lib.IntTypes.fsti(145,22-145,30); use=Spec.Kyber2.Reduce.fst(192,40-192,41)
(or label_236

;; def=/home/caerbannog/dev/hacl-star/lib/Lib.IntTypes.fsti(145,22-145,30); use=Spec.Kyber2.Reduce.fst(192,40-192,41)
(BoxBool_proj_0 (Lib.IntTypes.signed Lib.IntTypes.S16@tok))
)


;; def=prims.fst(182,5-182,58); use=Spec.Kyber2.Reduce.fst(187,2-194,46)
(forall ((@x14 Term))
 (! (implies (and (HasType @x14
Lib.IntTypes.inttype)

;; def=prims.fst(182,28-182,41); use=Spec.Kyber2.Reduce.fst(187,2-194,46)
(= @x14
Lib.IntTypes.S16@tok)
)

;; def=prims.fst(214,45-214,80); use=Spec.Kyber2.Reduce.fst(187,2-194,46)
(forall ((@x15 Term))
 (! (implies (and (HasType @x15
Tm_refine_b2401a8cabe2f9a01538f32548fa9f6c)

;; def=/home/caerbannog/dev/hacl-star/lib/Lib.IntTypes.fsti(79,27-79,43); use=Spec.Kyber2.Reduce.fst(192,32-192,42)
(= (Lib.IntTypes.v Lib.IntTypes.S16@tok
Lib.IntTypes.SEC@tok
@x0)
@x15)
)

;; def=prims.fst(182,5-182,58); use=Spec.Kyber2.Reduce.fst(187,2-194,46)
(forall ((@x16 Term))
 (! (implies (and (HasType @x16
Tm_refine_b2401a8cabe2f9a01538f32548fa9f6c)

;; def=prims.fst(182,28-182,41); use=Spec.Kyber2.Reduce.fst(187,2-194,46)
(= @x16
(Lib.IntTypes.v Lib.IntTypes.S16@tok
Lib.IntTypes.SEC@tok
@x0))


;; def=FStar.Math.Lemmas.fst(33,33-33,34); use=Spec.Kyber2.Reduce.fst(187,2-194,46)
(= (Lib.IntTypes.v Lib.IntTypes.S16@tok
Lib.IntTypes.SEC@tok
@x0)
@x16)
)

;; def=prims.fst(237,39-237,106); use=Spec.Kyber2.Reduce.fst(192,2-192,20)
(and 
;; def=FStar.Math.Lemmas.fst(34,12-34,20); use=Spec.Kyber2.Reduce.fst(192,2-192,20)
(or label_237

;; def=FStar.Math.Lemmas.fst(34,12-34,20); use=Spec.Kyber2.Reduce.fst(192,2-192,20)
(<= (BoxInt_proj_0 (Lib.IntTypes.v Lib.IntTypes.S16@tok
Lib.IntTypes.SEC@tok
@x0))
(BoxInt_proj_0 (Prims.pow2 (BoxInt 15))))
)


;; def=prims.fst(237,46-237,106); use=Spec.Kyber2.Reduce.fst(192,2-192,20)
(forall ((@x17 Term))
 (! (implies (and (HasType @x17
Prims.unit)

;; def=FStar.Math.Lemmas.fst(35,12-35,28); use=Spec.Kyber2.Reduce.fst(192,2-192,20)
(<= (BoxInt_proj_0 (Prims.op_Multiply (Lib.IntTypes.v Lib.IntTypes.S32@tok
Lib.IntTypes.SEC@tok
(Lib.IntTypes.mk_int Lib.IntTypes.S32@tok
Lib.IntTypes.SEC@tok
(Prims.op_Addition (Prims.op_Division (Prims.pow2 (BoxInt 26))
(BoxInt 3329))
(BoxInt 1))))
(Lib.IntTypes.v Lib.IntTypes.S16@tok
Lib.IntTypes.SEC@tok
@x0)))
(BoxInt_proj_0 (Prims.op_Multiply (Lib.IntTypes.v Lib.IntTypes.S32@tok
Lib.IntTypes.SEC@tok
(Lib.IntTypes.mk_int Lib.IntTypes.S32@tok
Lib.IntTypes.SEC@tok
(Prims.op_Addition (Prims.op_Division (Prims.pow2 (BoxInt 26))
(BoxInt 3329))
(BoxInt 1))))
(Prims.pow2 (BoxInt 15)))))
)

;; def=prims.fst(208,69-208,78); use=Spec.Kyber2.Reduce.fst(187,2-194,46)
(and (implies 
;; def=prims.fst(442,17-442,22); use=Spec.Kyber2.Reduce.fst(193,22-193,31)
(> (BoxInt_proj_0 (Prims.pow2 (BoxInt 15)))
(BoxInt_proj_0 (BoxInt 0)))


;; def=prims.fst(441,17-441,23); use=Spec.Kyber2.Reduce.fst(193,22-193,31)
(or label_238

;; def=prims.fst(441,17-441,23); use=Spec.Kyber2.Reduce.fst(193,22-193,31)
(>= (BoxInt_proj_0 (Prims.pow2 (BoxInt 15)))
(BoxInt_proj_0 (BoxInt 0)))
)
)

;; def=prims.fst(182,5-182,58); use=Spec.Kyber2.Reduce.fst(187,2-194,46)
(forall ((@x18 Term))
 (! (implies (and (HasType @x18
Prims.nat)

;; def=prims.fst(182,28-182,41); use=Spec.Kyber2.Reduce.fst(187,2-194,46)
(= @x18
(Prims.pow2 (BoxInt 15)))
)

;; def=prims.fst(208,69-208,78); use=Spec.Kyber2.Reduce.fst(187,2-194,46)
(and 
;; def=/home/caerbannog/dev/hacl-star/lib/Lib.IntTypes.fsti(145,22-145,30); use=Spec.Kyber2.Reduce.fst(193,40-193,41)
(or label_239

;; def=/home/caerbannog/dev/hacl-star/lib/Lib.IntTypes.fsti(145,22-145,30); use=Spec.Kyber2.Reduce.fst(193,40-193,41)
(BoxBool_proj_0 (Lib.IntTypes.signed Lib.IntTypes.S32@tok))
)


;; def=prims.fst(182,5-182,58); use=Spec.Kyber2.Reduce.fst(187,2-194,46)
(forall ((@x19 Term))
 (! (implies (and (HasType @x19
Lib.IntTypes.inttype)

;; def=prims.fst(182,28-182,41); use=Spec.Kyber2.Reduce.fst(187,2-194,46)
(= @x19
Lib.IntTypes.S32@tok)
)

;; def=prims.fst(214,45-214,80); use=Spec.Kyber2.Reduce.fst(187,2-194,46)
(forall ((@x20 Term))
 (! (implies (and (HasType @x20
Tm_refine_ee21347fbca1d214410772ef0425736c)

;; def=/home/caerbannog/dev/hacl-star/lib/Lib.IntTypes.fsti(79,27-79,43); use=Spec.Kyber2.Reduce.fst(193,32-193,42)
(= (Lib.IntTypes.v Lib.IntTypes.S32@tok
Lib.IntTypes.SEC@tok
(Lib.IntTypes.mk_int Lib.IntTypes.S32@tok
Lib.IntTypes.SEC@tok
(Prims.op_Addition (Prims.op_Division (Prims.pow2 (BoxInt 26))
(BoxInt 3329))
(BoxInt 1))))
@x20)
)

;; def=prims.fst(182,5-182,58); use=Spec.Kyber2.Reduce.fst(187,2-194,46)
(forall ((@x21 Term))
 (! (implies (and (HasType @x21
Tm_refine_ee21347fbca1d214410772ef0425736c)

;; def=prims.fst(182,28-182,41); use=Spec.Kyber2.Reduce.fst(187,2-194,46)
(= @x21
(Lib.IntTypes.v Lib.IntTypes.S32@tok
Lib.IntTypes.SEC@tok
(Lib.IntTypes.mk_int Lib.IntTypes.S32@tok
Lib.IntTypes.SEC@tok
(Prims.op_Addition (Prims.op_Division (Prims.pow2 (BoxInt 26))
(BoxInt 3329))
(BoxInt 1)))))


;; def=FStar.Math.Lemmas.fst(38,34-38,35); use=Spec.Kyber2.Reduce.fst(187,2-194,46)
(= (Lib.IntTypes.v Lib.IntTypes.S32@tok
Lib.IntTypes.SEC@tok
(Lib.IntTypes.mk_int Lib.IntTypes.S32@tok
Lib.IntTypes.SEC@tok
(Prims.op_Addition (Prims.op_Division (Prims.pow2 (BoxInt 26))
(BoxInt 3329))
(BoxInt 1))))
@x21)
)

;; def=prims.fst(237,39-237,106); use=Spec.Kyber2.Reduce.fst(193,2-193,21)
(and 
;; def=FStar.Math.Lemmas.fst(39,12-39,20); use=Spec.Kyber2.Reduce.fst(193,2-193,21)
(or label_240

;; def=FStar.Math.Lemmas.fst(39,12-39,20); use=Spec.Kyber2.Reduce.fst(193,2-193,21)
(<= (BoxInt_proj_0 (Lib.IntTypes.v Lib.IntTypes.S32@tok
Lib.IntTypes.SEC@tok
(Lib.IntTypes.mk_int Lib.IntTypes.S32@tok
Lib.IntTypes.SEC@tok
(Prims.op_Addition (Prims.op_Division (Prims.pow2 (BoxInt 26))
(BoxInt 3329))
(BoxInt 1)))))
(BoxInt_proj_0 (Prims.op_Subtraction (Prims.pow2 (BoxInt 15))
(BoxInt 1))))
)


;; def=prims.fst(237,46-237,106); use=Spec.Kyber2.Reduce.fst(193,2-193,21)
(forall ((@x22 Term))
 (! (implies (and (HasType @x22
Prims.unit)

;; def=FStar.Math.Lemmas.fst(40,12-40,28); use=Spec.Kyber2.Reduce.fst(193,2-193,21)
(<= (BoxInt_proj_0 (Prims.op_Multiply (Lib.IntTypes.v Lib.IntTypes.S32@tok
Lib.IntTypes.SEC@tok
(Lib.IntTypes.mk_int Lib.IntTypes.S32@tok
Lib.IntTypes.SEC@tok
(Prims.op_Addition (Prims.op_Division (Prims.pow2 (BoxInt 26))
(BoxInt 3329))
(BoxInt 1))))
(Prims.pow2 (BoxInt 15))))
(BoxInt_proj_0 (Prims.op_Multiply (Prims.op_Subtraction (Prims.pow2 (BoxInt 15))
(BoxInt 1))
(Prims.pow2 (BoxInt 15)))))
)

;; def=prims.fst(208,69-208,78); use=Spec.Kyber2.Reduce.fst(187,2-194,46)
(and 
;; def=/home/caerbannog/dev/hacl-star/lib/Lib.IntTypes.fsti(145,22-145,30); use=Spec.Kyber2.Reduce.fst(194,28-194,29)
(or label_241

;; def=/home/caerbannog/dev/hacl-star/lib/Lib.IntTypes.fsti(145,22-145,30); use=Spec.Kyber2.Reduce.fst(194,28-194,29)
(BoxBool_proj_0 (Lib.IntTypes.signed Lib.IntTypes.S32@tok))
)


;; def=prims.fst(182,5-182,58); use=Spec.Kyber2.Reduce.fst(187,2-194,46)
(forall ((@x23 Term))
 (! (implies (and (HasType @x23
Lib.IntTypes.inttype)

;; def=prims.fst(182,28-182,41); use=Spec.Kyber2.Reduce.fst(187,2-194,46)
(= @x23
Lib.IntTypes.S32@tok)
)

;; def=prims.fst(214,45-214,80); use=Spec.Kyber2.Reduce.fst(187,2-194,46)
(forall ((@x24 Term))
 (! (implies (and (HasType @x24
Tm_refine_ee21347fbca1d214410772ef0425736c)

;; def=/home/caerbannog/dev/hacl-star/lib/Lib.IntTypes.fsti(79,27-79,43); use=Spec.Kyber2.Reduce.fst(194,21-194,29)
(= (Lib.IntTypes.v Lib.IntTypes.S32@tok
Lib.IntTypes.SEC@tok
(Lib.IntTypes.mk_int Lib.IntTypes.S32@tok
Lib.IntTypes.SEC@tok
(Prims.op_Addition (Prims.op_Division (Prims.pow2 (BoxInt 26))
(BoxInt 3329))
(BoxInt 1))))
@x24)
)

;; def=prims.fst(182,5-182,58); use=Spec.Kyber2.Reduce.fst(187,2-194,46)
(forall ((@x25 Term))
 (! (implies (and (HasType @x25
Tm_refine_ee21347fbca1d214410772ef0425736c)

;; def=prims.fst(182,28-182,41); use=Spec.Kyber2.Reduce.fst(187,2-194,46)
(= @x25
(Lib.IntTypes.v Lib.IntTypes.S32@tok
Lib.IntTypes.SEC@tok
(Lib.IntTypes.mk_int Lib.IntTypes.S32@tok
Lib.IntTypes.SEC@tok
(Prims.op_Addition (Prims.op_Division (Prims.pow2 (BoxInt 26))
(BoxInt 3329))
(BoxInt 1)))))


;; def=<dummy>(0,0-0,0); use=Spec.Kyber2.Reduce.fst(187,2-194,46)
(= (Lib.IntTypes.v Lib.IntTypes.S32@tok
Lib.IntTypes.SEC@tok
(Lib.IntTypes.mk_int Lib.IntTypes.S32@tok
Lib.IntTypes.SEC@tok
(Prims.op_Addition (Prims.op_Division (Prims.pow2 (BoxInt 26))
(BoxInt 3329))
(BoxInt 1))))
@x25)
)

;; def=prims.fst(208,69-208,78); use=Spec.Kyber2.Reduce.fst(187,2-194,46)
(and 
;; def=/home/caerbannog/dev/hacl-star/lib/Lib.IntTypes.fsti(145,22-145,30); use=Spec.Kyber2.Reduce.fst(194,39-194,40)
(or label_242

;; def=/home/caerbannog/dev/hacl-star/lib/Lib.IntTypes.fsti(145,22-145,30); use=Spec.Kyber2.Reduce.fst(194,39-194,40)
(BoxBool_proj_0 (Lib.IntTypes.signed Lib.IntTypes.S16@tok))
)


;; def=prims.fst(182,5-182,58); use=Spec.Kyber2.Reduce.fst(187,2-194,46)
(forall ((@x26 Term))
 (! (implies (and (HasType @x26
Lib.IntTypes.inttype)

;; def=prims.fst(182,28-182,41); use=Spec.Kyber2.Reduce.fst(187,2-194,46)
(= @x26
Lib.IntTypes.S16@tok)
)

;; def=prims.fst(214,45-214,80); use=Spec.Kyber2.Reduce.fst(187,2-194,46)
(forall ((@x27 Term))
 (! (implies (and (HasType @x27
Tm_refine_b2401a8cabe2f9a01538f32548fa9f6c)

;; def=/home/caerbannog/dev/hacl-star/lib/Lib.IntTypes.fsti(79,27-79,43); use=Spec.Kyber2.Reduce.fst(194,32-194,40)
(= (Lib.IntTypes.v Lib.IntTypes.S16@tok
Lib.IntTypes.SEC@tok
@x0)
@x27)
)

;; def=prims.fst(182,5-182,58); use=Spec.Kyber2.Reduce.fst(187,2-194,46)
(forall ((@x28 Term))
 (! (implies (and (HasType @x28
Tm_refine_b2401a8cabe2f9a01538f32548fa9f6c)

;; def=prims.fst(182,28-182,41); use=Spec.Kyber2.Reduce.fst(187,2-194,46)
(= @x28
(Lib.IntTypes.v Lib.IntTypes.S16@tok
Lib.IntTypes.SEC@tok
@x0))


;; def=<dummy>(0,0-0,0); use=Spec.Kyber2.Reduce.fst(187,2-194,46)
(= (Lib.IntTypes.v Lib.IntTypes.S16@tok
Lib.IntTypes.SEC@tok
@x0)
@x28)
)

;; def=prims.fst(214,45-214,80); use=Spec.Kyber2.Reduce.fst(187,2-194,46)
(forall ((@x29 Term))
 (! (implies (and (HasType @x29
Prims.int)

;; def=/home/caerbannog/dev/hacl-star/lib/Lib.IntTypes.fsti(75,11-75,12); use=Spec.Kyber2.Reduce.fst(187,2-194,46)
(= (Prims.op_Multiply (Lib.IntTypes.v Lib.IntTypes.S32@tok
Lib.IntTypes.SEC@tok
(Lib.IntTypes.mk_int Lib.IntTypes.S32@tok
Lib.IntTypes.SEC@tok
(Prims.op_Addition (Prims.op_Division (Prims.pow2 (BoxInt 26))
(BoxInt 3329))
(BoxInt 1))))
(Lib.IntTypes.v Lib.IntTypes.S16@tok
Lib.IntTypes.SEC@tok
@x0))
@x29)
)

;; def=prims.fst(214,45-214,80); use=Spec.Kyber2.Reduce.fst(187,2-194,46)
(forall ((@x30 Term))
 (! (implies (and (HasType @x30
Tm_type)

;; def=FStar.Pervasives.fst(460,27-460,28); use=Spec.Kyber2.Reduce.fst(187,2-194,46)
(= (Lib.IntTypes.range (Prims.op_Multiply (Lib.IntTypes.v Lib.IntTypes.S32@tok
Lib.IntTypes.SEC@tok
(Lib.IntTypes.mk_int Lib.IntTypes.S32@tok
Lib.IntTypes.SEC@tok
(Prims.op_Addition (Prims.op_Division (Prims.pow2 (BoxInt 26))
(BoxInt 3329))
(BoxInt 1))))
(Lib.IntTypes.v Lib.IntTypes.S16@tok
Lib.IntTypes.SEC@tok
@x0))
Lib.IntTypes.S32@tok)
@x30)
)

;; def=prims.fst(237,39-237,106); use=Spec.Kyber2.Reduce.fst(194,2-194,13)
(and 
;; def=prims.fst(47,31-47,40); use=prims.fst(47,31-47,40)
(or label_243

;; def=prims.fst(47,31-47,40); use=prims.fst(47,31-47,40)
(= (Prims.op_LessThanOrEqual (BoxInt -2147483648)
(Prims.op_Multiply (Lib.IntTypes.sec_int_v Lib.IntTypes.S32@tok
(Lib.IntTypes.mk_int Lib.IntTypes.S32@tok
Lib.IntTypes.SEC@tok
(BoxInt 20159)))
(Lib.IntTypes.sec_int_v Lib.IntTypes.S16@tok
@x0)))
(BoxBool true))
)


;; def=prims.fst(47,31-47,40); use=prims.fst(47,31-47,40)
(or label_244

;; def=prims.fst(47,31-47,40); use=prims.fst(47,31-47,40)
(= (Prims.op_LessThanOrEqual (Prims.op_Multiply (Lib.IntTypes.sec_int_v Lib.IntTypes.S32@tok
(Lib.IntTypes.mk_int Lib.IntTypes.S32@tok
Lib.IntTypes.SEC@tok
(BoxInt 20159)))
(Lib.IntTypes.sec_int_v Lib.IntTypes.S16@tok
@x0))
(BoxInt 2147483647))
(BoxBool true))
)


;; def=prims.fst(237,46-237,106); use=Spec.Kyber2.Reduce.fst(194,2-194,13)
(forall ((@x31 Term))
 (! (implies (and (HasType @x31
Prims.unit)

;; def=Spec.Kyber2.Reduce.fst(194,13-194,46); use=Spec.Kyber2.Reduce.fst(194,2-194,13)
(Valid 
;; def=Spec.Kyber2.Reduce.fst(194,13-194,46); use=Spec.Kyber2.Reduce.fst(194,2-194,13)
(Lib.IntTypes.range (Prims.op_Multiply (Lib.IntTypes.v Lib.IntTypes.S32@tok
Lib.IntTypes.SEC@tok
(Lib.IntTypes.mk_int Lib.IntTypes.S32@tok
Lib.IntTypes.SEC@tok
(Prims.op_Addition (Prims.op_Division (Prims.pow2 (BoxInt 26))
(BoxInt 3329))
(BoxInt 1))))
(Lib.IntTypes.v Lib.IntTypes.S16@tok
Lib.IntTypes.SEC@tok
@x0))
Lib.IntTypes.S32@tok)
)
)

;; def=prims.fst(237,92-237,105); use=Spec.Kyber2.Reduce.fst(194,2-194,13)
(Valid 
;; def=prims.fst(237,92-237,105); use=Spec.Kyber2.Reduce.fst(194,2-194,13)
(ApplyTT @x1
@x31)
)
)
 
;;no pats
:qid @query.35))
)
)
 
;;no pats
:qid @query.34))
)
 
;;no pats
:qid @query.33))
)
 
;;no pats
:qid @query.32))
)
 
;;no pats
:qid @query.31))
)
 
;;no pats
:qid @query.30))
)
)
 
;;no pats
:qid @query.29))
)
 
;;no pats
:qid @query.28))
)
 
;;no pats
:qid @query.27))
)
)
 
;;no pats
:qid @query.26))
)
)
 
;;no pats
:qid @query.25))
)
 
;;no pats
:qid @query.24))
)
 
;;no pats
:qid @query.23))
)
)
 
;;no pats
:qid @query.22))
)
)
 
;;no pats
:qid @query.21))
)
)
 
;;no pats
:qid @query.20))
)
 
;;no pats
:qid @query.19))
)
 
;;no pats
:qid @query.18))
)
)
 
;;no pats
:qid @query.17))
)
)
 
;;no pats
:qid @query.16))
)
 
;;no pats
:qid @query.15))
)
)
 
;;no pats
:qid @query.14))
)
 
;;no pats
:qid @query.13))
)
 
;;no pats
:qid @query.12))
)
 
;;no pats
:qid @query.11))
)
 
;;no pats
:qid @query.10))
)
)
 
;;no pats
:qid @query.8))
)
 
;;no pats
:qid @query.7))
)
 
;;no pats
:qid @query.6))
)
)
 
;;no pats
:qid @query.4))
)
 
;;no pats
:qid @query.2))
)
)
 
;;no pats
:qid @query)))
:named @query))
(set-option :rlimit 544656000)
(echo "<result>")
(check-sat)
(echo "</result>")
(set-option :rlimit 0)
(echo "<reason-unknown>")
(get-info :reason-unknown)
(echo "</reason-unknown>")
(echo "<unsat-core>")
(get-unsat-core)
(echo "</unsat-core>")
(echo "<statistics>")
(get-info :all-statistics)
(echo "</statistics>")
(echo "<labels>")
(echo "label_244")
(eval label_244)
(echo "label_243")
(eval label_243)
(echo "label_242")
(eval label_242)
(echo "label_241")
(eval label_241)
(echo "label_240")
(eval label_240)
(echo "label_239")
(eval label_239)
(echo "label_238")
(eval label_238)
(echo "label_237")
(eval label_237)
(echo "label_236")
(eval label_236)
(echo "label_235")
(eval label_235)
(echo "label_234")
(eval label_234)
(echo "label_233")
(eval label_233)
(echo "label_232")
(eval label_232)
(echo "label_231")
(eval label_231)
(echo "label_230")
(eval label_230)
(echo "label_229")
(eval label_229)
(echo "label_228")
(eval label_228)
(echo "label_227")
(eval label_227)
(echo "</labels>")
(echo "Done!")
(pop)

; UNSAT CORE: @MaxFuel_assumption, @MaxIFuel_assumption, @fuel_correspondence_Prims.pow2.fuel_instrumented, @query, constructor_distinct_Lib.IntTypes.S16, constructor_distinct_Lib.IntTypes.S32, constructor_distinct_Lib.IntTypes.SEC, equality_tok_Lib.IntTypes.S16@tok, equality_tok_Lib.IntTypes.S32@tok, equality_tok_Lib.IntTypes.SEC@tok, equation_Lib.IntTypes.bits, equation_Lib.IntTypes.range, equation_Lib.IntTypes.signed, equation_Lib.IntTypes.unsigned, equation_Lib.IntTypes.v, equation_Prims.nat, equation_Prims.pos, equation_Spec.Kyber2.Params.params_q, int_inversion, int_typing, lemma_FStar.UInt.pow2_values, primitive_Prims.op_Addition, primitive_Prims.op_Division, primitive_Prims.op_LessThanOrEqual, primitive_Prims.op_Minus, primitive_Prims.op_Multiply, primitive_Prims.op_Subtraction, projection_inverse_BoxBool_proj_0, projection_inverse_BoxInt_proj_0, refinement_interpretation_Tm_refine_2b320913041b873fce938dd17eebb3e2, refinement_interpretation_Tm_refine_542f9d4f129664613f2483a6c88bc7c2, refinement_interpretation_Tm_refine_774ba3f728d91ead8ef40be66c9802e5, refinement_interpretation_Tm_refine_83845a86f2550cdf941eeb1d9b59602b, refinement_interpretation_Tm_refine_9d3fd79fd314167f1a9c213a188da3ec, refinement_interpretation_Tm_refine_b2401a8cabe2f9a01538f32548fa9f6c, typing_Lib.IntTypes.mk_int, typing_Prims.pow2, typing_tok_Lib.IntTypes.S32@tok, typing_tok_Lib.IntTypes.SEC@tok

