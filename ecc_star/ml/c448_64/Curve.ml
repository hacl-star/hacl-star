
open Prims
let a = (FStar_All.failwith "Not yet implemented:a")

let b = (FStar_All.failwith "Not yet implemented:b")

let is_weierstrass_curve = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_weierstrass_curve"))))

let characteristic_corollary = (Obj.magic ((fun x -> (FStar_All.failwith "Not yet implemented:characteristic_corollary"))))

type affine_point =
| Inf
| Finite of Field.felem * Field.felem

let is_Inf = (fun _discr_ -> (match (_discr_) with
| Inf -> begin
true
end
| _ -> begin
false
end))

let is_Finite = (fun _discr_ -> (match (_discr_) with
| Finite (_) -> begin
true
end
| _ -> begin
false
end))

let ___Finite___x = (fun projectee -> (match (projectee) with
| Finite (_15_7, _15_8) -> begin
_15_7
end))

let ___Finite___y = (fun projectee -> (match (projectee) with
| Finite (_15_10, _15_9) -> begin
_15_9
end))

let get_x = (fun p -> (___Finite___x p))

let get_y = (fun p -> (___Finite___y p))

let on_curve = (fun p -> ((is_Inf p) || ((is_Finite p) && (let _15_20 = ((get_x p), (get_y p))
in (match (_15_20) with
| (x, y) -> begin
((Field.op_Hat_Hat y 2) = (Field.op_Hat_Plus (Field.op_Hat_Plus (Field.op_Hat_Hat x 3) (Field.op_Hat_Star a x)) b))
end)))))

type ' p l__CurvePoint =
Prims.unit Prims.b2t

type celem =
affine_point

let neg' = (fun p -> if (is_Inf p) then begin
Inf
end else begin
Finite ((___Finite___x p), (Field.opp (___Finite___y p)))
end)

let neg_lemma = (Obj.magic ((fun p -> (FStar_All.failwith "Not yet implemented:neg_lemma"))))

let neg = (fun p -> (let _15_26 = ()
in (neg' p)))

let add' = (fun p1 p2 -> if (not ((on_curve p1))) then begin
Inf
end else begin
if (not ((on_curve p2))) then begin
Inf
end else begin
if (is_Inf p1) then begin
p2
end else begin
if (is_Inf p2) then begin
p1
end else begin
(let _15_30 = ()
in (let x1 = (get_x p1)
in (let x2 = (get_x p2)
in (let y1 = (get_y p1)
in (let y2 = (get_y p2)
in if (x1 = x2) then begin
if ((y1 = y2) && (y1 <> Field.zero)) then begin
(let _15_36 = ()
in (let lam = (Field.op_Hat_Slash (Field.op_Hat_Plus (Field.op_Plus_Star 3 (Field.op_Hat_Hat x1 2)) a) (Field.op_Plus_Star 2 y1))
in (let x = (Field.op_Hat_Subtraction (Field.op_Hat_Hat lam 2) (Field.op_Plus_Star 2 x1))
in (let y = (Field.op_Hat_Subtraction (Field.op_Hat_Star lam (Field.op_Hat_Subtraction x1 x)) y1)
in Finite (x, y)))))
end else begin
Inf
end
end else begin
(let _15_41 = ()
in (let lam = (Field.op_Hat_Slash (Field.op_Hat_Subtraction y2 y1) (Field.op_Hat_Subtraction x2 x1))
in (let x = (Field.op_Hat_Subtraction (Field.op_Hat_Subtraction (Field.op_Hat_Hat lam 2) x1) x2)
in (let y = (Field.op_Hat_Subtraction (Field.op_Hat_Star lam (Field.op_Hat_Subtraction x1 x)) y1)
in Finite (x, y)))))
end)))))
end
end
end
end)

let add_lemma = (Obj.magic ((fun p q -> (FStar_All.failwith "Not yet implemented:add_lemma"))))

let add = (fun p q -> (let _15_52 = ()
in (add' p q)))

let ec_group_lemma = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:ec_group_lemma"))))

let smul = (fun n p -> (let _15_56 = ()
in (Definitions.scalar_multiplication Inf neg add n p)))

let lemma_equal_intro = (Obj.magic ((fun e1 e2 -> (FStar_All.failwith "Not yet implemented:lemma_equal_intro"))))

let lemma_equal_elim = (Obj.magic ((fun e1 e2 -> (FStar_All.failwith "Not yet implemented:lemma_equal_elim"))))

let lemma_equal_refl = (Obj.magic ((fun e1 e2 -> (FStar_All.failwith "Not yet implemented:lemma_equal_refl"))))

let add_equality = (fun a b c d -> ())

let add_commutativity = (fun a b -> ())

type projective_point =
| Proj of Field.felem * Field.felem * Field.felem

let is_Proj = (fun _discr_ -> (match (_discr_) with
| Proj (_) -> begin
true
end
| _ -> begin
false
end))

let ___Proj___x = (fun projectee -> (match (projectee) with
| Proj (_15_80, _15_81, _15_82) -> begin
_15_80
end))

let ___Proj___y = (fun projectee -> (match (projectee) with
| Proj (_15_84, _15_83, _15_85) -> begin
_15_83
end))

let ___Proj___z = (fun projectee -> (match (projectee) with
| Proj (_15_87, _15_88, _15_86) -> begin
_15_86
end))

type jacobian_point =
| Jac of Field.felem * Field.felem * Field.felem

let is_Jac = (fun _discr_ -> (match (_discr_) with
| Jac (_) -> begin
true
end
| _ -> begin
false
end))

let ___Jac___x = (fun projectee -> (match (projectee) with
| Jac (_15_93, _15_94, _15_95) -> begin
_15_93
end))

let ___Jac___y = (fun projectee -> (match (projectee) with
| Jac (_15_97, _15_96, _15_98) -> begin
_15_96
end))

let ___Jac___z = (fun projectee -> (match (projectee) with
| Jac (_15_100, _15_101, _15_99) -> begin
_15_99
end))

type point =
| Affine of affine_point
| Projective of projective_point
| Jacobian of jacobian_point

let is_Affine = (fun _discr_ -> (match (_discr_) with
| Affine (_) -> begin
true
end
| _ -> begin
false
end))

let is_Projective = (fun _discr_ -> (match (_discr_) with
| Projective (_) -> begin
true
end
| _ -> begin
false
end))

let is_Jacobian = (fun _discr_ -> (match (_discr_) with
| Jacobian (_) -> begin
true
end
| _ -> begin
false
end))

let ___Affine___p = (fun projectee -> (match (projectee) with
| Affine (_15_107) -> begin
_15_107
end))

let ___Projective___p = (fun projectee -> (match (projectee) with
| Projective (_15_110) -> begin
_15_110
end))

let ___Jacobian___p = (fun projectee -> (match (projectee) with
| Jacobian (_15_113) -> begin
_15_113
end))

let to_affine = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:to_affine"))))

let to_projective = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:to_projective"))))

let to_jacobian = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:to_jacobian"))))

type ' p l__OnCurve =
(affine_point, Prims.unit, Prims.unit l__CurvePoint) Prims.l__Let

type ec_elem =
point

let add_point = (fun p q -> (let p' = (___Affine___p (to_affine p))
in (let q' = (___Affine___p (to_affine q))
in Affine ((add' p' q')))))

let op_Plus_Star = (fun n p -> (smul n p))

let smul_lemma = (Obj.magic ((fun q n m -> (FStar_All.failwith "Not yet implemented:smul_lemma"))))




