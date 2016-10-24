
open Prims
let zero = (FStar_All.failwith "Not yet implemented:zero")

type non_zero =
felem

let one = (FStar_All.failwith "Not yet implemented:one")

let add = (Obj.magic ((fun _ _ -> (FStar_All.failwith "Not yet implemented:add"))))

let mul = (Obj.magic ((fun _ _ -> (FStar_All.failwith "Not yet implemented:mul"))))

let opp = (Obj.magic ((fun x -> (FStar_All.failwith "Not yet implemented:opp"))))

let inv = (Obj.magic ((fun x -> (FStar_All.failwith "Not yet implemented:inv"))))

let mul_non_zero = (Obj.magic ((fun x y -> (FStar_All.failwith "Not yet implemented:mul_non_zero"))))

let field_is_group_1 = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:field_is_group_1"))))

let field_is_group_2 = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:field_is_group_2"))))

let field_is_commutative_field = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:field_is_commutative_field"))))

let lemma_equal_intro = (Obj.magic ((fun x y -> (FStar_All.failwith "Not yet implemented:lemma_equal_intro"))))

let lemma_equal_elim = (Obj.magic ((fun x y -> (FStar_All.failwith "Not yet implemented:lemma_equal_elim"))))

let lemma_equal_refl = (Obj.magic ((fun x y -> (FStar_All.failwith "Not yet implemented:lemma_equal_refl"))))

let sub = (fun x y -> (add x (opp y)))

let div = (fun x y -> (mul x (inv y)))

let op_Hat_Plus = add

let op_Hat_Star = mul

let op_Plus_Star = (fun n x -> (let _14_26 = ()
in (Definitions.scalar_multiplication zero opp add n x)))

let rec op_Hat_Hat = (fun x n -> (match (n) with
| 0 -> begin
one
end
| _14_32 -> begin
(mul x (op_Hat_Hat x (n - 1)))
end))

let op_Hat_Subtraction = sub

let op_Hat_Slash = div

let characteristic = (FStar_All.failwith "Not yet implemented:characteristic")

let sub_lemma = (fun x y -> ())

let to_felem = (Obj.magic ((fun x -> (FStar_All.failwith "Not yet implemented:to_felem"))))




