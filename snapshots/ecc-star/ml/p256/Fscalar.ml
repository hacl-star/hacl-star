
open Prims
let gscalar_multiplication_lemma_aux = (fun h0 h1 a b s len -> ())

let scalar_multiplication_lemma_aux = (fun h0 h1 a b s len -> ())

let rec scalar_multiplication_lemma = (fun h0 h1 a b s len -> ())

let rec scalar_multiplication_tr_1 = (fun res a s ctr -> (let ai = (Bigint.index_limb a ctr)
in (let z = (UInt.mul_limb_to_wide ai s)
in (Bigint.upd_wide res ctr z))))

let scalar_multiplication_tr_2 = (fun h0 h1 h2 res a s ctr -> ())

let rec scalar_multiplication_tr = (fun res a s ctr -> (let h0 = (FStar_ST.get ())
in (match ((Parameters.norm_length - ctr)) with
| 0 -> begin
()
end
| _31_155 -> begin
(let i = ctr
in (let _31_157 = ()
in (let _31_159 = (scalar_multiplication_tr_1 res a s ctr)
in (let h1 = (FStar_ST.get ())
in (let _31_162 = ()
in (let _31_164 = (scalar_multiplication_tr res a s (ctr + 1))
in (let h2 = (FStar_ST.get ())
in ())))))))
end)))

let gtheorem_scalar_multiplication = (fun h0 h1 a s len b -> ())

let theorem_scalar_multiplication = (fun h0 h1 a s len b -> ())

let gauxiliary_lemma_2 = (fun ha a s i -> ())

let auxiliary_lemma_2 = (fun ha a s i -> ())

let auxiliary_lemma_0 = (fun ha a s -> ())

let auxiliary_lemma_1 = (fun h0 h1 b mods -> ())

let scalar' = (fun res a s -> (let h0 = (FStar_ST.get ())
in (let _31_260 = ()
in (let _31_262 = (scalar_multiplication_tr res a s 0)
in (let h1 = (FStar_ST.get ())
in ())))))




