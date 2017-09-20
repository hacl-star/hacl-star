
open Prims
let rec loop = (fun tmp v ctr -> (match (ctr) with
| 0 -> begin
()
end
| _37_14 -> begin
(let _37_15 = (Bignum.fsquare tmp v)
in (let _37_17 = (Bignum.fsquare v tmp)
in (loop tmp v (ctr - 1))))
end))

let crecip = (fun output z -> (let t0 = (Bigint.create_limb Parameters.norm_length)
in (let t1 = (Bigint.create_limb Parameters.norm_length)
in (let t2 = (Bigint.create_limb Parameters.norm_length)
in (let _37_31 = (Bignum.fsquare t1 z)
in (let _37_33 = (Bignum.fmul t2 z t1)
in (let _37_35 = (Bignum.fsquare t1 t2)
in (let _37_37 = (Bignum.fmul t2 t1 z)
in (let _37_39 = (Bignum.fsquare t0 t2)
in (let _37_41 = (loop t1 t0 1)
in (let _37_43 = (Bignum.fmul t1 t0 t2)
in (let _37_45 = (Bignum.fsquare t0 t1)
in (let _37_47 = (loop t1 t0 1)
in (let _37_49 = (Bignum.fmul t1 t2 t0)
in (let _37_51 = (Bignum.fsquare t0 t1)
in (let _37_53 = (loop t2 t0 4)
in (let _37_55 = (Bignum.fmul t2 t0 t1)
in (let _37_57 = (Bignum.fsquare t0 t2)
in (let _37_59 = (Bignum.fmul t1 z t0)
in (let _37_61 = (loop t0 t1 9)
in (let _37_63 = (Bignum.fmul t0 t1 t2)
in (let _37_65 = (Bignum.fsquare t1 t0)
in (let _37_67 = (loop t2 t1 18)
in (let _37_69 = (Bignum.fmul t2 t1 t0)
in (let _37_71 = (Bignum.fsquare t1 t2)
in (let _37_73 = (loop t2 t1 18)
in (let _37_75 = (Bignum.fmul t2 t1 t0)
in (let _37_77 = (Bignum.fsquare t1 t2)
in (let _37_79 = (loop t0 t1 55)
in (let _37_81 = (Bignum.fmul t0 t2 t1)
in (let _37_83 = (Bignum.fsquare t2 t0)
in (let _37_85 = (Bignum.fmul t1 z t2)
in (let _37_87 = (Bignum.fsquare t2 t1)
in (let _37_89 = (loop t1 t2 111)
in (let _37_91 = (Bignum.fmul t1 t0 t2)
in (let _37_93 = (loop t0 t1 1)
in (Bignum.fmul output t1 z)))))))))))))))))))))))))))))))))))))




