
open Prims
let rec loop = (fun tmp v ctr -> (match (ctr) with
| 0 -> begin
()
end
| _36_14 -> begin
(let _36_15 = (Bignum.fsquare tmp v)
in (let _36_17 = (Bignum.fsquare v tmp)
in (loop tmp v (ctr - 1))))
end))

let assign = (fun output input -> (Bigint.blit_limb input output Parameters.norm_length))

let crecip = (fun output input -> (let ftmp = (Bigint.create_limb Parameters.norm_length)
in (let ftmp2 = (Bigint.create_limb Parameters.norm_length)
in (let e2 = (Bigint.create_limb Parameters.norm_length)
in (let e4 = (Bigint.create_limb Parameters.norm_length)
in (let e8 = (Bigint.create_limb Parameters.norm_length)
in (let e16 = (Bigint.create_limb Parameters.norm_length)
in (let e32 = (Bigint.create_limb Parameters.norm_length)
in (let e64 = (Bigint.create_limb Parameters.norm_length)
in (let tmp = (Bigint.create_limb Parameters.norm_length)
in (let _36_44 = (Bignum.fsquare ftmp input)
in (let _36_46 = (Bignum.fmul ftmp input ftmp)
in (let _36_48 = (assign e2 ftmp)
in (let _36_50 = (Bignum.fsquare ftmp ftmp)
in (let _36_52 = (Bignum.fsquare ftmp ftmp)
in (let _36_54 = (Bignum.fmul ftmp ftmp e2)
in (let _36_56 = (assign e4 ftmp)
in (let _36_58 = (Bignum.fsquare ftmp ftmp)
in (let _36_60 = (Bignum.fsquare ftmp ftmp)
in (let _36_62 = (Bignum.fsquare ftmp ftmp)
in (let _36_64 = (Bignum.fsquare ftmp ftmp)
in (let _36_66 = (Bignum.fmul ftmp ftmp e4)
in (let _36_68 = (assign e8 ftmp)
in (let _36_70 = (loop tmp ftmp 4)
in (let _36_72 = (Bignum.fmul ftmp ftmp e8)
in (let _36_74 = (assign e16 ftmp)
in (let _36_76 = (loop tmp ftmp 8)
in (let _36_78 = (Bignum.fmul ftmp ftmp e16)
in (let _36_80 = (assign e32 ftmp)
in (let _36_82 = (loop tmp ftmp 16)
in (let _36_84 = (assign e64 ftmp)
in (let _36_86 = (Bignum.fmul ftmp ftmp input)
in (let _36_88 = (loop tmp ftmp 96)
in (let _36_90 = (Bignum.fmul ftmp2 e64 e32)
in (let _36_92 = (loop tmp ftmp2 8)
in (let _36_94 = (Bignum.fmul ftmp2 ftmp2 e16)
in (let _36_96 = (loop tmp ftmp2 4)
in (let _36_98 = (Bignum.fmul ftmp2 ftmp2 e8)
in (let _36_100 = (loop tmp ftmp2 2)
in (let _36_102 = (Bignum.fmul ftmp2 ftmp2 e4)
in (let _36_104 = (Bignum.fsquare ftmp2 ftmp2)
in (let _36_106 = (Bignum.fsquare ftmp2 ftmp2)
in (let _36_108 = (Bignum.fmul ftmp2 ftmp2 e2)
in (let _36_110 = (Bignum.fsquare ftmp2 ftmp2)
in (let _36_112 = (Bignum.fsquare ftmp2 ftmp2)
in (let _36_114 = (Bignum.fmul ftmp2 ftmp2 input)
in (Bignum.fmul output ftmp2 ftmp)))))))))))))))))))))))))))))))))))))))))))))))




