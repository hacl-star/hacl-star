
open Prims
let op_Plus_Plus_Plus = (fun a b -> (FStar_Set.union a b))

let equation_1 = (fun x2 z2 -> (Obj.magic (())))

let equation_2 = (fun x2 z2 -> (Obj.magic (())))

let equation_3 = (fun x2 z2 x3 z3 -> (Obj.magic (())))

let equation_4 = (fun x2 z2 x3 z3 x1 -> (Obj.magic (())))

let double_and_add' = (fun two_p two_p_plus_q p p_plus_q q -> (let h0 = (FStar_ST.get ())
in (let qmqp = (ConcretePoint.get_x q)
in (let x = (ConcretePoint.get_x p)
in (let z = (ConcretePoint.get_z p)
in (let xprime = (ConcretePoint.get_x p_plus_q)
in (let zprime = (ConcretePoint.get_z p_plus_q)
in (let x2 = (ConcretePoint.get_x two_p)
in (let z2 = (ConcretePoint.get_z two_p)
in (let origx = (Bigint.create_limb Parameters.norm_length)
in (let origxprime = (Bigint.create_limb Parameters.norm_length)
in (let zzz = (Bigint.create_limb ((2 * Parameters.norm_length) - 1))
in (let xx = (Bigint.create_limb ((2 * Parameters.norm_length) - 1))
in (let zz = (Bigint.create_limb ((2 * Parameters.norm_length) - 1))
in (let xxprime = (Bigint.create_limb ((2 * Parameters.norm_length) - 1))
in (let zzprime = (Bigint.create_limb ((2 * Parameters.norm_length) - 1))
in (let xxxprime = (Bigint.create_limb ((2 * Parameters.norm_length) - 1))
in (let zzzprime = (Bigint.create_limb ((2 * Parameters.norm_length) - 1))
in (let _39_53 = (Bigint.blit Parameters.platform_size x origx Parameters.norm_length)
in (let _39_55 = (Bignum.fsum x z)
in (let _39_57 = (Bignum.fdifference z origx)
in (let _39_59 = (Bigint.blit Parameters.platform_size xprime origxprime Parameters.norm_length)
in (let _39_61 = (Bignum.fsum xprime zprime)
in (let _39_63 = (Bignum.fdifference zprime origxprime)
in (let _39_65 = (Bignum.fmul xxprime xprime z)
in (let _39_67 = (Bignum.fmul zzprime x zprime)
in (let _39_69 = (Bigint.blit Parameters.platform_size xxprime origxprime Parameters.norm_length)
in (let _39_71 = (Bignum.fsum xxprime zzprime)
in (let _39_73 = (Bignum.fdifference zzprime origxprime)
in (let _39_75 = (Bignum.fsquare xxxprime xxprime)
in (let _39_77 = (Bignum.fsquare zzzprime zzprime)
in (let _39_79 = (Bignum.fmul zzprime zzzprime qmqp)
in (let _39_81 = (Bigint.blit Parameters.platform_size xxxprime (ConcretePoint.get_x two_p_plus_q) Parameters.norm_length)
in (let _39_83 = (Bigint.blit Parameters.platform_size zzprime (ConcretePoint.get_z two_p_plus_q) Parameters.norm_length)
in (let _39_85 = (Bignum.fsquare xx x)
in (let _39_87 = (Bignum.fsquare zz z)
in (let _39_89 = (Bignum.fmul x2 xx zz)
in (let _39_91 = (Bignum.fdifference zz xx)
in (let _39_93 = (Bignum.erase zzz Parameters.norm_length (Parameters.norm_length - 1) 0)
in (let _39_95 = (Bignum.fscalar zzz zz 12 (UInt.to_limb Parameters.a24))
in (let _39_97 = (Bignum.fsum zzz xx)
in (Bignum.fmul z2 zz zzz))))))))))))))))))))))))))))))))))))))))))

let double_and_add = (fun two_p two_p_plus_q p p_plus_q q -> (double_and_add' two_p two_p_plus_q p p_plus_q q))




