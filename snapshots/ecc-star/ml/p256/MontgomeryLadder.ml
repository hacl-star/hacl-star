
open Prims
let op_Plus_Star = (fun n x -> (Obj.magic (())))

let op_Plus_Plus_Plus = (fun a b -> (FStar_Set.union a b))

let op_Plus_Star_Plus = (Obj.magic ((fun x y -> (FStar_All.failwith "Not yet implemented:op_Plus_Star_Plus"))))

let mk_mask = (fun x -> (let y = (UInt.byte_to_limb x)
in (UInt.neg_limb y)))

let small_step_exit = (Obj.magic ((fun pp ppq p pq q n byte scalar -> (let h0 = (FStar_ST.get ())
in (let _40_45 = (ConcretePoint.copy2 pp ppq p pq)
in (let h1 = (FStar_ST.get ())
in ()))))))

let nth_bit = (fun byte idx -> (let bit = (UInt.log_and_byte (UInt.shift_right_byte byte (7 - idx)) UInt.one_byte)
in (let _40_74 = ()
in bit)))

let gdouble_and_add_lemma_1 = (Obj.magic ((fun q n m -> ())))

let double_and_add_lemma_1 = (fun q n m -> ())

let gsmall_step_core_lemma_1 = (fun h0 h1 pp ppq p pq q -> ())

let small_step_core_lemma_1 = (fun h0 h1 pp ppq p pq q -> ())

let small_step_core_lemma_2 = (fun h0 h h2 h1 pp ppq p pq q -> ())

let gsmall_step_core_lemma_3 = (Obj.magic ((fun h0 h h2 h1 pp ppq p pq q n ctr byt scalar -> ())))

let small_step_core_lemma_3 = (fun h0 h h2 h1 pp ppq p pq q n ctr byt scalar -> ())

let small_step_core = (Obj.magic ((fun pp ppq p pq q n ctr b scalar -> (let h0 = (FStar_ST.get ())
in (let _40_307 = ()
in (let bit = (nth_bit b ctr)
in (let mask = (mk_mask bit)
in (let _40_311 = ()
in (let _40_313 = (ConcretePoint.swap_conditional p pq mask)
in (let h = (FStar_ST.get ())
in (let _40_316 = ()
in (let _40_318 = ()
in (let _40_320 = (DoubleAndAdd.double_and_add pp ppq p pq q)
in (let h2 = (FStar_ST.get ())
in (let _40_323 = (ConcretePoint.swap_conditional pp ppq mask)
in (let _40_325 = ()
in (let h1 = (FStar_ST.get ())
in ())))))))))))))))))

let gsmall_step_lemma_1 = (fun h0 h1 h2 pp ppq p pq q -> ())

let small_step_lemma_1 = (fun h0 h1 h2 pp ppq p pq q -> ())

let gsmall_step_lemma_2 = (fun h0 h1 h2 h3 pp ppq p pq q -> ())

let small_step_lemma_2 = (fun h0 h1 h2 h3 pp ppq p pq q -> ())

let rec small_step = (((fun pp ppq p pq q n ctr b scalar -> (match ((8 - ctr)) with
| 0 -> begin
()
end
| _40_483 -> begin
(let h0 = (FStar_ST.get ())
in (let _40_485 = ()
in (let _40_487 = (small_step_core pp ppq p pq q () ctr b (Obj.magic (())))
in (let h1 = (FStar_ST.get ())
in (let bit = (nth_bit b ctr)
in (let _40_491 = ()
in (let _40_493 = ()
in (let _40_495 = ()
in (let _40_497 = ()
in (let _40_499 = ()
in (let _40_501 = (ConcretePoint.swap_both pp ppq p pq)
in (let h2 = (FStar_ST.get ())
in (let _40_504 = ()
in (let _40_506 = ()
in (let _40_508 = ()
in (let _40_510 = ()
in (let _40_512 = (small_step pp ppq p pq q () (ctr + 1) b (Obj.magic (())))
in (let h3 = (FStar_ST.get ())
in ()))))))))))))))))))
end))))

let formula_4 = (Obj.magic ((fun h n ctr -> (FStar_All.failwith "Not yet implemented:formula_4"))))

type (' n, ' p) l__Distinct2 =
Prims.unit Prims.b2t

let serialized_lemma = (fun h0 h1 n mods -> ())

let gbig_step_lemma_1 = (fun h0 h1 n pp ppq p pq q ctr b -> ())

let big_step_lemma_1 = (fun h0 h1 n pp ppq p pq q ctr b -> ())

let gbig_step_lemma_2 = (fun h0 h1 h2 n pp ppq p pq q ctr byte -> ())

let big_step_lemma_2 = (fun h0 h1 h2 n pp ppq p pq q ctr b -> ())

let rec big_step = (fun n pp ppq p pq q ctr -> (let h0 = (FStar_ST.get ())
in (match ((Parameters.bytes_length - ctr)) with
| 0 -> begin
()
end
| _40_702 -> begin
(let _40_703 = ()
in (let byte = (Bigint.index_byte n ((Parameters.bytes_length - 1) - ctr))
in (let m = ()
in (let _40_707 = ()
in (let _40_709 = (small_step pp ppq p pq q () 0 byte (Obj.magic (())))
in (let h1 = (FStar_ST.get ())
in (let _40_712 = ()
in (let _40_714 = (big_step n pp ppq p pq q (ctr + 1))
in (let h2 = (FStar_ST.get ())
in ())))))))))
end)))

let untouched_point_lemma = (fun h0 h1 p q -> ())

let guntouched_point_lemma_2 = (fun h0 h1 p q -> ())

let untouched_point_lemma_2 = (fun h0 h1 p q -> ())

let untouched_point_lemma_3 = (fun h0 h1 p q -> ())

let untouched_point_lemma_4 = (fun h0 h1 p q -> ())

let init_points = (fun pp ppq p inf q -> (let h0 = (FStar_ST.get ())
in (let _40_801 = (ConcretePoint.copy p q)
in (let h1 = (FStar_ST.get ())
in (let _40_804 = ()
in (let _40_806 = ()
in (let _40_808 = ()
in (let _40_810 = ()
in (let _40_812 = (Bigint.upd_limb (ConcretePoint.get_x inf) 0 UInt.one_limb)
in (let h2 = (FStar_ST.get ())
in ()))))))))))

let oncurve_lemma_0 = (fun h0 h1 p -> ())

let live_lemma_0 = (fun h0 h1 p -> ())

let montgomery_ladder = (fun res n q -> (let h0 = (FStar_ST.get ())
in (let two_p_x = (Bigint.create_limb Parameters.norm_length)
in (let two_p_y = (Bigint.create_limb Parameters.norm_length)
in (let two_p_z = (Bigint.create_limb Parameters.norm_length)
in (let two_p = (ConcretePoint.make two_p_x two_p_y two_p_z)
in (let h = (FStar_ST.get ())
in (let _40_858 = ()
in (let two_p_plus_q_x = (Bigint.create_limb Parameters.norm_length)
in (let two_p_plus_q_y = (Bigint.create_limb Parameters.norm_length)
in (let two_p_plus_q_z = (Bigint.create_limb Parameters.norm_length)
in (let two_p_plus_q = (ConcretePoint.make two_p_plus_q_x two_p_plus_q_y two_p_plus_q_z)
in (let h' = (FStar_ST.get ())
in (let _40_865 = ()
in (let p_x = (Bigint.create_limb Parameters.norm_length)
in (let p_y = (Bigint.create_limb Parameters.norm_length)
in (let p_z = (Bigint.create_limb Parameters.norm_length)
in (let p = (ConcretePoint.make p_x p_y p_z)
in (let h'' = (FStar_ST.get ())
in (let _40_872 = ()
in (let inf_x = (Bigint.create_limb Parameters.norm_length)
in (let inf_y = (Bigint.create_limb Parameters.norm_length)
in (let inf_z = (Bigint.create_limb Parameters.norm_length)
in (let inf = (ConcretePoint.make inf_x inf_y inf_z)
in (let h1 = (FStar_ST.get ())
in (let _40_879 = ()
in (let _40_881 = ()
in (let _40_883 = ()
in (let _40_885 = ()
in (let _40_887 = ()
in (let _40_889 = ()
in (let _40_891 = ()
in (let _40_893 = ()
in (let _40_895 = ()
in (let _40_897 = (init_points two_p two_p_plus_q p inf q)
in (let h2 = (FStar_ST.get ())
in (let _40_900 = ()
in (let _40_902 = ()
in (let _40_904 = ()
in (let _40_906 = (big_step n two_p two_p_plus_q inf p q 0)
in (let h3 = (FStar_ST.get ())
in (let _40_909 = ()
in (ConcretePoint.copy res two_p)))))))))))))))))))))))))))))))))))))))))))




