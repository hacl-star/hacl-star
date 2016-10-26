
open Prims
let op_Bar_Amp = (fun x y -> (UInt.log_and_wide x y))

let op_Bar_Greater_Greater = (fun x y -> (UInt.shift_right_wide x y))

let op_Bar_Less_Less = (fun x y -> (UInt.shift_left_wide x y))

let op_Bar_Plus = (fun x y -> (UInt.add_wide x y))

let op_Bar_Star = (fun x y -> (UInt.mul_wide x y))

let prime_modulo_lemma = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:prime_modulo_lemma"))))

let modulo_lemma = (Obj.magic ((fun a b -> (FStar_All.failwith "Not yet implemented:modulo_lemma"))))

let pow2_4_lemma = (fun _25_13 -> ())

let pow2_5_lemma = (fun _25_14 -> ())

let satisfies_modulo_constraints = (fun h b -> (Obj.magic (())))

let times_19 = (fun x -> (let y = (op_Bar_Less_Less x 4)
in (let z = (op_Bar_Less_Less x 1)
in (op_Bar_Plus (op_Bar_Plus x y) z))))

let lemma_helper_00 = (fun ctr -> ())

let lemma_helper_01 = (fun ctr -> ())

let rec lemma_helper_02 = (fun a b -> ())

let lemma_helper_03 = (fun ctr -> ())

let lemma_helper_04 = (fun ctr -> ())

let rec pow2_bitweight_lemma_1 = (fun ctr -> ())

let bitweight_norm_length_lemma = (fun _25_99 -> ())

let lemma_helper_10 = (fun h0 b ctr -> ())

let lemma_helper_12 = (fun a b c -> ())

let lemma_helper_11 = (fun h0 h1 b ctr prime -> ())

let freduce_degree_lemma_2 = (fun h0 h1 b ctr -> ())

let gfreduce_degree_lemma = (fun h0 h1 b ctr -> ())

let freduce_degree_lemma = (fun h0 h1 b ctr -> ())

let rec freduce_degree' = (fun b ctr' -> (let h0 = (FStar_ST.get ())
in (match (ctr') with
| 0 -> begin
(let b5ctr = (Bigint.index_wide b (0 + Parameters.norm_length))
in (let bctr = (Bigint.index_wide b 0)
in (let b5ctr = (times_19 b5ctr)
in (let bctr = (op_Bar_Plus bctr b5ctr)
in (let _25_265 = (Bigint.upd_wide b 0 bctr)
in (let h1 = (FStar_ST.get ())
in ()))))))
end
| _25_275 -> begin
(let ctr = ctr'
in (let b5ctr = (Bigint.index_wide b (ctr + Parameters.norm_length))
in (let bctr = (Bigint.index_wide b ctr)
in (let b5ctr = (times_19 b5ctr)
in (let bctr = (op_Bar_Plus bctr b5ctr)
in (let _25_281 = (Bigint.upd_wide b ctr bctr)
in (let h1 = (FStar_ST.get ())
in (let _25_284 = ()
in (let _25_286 = ()
in (let _25_288 = ()
in (let _25_290 = ()
in (let _25_292 = (freduce_degree' b (ctr - 1))
in (let h2 = (FStar_ST.get ())
in ())))))))))))))
end)))

let aux_lemma_4 = (fun h b -> ())

let aux_lemma_5 = (fun h0 h1 b -> ())

let freduce_degree = (fun b -> (let h0 = (FStar_ST.get ())
in (let _25_329 = ()
in (let _25_331 = (freduce_degree' b (Parameters.norm_length - 2))
in (let h1 = (FStar_ST.get ())
in ())))))

let pow2_bitweight_lemma = (fun ctr -> ())

let geval_carry_lemma = (fun ha a hb b ctr -> ())

let eval_carry_lemma = (fun ha a hb b ctr -> ())

let gauxiliary_lemma_1 = (fun bip1 c -> ())

let auxiliary_lemma_1 = (fun bip1 c -> ())

let mod_lemma_1 = (fun a b -> ())

let mod2_51 = (fun a -> (let mask = (UInt.shift_left_wide UInt.one_wide 51)
in (let _25_425 = ()
in (let _25_427 = ()
in (let _25_429 = ()
in (let mask = (UInt.sub_wide mask UInt.one_wide)
in (let res = (op_Bar_Amp a mask)
in (let _25_433 = ()
in res))))))))

let rec carry = (fun b i -> (let h0 = (FStar_ST.get ())
in (match ((Parameters.norm_length - i)) with
| 0 -> begin
()
end
| _25_468 -> begin
(let bi = (Bigint.index_wide b i)
in (let ri = (mod2_51 bi)
in (let _25_471 = ()
in (let _25_473 = (Bigint.upd_wide b i ri)
in (let h1 = (FStar_ST.get ())
in (let _25_476 = ()
in (let c = (op_Bar_Greater_Greater bi 51)
in (let _25_479 = ()
in (let bip1 = (Bigint.index_wide b (i + 1))
in (let _25_482 = ()
in (let _25_484 = ()
in (let _25_486 = ()
in (let z = (op_Bar_Plus bip1 c)
in (let _25_489 = (Bigint.upd_wide b (i + 1) z)
in (let h2 = (FStar_ST.get ())
in (let _25_492 = ()
in (let _25_494 = ()
in (let _25_497 = ()
in (carry b (i + 1))))))))))))))))))))
end)))

let carry_top_to_0 = (fun b -> (let h0 = (FStar_ST.get ())
in (let b0 = (Bigint.index_wide b 0)
in (let btop = (Bigint.index_wide b Parameters.norm_length)
in (let btop_19 = (times_19 btop)
in (let _25_511 = (Bigint.upd_wide b 0 (op_Bar_Plus b0 btop_19))
in (let h1 = (FStar_ST.get ())
in ())))))))

let helper_lemma_20 = (fun a b -> ())

let helper_lemma_21 = (fun a -> ())

let rec carry2 = (fun b i -> (let h0 = (FStar_ST.get ())
in (match ((Parameters.norm_length - i)) with
| 0 -> begin
()
end
| _25_543 -> begin
(let bi = (Bigint.index_wide b i)
in (let ri = (mod2_51 bi)
in (let _25_546 = ()
in (let _25_548 = (Bigint.upd_wide b i ri)
in (let h1 = (FStar_ST.get ())
in (let _25_551 = ()
in (let bip1 = (Bigint.index_wide b (i + 1))
in (let c = (op_Bar_Greater_Greater bi 51)
in (let _25_555 = ()
in (let _25_557 = ()
in (let _25_559 = ()
in (let _25_561 = ()
in (let _25_563 = ()
in (let _25_565 = ()
in (let z = (op_Bar_Plus bip1 c)
in (let _25_568 = ()
in (let _25_570 = ()
in (let _25_572 = ()
in (let _25_574 = ()
in (let _25_576 = (Bigint.upd_wide b (i + 1) z)
in (let h2 = (FStar_ST.get ())
in (let _25_579 = ()
in (let _25_581 = ()
in (let _25_583 = ()
in (carry2 b (i + 1))))))))))))))))))))))))))
end)))

let helper_lemma_30 = (fun a b -> ())

let helper_lemma_32 = (fun a -> ())

let helper_lemma_33 = (fun a b -> ())

let last_carry = (fun b -> (let h0 = (FStar_ST.get ())
in (let b0 = (Bigint.index_wide b 0)
in (let btop = (Bigint.index_wide b Parameters.norm_length)
in (let _25_608 = ()
in (let _25_610 = ()
in (let _25_612 = ()
in (let _25_614 = ()
in (let _25_616 = ()
in (let _25_618 = ()
in (let _25_620 = ()
in (let _25_622 = ()
in (let btop_19 = (times_19 btop)
in (let bi = (op_Bar_Plus b0 btop_19)
in (let _25_626 = (Bigint.upd_wide b 0 bi)
in (let h1 = (FStar_ST.get ())
in (let _25_629 = ()
in (let _25_631 = (Bigint.upd_wide b Parameters.norm_length UInt.zero_wide)
in (let h2 = (FStar_ST.get ())
in (let _25_634 = ()
in (let _25_636 = ()
in (let ri = (mod2_51 bi)
in (let _25_639 = (Bigint.upd_wide b 0 ri)
in (let h3 = (FStar_ST.get ())
in (let c = (op_Bar_Greater_Greater bi 51)
in (let _25_643 = ()
in (let _25_645 = ()
in (let _25_647 = ()
in (let _25_649 = ()
in (let _25_651 = ()
in (let bip1 = (Bigint.index_wide b 1)
in (let _25_654 = ()
in (let _25_656 = ()
in (let _25_658 = ()
in (let _25_660 = ()
in (let z = (op_Bar_Plus bip1 c)
in (let _25_663 = (Bigint.upd_wide b 1 z)
in (let h4 = (FStar_ST.get ())
in ()))))))))))))))))))))))))))))))))))))))

let lemma_helper_40 = (fun h b -> ())

let lemma_helper_41 = (fun a -> ())

let lemma_helper_42 = (fun a b -> ())

let freduce_coefficients = (fun b -> (let h = (FStar_ST.get ())
in (let _25_700 = (Bigint.upd_wide b Parameters.norm_length UInt.zero_wide)
in (let h' = (FStar_ST.get ())
in (let _25_703 = ()
in (let _25_705 = ()
in (let _25_707 = ()
in (let _25_709 = (carry b 0)
in (let h = (FStar_ST.get ())
in (let _25_712 = ()
in (let _25_714 = (carry_top_to_0 b)
in (let h1 = (FStar_ST.get ())
in (let _25_717 = (Bigint.upd_wide b Parameters.norm_length UInt.zero_wide)
in (let h2 = (FStar_ST.get ())
in (let _25_720 = ()
in (let _25_722 = ()
in (let b0 = (Bigint.index_wide b 0)
in (let b1 = (Bigint.index_wide b 1)
in (let r0 = (mod2_51 b0)
in (let c0 = (op_Bar_Greater_Greater b0 51)
in (let _25_728 = ()
in (let _25_730 = ()
in (let h = (FStar_ST.get ())
in (let _25_733 = (Bigint.upd_wide b 0 r0)
in (let _25_735 = (Bigint.upd_wide b 1 (op_Bar_Plus b1 c0))
in (let h' = (FStar_ST.get ())
in (let _25_738 = ()
in (let _25_740 = (carry2 b 1)
in (last_carry b)))))))))))))))))))))))))))))

let gaddition_lemma = (fun a m b n -> ())

let addition_lemma = (fun a m b n -> ())

let aux_lemma_1 = (fun _25_760 -> ())

let add_big_zero_core = (fun b -> (let h0 = (FStar_ST.get ())
in (let two52m38 = (UInt.to_limb "0xfffffffffffda")
in (let two52m2 = (UInt.to_limb "0xffffffffffffe")
in (let _25_777 = ()
in (let b0 = (Bigint.index_limb b 0)
in (let _25_780 = ()
in (let _25_783 = ()
in (let _25_786 = ()
in (let _25_788 = ()
in (let _25_790 = ()
in (let _25_792 = ()
in (let _25_794 = (Bigint.upd_limb b 0 (UInt.add_limb b0 two52m38))
in (let h1 = (FStar_ST.get ())
in (let _25_797 = ()
in (let b1 = (Bigint.index_limb b 1)
in (let _25_800 = ()
in (let _25_802 = ()
in (let _25_804 = ()
in (let _25_806 = (Bigint.upd_limb b 1 (UInt.add_limb b1 two52m2))
in (let h2 = (FStar_ST.get ())
in (let _25_809 = ()
in (let b2 = (Bigint.index_limb b 2)
in (let _25_812 = ()
in (let _25_814 = ()
in (let _25_816 = ()
in (let _25_818 = (Bigint.upd_limb b 2 (UInt.add_limb b2 two52m2))
in (let h3 = (FStar_ST.get ())
in (let _25_821 = ()
in (let b3 = (Bigint.index_limb b 3)
in (let _25_824 = ()
in (let _25_826 = ()
in (let _25_828 = ()
in (let _25_830 = (Bigint.upd_limb b 3 (UInt.add_limb b3 two52m2))
in (let h4 = (FStar_ST.get ())
in (let _25_833 = ()
in (let b4 = (Bigint.index_limb b 4)
in (let _25_836 = ()
in (let _25_838 = ()
in (let _25_840 = ()
in (let _25_842 = (Bigint.upd_limb b 4 (UInt.add_limb b4 two52m2))
in (let h5 = (FStar_ST.get ())
in ()))))))))))))))))))))))))))))))))))))))))))

let aux_lemma_2 = (fun a b c d e -> ())

let modulo_lemma_2 = (Obj.magic ((fun a b -> (FStar_All.failwith "Not yet implemented:modulo_lemma_2"))))

let gaux_lemma_3 = (fun a -> ())

let aux_lemma_3 = (fun a -> ())

let gadd_big_zero_lemma = (fun h0 h1 b -> ())

let add_big_zero_lemma = (fun h0 h1 b -> ())

let n0 = Parameters.ndiff'

let n1 = Parameters.ndiff

let add_big_zero = (fun b -> (let h0 = (FStar_ST.get ())
in (let _25_953 = (add_big_zero_core b)
in (let h1 = (FStar_ST.get ())
in ()))))

let normalize = (fun b -> (let _25_957 = ()
in (let two51m1 = (UInt.to_limb "0x7ffffffffffff")
in (let two51m19 = (UInt.to_limb "0x7ffffffffffed")
in (let b4 = (Bigint.index_limb b 4)
in (let b3 = (Bigint.index_limb b 3)
in (let b2 = (Bigint.index_limb b 2)
in (let b1 = (Bigint.index_limb b 1)
in (let b0 = (Bigint.index_limb b 0)
in (let mask = (UInt.eq_limb b4 two51m1)
in (let mask = (UInt.log_and_limb mask (UInt.eq_limb b3 two51m1))
in (let mask = (UInt.log_and_limb mask (UInt.eq_limb b2 two51m1))
in (let mask = (UInt.log_and_limb mask (UInt.eq_limb b1 two51m1))
in (let mask = (UInt.log_and_limb mask (UInt.gte_limb b0 two51m19))
in (let sub_mask = (UInt.log_and_limb mask two51m1)
in (let sub_mask2 = (UInt.log_and_limb mask two51m19)
in (let b4 = (Bigint.index_limb b 4)
in (let _25_974 = (Bigint.upd_limb b 4 (UInt.sub_limb b4 sub_mask))
in (let b3 = (Bigint.index_limb b 3)
in (let _25_977 = (Bigint.upd_limb b 3 (UInt.sub_limb b3 sub_mask))
in (let b2 = (Bigint.index_limb b 2)
in (let _25_980 = (Bigint.upd_limb b 2 (UInt.sub_limb b2 sub_mask))
in (let b1 = (Bigint.index_limb b 1)
in (let _25_983 = (Bigint.upd_limb b 1 (UInt.sub_limb b1 sub_mask))
in (let b0 = (Bigint.index_limb b 0)
in (Bigint.upd_limb b 0 (UInt.sub_limb b0 sub_mask2)))))))))))))))))))))))))))

let lemma_helper_100 = (fun a b c d -> ())

let lemma_satisfies_0 = (fun a -> ())

let lemma_satisfies = (fun h b n -> ())

let sum_satisfies_constraints = (fun h0 h1 cpy a b -> ())

let difference_satisfies_constraints = (fun h0 h1 cpy a b -> ())

let lemma_satisfies_2 = (fun h b -> ())

let lemma_satisfies_4 = (fun a b c d -> ())

let lemma_satisfies_3 = (fun b c -> ())

let mul_satisfies_constraints = (fun h0 h1 res a b -> ())




