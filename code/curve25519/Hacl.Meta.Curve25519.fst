module Hacl.Meta.Curve25519

#set-options "--max_fuel 2 --max_ifuel 1 --z3rlimit 300 --print_implicits --print_full_names"

// For debugging
#set-options "--admit_smt_queries true --print_effect_args"

friend Hacl.Impl.Curve25519.Generic

// START DEBUGGING

let ( |+| ) = Lib.Buffer.(( |+| ))
open FStar.Mul

%splice[
  carry_pass_store_higher
]
(Meta.Interface.specialize (`Hacl.Impl.Curve25519.Fields.field_spec) [
  `Hacl.Impl.Curve25519.Field64.carry_pass_store
])

let store_felem_higher_t: Type0 = 
    u64s28607: Lib.Buffer.lbuffer Lib.IntTypes.uint64 4ul ->
    f28608: Hacl.Impl.Curve25519.Field64.felem
  -> FStar.HyperStack.ST.Stack Prims.unit
      (fun h28609 ->
          Prims.b2t Vale.X64.CPU_Features_s.adx_enabled /\
          Prims.b2t Vale.X64.CPU_Features_s.bmi2_enabled /\
          Lib.Buffer.live #(Lib.Buffer.MUT) #Lib.IntTypes.uint64 h28609 f28608 /\
          Lib.Buffer.live #(Lib.Buffer.MUT) #Lib.IntTypes.uint64 h28609 u64s28607 /\
          Lib.Buffer.disjoint #(Lib.Buffer.MUT)
            #(Lib.Buffer.MUT)
            #Lib.IntTypes.uint64
            #Lib.IntTypes.uint64
            u64s28607
            f28608)
      (fun h028610 _ h128612 ->
          Lib.Buffer.modifies (Lib.Buffer.loc #(Lib.Buffer.MUT) #Lib.IntTypes.uint64 u64s28607 |+|
              Lib.Buffer.loc #(Lib.Buffer.MUT) #Lib.IntTypes.uint64 f28608)
            h028610
            h128612 /\
          Prims.eq2 #(s28613:
              Lib.Sequence.seq Lib.IntTypes.uint64
                { Prims.eq2 #Prims.nat
                    (FStar.Seq.Base.length #Lib.IntTypes.uint64 s28613)
                    (Lib.IntTypes.v #(Lib.IntTypes.U32)
                        #(Lib.IntTypes.PUB)
                        4ul) \/
                  Prims.eq2 #Prims.nat
                    (Lib.Sequence.length #(Lib.IntTypes.uint_t (Lib.IntTypes.U64) (Lib.IntTypes.SEC)
                        )
                        s28613)
                    4 /\
                  Prims.eq2 #(n28614:
                      Prims.nat
                        { Prims.b2t (n28614 <
                              Prims.pow2 (Lib.Sequence.length #(Lib.IntTypes.uint_t (Lib.IntTypes.U64
                                        )
                                        (Lib.IntTypes.SEC))
                                    s28613 *
                                  Lib.IntTypes.bits (Lib.IntTypes.U64))) \/
                          Prims.b2t (n28614 < Prims.pow2 (Lib.IntTypes.bits (Lib.IntTypes.U64) * 4))
                        })
                    (Hacl.Impl.Curve25519.Field64.Core.fevalh h028610 f28608)
                    (Lib.ByteSequence.nat_from_intseq_le #(Lib.IntTypes.U64)
                        #(Lib.IntTypes.SEC)
                        s28613) })
            (Lib.Buffer.as_seq #(Lib.Buffer.MUT)
                #Lib.IntTypes.uint64
                #4ul
                h128612
                u64s28607)
            (Lib.ByteSequence.nat_to_intseq_le #(Lib.IntTypes.U64)
                #(Lib.IntTypes.SEC)
                4
                (Hacl.Impl.Curve25519.Field64.Core.fevalh h028610 f28608)))

let store_felem_higher:

    arg_Hacl_Impl_Curve25519_Field64_Core_add128696:
      (
            out28697: Hacl.Impl.Curve25519.Field64.Core.u256 ->
            f128698: Hacl.Impl.Curve25519.Field64.Core.u256 ->
            f228699: Lib.IntTypes.uint64
          -> FStar.HyperStack.ST.Stack Lib.IntTypes.uint64
              (fun h28700 ->
                  Prims.b2t Vale.X64.CPU_Features_s.adx_enabled /\
                  Prims.b2t Vale.X64.CPU_Features_s.bmi2_enabled /\
                  Lib.Buffer.live #(Lib.Buffer.MUT) #Lib.IntTypes.uint64 h28700 f128698 /\
                  Lib.Buffer.live #(Lib.Buffer.MUT) #Lib.IntTypes.uint64 h28700 out28697 /\
                  (Lib.Buffer.disjoint #(Lib.Buffer.MUT)
                      #(Lib.Buffer.MUT)
                      #Lib.IntTypes.uint64
                      #Lib.IntTypes.uint64
                      out28697
                      f128698 \/ Prims.eq2 #Hacl.Impl.Curve25519.Field64.Core.u256 out28697 f128698)
              )
              (fun h028701 c28702 h128703 ->
                  Lib.Buffer.modifies (Lib.Buffer.loc #(Lib.Buffer.MUT)
                        #Lib.IntTypes.uint64
                        out28697)
                    h028701
                    h128703 /\
                  Prims.eq2 #Prims.int
                    (Hacl.Impl.Curve25519.Field64.Core.as_nat h128703 out28697 +
                      Lib.IntTypes.v #(Lib.IntTypes.U64) #(Lib.IntTypes.SEC) c28702 * Prims.pow2 256
                    )
                    (Hacl.Impl.Curve25519.Field64.Core.as_nat h028701 f128698 +
                      Lib.IntTypes.v #(Lib.IntTypes.U64) #(Lib.IntTypes.SEC) f228699)))
  -> Prims.Tot store_felem_higher_t
=
fun arg_Hacl_Impl_Curve25519_Field64_Core_add128704 u64s28705 f28706 ->
  let h028707 = FStar.HyperStack.ST.get () in
  let _uu___28708 =
    carry_pass_store_higher arg_Hacl_Impl_Curve25519_Field64_Core_add128704
      f28706
  in
  let h128709 = FStar.HyperStack.ST.get () in
  let _uu___28710 =
    Hacl.Spec.Curve25519.Field64.lemma_carry_pass_store0 (Hacl.Impl.Curve25519.Field64.as_tup4 h028707
          f28706)
  in
  let _uu___28711 =
    carry_pass_store_higher arg_Hacl_Impl_Curve25519_Field64_Core_add128704
      f28706
  in
  let h228712 = FStar.HyperStack.ST.get () in
  let _uu___28713 =
    Hacl.Spec.Curve25519.Field64.lemma_carry_pass_store1 (Hacl.Impl.Curve25519.Field64.as_tup4 h128709
          f28706)
  in
  let f028714 =
    Lib.Buffer.op_Array_Access #(Lib.Buffer.MUT)
      #Lib.IntTypes.uint64
      #4ul
      f28706
      0ul
  in
  let f128715 =
    Lib.Buffer.op_Array_Access #(Lib.Buffer.MUT)
      #Lib.IntTypes.uint64
      #4ul
      f28706
      1ul
  in
  let f228716 =
    Lib.Buffer.op_Array_Access #(Lib.Buffer.MUT)
      #Lib.IntTypes.uint64
      #4ul
      f28706
      2ul
  in
  let f328717 =
    Lib.Buffer.op_Array_Access #(Lib.Buffer.MUT)
      #Lib.IntTypes.uint64
      #4ul
      f28706
      3ul
  in
  let _uu___28718 =
    assert (Prims.b2t (Prims.op_LessThan (Lib.IntTypes.v #(Lib.IntTypes.U64)
                  #(Lib.IntTypes.SEC)
                  f328717)
              (Prims.pow2 63)))
  in
  let _uu___28719 =
    assert (Prims.b2t (Prims.op_LessThan (Hacl.Impl.Curve25519.Field64.Core.as_nat h228712 f28706)
              (Prims.pow2 255)))
  in
  let _uu___28720 =
    Hacl.Spec.Curve25519.Field64.subtract_p4 (FStar.Pervasives.Native.Mktuple4 #Lib.IntTypes.uint64
          #Lib.IntTypes.uint64
          #Lib.IntTypes.uint64
          #Lib.IntTypes.uint64
          f028714
          f128715
          f228716
          f328717)
  in
  let FStar.Pervasives.Native.Mktuple4 #_ #_ #_ #_ o028721 o128722 o228723 o328724 = _uu___28720 in
  let _uu___28725 =
    assert (Prims.b2t (Prims.op_LessThan (Hacl.Spec.Curve25519.Field64.Definition.as_nat4 (FStar.Pervasives.Native.Mktuple4
                      #Lib.IntTypes.uint64
                      #Lib.IntTypes.uint64
                      #Lib.IntTypes.uint64
                      #Lib.IntTypes.uint64
                      o028721
                      o128722
                      o228723
                      o328724))
              Spec.Curve25519.prime))
  in
  let _uu___28726 =
    assert (Prims.eq2 #Prims.int
          (Hacl.Spec.Curve25519.Field64.Definition.as_nat4 (FStar.Pervasives.Native.Mktuple4
                  #Lib.IntTypes.uint64
                  #Lib.IntTypes.uint64
                  #Lib.IntTypes.uint64
                  #Lib.IntTypes.uint64
                  o028721
                  o128722
                  o228723
                  o328724))
          (Prims.op_Modulus (Hacl.Impl.Curve25519.Field64.Core.as_nat h228712 f28706)
              Spec.Curve25519.prime))
  in
  let _uu___28727 =
    Lib.Buffer.op_Array_Assignment #Lib.IntTypes.uint64
      #4ul
      u64s28705
      0ul
      o028721
  in
  let _uu___28728 =
    Lib.Buffer.op_Array_Assignment #Lib.IntTypes.uint64
      #4ul
      u64s28705
      1ul
      o128722
  in
  let _uu___28729 =
    Lib.Buffer.op_Array_Assignment #Lib.IntTypes.uint64
      #4ul
      u64s28705
      2ul
      o228723
  in
  let _uu___28730 =
    Lib.Buffer.op_Array_Assignment #Lib.IntTypes.uint64
      #4ul
      u64s28705
      3ul
      o328724
  in
  let h328731 = FStar.HyperStack.ST.get () in
  let _uu___28732 =
    Hacl.Impl.Curve25519.Lemmas.lemma_nat_from_uints64_le_4 (Lib.Buffer.as_seq #(Lib.Buffer.MUT)
          #Lib.IntTypes.uint64
          #4ul
          h328731
          u64s28705)
  in
  Lib.ByteSequence.lemma_nat_from_to_intseq_le_preserves_value #(Lib.IntTypes.U64)
    #(Lib.IntTypes.SEC)
    4
    (Lib.Buffer.as_seq #(Lib.Buffer.MUT)
        #Lib.IntTypes.uint64
        #4ul
        h328731
        u64s28705)

// END DEBUGGING

%splice[
(*  // From Finv.
  fsqr_s_higher;
  fmul_s_higher;
  fsquare_times_higher;
  finv_higher;
  // From AddAnddouble
  point_add_and_double_higher;
  point_double_higher;
  // From Generic
  encode_higher;
  cswap2_higher;
  montgomery_ladder_higher;
  decode_point_higher;
  scalarmult_higher;
  secret_to_public_higher;
  ecdh_higher *)
]
(Meta.Interface.specialize (`Hacl.Impl.Curve25519.Fields.field_spec) [
  `Hacl.Impl.Curve25519.Field64.store_felem
  (*`Hacl.Impl.Curve25519.Generic.scalarmult;
  `Hacl.Impl.Curve25519.Generic.secret_to_public;
  `Hacl.Impl.Curve25519.Generic.ecdh*)
])
