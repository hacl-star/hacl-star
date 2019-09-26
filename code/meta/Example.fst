module Example

module I = Interface

open FStar.Mul

#set-options "--print_bound_var_types --print_implicits --print_full_names"

// This is what comes out of the tactic.
(*
let times_two_inline_t =
  fun (#w2285: Interface.w) -> x2286: Interface.word w2285 -> Prims.Tot (Interface.word w2285)

let times_two_inline:
    #w2392: Interface.w
  -> Prims.Tot
    (arg_Interface_add2393: (fun (#w2394: Interface.w) -> Interface.add_st w2394) #w2392
        -> Prims.Tot (times_two_inline_t #w2392))
=
      fun
  (#w2365: Interface.w)
  (arg_Interface_add2366: (fun (#w2368: Interface.w) -> Interface.add_st w2368) #w2365)
  (x2367: Interface.word w2365)
  ->
  arg_Interface_add2366 x2367 x2367

let times_four_inline_t = fun (#w3040: Interface.w) -> x3041: Interface.word w3040 -> Prims.Tot (Interface.word w3040)

let times_four_inline:   #w3147: Interface.w
  -> Prims.Tot
    (arg_Interface_add3148: (fun (#w3149: Interface.w) -> Interface.add_st w3149) #w3147
        -> Prims.Tot (times_four_inline_t #w3147))
=
  fun
  (#w3120: Interface.w)
  (arg_Interface_add3121: (fun (#w3123: Interface.w) -> Interface.add_st w3123) #w3120)
  (x3122: Interface.word w3120)
  ->
  times_two_inline #w3120
    arg_Interface_add3121
    (times_two_inline #w3120 arg_Interface_add3121 x3122)

let times_sixteen_inline_t = fun (#w3675: Interface.w) -> x3676: Interface.word w3675 -> Prims.Tot (Interface.word w3675)
let times_sixteen_inline:
#w3740: Interface.w
  -> Prims.Tot
    (arg_Client_times_four3741: times_four_inline_t #w3740
        -> Prims.Tot (times_sixteen_inline_t #w3740))
=
fun
  (#w3742: Interface.w)
  (arg_Client_times_four3743: times_four_inline_t #w3742)
  (x3744: Interface.word w3742)
  ->
  arg_Client_times_four3743 (arg_Client_times_four3743 x3744)

let four_inline_t = fun (#w6290: Interface.w) -> Interface.word w6290
let four_inline:
    #w6354: Interface.w -> Prims.Tot (four_inline_t #w6354)
    =
    fun (#w6355: Interface.w) ->
  if Prims.op_Equality #Interface.w w6355 (Interface.W32)
  then 4ul
  else 4UL

let times_four'_inline_t = fun (#w7062: Interface.w) -> x7063: Interface.word w7062 -> Prims.Tot (Interface.word w7062)
let times_four'_inline:
  #w7127: Interface.w
  -> Prims.Tot
    (arg_Interface_mul7128: (fun (#w7129: Interface.w) -> Interface.mul_st w7129) #w7127
        -> Prims.Tot (times_four'_inline_t #w7127))
  =
  fun
  (#w7130: Interface.w)
  (arg_Interface_mul7131: (fun (#w7133: Interface.w) -> Interface.mul_st w7133) #w7130)
  (x7132: Interface.word w7130)
  ->
  arg_Interface_mul7131 (four_inline #w7130) x7132

let times_sixteen'_inline_t = fun (#w7808: Interface.w) -> x7809: Interface.word w7808 -> Prims.Tot (Interface.word w7808)
let times_sixteen'_inline:
#w7873: Interface.w
  -> Prims.Tot
    (arg_Client_times_four7874: times_four_inline_t #w7873
        -> Prims.Tot
          (arg_Interface_mul7875: (fun (#w7876: Interface.w) -> Interface.mul_st w7876) #w7873
              -> Prims.Tot (times_sixteen'_inline_t #w7873)))
=
fun
  (#w7877: Interface.w)
  (arg_Client_times_four7878: times_four_inline_t #w7877)
  (arg_Interface_mul7879: (fun (#w7881: Interface.w) -> Interface.mul_st w7881) #w7877)
  (x7880: Interface.word w7877)
  ->
  arg_Client_times_four7878 (times_four'_inline #w7877 arg_Interface_mul7879 x7880)

*)

// BUG: this is what the tactic generates (see debug output)

let four_inline_t: #w1639: Interface.w -> Prims.Tot Type0 = fun (#w1640: Interface.w) -> Interface.word w1640
let four_inline:
#w1700: Interface.w -> Prims.Tot (four_inline_t #w1700)
=
fun (#w1701: Interface.w) ->
  if Prims.op_Equality #Interface.w w1701 (Interface.W32)
  then 4ul
  else 4UL

let u1 = ()

// But when trying to actually call the tactic, I get:
//   Expected type "Example.four_inline_t #w1870"; but "FStar.UInt32.__uint_to_t
//     4" has type "FStar.UInt32.t"
// There seems to be a proof obligation emitted to Z3 when splicing; I don't
// understand what the query is, and why it shows up.
//
// Note that the problem is somewhere in the definition of four_inline since
// commenting out line 172 of the tactic fixes the problem.

%splice[
  //times_four_inline;
  //times_sixteen_inline;
  //times_sixteen'_inline
] (MetaInterface.specialize [ `Client.four ])
//] (MetaInterface.specialize [ `Client.times_sixteen; `Client.times_sixteen' ])

let add: I.add_st I.W32 = FStar.UInt32.add_mod
let mul: I.mul_st I.W32 = FStar.UInt32.mul_mod
// let times_four = times_four_inline add
// let times_sixteen = times_sixteen_inline times_four
// let times_sixteen' = times_sixteen'_inline times_four mul

// Rolling our sleeves up.

// This is what comes out of the tactic (see debug output).

#reset-options "--using_facts_from '* -FStar.Seq'"
#set-options "--z3rlimit 100 --max_fuel 0 --max_ifuel 0"

// TODO: optimize this as the identity (leaf of the call-graph)
let mk_double_round:
    #w30249: Hacl.Impl.Chacha20.Core32xN.lanes
  -> Prims.Tot
    ((fun (#w30250: Hacl.Impl.Chacha20.Core32xN.lanes) ->
          st30251: Hacl.Impl.Chacha20.Core32xN.state w30250
            -> FStar.HyperStack.ST.Stack Prims.unit
                (fun (h30252: FStar.Monotonic.HyperStack.mem) ->
                    Lib.Buffer.live #(Lib.Buffer.MUT)
                      #(Hacl.Impl.Chacha20.Core32xN.uint32xN w30250)
                      h30252
                      st30251)
                (fun
                    (h030253: FStar.Monotonic.HyperStack.mem)
                    (_: Prims.unit)
                    (h130255:
                      (_uu___030256:
                        FStar.Monotonic.HyperStack.mem
                          { Lib.Buffer.live #(Lib.Buffer.MUT)
                              #(Hacl.Impl.Chacha20.Core32xN.uint32xN w30250)
                              h030253
                              st30251 }))
                    ->
                    Lib.Buffer.modifies (Lib.Buffer.loc #(Lib.Buffer.MUT)
                          #(Hacl.Impl.Chacha20.Core32xN.uint32xN w30250)
                          st30251)
                      h030253
                      h130255 /\
                    Prims.eq2 #(s30257:
                        Lib.Sequence.seq (Hacl.Impl.Chacha20.Core32xN.uint32xN w30250)
                          { Prims.eq2 #Prims.nat
                              (FStar.Seq.Base.length #(Hacl.Impl.Chacha20.Core32xN.uint32xN w30250)
                                  s30257)
                              (Lib.IntTypes.v #(Lib.IntTypes.U32)
                                  #(Lib.IntTypes.PUB)
                                  16ul) \/
                            Prims.eq2 #Prims.nat
                              (FStar.Seq.Base.length #(Hacl.Spec.Chacha20.Vec.uint32xN w30250)
                                  s30257)
                              16 })
                      (Lib.Buffer.as_seq #(Lib.Buffer.MUT)
                          #(Hacl.Impl.Chacha20.Core32xN.uint32xN w30250)
                          #16ul
                          h130255
                          st30251)
                      (Hacl.Spec.Chacha20.Vec.double_round #w30250
                          (Lib.Buffer.as_seq #(Lib.Buffer.MUT)
                              #(Hacl.Impl.Chacha20.Core32xN.uint32xN w30250)
                              #16ul
                              h030253
                              st30251)))) #w30249)
=
    fun
  (#w30217: Hacl.Impl.Chacha20.Core32xN.lanes)
  (st30218: Hacl.Impl.Chacha20.Core32xN.state w30217)
  ->
  let _uu___30219 =
    Hacl.Impl.Chacha20.Core32xN.quarter_round #w30217
      st30218
      (Lib.IntTypes.size 0)
      (Lib.IntTypes.size 4)
      (Lib.IntTypes.size 8)
      (Lib.IntTypes.size 12)
  in
  let _uu___30220 =
    Hacl.Impl.Chacha20.Core32xN.quarter_round #w30217
      st30218
      (Lib.IntTypes.size 1)
      (Lib.IntTypes.size 5)
      (Lib.IntTypes.size 9)
      (Lib.IntTypes.size 13)
  in
  let _uu___30221 =
    Hacl.Impl.Chacha20.Core32xN.quarter_round #w30217
      st30218
      (Lib.IntTypes.size 2)
      (Lib.IntTypes.size 6)
      (Lib.IntTypes.size 10)
      (Lib.IntTypes.size 14)
  in
  let _uu___30222 =
    Hacl.Impl.Chacha20.Core32xN.quarter_round #w30217
      st30218
      (Lib.IntTypes.size 3)
      (Lib.IntTypes.size 7)
      (Lib.IntTypes.size 11)
      (Lib.IntTypes.size 15)
  in
  let _uu___30223 =
    Hacl.Impl.Chacha20.Core32xN.quarter_round #w30217
      st30218
      (Lib.IntTypes.size 0)
      (Lib.IntTypes.size 5)
      (Lib.IntTypes.size 10)
      (Lib.IntTypes.size 15)
  in
  let _uu___30224 =
    Hacl.Impl.Chacha20.Core32xN.quarter_round #w30217
      st30218
      (Lib.IntTypes.size 1)
      (Lib.IntTypes.size 6)
      (Lib.IntTypes.size 11)
      (Lib.IntTypes.size 12)
  in
  let _uu___30225 =
    Hacl.Impl.Chacha20.Core32xN.quarter_round #w30217
      st30218
      (Lib.IntTypes.size 2)
      (Lib.IntTypes.size 7)
      (Lib.IntTypes.size 8)
      (Lib.IntTypes.size 13)
  in
  Hacl.Impl.Chacha20.Core32xN.quarter_round #w30217
    st30218
    (Lib.IntTypes.size 3)
    (Lib.IntTypes.size 4)
    (Lib.IntTypes.size 9)
    (Lib.IntTypes.size 14)

// BUG: if instead of:
//   let mk_rounds_t = ...
//   let mk_rounds: mk_rounds_t =
// I do:
//   let mk_rounds: ... =
// Then F* loops (or OOMs).

let mk_rounds_t =
  #w35464: Hacl.Impl.Chacha20.Core32xN.lanes
  -> Prims.Tot
    (
          arg_Hacl_Impl_Chacha20_Core32xN_double_round35465:
            (fun (#w35474: Hacl.Impl.Chacha20.Core32xN.lanes) ->
                st35475: Hacl.Impl.Chacha20.Core32xN.state w35474
                  -> FStar.HyperStack.ST.Stack Prims.unit
                      (fun (h35476: FStar.Monotonic.HyperStack.mem) ->
                          Lib.Buffer.live #(Lib.Buffer.MUT)
                            #(Hacl.Impl.Chacha20.Core32xN.uint32xN w35474)
                            h35476
                            st35475)
                      (fun
                          (h035477: FStar.Monotonic.HyperStack.mem)
                          (_: Prims.unit)
                          (h135479:
                            (_uu___035480:
                              FStar.Monotonic.HyperStack.mem
                                { Lib.Buffer.live #(Lib.Buffer.MUT)
                                    #(Hacl.Impl.Chacha20.Core32xN.uint32xN w35474)
                                    h035477
                                    st35475 }))
                          ->
                          Lib.Buffer.modifies (Lib.Buffer.loc #(Lib.Buffer.MUT)
                                #(Hacl.Impl.Chacha20.Core32xN.uint32xN w35474)
                                st35475)
                            h035477
                            h135479 /\
                          Prims.eq2 #(s35481:
                              Lib.Sequence.seq (Hacl.Impl.Chacha20.Core32xN.uint32xN w35474)
                                { Prims.eq2 #Prims.nat
                                    (FStar.Seq.Base.length #(Hacl.Impl.Chacha20.Core32xN.uint32xN w35474
                                          )
                                        s35481)
                                    (Lib.IntTypes.v #(Lib.IntTypes.U32)
                                        #(Lib.IntTypes.PUB)
                                        16ul) \/
                                  Prims.eq2 #Prims.nat
                                    (FStar.Seq.Base.length #(Hacl.Spec.Chacha20.Vec.uint32xN w35474)
                                        s35481)
                                    16 })
                            (Lib.Buffer.as_seq #(Lib.Buffer.MUT)
                                #(Hacl.Impl.Chacha20.Core32xN.uint32xN w35474)
                                #16ul
                                h135479
                                st35475)
                            (Hacl.Spec.Chacha20.Vec.double_round #w35474
                                (Lib.Buffer.as_seq #(Lib.Buffer.MUT)
                                    #(Hacl.Impl.Chacha20.Core32xN.uint32xN w35474)
                                    #16ul
                                    h035477
                                    st35475)))) #w35464
        -> Prims.Tot
          ((fun (#w35466: Hacl.Impl.Chacha20.Core32xN.lanes) ->
                st35467: Hacl.Impl.Chacha20.Core32xN.state w35466
                  -> FStar.HyperStack.ST.Stack Prims.unit
                      (fun (h35468: FStar.Monotonic.HyperStack.mem) ->
                          Lib.Buffer.live #(Lib.Buffer.MUT)
                            #(Hacl.Impl.Chacha20.Core32xN.uint32xN w35466)
                            h35468
                            st35467)
                      (fun
                          (h035469: FStar.Monotonic.HyperStack.mem)
                          (_: Prims.unit)
                          (h135471:
                            (_uu___035472:
                              FStar.Monotonic.HyperStack.mem
                                { Lib.Buffer.live #(Lib.Buffer.MUT)
                                    #(Hacl.Impl.Chacha20.Core32xN.uint32xN w35466)
                                    h035469
                                    st35467 }))
                          ->
                          Lib.Buffer.modifies (Lib.Buffer.loc #(Lib.Buffer.MUT)
                                #(Hacl.Impl.Chacha20.Core32xN.uint32xN w35466)
                                st35467)
                            h035469
                            h135471 /\
                          Prims.eq2 #(s35473:
                              Lib.Sequence.seq (Hacl.Impl.Chacha20.Core32xN.uint32xN w35466)
                                { Prims.eq2 #Prims.nat
                                    (FStar.Seq.Base.length #(Hacl.Impl.Chacha20.Core32xN.uint32xN w35466
                                          )
                                        s35473)
                                    (Lib.IntTypes.v #(Lib.IntTypes.U32)
                                        #(Lib.IntTypes.PUB)
                                        16ul) \/
                                  Prims.eq2 #Prims.nat
                                    (FStar.Seq.Base.length #(Hacl.Spec.Chacha20.Vec.uint32xN w35466)
                                        s35473)
                                    16 })
                            (Lib.Buffer.as_seq #(Lib.Buffer.MUT)
                                #(Hacl.Impl.Chacha20.Core32xN.uint32xN w35466)
                                #16ul
                                h135471
                                st35467)
                            (Hacl.Spec.Chacha20.Vec.rounds #w35466
                                (Lib.Buffer.as_seq #(Lib.Buffer.MUT)
                                    #(Hacl.Impl.Chacha20.Core32xN.uint32xN w35466)
                                    #16ul
                                    h035469
                                    st35467)))) #w35464))

let mk_rounds: mk_rounds_t =
  fun
  (#w35421: Hacl.Impl.Chacha20.Core32xN.lanes)
  (arg_Hacl_Impl_Chacha20_Core32xN_double_round35422:
    (fun (#w35424: Hacl.Impl.Chacha20.Core32xN.lanes) ->
        st35425: Hacl.Impl.Chacha20.Core32xN.state w35424
          -> FStar.HyperStack.ST.Stack Prims.unit
              (fun (h35426: FStar.Monotonic.HyperStack.mem) ->
                  Lib.Buffer.live #(Lib.Buffer.MUT)
                    #(Hacl.Impl.Chacha20.Core32xN.uint32xN w35424)
                    h35426
                    st35425)
              (fun
                  (h035427: FStar.Monotonic.HyperStack.mem)
                  (_: Prims.unit)
                  (h135429:
                    (_uu___035430:
                      FStar.Monotonic.HyperStack.mem
                        { Lib.Buffer.live #(Lib.Buffer.MUT)
                            #(Hacl.Impl.Chacha20.Core32xN.uint32xN w35424)
                            h035427
                            st35425 }))
                  ->
                  Lib.Buffer.modifies (Lib.Buffer.loc #(Lib.Buffer.MUT)
                        #(Hacl.Impl.Chacha20.Core32xN.uint32xN w35424)
                        st35425)
                    h035427
                    h135429 /\
                  Prims.eq2 #(s35431:
                      Lib.Sequence.seq (Hacl.Impl.Chacha20.Core32xN.uint32xN w35424)
                        { Prims.eq2 #Prims.nat
                            (FStar.Seq.Base.length #(Hacl.Impl.Chacha20.Core32xN.uint32xN w35424)
                                s35431)
                            (Lib.IntTypes.v #(Lib.IntTypes.U32)
                                #(Lib.IntTypes.PUB)
                                16ul) \/
                          Prims.eq2 #Prims.nat
                            (FStar.Seq.Base.length #(Hacl.Spec.Chacha20.Vec.uint32xN w35424) s35431)
                            16 })
                    (Lib.Buffer.as_seq #(Lib.Buffer.MUT)
                        #(Hacl.Impl.Chacha20.Core32xN.uint32xN w35424)
                        #16ul
                        h135429
                        st35425)
                    (Hacl.Spec.Chacha20.Vec.double_round #w35424
                        (Lib.Buffer.as_seq #(Lib.Buffer.MUT)
                            #(Hacl.Impl.Chacha20.Core32xN.uint32xN w35424)
                            #16ul
                            h035427
                            st35425)))) #w35421)
  (st35423: Hacl.Impl.Chacha20.Core32xN.state w35421)
  ->
  let _uu___35432 = arg_Hacl_Impl_Chacha20_Core32xN_double_round35422 st35423 in
  let _uu___35433 = arg_Hacl_Impl_Chacha20_Core32xN_double_round35422 st35423 in
  let _uu___35434 = arg_Hacl_Impl_Chacha20_Core32xN_double_round35422 st35423 in
  let _uu___35435 = arg_Hacl_Impl_Chacha20_Core32xN_double_round35422 st35423 in
  let _uu___35436 = arg_Hacl_Impl_Chacha20_Core32xN_double_round35422 st35423 in
  let _uu___35437 = arg_Hacl_Impl_Chacha20_Core32xN_double_round35422 st35423 in
  let _uu___35438 = arg_Hacl_Impl_Chacha20_Core32xN_double_round35422 st35423 in
  let _uu___35439 = arg_Hacl_Impl_Chacha20_Core32xN_double_round35422 st35423 in
  let _uu___35440 = arg_Hacl_Impl_Chacha20_Core32xN_double_round35422 st35423 in
  arg_Hacl_Impl_Chacha20_Core32xN_double_round35422 st35423

let mk_core_t =
  #w39947: Hacl.Impl.Chacha20.Core32xN.lanes
  -> Prims.Tot
    (
          arg_Hacl_Impl_Chacha20_Core32xN_double_round39948:
            (fun (#w39960: Hacl.Impl.Chacha20.Core32xN.lanes) ->
                st39961: Hacl.Impl.Chacha20.Core32xN.state w39960
                  -> FStar.HyperStack.ST.Stack Prims.unit
                      (fun (h39962: FStar.Monotonic.HyperStack.mem) ->
                          Lib.Buffer.live #(Lib.Buffer.MUT)
                            #(Hacl.Impl.Chacha20.Core32xN.uint32xN w39960)
                            h39962
                            st39961)
                      (fun
                          (h039963: FStar.Monotonic.HyperStack.mem)
                          (_: Prims.unit)
                          (h139965:
                            (_uu___039966:
                              FStar.Monotonic.HyperStack.mem
                                { Lib.Buffer.live #(Lib.Buffer.MUT)
                                    #(Hacl.Impl.Chacha20.Core32xN.uint32xN w39960)
                                    h039963
                                    st39961 }))
                          ->
                          Lib.Buffer.modifies (Lib.Buffer.loc #(Lib.Buffer.MUT)
                                #(Hacl.Impl.Chacha20.Core32xN.uint32xN w39960)
                                st39961)
                            h039963
                            h139965 /\
                          Prims.eq2 #(s39967:
                              Lib.Sequence.seq (Hacl.Impl.Chacha20.Core32xN.uint32xN w39960)
                                { Prims.eq2 #Prims.nat
                                    (FStar.Seq.Base.length #(Hacl.Impl.Chacha20.Core32xN.uint32xN w39960
                                          )
                                        s39967)
                                    (Lib.IntTypes.v #(Lib.IntTypes.U32)
                                        #(Lib.IntTypes.PUB)
                                        16ul) \/
                                  Prims.eq2 #Prims.nat
                                    (FStar.Seq.Base.length #(Hacl.Spec.Chacha20.Vec.uint32xN w39960)
                                        s39967)
                                    16 })
                            (Lib.Buffer.as_seq #(Lib.Buffer.MUT)
                                #(Hacl.Impl.Chacha20.Core32xN.uint32xN w39960)
                                #16ul
                                h139965
                                st39961)
                            (Hacl.Spec.Chacha20.Vec.double_round #w39960
                                (Lib.Buffer.as_seq #(Lib.Buffer.MUT)
                                    #(Hacl.Impl.Chacha20.Core32xN.uint32xN w39960)
                                    #16ul
                                    h039963
                                    st39961)))) #w39947
        -> Prims.Tot
          ((fun (#w39949: Hacl.Impl.Chacha20.Core32xN.lanes) ->
                    k39950: Hacl.Impl.Chacha20.Core32xN.state w39949 ->
                    ctx039951: Hacl.Impl.Chacha20.Core32xN.state w39949 ->
                    ctr39952:
                      (ctr39959:
                      Lib.IntTypes.size_t
                        { Prims.b2t (w39949 *
                              Lib.IntTypes.v #(Lib.IntTypes.U32) #(Lib.IntTypes.PUB) ctr39959 <=
                              Lib.IntTypes.max_size_t) })
                  -> FStar.HyperStack.ST.Stack Prims.unit
                      (fun (h39953: FStar.Monotonic.HyperStack.mem) ->
                          Lib.Buffer.live #(Lib.Buffer.MUT)
                            #(Hacl.Impl.Chacha20.Core32xN.uint32xN w39949)
                            h39953
                            ctx039951 /\
                          Lib.Buffer.live #(Lib.Buffer.MUT)
                            #(Hacl.Impl.Chacha20.Core32xN.uint32xN w39949)
                            h39953
                            k39950 /\
                          Lib.Buffer.disjoint #(Lib.Buffer.MUT)
                            #(Lib.Buffer.MUT)
                            #(Hacl.Impl.Chacha20.Core32xN.uint32xN w39949)
                            #(Hacl.Impl.Chacha20.Core32xN.uint32xN w39949)
                            ctx039951
                            k39950)
                      (fun
                          (h039954: FStar.Monotonic.HyperStack.mem)
                          (_: Prims.unit)
                          (h139956:
                            (_uu___039957:
                              FStar.Monotonic.HyperStack.mem
                                { Lib.Buffer.live #(Lib.Buffer.MUT)
                                    #(Hacl.Impl.Chacha20.Core32xN.uint32xN w39949)
                                    h039954
                                    ctx039951 /\
                                  Lib.Buffer.live #(Lib.Buffer.MUT)
                                    #(Hacl.Impl.Chacha20.Core32xN.uint32xN w39949)
                                    h039954
                                    k39950 /\
                                  Lib.Buffer.disjoint #(Lib.Buffer.MUT)
                                    #(Lib.Buffer.MUT)
                                    #(Hacl.Impl.Chacha20.Core32xN.uint32xN w39949)
                                    #(Hacl.Impl.Chacha20.Core32xN.uint32xN w39949)
                                    ctx039951
                                    k39950 }))
                          ->
                          Lib.Buffer.modifies (Lib.Buffer.loc #(Lib.Buffer.MUT)
                                #(Hacl.Impl.Chacha20.Core32xN.uint32xN w39949)
                                k39950)
                            h039954
                            h139956 /\
                          Prims.eq2 #(s39958:
                              Lib.Sequence.seq (Hacl.Impl.Chacha20.Core32xN.uint32xN w39949)
                                { Prims.eq2 #Prims.nat
                                    (FStar.Seq.Base.length #(Hacl.Impl.Chacha20.Core32xN.uint32xN w39949
                                          )
                                        s39958)
                                    (Lib.IntTypes.v #(Lib.IntTypes.U32)
                                        #(Lib.IntTypes.PUB)
                                        16ul) \/
                                  Prims.eq2 #Prims.nat
                                    (FStar.Seq.Base.length #(Hacl.Spec.Chacha20.Vec.uint32xN w39949)
                                        s39958)
                                    16 })
                            (Lib.Buffer.as_seq #(Lib.Buffer.MUT)
                                #(Hacl.Impl.Chacha20.Core32xN.uint32xN w39949)
                                #16ul
                                h139956
                                k39950)
                            (Hacl.Spec.Chacha20.Vec.chacha20_core #w39949
                                (Lib.IntTypes.v #(Lib.IntTypes.U32) #(Lib.IntTypes.PUB) ctr39952)
                                (Lib.Buffer.as_seq #(Lib.Buffer.MUT)
                                    #(Hacl.Impl.Chacha20.Core32xN.uint32xN w39949)
                                    #16ul
                                    h039954
                                    ctx039951)))) #w39947))

let mk_core: mk_core_t =
  fun
  (#w39900: Hacl.Impl.Chacha20.Core32xN.lanes)
  (arg_Hacl_Impl_Chacha20_Core32xN_double_round39901:
    (fun (#w39905: Hacl.Impl.Chacha20.Core32xN.lanes) ->
        st39906: Hacl.Impl.Chacha20.Core32xN.state w39905
          -> FStar.HyperStack.ST.Stack Prims.unit
              (fun (h39907: FStar.Monotonic.HyperStack.mem) ->
                  Lib.Buffer.live #(Lib.Buffer.MUT)
                    #(Hacl.Impl.Chacha20.Core32xN.uint32xN w39905)
                    h39907
                    st39906)
              (fun
                  (h039908: FStar.Monotonic.HyperStack.mem)
                  (_: Prims.unit)
                  (h139910:
                    (_uu___039911:
                      FStar.Monotonic.HyperStack.mem
                        { Lib.Buffer.live #(Lib.Buffer.MUT)
                            #(Hacl.Impl.Chacha20.Core32xN.uint32xN w39905)
                            h039908
                            st39906 }))
                  ->
                  Lib.Buffer.modifies (Lib.Buffer.loc #(Lib.Buffer.MUT)
                        #(Hacl.Impl.Chacha20.Core32xN.uint32xN w39905)
                        st39906)
                    h039908
                    h139910 /\
                  Prims.eq2 #(s39912:
                      Lib.Sequence.seq (Hacl.Impl.Chacha20.Core32xN.uint32xN w39905)
                        { Prims.eq2 #Prims.nat
                            (FStar.Seq.Base.length #(Hacl.Impl.Chacha20.Core32xN.uint32xN w39905)
                                s39912)
                            (Lib.IntTypes.v #(Lib.IntTypes.U32)
                                #(Lib.IntTypes.PUB)
                                16ul) \/
                          Prims.eq2 #Prims.nat
                            (FStar.Seq.Base.length #(Hacl.Spec.Chacha20.Vec.uint32xN w39905) s39912)
                            16 })
                    (Lib.Buffer.as_seq #(Lib.Buffer.MUT)
                        #(Hacl.Impl.Chacha20.Core32xN.uint32xN w39905)
                        #16ul
                        h139910
                        st39906)
                    (Hacl.Spec.Chacha20.Vec.double_round #w39905
                        (Lib.Buffer.as_seq #(Lib.Buffer.MUT)
                            #(Hacl.Impl.Chacha20.Core32xN.uint32xN w39905)
                            #16ul
                            h039908
                            st39906)))) #w39900)
  (k39902: Hacl.Impl.Chacha20.Core32xN.state w39900)
  (ctx39903: Hacl.Impl.Chacha20.Core32xN.state w39900)
  (ctr39904:
    (ctr39913:
      Lib.IntTypes.size_t
        { Prims.b2t (w39900 * Lib.IntTypes.v #(Lib.IntTypes.U32) #(Lib.IntTypes.PUB) ctr39913 <=
              Lib.IntTypes.max_size_t) }))
  ->
  let _uu___39914 = Hacl.Impl.Chacha20.Core32xN.copy_state #w39900 k39902 ctx39903 in
  let ctr_u3239915 =
    Lib.IntTypes.op_Star_Bang #(Lib.IntTypes.U32)
      #(Lib.IntTypes.SEC)
      (Lib.IntTypes.u32 w39900)
      (Lib.IntTypes.size_to_uint32 ctr39904)
  in
  let cv39916 = Lib.IntVector.vec_load #(Lib.IntTypes.U32) ctr_u3239915 w39900 in
  let _uu___39917 =
    let _uu___39918 =
      let _uu___39919 =
        Lib.Buffer.op_Array_Access #(Lib.Buffer.MUT)
          #(Hacl.Impl.Chacha20.Core32xN.uint32xN w39900)
          #16ul
          k39902
          12ul
      in
      Lib.IntVector.op_Plus_Bar #(Lib.IntTypes.U32) #w39900 _uu___39919 cv39916
    in
    Lib.Buffer.op_Array_Assignment #(Hacl.Impl.Chacha20.Core32xN.uint32xN w39900)
      #16ul
      k39902
      12ul
      _uu___39918
  in
  let _uu___39920 =
    mk_rounds #w39900 arg_Hacl_Impl_Chacha20_Core32xN_double_round39901 k39902
  in
  let _uu___39921 = Hacl.Impl.Chacha20.Core32xN.sum_state #w39900 k39902 ctx39903 in
  let _uu___39922 =
    let _uu___39923 =
      Lib.Buffer.op_Array_Access #(Lib.Buffer.MUT)
        #(Hacl.Impl.Chacha20.Core32xN.uint32xN w39900)
        #16ul
        k39902
        12ul
    in
    Lib.IntVector.op_Plus_Bar #(Lib.IntTypes.U32) #w39900 _uu___39923 cv39916
  in
  Lib.Buffer.op_Array_Assignment #(Hacl.Impl.Chacha20.Core32xN.uint32xN w39900)
    #16ul
    k39902
    12ul
    _uu___39922

let double_round_32 = mk_double_round #1
let core_32 = mk_core #1 double_round_32

// This sends F* into a loop!

%splice[
  chacha20_core_inline
] (MetaInterface.specialize [ `Hacl.Impl.Chacha20.Vec.chacha20_core ])
