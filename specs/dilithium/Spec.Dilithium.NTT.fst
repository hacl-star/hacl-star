module Spec.Dilithium.NTT

open Spec.Dilithium.Params
open Spec.Dilithium.Poly
open Spec.Dilithium.Montgomery

open FStar.Mul
open FStar.Math.Lemmas
open Lib.IntTypes
open Lib.RawIntTypes
open Lib.Sequence
open Lib.ByteSequence
open Lib.LoopCombinators

#reset-options "--z3rlimit 100 --max_fuel 0"

// magic constants, should add some sort of formula for these

let zetas_list = normalize_term (List.Tot.map u32 [0; 25847; 5771523; 7861508; 237124; 7602457; 7504169; 466468; 1826347; 2353451; 8021166; 6288512; 3119733; 5495562; 3111497; 2680103; 2725464; 1024112; 7300517; 3585928; 7830929; 7260833; 2619752; 6271868; 6262231; 4520680; 6980856; 5102745; 1757237; 8360995; 4010497; 280005; 2706023; 95776; 3077325; 3530437; 6718724; 4788269; 5842901; 3915439; 4519302; 5336701; 3574422; 5512770; 3539968; 8079950; 2348700; 7841118; 6681150; 6736599; 3505694; 4558682; 3507263; 6239768; 6779997; 3699596; 811944; 531354; 954230; 3881043; 3900724; 5823537; 2071892; 5582638; 4450022; 6851714; 4702672; 5339162; 6927966; 3475950; 2176455; 6795196; 7122806; 1939314; 4296819; 7380215; 5190273; 5223087; 4747489; 126922; 3412210; 7396998; 2147896; 2715295; 5412772; 4686924; 7969390; 5903370; 7709315; 7151892; 8357436; 7072248; 7998430; 1349076; 1852771; 6949987; 5037034; 264944; 508951; 3097992; 44288; 7280319; 904516; 3958618; 4656075; 8371839; 1653064; 5130689; 2389356; 8169440; 759969; 7063561; 189548; 4827145; 3159746; 6529015; 5971092; 8202977; 1315589; 1341330; 1285669; 6795489; 7567685; 6940675; 5361315; 4499357; 4751448; 3839961; 2091667; 3407706; 2316500; 3817976; 5037939; 2244091; 5933984; 4817955; 266997; 2434439; 7144689; 3513181; 4860065; 4621053; 7183191; 5187039; 900702; 1859098; 909542; 819034; 495491; 6767243; 8337157; 7857917; 7725090; 5257975; 2031748; 3207046; 4823422; 7855319; 7611795; 4784579; 342297; 286988; 5942594; 4108315; 3437287; 5038140; 1735879; 203044; 2842341; 2691481; 5790267; 1265009; 4055324; 1247620; 2486353; 1595974; 4613401; 1250494; 2635921; 4832145; 5386378; 1869119; 1903435; 7329447; 7047359; 1237275; 5062207; 6950192; 7929317; 1312455; 3306115; 6417775; 7100756; 1917081; 5834105; 7005614; 1500165; 777191; 2235880; 3406031; 7838005; 5548557; 6709241; 6533464; 5796124; 4656147; 594136; 4603424; 6366809; 2432395; 2454455; 8215696; 1957272; 3369112; 185531; 7173032; 5196991; 162844; 1616392; 3014001; 810149; 1652634; 4686184; 6581310; 5341501; 3523897; 3866901; 269760; 2213111; 7404533; 1717735; 472078; 7953734; 1723600; 6577327; 1910376; 6712985; 7276084; 8119771; 4546524; 5441381; 6144432; 7959518; 6094090; 183443; 7403526; 1612842; 4834730; 7826001; 3919660; 8332111; 7018208; 3937738; 1400424; 7534263; 1976782 ])

let zetas:poly = assert_norm (List.Tot.length zetas_list = param_n); of_list zetas_list

let izetas_list = normalize_term (List.Tot.map u32 [6403635; 846154; 6979993; 4442679; 1362209; 48306; 4460757; 554416; 3545687; 6767575; 976891; 8196974; 2286327; 420899; 2235985; 2939036; 3833893; 260646; 1104333; 1667432; 6470041; 1803090; 6656817; 426683; 7908339; 6662682; 975884; 6167306; 8110657; 4513516; 4856520; 3038916; 1799107; 3694233; 6727783; 7570268; 5366416; 6764025; 8217573; 3183426; 1207385; 8194886; 5011305; 6423145; 164721; 5925962; 5948022; 2013608; 3776993; 7786281; 3724270; 2584293; 1846953; 1671176; 2831860; 542412; 4974386; 6144537; 7603226; 6880252; 1374803; 2546312; 6463336; 1279661; 1962642; 5074302; 7067962; 451100; 1430225; 3318210; 7143142; 1333058; 1050970; 6476982; 6511298; 2994039; 3548272; 5744496; 7129923; 3767016; 6784443; 5894064; 7132797; 4325093; 7115408; 2590150; 5688936; 5538076; 8177373; 6644538; 3342277; 4943130; 4272102; 2437823; 8093429; 8038120; 3595838; 768622; 525098; 3556995; 5173371; 6348669; 3122442; 655327; 522500; 43260; 1613174; 7884926; 7561383; 7470875; 6521319; 7479715; 3193378; 1197226; 3759364; 3520352; 4867236; 1235728; 5945978; 8113420; 3562462; 2446433; 6136326; 3342478; 4562441; 6063917; 4972711; 6288750; 4540456; 3628969; 3881060; 3019102; 1439742; 812732; 1584928; 7094748; 7039087; 7064828; 177440; 2409325; 1851402; 5220671; 3553272; 8190869; 1316856; 7620448; 210977; 5991061; 3249728; 6727353; 8578; 3724342; 4421799; 7475901; 1100098; 8336129; 5282425; 7871466; 8115473; 3343383; 1430430; 6527646; 7031341; 381987; 1308169; 22981; 1228525; 671102; 2477047; 411027; 3693493; 2967645; 5665122; 6232521; 983419; 4968207; 8253495; 3632928; 3157330; 3190144; 1000202; 4083598; 6441103; 1257611; 1585221; 6203962; 4904467; 1452451; 3041255; 3677745; 1528703; 3930395; 2797779; 6308525; 2556880; 4479693; 4499374; 7426187; 7849063; 7568473; 4680821; 1600420; 2140649; 4873154; 3821735; 4874723; 1643818; 1699267; 539299; 6031717; 300467; 4840449; 2867647; 4805995; 3043716; 3861115; 4464978; 2537516; 3592148; 1661693; 4849980; 5303092; 8284641; 5674394; 8100412; 4369920; 19422; 6623180; 3277672; 1399561; 3859737; 2118186; 2108549; 5760665; 1119584; 549488; 4794489; 1079900; 7356305; 5654953; 5700314; 5268920; 2884855; 5260684; 2091905; 359251; 6026966; 6554070; 7913949; 876248; 777960; 8143293; 518909; 2608894; 8354570; 0])

let izetas:poly = assert_norm (List.Tot.length izetas_list = param_n); of_list izetas_list



(*****************************
            NTT
******************************)

val ntt_loop3:
    len: nat {len <= 128}
  -> zeta: uint32
  -> start: nat {start + len + len <= param_n}
  -> j: nat {j < start + len}
  -> p: poly
  -> Tot poly (decreases (start + len - j))

let rec ntt_loop3 len zeta start j p =
  let (x:uint64) = ((to_u64 zeta) *. (to_u64 p.[j+len])) in
  let t = montgomery_reduce x in
  let p = p.[j + len] <- p.[j] +. u32 (2 * param_q) -. t in
  let p = p.[j] <- p.[j] +. t in
  if j + 1 < start + len
    then ntt_loop3 len zeta start (j+1) p
    else p


val loop2_lemma_bound_n: i: nat {i < 8} -> j: nat {j < pow2 (7 - i)}
  -> len: nat {len = pow2 i} -> start: nat {start = j * (len + len)}
  -> Lemma (j * (len + len) < param_n)

let loop2_lemma_bound_n i j len start =
  calc (<) {
    j * (len + len);
    = {pow2_double_sum i}
    j * pow2 (i+1);
    < {}
    pow2 (7-i) * pow2 (i+1);
    = {pow2_plus (7-i) (i+1)}
    pow2 8;
    = {assert_norm (param_n = pow2 8)}
    param_n;
  }


let ntt_k_of_i (i:nat {i < 8}) = pow2 (7 - i)


val ntt_loop2:
  // i and j exist purely for proofs, use Ghost.erased or smth?
    i: nat {i < 8}
  -> j: nat {j < pow2 (7 - i)}
  -> len: nat {len = pow2 i}
  -> start: nat {start = j * (len + len)}
  -> k: nat {k = ntt_k_of_i i + j}
  -> p: poly
  -> Tot (kn:(nat & poly) {let k,n = kn in k = ntt_k_of_i i + ntt_k_of_i i}) (decreases (param_n - start))

let rec ntt_loop2 i j len start k p =
  pow2_double_sum i;
  pow2_plus (7-i) (i+1);
  assert (pow2 (7-i) * (len + len) <= param_n);
  loop2_lemma_bound_n i j len start;
  assert (start < pow2 8);
  pow2_le_compat 7 i;
  assert_norm (pow2 7 = 128);
  assert (len <= 128);
  assert (k < ntt_k_of_i i + pow2 (7 - i));
  pow2_lt_compat (8 - i) (7 - i);
  assert (ntt_k_of_i i + pow2 (7 - i) <= param_n);
  let p = ntt_loop3 len (zetas.[k]) start start p in
  let start = start + len + len in
  assert (start = (j+1) * (len + len));
  assert (j+1 = pow2 (7-i) ==> start = param_n);
  if start < param_n
    then ntt_loop2 i (j+1) len start (k+1) p
    else ((k+1), p)


val ntt_loop1:
    i: nat {i < 8}
  -> k: nat {k = ntt_k_of_i i}
  -> len: nat {len = pow2 i}
  -> p: poly
  -> Tot poly

let rec ntt_loop1 i k len p =
  let k, p = ntt_loop2 i 0 len 0 k p in
  pow2_double_sum (7 - i);
  let len = len / 2 in
  if len > 0 then (
    assert (i >= 1);
    assert_norm (pow2 1 = 2);
    pow2_minus i 1;
    assert (pow2 i / 2 = pow2 (i-1));
    assert (k = pow2 (7 - (i-1)));
    ntt_loop1 (i-1) k len p
  ) else p

val ntt: p:poly -> poly

let ntt p = assert_norm (pow2 7 = 128); ntt_loop1 7 1 128 p

let polyvecl_ntt = map #poly #poly #param_l ntt
let polyveck_ntt = map #poly #poly #param_k ntt


(*****************************
        Inverse NTT
******************************)

val intt_loop3:
    len: nat {len <= 128}
  -> zeta: uint32
  -> start: nat {start + len + len <= param_n}
  -> j: nat {j < start + len}
  -> p: poly
  -> Tot poly (decreases (start + len - j))

let rec intt_loop3 len zeta start j p =
  let t = p.[j] in
  let p = p.[j] <- t +. p.[j + len] in
  let p = p.[j + len] <- t +. u32 (256*param_q) -. p.[j + len] in
  let p = p.[j + len] <- montgomery_reduce (to_u64 zeta *. to_u64 p.[j + len]) in
  if j + 1 < start + len
    then intt_loop3 len zeta start (j+1) p
    else p


let intt_k_of_i (i:nat {i < 8}) = param_n - pow2 (8 - i)


val intt_loop2:
  // i and j exist purely for proofs
    i: nat {i < 8}
  -> j: nat {j < pow2 (7 - i)}
  -> len: nat {len = pow2 i}
  -> start: nat {start = j * (len + len)}
  -> k: nat {k = intt_k_of_i i + j}
  -> p: poly
  -> Tot (kn:(nat & poly) {let k,n = kn in k = intt_k_of_i i + pow2 (7 - i)}) (decreases (param_n - start))

let rec intt_loop2 i j len start k p =
  pow2_double_sum i;
  pow2_plus (7-i) (i+1);
  assert (pow2 (7-i) * (len + len) <= param_n);
  loop2_lemma_bound_n i j len start;
  assert (start < pow2 8);
  pow2_le_compat 7 i;
  assert_norm (pow2 7 = 128);
  assert (len <= 128);
  assert (k < intt_k_of_i i + pow2 (7 - i));
  pow2_lt_compat (8 - i) (7 - i);
  assert (intt_k_of_i i + pow2 (7 - i) <= param_n);
  let p = intt_loop3 len (izetas.[k]) start start p in
  let start = start + len + len in
  assert (start = (j+1) * (len + len));
  assert (j+1 = pow2 (7-i) ==> start = param_n);
  if start < param_n
    then intt_loop2 i (j+1) len start (k+1) p
    else ((k+1), p)


val intt_loop1:
    i: nat {i < 8}
  -> k: nat {k = intt_k_of_i i}
  -> len: nat {len = pow2 i}
  -> p: poly
  -> Tot poly (decreases (param_n - len))

let rec intt_loop1 i k len p =
  let k, p = intt_loop2 i 0 len 0 k p in
  pow2_double_sum (7 - i);
  let len = len * 2 in
  if len < param_n then (
    pow2_double_mult i;
    intt_loop1 (i+1) k len p
  ) else p


let intt_const_f = (((mont * mont) % param_q) * (param_q-1) % param_q) * ((param_q - 1) / pow2 8) % param_q


val intt_tomont: p:poly -> poly

let intt_tomont p =
  assert_norm (pow2 7 = 128);
  let p = intt_loop1 0 0 1 p in
  map #uint32 #uint32 #param_n (fun x -> montgomery_reduce (u64 intt_const_f *. to_u64 x)) p


let polyvecl_intt_tomont = map #poly #poly #param_l intt_tomont
let polyveck_intt_tomont = map #poly #poly #param_k intt_tomont

let poly_poly_mul (p1:poly) (p2:poly) : poly =
  intt_tomont (poly_pointwise_mont (ntt p1) (ntt p2))
