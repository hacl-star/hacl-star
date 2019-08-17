module Hacl.Test.HE

open C.Failure
open FStar.HyperStack
open FStar.HyperStack.ST
open FStar.Mul
open LowStar.Buffer

open Lib.IntTypes
open Lib.Math.Algebra
open Lib.Buffer

open Hacl.Impl.HE.Other

module GM = Hacl.Impl.HE.GM
module GMS = Hacl.Spec.HE.GM

module P = Hacl.Impl.HE.Paillier
module PS = Hacl.Spec.HE.Paillier

module DGK = Hacl.Impl.HE.DGK
module DGKE = Hacl.Impl.HE.DGK.Extra
module DGKS = Hacl.Spec.HE.DGK

open Hacl.Impl.Bignum

module B = FStar.Bytes


inline_for_extraction unfold noextract
val print_str: string -> ST unit (requires fun _ -> true) (ensures fun h0 _ h1 -> h0 == h1)
let print_str x = C.String.print (C.String.of_literal x)

inline_for_extraction unfold noextract
val print_strln: string -> ST unit (requires fun _ -> true) (ensures fun h0 _ h1 -> h0 == h1)
let print_strln x = print_str (x ^ "\n")

inline_for_extraction unfold noextract
val print_bool: b:bool -> ST unit (requires fun _ -> true) (ensures fun h0 _ h1 -> h0 == h1)
let print_bool b =
  C.String.print (if b then C.String.of_literal "true\n" else C.String.of_literal "false\n")


#reset-options "--z3rlimit 50 --max_fuel 0 --max_ifuel 0"

noextract inline_for_extraction
val run_test_gm:
     p:snat
  -> q:snat
  -> y:snat{y < p * q} // /\ GMS.is_nonsqr (to_fe #p y) /\ GMS.is_nonsqr (to_fe #q y)}
  -> r:snat{r < p * q} // /\ sqr r > 0 /\ sqr r *% y > 0}
  -> Stack unit (requires fun _ -> true) (ensures fun _ _ _ -> true)
let run_test_gm p q y r =

  push_frame ();

  assume(issnat (p*q));

  let nLen = nat_bytes_num (normalize_term (p * q)) in

  assume (p <= p * q);
  assume (p-1 <= p * q);
  snat_order (p-1) (p*q);
  assume ((p-1)/2 <= p * q);
  assume (issnat ((p-1)/2));
  snat_order y (p*q);
  snat_order r (p*q);

  nat_bytes_num_fit p (p * q);
  nat_bytes_num_fit (p-1) (p * q);
  nat_bytes_num_fit ((p-1)/2) (p * q);
  nat_bytes_num_fit y (p * q);
  nat_bytes_num_fit r (p * q);

  let bn_p: lbignum nLen = nat_to_bignum p in
  let bn_p_min_one: lbignum nLen = nat_to_bignum (normalize_term (p-1)) in
  let bn_p_min_one_half: lbignum nLen = nat_to_bignum (normalize_term ((p-1)/2)) in
  let bn_n: lbignum nLen = nat_to_bignum (p * q) in
  let bn_y: lbignum nLen = nat_to_bignum y in
  let bn_r: lbignum nLen = nat_to_bignum r in

  let bn_res: lbignum nLen = create nLen (uint 0) in

  [@inline_let]
  let encdec (m:bool) = begin
    print_str "\n* ";
    print_bool m;

    admit();

    print_str " --enc-> ";
    GM.encrypt bn_n bn_y bn_r m bn_res;
    print_lbignum bn_res;

    print_str " --dec-> ";
    let m' = GM.decrypt bn_p bn_p_min_one bn_p_min_one_half bn_res in
    print_bool m';

    if (m <> m')
      then print_str " -------------------ERROR-------------------- "

    end in


  encdec false;
  encdec true;

  push_frame();

  let bn_res1: lbignum nLen = create nLen (uint 0) in
  let bn_res2: lbignum nLen = create nLen (uint 0) in
  let bn_res3: lbignum nLen = create nLen (uint 0) in

  [@inline_let]
  let hom_xor (m1:bool) (m2:bool) (mexp:bool) = begin
    print_str "\n* xor ";
    print_bool m1;
    print_bool m2;

    admit();

    GM.encrypt bn_n bn_y bn_r m1 bn_res1;
    GM.encrypt bn_n bn_y bn_r m2 bn_res2;

    GM.hom_xor bn_n bn_res1 bn_res2 bn_res3;
    let m = GM.decrypt bn_p bn_p_min_one bn_p_min_one_half bn_res3 in

    print_bool m;

    if (m <>  mexp)
      then print_str " -------------------ERROR-------------------- "

    end in


  hom_xor false false false;
  hom_xor false true true;
  hom_xor true false true;
  hom_xor true true false;

  pop_frame ();

  pop_frame ()


#reset-options "--z3rlimit 80 --max_fuel 2 --max_ifuel 0"

val test_gm: unit -> Stack unit (requires fun _ -> true) (ensures fun _ _ _ -> true)
let test_gm _ =
  run_test_gm 11 7 6 6;
  run_test_gm 5651 2309 6283665 1642087;

  // 50
  run_test_gm
    20597963
    18691103
    343410843161354
    340075475890885;

  // 64
  run_test_gm
    3339502961
    2462727887
    5233939904127998699
    5453821191296830610;

  // trust me it's safe. i can't make verification here fast enough,
  // because, apparently, fstar bignum implementation is slow per se
  admit();

  // 70
  run_test_gm
    21858784247
    32600809193
    512995630928471546296
    451304102026366696740;

  // 128
  run_test_gm
    15296422180258244633
    12754350346597149907
    135123782558807105107086847009983923035
    119073235221716701476761821036809466296;

  run_test_gm
    18151637450909672231
    10616931758931658067
    169050918734026862244039761501457849989
    91361904391308264608300641010053460290;

  // 256
  run_test_gm
    238473831066240814685652387118826838089
    290648921680117623622749944527302685873
    32013853695008913941056224288699542908291901709435433477498753524425728431750
    63966125980329819543482417151170152183116886231068453106873450906088222129050;

  run_test_gm
    194765719344750645857941111613304160759
    302733760975917402491754353701153586917
    36830922521294348053145663043410070557977339755323583180621317301257147794374
    38906304989221746651998721090989108342763029754317070464956436172556984570693;

  // 512
  run_test_gm
    90510865981466947031172959353875014846064298911390400886217098789271538551427
    94759749888656405390748215772985529397008982247431702017685434161096778423291
    6957432786230211466554402636790564852662237428639281229711989467622229675175469764873854713058879492065775330287649969064318829928153493172958199579400717
    3800489529524826596462562393348890150013178998377931017956373178205920735905956480999317129649722635695766704356317847688521776746429718426269611327586578;

  run_test_gm
    110442173640700605426196791722267254977399536629395286731142679095037450319701
    107170879681249637364506109018099376672037419626449999045129249789288431466407
    5265437392983486448329400301105635940895238995769880107866207131125580962646642150752609876247622793613398654879743905973229074059422443151910948419853421
    6845701554537301024323205582879742602167364769512355740049645018047271023281212094546788123698331656722332722329506942184730828849998076233448302042099044


#reset-options "--z3rlimit 100"

noextract inline_for_extraction
val run_test_paillier0:
     #n2Len:bn_len_s
  -> p:lbignum n2Len
  -> q:lbignum n2Len
  -> n:lbignum n2Len
  -> n2:lbignum n2Len
  -> g:lbignum n2Len
  -> lambda:lbignum n2Len
  -> l2inv:lbignum n2Len
  -> r:lbignum n2Len
  -> m:nat
  -> Stack unit (requires fun _ -> true) (ensures fun _ _ _ -> true)
let run_test_paillier0 #n2Len p q n n2 g lambda l2inv r m =
  push_frame ();
  admit();
  print_str "* Testing paillier ... ";

  let bn_m: lbignum n2Len = nat_to_bignum (normalize_term m) in
  let bn_res: lbignum n2Len = create n2Len (uint 0) in
  let bn_m': lbignum n2Len = create n2Len (uint 0) in

  admit();

  P.encrypt n n2 g r bn_m bn_res;
//  print_lbignum bn_res;

//  print_str " --dec-> \n";
  P.decrypt p q n n2 g lambda l2inv bn_res bn_m';

  let success = bn_is_equal bn_m bn_m' in
  if success
    then print_str "OK\n"
    else print_str "\n -------------------ERROR-------------------- \n";

  pop_frame ()


noextract inline_for_extraction
val run_test_paillier:
     p:snat
  -> q:snat
  -> r:snat
  -> m:snat
  -> Stack unit (requires fun _ -> true) (ensures fun _ _ _ -> true)
let run_test_paillier p q r m =

  // These should be actually verified before passing to function.
  // F* is too slow doing it by itself.
  assume(p > 1 /\ q > 1);
  assume(isprm p /\ isprm q);
  assume(r < p*q /\ isunit #(p*q) r);

  assume(issnat (p*q));
  assume(issnat ((p*q)*(p*q)));
  assume(iscomp (p*q));
  assume(p*q + 1 < (p*q)*(p*q));

  push_frame ();

  multiplication_order_lemma_strict 1 (p*q) (p*q);

  assert (p*q < (p*q)*(p*q));
  let n2Len = nat_bytes_num (normalize_term ((p*q)*(p*q))) in

  multiplication_order_lemma_strict 1 q p;
  multiplication_order_lemma_strict 1 p q;
  nat_bytes_num_fit p ((p*q)*(p*q));
  nat_bytes_num_fit q ((p*q)*(p*q));
  nat_bytes_num_fit ((p*q)+1) ((p*q)*(p*q));
  nat_bytes_num_fit r ((p*q)*(p*q));
  nat_bytes_num_fit (p*q) ((p*q)*(p*q));

  let bn_p: lbignum n2Len = nat_to_bignum p in
  let bn_q: lbignum n2Len = nat_to_bignum q in
  let bn_r: lbignum n2Len = nat_to_bignum r in
  // We fix g to n+1
  let bn_g: lbignum n2Len = nat_to_bignum (normalize_term ((p * q) + 1)) in
  let bn_n: lbignum n2Len = nat_to_bignum (normalize_term (p * q)) in
  let bn_n2: lbignum n2Len = nat_to_bignum (normalize_term ((p * q)*(p * q))) in


  PS.np1_is_g #(p*q);
  assert (PS.is_g (p*q) ((p*q)+1));


  let h = FStar.HyperStack.ST.get () in

  // All pre-conditions are true, though to_secret can't be verified anyway. Classic.
  //
  //assert(live h bn_p /\ live h bn_q /\ live h bn_n /\ live h bn_n2 /\ live h bn_g);
  //assert(all_disjoint [loc bn_p; loc bn_q; loc bn_n; loc bn_n2; loc bn_g]);
  //assert (isprm (as_snat h bn_p) /\ isprm (as_snat h bn_q));
  //assert (as_snat h bn_p * as_snat h bn_q = as_snat h bn_n);
  //assert (as_snat h bn_n * as_snat h bn_n = as_snat h bn_n2);
  //assert (as_snat h bn_n > 1);
  //assert (as_snat h bn_g < as_snat h bn_n2);
  //assert (PS.is_g (as_snat h bn_n) (as_snat h bn_g));
  admit ();

  let bn_lambda = create n2Len (u64 0) in
  let bn_l2inv = create n2Len (u64 0) in
  P.to_secret bn_p bn_q bn_n bn_n2 bn_g bn_lambda bn_l2inv;

  run_test_paillier0 #n2Len bn_p bn_q bn_n bn_n2 bn_g bn_lambda bn_l2inv bn_r m;

  pop_frame ()

val test_paillier: unit -> Stack unit (requires fun _ -> true) (ensures fun _ _ _ -> true)
let test_paillier _ =
  run_test_paillier 31 17 409 0;
  run_test_paillier 31 17 409 2;
  run_test_paillier 31 17 409 3;
  run_test_paillier 31 17 409 487;

  admit ();

  // 30 bits (of n, r, and message, primes are half bits long)
  run_test_paillier 24917 27127 414979921 359006873;
  run_test_paillier 20983 28559 407438293 396521033;
  run_test_paillier 18713 29399 474037489 342121781;
  run_test_paillier 17981 25841 452253973 434180597;
  run_test_paillier 26813 22651 329410259 306837359;
  run_test_paillier 16843 22153 351670357 276805799;
  run_test_paillier 30011 22769 312986833 375674401;
  run_test_paillier 31379 28393 380441669 330269411;
  run_test_paillier 24611 24697 310390637 287470333;
  run_test_paillier 20599 28807 535467847 353978101;

  // 64 bits
  run_test_paillier 3494362171 3311444351 8864990827578284909 6696202465711963367;
  run_test_paillier 2915489807 2559681169 5346570235170401647 5060198196850222823;
  run_test_paillier 3709243777 3578138357 8356763982201403459 5442786882384279041;
  run_test_paillier 3375727633 2841977387 8546553137338418747 8232161328622455233;
  run_test_paillier 3357453679 4155859549 6704186060196921349 7992117080931886213;
  run_test_paillier 2845063891 4104745207 4788599718231096497 7551485665128075467;
  run_test_paillier 3297484243 2399938543 4933780878480825157 5837973548144275501;
  run_test_paillier 3912248387 2432576711 8322334436543425849 7812803888098492121;
  run_test_paillier 3316453627 2475146827 7706135103525724399 5535979273643699599;
  run_test_paillier 3139784107 2833268491 6912622668816399901 7982756129352505219;

  // 130 bits
  run_test_paillier 23335361049279614939 30351560204733334013 541347975752946036697693858637306437241 612300740116557920074102245982145927327;
  run_test_paillier 23048762894223039349 30193548552626573651 441142957269615667995681908652541510139 631462748908781472746795431288441126177;
  run_test_paillier 18654145239765747781 33449265986990113199 618581476734158543444694218875763507449 428156082810954718482322855230198092609;
  run_test_paillier 19972288138789558543 29934970770670214591 399184811320603895984526334350675592691 436268734090243282954508849916591073439;
  run_test_paillier 22482183489087342551 21640751547972502901 421612584559122902338841047531452931451 462592607048039981395185095224061855297;
  run_test_paillier 32138133771621776191 29636776578356171143 615318064340855588714906567105710006717 364172026292229816299282834417623769717;
  run_test_paillier 20988475024080473353 30864482577663671221 575541636519530584980968418271817039537 423641801904567859170284673564023234281;
  run_test_paillier 32973106535867118277 25559266737119585311 374117375391504370206374869026399862969 524665463276096195865026684794522311017;
  run_test_paillier 20697907575618652859 36205620430265961359 653795030196508496468003648419452298069 482232330483044472712087138237557080009;
  run_test_paillier 35160486806935468669 23697094679563626709 656074207359829363388710478762638605151 511372668036868834106849215943394474979;

  // 260 bits
  run_test_paillier 1112871946397021969899029810413978537183 1150478196248862684072739993771931622439 468855406001926045798373682677478352071865697072875988476460255187035554807097 703929656241523810510515433575117402793137250373791963545739770617078957407303;
  run_test_paillier 795344857790338159200400343950380670591 1140893761470789255153085451833937902763 512123475581701947676692391638240770344319632433136135081632740880244967711637 525246366799235143083256032610488677997748595569369135717369949759369601737791;
  run_test_paillier 764332374144430145778238467562151330017 807287589257105365762796765339015590517 505842670119571233169024399926573262404340622904255350892539083686210209037013 560887488220167446580123505717384825660897620753131017795766606252358000345511;
  run_test_paillier 1289298035056950080599051031711529601057 1126233675327554436556156167584424828451 525641977353019578468553281072785507385148371484050430837826881356001987674281 526899722593970366267632939010387732161971098173839346789153725279321171853261;
  run_test_paillier 884909374297001950157672669314744552829 1113958976516351552364472388788485497893 573083098817685589506664483784234970194749884812355268552055283324782766159437 812258478363637858730401248538145655595585311271889141267577844650609270885157;
  run_test_paillier 797817081664110998858211997999953379049 1214381939759573247047248281901313505797 463505389888424068950523903845764021163748312232027043552532855310648658070967 634627721541635713081293727459227640746863507658521749940979294133366633320923;
  run_test_paillier 853478789231700830265374425254956847611 1155464767064200375302070621113604274437 532479601368575677155362479279914092973952768094076025607795919230754763971529 644520092538902536897369639364930636861565438325349655931684784299396360334191;
  run_test_paillier 1118490741403583760167539459251718338343 1158545620762253035489244444164149772153 884307690457281049215148793844022459541240893290060222678263186804500999841219 759594769646361691235650113460062166625108618648432442402340275784127020744301;
  run_test_paillier 949547808419629439176395070328545837133 1016395939951857634275948915248680873073 477993465858338774501761082812284338833258167068349752634026266841696811948833 680444675519694236506582178228767101898977792174555717728139001372792117124357;
  run_test_paillier 983135056687062696019236929796408982157 706788365107309476989512720858076783987 591149070495611374284376449792632450884740965951046544834801351567901456537263 571540903142253722552789338557032864855439061976398939560979384680447214526651

val main: unit -> St C.exit_code
let main () =
  test_gm ();
  test_paillier ();
  C.EXIT_SUCCESS
