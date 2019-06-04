module Hacl.Test.HE

open C.Failure
open FStar.HyperStack
open FStar.HyperStack.ST
open FStar.Mul

open Lib.IntTypes
open Lib.Math.Algebra
open Lib.Buffer

module GM = Hacl.Impl.HE.GM
module GMS = Hacl.Spec.HE.GM

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

  let aLen = nat_bytes_num p in
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

val main: unit -> St C.exit_code
let main () =
  test_gm ();
  C.EXIT_SUCCESS
