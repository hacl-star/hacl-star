module Test.MPFR

open FStar.HyperStack.All
open FStar.HyperStack.IO
open FStar.Buffer

module U64 = FStar.UInt64
module U32 = FStar.UInt32
module I64 = FStar.Int64
module I32 = FStar.Int32

open MPFR.Lib
open MPFR.RoundingMode
open MPFR

#set-options "--z3refresh --lax --max_fuel 1 --initial_fuel 0 --max_ifuel 1 --initial_ifuel 0"

let cprint x = (*C.String.print (C.String.of_literal x)*) print_string x

let print_i32 x = cprint (string_of_int (I32.v x)); cprint " "
let print_i64 x = cprint (string_of_int (I64.v x)); cprint " "
let print_u64 x = cprint (string_of_int (U64.v x)); cprint " "

let print_rnd rnd = match rnd with
    | MPFR_RNDN -> cprint "MPFR_RNDN "
    | MPFR_RNDZ -> cprint "MPFR_RNDZ "
    | MPFR_RNDA -> cprint "MPFR_RNDA "
    | MPFR_RNDU -> cprint "MPFR_RNDU "
    | MPFR_RNDD -> cprint "MPFR_RNDD "

val test_add1sp1: mpfr_sign_t -> mp_limb_t -> mpfr_exp_t -> mp_limb_t -> mpfr_exp_t -> mpfr_rnd_t ->
    mpfr_prec_t -> mp_limb_t -> mpfr_exp_t -> I32.t -> ST bool
    (requires (fun h -> True))
    (ensures  (fun h0 r h1 -> True))

let test_add1sp1 s bp bx cp cx rnd_mode p rp rx rt =
    cprint "Testing add1sp1: \n";
    print_i32 s; print_u64 bp; print_i64 bx; print_u64 cp; print_i64 cx; print_rnd rnd_mode;
    print_i64 p; print_u64 rp; print_i64 rx; print_i32 rt;
    cprint "\n";
    push_frame();
    let bm = createL [bp] in
    let bs = mk_mpfr_struct p s bx bm in
    let b = createL [bs] in
    let cm = createL [cp] in
    let cs = mk_mpfr_struct p s cx cm in
    let c = createL [cs] in
    let at = mpfr_add1sp1 c b c rnd_mode p in
    let asign = mpfr_SIGN c in
    let am = mpfr_MANT c in
    let ap = am.(0ul) in
    let ax = mpfr_EXP c in
    pop_frame ();
    cprint "Result: \n";
    print_i32 asign;
    print_u64 ap;
    print_i64 ax;
    print_i32 at;
    if ((U64.(ap =^ rp) && I64.(ax =^ rx)) || (I64.(ax =^ mpfr_EXP_INF) && I64.(ax =^ rx))) && 
         I32.(asign =^ s) && I32.(at =^ rt) then begin
        cprint "YES!!!\n";
	true
    end else begin
        cprint "no...\n";
	false
    end
    
let test1 () =
    test_add1sp1 1l 9223372036854775808uL 53L 9223372036854775808uL 0L MPFR_RNDN 53L 9223372036854775808uL 53L (-1l)
    
let test2 () =
    test_add1sp1 (-1l) 9223372036854775808uL 0L 9223372036854775808uL 5L MPFR_RNDU 1L 9223372036854775808uL 5L 1l

let test3 () =
    test_add1sp1 1l 13835058055282163712uL 1073741823L 13835058055282163712uL 1073741822L MPFR_RNDN 2L 9223372036854779904uL mpfr_EXP_INF 1l

let test4 () =
    test_add1sp1 1l 11284843200441646272uL 12L 14910977271964212488uL (-1L) MPFR_RNDD 62L 11286663388096915340uL 12L (-1l)

val main: unit -> ST int
    (requires (fun h -> True))
    (ensures  (fun h0 r h1 -> True))

let main () =
    push_frame();
    let t1 = test1 () in
    let t2 = test2 () in
    let t3 = test3 () in
    let t4 = test4 () in
    if t1 && t2 && t3 && t4 then
        cprint "\n === Congratulations!!! WE MADE IT!!! ===\n"
    else 
        cprint "\n I'm so sorry, but the tests failed...\n";
    pop_frame();
    0
