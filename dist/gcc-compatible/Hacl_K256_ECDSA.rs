#![allow(
    dead_code,
    mutable_transmutes,
    non_camel_case_types,
    non_snake_case,
    non_upper_case_globals,
    unused_assignments,
    unused_mut
)]
extern "C" {
    fn memcpy(
        _: *mut libc::c_void,
        _: *const libc::c_void,
        _: libc::c_ulong,
    ) -> *mut libc::c_void;
    fn memset(
        _: *mut libc::c_void,
        _: libc::c_int,
        _: libc::c_ulong,
    ) -> *mut libc::c_void;
    fn printf(_: *const libc::c_char, _: ...) -> libc::c_int;
    fn exit(_: libc::c_int) -> !;
    fn Hacl_Hash_SHA2_hash_256(
        output: *mut uint8_t,
        input: *mut uint8_t,
        input_len: uint32_t,
    );
}
pub type __uint64_t = libc::c_ulonglong;
pub type __darwin_size_t = libc::c_ulong;
pub type size_t = __darwin_size_t;
pub type uint8_t = libc::c_uchar;
pub type uint32_t = libc::c_uint;
pub type uint64_t = libc::c_ulonglong;
pub type FStar_UInt128_uint128 = u128;
pub type uint128_t = FStar_UInt128_uint128;
pub type __bool_bool_bool_bool = __bool_bool_bool_bool_s;
#[derive(Copy, Clone)]
#[repr(C)]
pub struct __bool_bool_bool_bool_s {
    pub fst: bool,
    pub snd: bool,
    pub thd: bool,
    pub f3: bool,
}
pub type __bool_bool = __bool_bool_s;
#[derive(Copy, Clone)]
#[repr(C)]
pub struct __bool_bool_s {
    pub fst: bool,
    pub snd: bool,
}
#[inline]
unsafe extern "C" fn _OSSwapInt64(mut _data: __uint64_t) -> __uint64_t {
    return _data.swap_bytes();
}
#[inline]
unsafe extern "C" fn load64(mut b: *mut uint8_t) -> uint64_t {
    let mut x: uint64_t = 0;
    memcpy(
        &mut x as *mut uint64_t as *mut libc::c_void,
        b as *const libc::c_void,
        8 as libc::c_int as libc::c_ulong,
    );
    return x;
}
#[inline]
unsafe extern "C" fn store64(mut b: *mut uint8_t, mut i: uint64_t) {
    memcpy(
        b as *mut libc::c_void,
        &mut i as *mut uint64_t as *const libc::c_void,
        8 as libc::c_int as libc::c_ulong,
    );
}
#[inline]
unsafe extern "C" fn FStar_UInt128_add(
    mut x: uint128_t,
    mut y: uint128_t,
) -> FStar_UInt128_uint128 {
    return x.wrapping_add(y);
}
#[inline]
unsafe extern "C" fn FStar_UInt128_add_mod(
    mut x: uint128_t,
    mut y: uint128_t,
) -> FStar_UInt128_uint128 {
    return x.wrapping_add(y);
}
#[inline]
unsafe extern "C" fn FStar_UInt128_sub_mod(
    mut x: uint128_t,
    mut y: uint128_t,
) -> FStar_UInt128_uint128 {
    return x.wrapping_sub(y);
}
#[inline]
unsafe extern "C" fn FStar_UInt128_shift_right(
    mut x: uint128_t,
    mut y: uint32_t,
) -> FStar_UInt128_uint128 {
    return x >> y;
}
#[inline]
unsafe extern "C" fn FStar_UInt128_uint64_to_uint128(
    mut x: uint64_t,
) -> FStar_UInt128_uint128 {
    return x as uint128_t;
}
#[inline]
unsafe extern "C" fn FStar_UInt128_uint128_to_uint64(mut x: uint128_t) -> uint64_t {
    return x as uint64_t;
}
#[inline]
unsafe extern "C" fn FStar_UInt128_mul_wide(
    mut x: uint64_t,
    mut y: uint64_t,
) -> FStar_UInt128_uint128 {
    return x as uint128_t * y as uint128_t;
}
#[inline(never)]
unsafe extern "C" fn FStar_UInt64_eq_mask(mut a: uint64_t, mut b: uint64_t) -> uint64_t {
    let mut x: uint64_t = a ^ b;
    let mut minus_x: uint64_t = (!x).wrapping_add(1 as libc::c_ulonglong);
    let mut x_or_minus_x: uint64_t = x | minus_x;
    let mut xnx: uint64_t = x_or_minus_x >> 63 as libc::c_uint;
    return xnx.wrapping_sub(1 as libc::c_ulonglong);
}
#[inline(never)]
unsafe extern "C" fn FStar_UInt64_gte_mask(
    mut a: uint64_t,
    mut b: uint64_t,
) -> uint64_t {
    let mut x: uint64_t = a;
    let mut y: uint64_t = b;
    let mut x_xor_y: uint64_t = x ^ y;
    let mut x_sub_y: uint64_t = x.wrapping_sub(y);
    let mut x_sub_y_xor_y: uint64_t = x_sub_y ^ y;
    let mut q: uint64_t = x_xor_y | x_sub_y_xor_y;
    let mut x_xor_q: uint64_t = x ^ q;
    let mut x_xor_q_: uint64_t = x_xor_q >> 63 as libc::c_uint;
    return x_xor_q_.wrapping_sub(1 as libc::c_ulonglong);
}
static mut Hacl_K256_PrecompTable_precomp_basepoint_table_w4: [uint64_t; 240] = [
    0 as libc::c_ulonglong,
    0 as libc::c_ulonglong,
    0 as libc::c_ulonglong,
    0 as libc::c_ulonglong,
    0 as libc::c_ulonglong,
    1 as libc::c_ulonglong,
    0 as libc::c_ulonglong,
    0 as libc::c_ulonglong,
    0 as libc::c_ulonglong,
    0 as libc::c_ulonglong,
    0 as libc::c_ulonglong,
    0 as libc::c_ulonglong,
    0 as libc::c_ulonglong,
    0 as libc::c_ulonglong,
    0 as libc::c_ulonglong,
    705178180786072 as libc::c_ulonglong,
    3855836460717471 as libc::c_ulonglong,
    4089131105950716 as libc::c_ulonglong,
    3301581525494108 as libc::c_ulonglong,
    133858670344668 as libc::c_ulonglong,
    2199641648059576 as libc::c_ulonglong,
    1278080618437060 as libc::c_ulonglong,
    3959378566518708 as libc::c_ulonglong,
    3455034269351872 as libc::c_ulonglong,
    79417610544803 as libc::c_ulonglong,
    1 as libc::c_ulonglong,
    0 as libc::c_ulonglong,
    0 as libc::c_ulonglong,
    0 as libc::c_ulonglong,
    0 as libc::c_ulonglong,
    1282049064345544 as libc::c_ulonglong,
    971732600440099 as libc::c_ulonglong,
    1014594595727339 as libc::c_ulonglong,
    4392159187541980 as libc::c_ulonglong,
    268327875692285 as libc::c_ulonglong,
    2411661712280539 as libc::c_ulonglong,
    1092576199280126 as libc::c_ulonglong,
    4328619610718051 as libc::c_ulonglong,
    3535440816471627 as libc::c_ulonglong,
    95182251488556 as libc::c_ulonglong,
    1893725512243753 as libc::c_ulonglong,
    3619861457111820 as libc::c_ulonglong,
    879374960417905 as libc::c_ulonglong,
    2868056058129113 as libc::c_ulonglong,
    273195291893682 as libc::c_ulonglong,
    2044797305960112 as libc::c_ulonglong,
    2357106853933780 as libc::c_ulonglong,
    3563112438336058 as libc::c_ulonglong,
    2430811541762558 as libc::c_ulonglong,
    106443809495428 as libc::c_ulonglong,
    2231357633909668 as libc::c_ulonglong,
    3641705835951936 as libc::c_ulonglong,
    80642569314189 as libc::c_ulonglong,
    2254841882373268 as libc::c_ulonglong,
    149848031966573 as libc::c_ulonglong,
    2304615661367764 as libc::c_ulonglong,
    2410957403736446 as libc::c_ulonglong,
    2712754805859804 as libc::c_ulonglong,
    2440183877540536 as libc::c_ulonglong,
    99784623895865 as libc::c_ulonglong,
    3667773127482758 as libc::c_ulonglong,
    1354899394473308 as libc::c_ulonglong,
    3636602998800808 as libc::c_ulonglong,
    2709296679846364 as libc::c_ulonglong,
    7253362091963 as libc::c_ulonglong,
    3585950735562744 as libc::c_ulonglong,
    935775991758415 as libc::c_ulonglong,
    4108078106735201 as libc::c_ulonglong,
    556081800336307 as libc::c_ulonglong,
    229585977163057 as libc::c_ulonglong,
    4055594186679801 as libc::c_ulonglong,
    1767681004944933 as libc::c_ulonglong,
    1432634922083242 as libc::c_ulonglong,
    534935602949197 as libc::c_ulonglong,
    251753159522567 as libc::c_ulonglong,
    2846474078499321 as libc::c_ulonglong,
    4488649590348702 as libc::c_ulonglong,
    2437476916025038 as libc::c_ulonglong,
    3040577412822874 as libc::c_ulonglong,
    79405234918614 as libc::c_ulonglong,
    3030621226551508 as libc::c_ulonglong,
    2801117003929806 as libc::c_ulonglong,
    1642927515498422 as libc::c_ulonglong,
    2802725079726297 as libc::c_ulonglong,
    8472780626107 as libc::c_ulonglong,
    866068070352655 as libc::c_ulonglong,
    188080768545106 as libc::c_ulonglong,
    2152119998903058 as libc::c_ulonglong,
    3391239985029665 as libc::c_ulonglong,
    23820026013564 as libc::c_ulonglong,
    2965064154891949 as libc::c_ulonglong,
    1846516097921398 as libc::c_ulonglong,
    4418379948133146 as libc::c_ulonglong,
    3137755426942400 as libc::c_ulonglong,
    47705291301781 as libc::c_ulonglong,
    4278533051105665 as libc::c_ulonglong,
    3453643211214931 as libc::c_ulonglong,
    3379734319145156 as libc::c_ulonglong,
    3762442192097039 as libc::c_ulonglong,
    40243003528694 as libc::c_ulonglong,
    4063448994211201 as libc::c_ulonglong,
    5697015368785 as libc::c_ulonglong,
    1006545411838613 as libc::c_ulonglong,
    4242291693755210 as libc::c_ulonglong,
    135184629190512 as libc::c_ulonglong,
    264898689131035 as libc::c_ulonglong,
    611796474823597 as libc::c_ulonglong,
    3255382250029089 as libc::c_ulonglong,
    3490429246984696 as libc::c_ulonglong,
    236558595864362 as libc::c_ulonglong,
    2055934691551704 as libc::c_ulonglong,
    1487711670114502 as libc::c_ulonglong,
    1823930698221632 as libc::c_ulonglong,
    2130937287438472 as libc::c_ulonglong,
    154610053389779 as libc::c_ulonglong,
    2746573287023216 as libc::c_ulonglong,
    2430987262221221 as libc::c_ulonglong,
    1668741642878689 as libc::c_ulonglong,
    904982541243977 as libc::c_ulonglong,
    56087343124948 as libc::c_ulonglong,
    393905062353536 as libc::c_ulonglong,
    412681877350188 as libc::c_ulonglong,
    3153602040979977 as libc::c_ulonglong,
    4466820876224989 as libc::c_ulonglong,
    146579165617857 as libc::c_ulonglong,
    2628741216508991 as libc::c_ulonglong,
    747994231529806 as libc::c_ulonglong,
    750506569317681 as libc::c_ulonglong,
    1887492790748779 as libc::c_ulonglong,
    35259008682771 as libc::c_ulonglong,
    2085116434894208 as libc::c_ulonglong,
    543291398921711 as libc::c_ulonglong,
    1144362007901552 as libc::c_ulonglong,
    679305136036846 as libc::c_ulonglong,
    141090902244489 as libc::c_ulonglong,
    632480954474859 as libc::c_ulonglong,
    2384513102652591 as libc::c_ulonglong,
    2225529790159790 as libc::c_ulonglong,
    692258664851625 as libc::c_ulonglong,
    198681843567699 as libc::c_ulonglong,
    2397092587228181 as libc::c_ulonglong,
    145862822166614 as libc::c_ulonglong,
    196976540479452 as libc::c_ulonglong,
    3321831130141455 as libc::c_ulonglong,
    69266673089832 as libc::c_ulonglong,
    4469644227342284 as libc::c_ulonglong,
    3899271145504796 as libc::c_ulonglong,
    1261890974076660 as libc::c_ulonglong,
    525357673886694 as libc::c_ulonglong,
    182135997828583 as libc::c_ulonglong,
    4292760618810332 as libc::c_ulonglong,
    3404186545541683 as libc::c_ulonglong,
    312297386688768 as libc::c_ulonglong,
    204377466824608 as libc::c_ulonglong,
    230900767857952 as libc::c_ulonglong,
    3871485172339693 as libc::c_ulonglong,
    779449329662955 as libc::c_ulonglong,
    978655822464694 as libc::c_ulonglong,
    2278252139594027 as libc::c_ulonglong,
    104641527040382 as libc::c_ulonglong,
    3528840153625765 as libc::c_ulonglong,
    4484699080275273 as libc::c_ulonglong,
    1463971951102316 as libc::c_ulonglong,
    4013910812844749 as libc::c_ulonglong,
    228915589433620 as libc::c_ulonglong,
    1209641433482461 as libc::c_ulonglong,
    4043178788774759 as libc::c_ulonglong,
    3008668238856634 as libc::c_ulonglong,
    1448425089071412 as libc::c_ulonglong,
    26269719725037 as libc::c_ulonglong,
    3330785027545223 as libc::c_ulonglong,
    852657975349259 as libc::c_ulonglong,
    227245054466105 as libc::c_ulonglong,
    1534632353984777 as libc::c_ulonglong,
    207715098574660 as libc::c_ulonglong,
    3209837527352280 as libc::c_ulonglong,
    4051688046309066 as libc::c_ulonglong,
    3839009590725955 as libc::c_ulonglong,
    1321506437398842 as libc::c_ulonglong,
    68340219159928 as libc::c_ulonglong,
    1806950276956275 as libc::c_ulonglong,
    3923908055275295 as libc::c_ulonglong,
    743963253393575 as libc::c_ulonglong,
    42162407478783 as libc::c_ulonglong,
    261334584474610 as libc::c_ulonglong,
    3728224928885214 as libc::c_ulonglong,
    4004701081842869 as libc::c_ulonglong,
    709043201644674 as libc::c_ulonglong,
    4267294249150171 as libc::c_ulonglong,
    255540582975025 as libc::c_ulonglong,
    875490593722211 as libc::c_ulonglong,
    796393708218375 as libc::c_ulonglong,
    14774425627956 as libc::c_ulonglong,
    1500040516752097 as libc::c_ulonglong,
    141076627721678 as libc::c_ulonglong,
    2634539368480628 as libc::c_ulonglong,
    1106488853550103 as libc::c_ulonglong,
    2346231921151930 as libc::c_ulonglong,
    897108283954283 as libc::c_ulonglong,
    64616679559843 as libc::c_ulonglong,
    400244949840943 as libc::c_ulonglong,
    1731263826831733 as libc::c_ulonglong,
    1649996579904651 as libc::c_ulonglong,
    3643693449640761 as libc::c_ulonglong,
    172543068638991 as libc::c_ulonglong,
    329537981097182 as libc::c_ulonglong,
    2029799860802869 as libc::c_ulonglong,
    4377737515208862 as libc::c_ulonglong,
    29103311051334 as libc::c_ulonglong,
    265583594111499 as libc::c_ulonglong,
    3798074876561255 as libc::c_ulonglong,
    184749333259352 as libc::c_ulonglong,
    3117395073661801 as libc::c_ulonglong,
    3695784565008833 as libc::c_ulonglong,
    64282709896721 as libc::c_ulonglong,
    1618968913246422 as libc::c_ulonglong,
    3185235128095257 as libc::c_ulonglong,
    3288745068118692 as libc::c_ulonglong,
    1963818603508782 as libc::c_ulonglong,
    281054350739495 as libc::c_ulonglong,
    1658639050810346 as libc::c_ulonglong,
    3061097601679552 as libc::c_ulonglong,
    3023781433263746 as libc::c_ulonglong,
    2770283391242475 as libc::c_ulonglong,
    144508864751908 as libc::c_ulonglong,
    173576288079856 as libc::c_ulonglong,
    46114579547054 as libc::c_ulonglong,
    1679480127300211 as libc::c_ulonglong,
    1683062051644007 as libc::c_ulonglong,
    117183826129323 as libc::c_ulonglong,
    1894068608117440 as libc::c_ulonglong,
    3846899838975733 as libc::c_ulonglong,
    4289279019496192 as libc::c_ulonglong,
    176995887914031 as libc::c_ulonglong,
    78074942938713 as libc::c_ulonglong,
    454207263265292 as libc::c_ulonglong,
    972683614054061 as libc::c_ulonglong,
    808474205144361 as libc::c_ulonglong,
    942703935951735 as libc::c_ulonglong,
    134460241077887 as libc::c_ulonglong,
];
static mut Hacl_K256_PrecompTable_precomp_g_pow2_64_table_w4: [uint64_t; 240] = [
    0 as libc::c_ulonglong,
    0 as libc::c_ulonglong,
    0 as libc::c_ulonglong,
    0 as libc::c_ulonglong,
    0 as libc::c_ulonglong,
    1 as libc::c_ulonglong,
    0 as libc::c_ulonglong,
    0 as libc::c_ulonglong,
    0 as libc::c_ulonglong,
    0 as libc::c_ulonglong,
    0 as libc::c_ulonglong,
    0 as libc::c_ulonglong,
    0 as libc::c_ulonglong,
    0 as libc::c_ulonglong,
    0 as libc::c_ulonglong,
    4496295042185355 as libc::c_ulonglong,
    3125448202219451 as libc::c_ulonglong,
    1239608518490046 as libc::c_ulonglong,
    2687445637493112 as libc::c_ulonglong,
    77979604880139 as libc::c_ulonglong,
    3360310474215011 as libc::c_ulonglong,
    1216410458165163 as libc::c_ulonglong,
    177901593587973 as libc::c_ulonglong,
    3209978938104985 as libc::c_ulonglong,
    118285133003718 as libc::c_ulonglong,
    434519962075150 as libc::c_ulonglong,
    1114612377498854 as libc::c_ulonglong,
    3488596944003813 as libc::c_ulonglong,
    450716531072892 as libc::c_ulonglong,
    66044973203836 as libc::c_ulonglong,
    2822827191156652 as libc::c_ulonglong,
    2417714248626059 as libc::c_ulonglong,
    2173117567943 as libc::c_ulonglong,
    961513119252459 as libc::c_ulonglong,
    233852556538333 as libc::c_ulonglong,
    3014783730323962 as libc::c_ulonglong,
    2955192634004574 as libc::c_ulonglong,
    580546524951282 as libc::c_ulonglong,
    2982973948711252 as libc::c_ulonglong,
    226295722018730 as libc::c_ulonglong,
    26457116218543 as libc::c_ulonglong,
    3401523493637663 as libc::c_ulonglong,
    2597746825024790 as libc::c_ulonglong,
    1789211180483113 as libc::c_ulonglong,
    155862365823427 as libc::c_ulonglong,
    4056806876632134 as libc::c_ulonglong,
    1742291745730568 as libc::c_ulonglong,
    3527759000626890 as libc::c_ulonglong,
    3740578471192596 as libc::c_ulonglong,
    177295097700537 as libc::c_ulonglong,
    1533961415657770 as libc::c_ulonglong,
    4305228982382487 as libc::c_ulonglong,
    4069090871282711 as libc::c_ulonglong,
    4090877481646667 as libc::c_ulonglong,
    220939617041498 as libc::c_ulonglong,
    2057548127959588 as libc::c_ulonglong,
    45185623103252 as libc::c_ulonglong,
    2871963270423449 as libc::c_ulonglong,
    3312974792248749 as libc::c_ulonglong,
    8710601879528 as libc::c_ulonglong,
    570612225194540 as libc::c_ulonglong,
    2045632925323972 as libc::c_ulonglong,
    1263913878297555 as libc::c_ulonglong,
    1294592284757719 as libc::c_ulonglong,
    238067747295054 as libc::c_ulonglong,
    1576659948829386 as libc::c_ulonglong,
    2315159636629917 as libc::c_ulonglong,
    3624867787891655 as libc::c_ulonglong,
    647628266663887 as libc::c_ulonglong,
    75788399640253 as libc::c_ulonglong,
    710811707847797 as libc::c_ulonglong,
    130020650130128 as libc::c_ulonglong,
    1975045425972589 as libc::c_ulonglong,
    136351545314094 as libc::c_ulonglong,
    229292031212337 as libc::c_ulonglong,
    1061471455264148 as libc::c_ulonglong,
    3281312694184822 as libc::c_ulonglong,
    1692442293921797 as libc::c_ulonglong,
    4171008525509513 as libc::c_ulonglong,
    275424696197549 as libc::c_ulonglong,
    1170296303921965 as libc::c_ulonglong,
    4154092952807735 as libc::c_ulonglong,
    4371262070870741 as libc::c_ulonglong,
    835769811036496 as libc::c_ulonglong,
    275812646528189 as libc::c_ulonglong,
    4006745785521764 as libc::c_ulonglong,
    1965172239781114 as libc::c_ulonglong,
    4121055644916429 as libc::c_ulonglong,
    3578995380229569 as libc::c_ulonglong,
    169798870760022 as libc::c_ulonglong,
    1834234783016431 as libc::c_ulonglong,
    3186919121688538 as libc::c_ulonglong,
    1894269993170652 as libc::c_ulonglong,
    868603832348691 as libc::c_ulonglong,
    110978471368876 as libc::c_ulonglong,
    1659296605881532 as libc::c_ulonglong,
    3257830829309297 as libc::c_ulonglong,
    3381509832701119 as libc::c_ulonglong,
    4016163121121296 as libc::c_ulonglong,
    265240263496294 as libc::c_ulonglong,
    4411285343933251 as libc::c_ulonglong,
    728746770806400 as libc::c_ulonglong,
    1767819098558739 as libc::c_ulonglong,
    3002081480892841 as libc::c_ulonglong,
    96312133241935 as libc::c_ulonglong,
    468184501392107 as libc::c_ulonglong,
    2061529496271208 as libc::c_ulonglong,
    801565111628867 as libc::c_ulonglong,
    3380678576799273 as libc::c_ulonglong,
    121814978170941 as libc::c_ulonglong,
    3340363319165433 as libc::c_ulonglong,
    2764604325746928 as libc::c_ulonglong,
    4475755976431968 as libc::c_ulonglong,
    3678073419927081 as libc::c_ulonglong,
    237001357924061 as libc::c_ulonglong,
    4110487014553450 as libc::c_ulonglong,
    442517757833404 as libc::c_ulonglong,
    3976758767423859 as libc::c_ulonglong,
    2559863799262476 as libc::c_ulonglong,
    178144664279213 as libc::c_ulonglong,
    2488702171798051 as libc::c_ulonglong,
    4292079598620208 as libc::c_ulonglong,
    1642918280217329 as libc::c_ulonglong,
    3694920319798108 as libc::c_ulonglong,
    111735528281657 as libc::c_ulonglong,
    2904433967156033 as libc::c_ulonglong,
    4391518032143166 as libc::c_ulonglong,
    3018885875516259 as libc::c_ulonglong,
    3730342681447122 as libc::c_ulonglong,
    10320273322750 as libc::c_ulonglong,
    555845881555519 as libc::c_ulonglong,
    58355404017985 as libc::c_ulonglong,
    379009359053696 as libc::c_ulonglong,
    450317203955503 as libc::c_ulonglong,
    271063299686173 as libc::c_ulonglong,
    910340241794202 as libc::c_ulonglong,
    4145234574853890 as libc::c_ulonglong,
    2059755654702755 as libc::c_ulonglong,
    626530377112246 as libc::c_ulonglong,
    188918989156857 as libc::c_ulonglong,
    3316657461542117 as libc::c_ulonglong,
    778033563170765 as libc::c_ulonglong,
    3568562306532187 as libc::c_ulonglong,
    2888619469733481 as libc::c_ulonglong,
    4364919962337 as libc::c_ulonglong,
    4095057288587059 as libc::c_ulonglong,
    2275461355379988 as libc::c_ulonglong,
    1507422995910897 as libc::c_ulonglong,
    3737691697116252 as libc::c_ulonglong,
    28779913258578 as libc::c_ulonglong,
    131453301647952 as libc::c_ulonglong,
    3613515597508469 as libc::c_ulonglong,
    2389606941441321 as libc::c_ulonglong,
    2135459302594806 as libc::c_ulonglong,
    105517262484263 as libc::c_ulonglong,
    2973432939331401 as libc::c_ulonglong,
    3447096622477885 as libc::c_ulonglong,
    684654106536844 as libc::c_ulonglong,
    2815198316729695 as libc::c_ulonglong,
    280303067216071 as libc::c_ulonglong,
    1841014812927024 as libc::c_ulonglong,
    1181026273060917 as libc::c_ulonglong,
    4092989148457730 as libc::c_ulonglong,
    1381045116206278 as libc::c_ulonglong,
    112475725893965 as libc::c_ulonglong,
    2309144740156686 as libc::c_ulonglong,
    1558825847609352 as libc::c_ulonglong,
    2008068002046292 as libc::c_ulonglong,
    3153511625856423 as libc::c_ulonglong,
    38469701427673 as libc::c_ulonglong,
    4240572315518056 as libc::c_ulonglong,
    2295170987320580 as libc::c_ulonglong,
    187734093837094 as libc::c_ulonglong,
    301041528077172 as libc::c_ulonglong,
    234553141005715 as libc::c_ulonglong,
    4170513699279606 as libc::c_ulonglong,
    1600132848196146 as libc::c_ulonglong,
    3149113064155689 as libc::c_ulonglong,
    2733255352600949 as libc::c_ulonglong,
    144915931419495 as libc::c_ulonglong,
    1221012073888926 as libc::c_ulonglong,
    4395668111081710 as libc::c_ulonglong,
    2464799161496070 as libc::c_ulonglong,
    3664256125241313 as libc::c_ulonglong,
    239705368981290 as libc::c_ulonglong,
    1415181408539490 as libc::c_ulonglong,
    2551836620449074 as libc::c_ulonglong,
    3003106895689578 as libc::c_ulonglong,
    968947218886924 as libc::c_ulonglong,
    270781532362673 as libc::c_ulonglong,
    2905980714350372 as libc::c_ulonglong,
    3246927349288975 as libc::c_ulonglong,
    2653377642686974 as libc::c_ulonglong,
    1577457093418263 as libc::c_ulonglong,
    279488238785848 as libc::c_ulonglong,
    568335962564552 as libc::c_ulonglong,
    4251365041645758 as libc::c_ulonglong,
    1257832559776007 as libc::c_ulonglong,
    2424022444243863 as libc::c_ulonglong,
    261166122046343 as libc::c_ulonglong,
    4399874608082116 as libc::c_ulonglong,
    640509987891568 as libc::c_ulonglong,
    3119706885332220 as libc::c_ulonglong,
    1990185416694007 as libc::c_ulonglong,
    119390098529341 as libc::c_ulonglong,
    220106534694050 as libc::c_ulonglong,
    937225880034895 as libc::c_ulonglong,
    656288151358882 as libc::c_ulonglong,
    1766967254772100 as libc::c_ulonglong,
    197900790969750 as libc::c_ulonglong,
    2992539221608875 as libc::c_ulonglong,
    3960297171111858 as libc::c_ulonglong,
    3499202002925081 as libc::c_ulonglong,
    1103060980924705 as libc::c_ulonglong,
    13670895919578 as libc::c_ulonglong,
    430132744187721 as libc::c_ulonglong,
    1206771838050953 as libc::c_ulonglong,
    2474749300167198 as libc::c_ulonglong,
    296299539510780 as libc::c_ulonglong,
    61565517686436 as libc::c_ulonglong,
    752778559080573 as libc::c_ulonglong,
    3049015829565410 as libc::c_ulonglong,
    3538647632527371 as libc::c_ulonglong,
    1640473028662032 as libc::c_ulonglong,
    182488721849306 as libc::c_ulonglong,
    1234378482161516 as libc::c_ulonglong,
    3736205988606381 as libc::c_ulonglong,
    2814216844344487 as libc::c_ulonglong,
    3877249891529557 as libc::c_ulonglong,
    51681412928433 as libc::c_ulonglong,
    4275336620301239 as libc::c_ulonglong,
    3084074032750651 as libc::c_ulonglong,
    42732308350456 as libc::c_ulonglong,
    3648603591552229 as libc::c_ulonglong,
    142450621701603 as libc::c_ulonglong,
    4020045475009854 as libc::c_ulonglong,
    1050293952073054 as libc::c_ulonglong,
    1974773673079851 as libc::c_ulonglong,
    1815515638724020 as libc::c_ulonglong,
    104845375825434 as libc::c_ulonglong,
];
static mut Hacl_K256_PrecompTable_precomp_g_pow2_128_table_w4: [uint64_t; 240] = [
    0 as libc::c_ulonglong,
    0 as libc::c_ulonglong,
    0 as libc::c_ulonglong,
    0 as libc::c_ulonglong,
    0 as libc::c_ulonglong,
    1 as libc::c_ulonglong,
    0 as libc::c_ulonglong,
    0 as libc::c_ulonglong,
    0 as libc::c_ulonglong,
    0 as libc::c_ulonglong,
    0 as libc::c_ulonglong,
    0 as libc::c_ulonglong,
    0 as libc::c_ulonglong,
    0 as libc::c_ulonglong,
    0 as libc::c_ulonglong,
    1277614565900951 as libc::c_ulonglong,
    378671684419493 as libc::c_ulonglong,
    3176260448102880 as libc::c_ulonglong,
    1575691435565077 as libc::c_ulonglong,
    167304528382180 as libc::c_ulonglong,
    2600787765776588 as libc::c_ulonglong,
    7497946149293 as libc::c_ulonglong,
    2184272641272202 as libc::c_ulonglong,
    2200235265236628 as libc::c_ulonglong,
    265969268774814 as libc::c_ulonglong,
    1913228635640715 as libc::c_ulonglong,
    2831959046949342 as libc::c_ulonglong,
    888030405442963 as libc::c_ulonglong,
    1817092932985033 as libc::c_ulonglong,
    101515844997121 as libc::c_ulonglong,
    3309468394859588 as libc::c_ulonglong,
    3965334773689948 as libc::c_ulonglong,
    1945272965790738 as libc::c_ulonglong,
    4450939211427964 as libc::c_ulonglong,
    211349698782702 as libc::c_ulonglong,
    2085160302160079 as libc::c_ulonglong,
    212812506072603 as libc::c_ulonglong,
    3646122434511764 as libc::c_ulonglong,
    1711405092320514 as libc::c_ulonglong,
    95160920508464 as libc::c_ulonglong,
    1677683368518073 as libc::c_ulonglong,
    4384656939250953 as libc::c_ulonglong,
    3548591046529893 as libc::c_ulonglong,
    1683233536091384 as libc::c_ulonglong,
    105919586159941 as libc::c_ulonglong,
    1941416002726455 as libc::c_ulonglong,
    246264372248216 as libc::c_ulonglong,
    3063044110922228 as libc::c_ulonglong,
    3772292170415825 as libc::c_ulonglong,
    222933374989815 as libc::c_ulonglong,
    2417211163452935 as libc::c_ulonglong,
    2018230365573200 as libc::c_ulonglong,
    1985974538911047 as libc::c_ulonglong,
    1387197705332739 as libc::c_ulonglong,
    186400825584956 as libc::c_ulonglong,
    2469330487750329 as libc::c_ulonglong,
    1291983813301638 as libc::c_ulonglong,
    333416733706302 as libc::c_ulonglong,
    3413315564261070 as libc::c_ulonglong,
    189444777569683 as libc::c_ulonglong,
    1062005622360420 as libc::c_ulonglong,
    1800197715938740 as libc::c_ulonglong,
    3693110992551647 as libc::c_ulonglong,
    626990328941945 as libc::c_ulonglong,
    40998857100520 as libc::c_ulonglong,
    3921983552805085 as libc::c_ulonglong,
    1016632437340656 as libc::c_ulonglong,
    4016615929950878 as libc::c_ulonglong,
    2682554586771281 as libc::c_ulonglong,
    7043555162389 as libc::c_ulonglong,
    3333819830676567 as libc::c_ulonglong,
    4120091964944036 as libc::c_ulonglong,
    1960788263484015 as libc::c_ulonglong,
    1642145656273304 as libc::c_ulonglong,
    252814075789128 as libc::c_ulonglong,
    3085777342821357 as libc::c_ulonglong,
    4166637997604052 as libc::c_ulonglong,
    1339401689756469 as libc::c_ulonglong,
    845938529607551 as libc::c_ulonglong,
    223351828189283 as libc::c_ulonglong,
    1148648705186890 as libc::c_ulonglong,
    1230525014760605 as libc::c_ulonglong,
    1869739475126720 as libc::c_ulonglong,
    4193966261205530 as libc::c_ulonglong,
    175684010336013 as libc::c_ulonglong,
    4476719358931508 as libc::c_ulonglong,
    4209547487457638 as libc::c_ulonglong,
    2197536411673724 as libc::c_ulonglong,
    3010838433412303 as libc::c_ulonglong,
    169318997251483 as libc::c_ulonglong,
    49493868302162 as libc::c_ulonglong,
    3594601099078584 as libc::c_ulonglong,
    3662420905445942 as libc::c_ulonglong,
    3606544932233685 as libc::c_ulonglong,
    270643652662165 as libc::c_ulonglong,
    180681786228544 as libc::c_ulonglong,
    2095882682308564 as libc::c_ulonglong,
    813484483841391 as libc::c_ulonglong,
    1622665392824698 as libc::c_ulonglong,
    113821770225137 as libc::c_ulonglong,
    3075432444115417 as libc::c_ulonglong,
    716502989978722 as libc::c_ulonglong,
    2304779892217245 as libc::c_ulonglong,
    1760144151770127 as libc::c_ulonglong,
    235719156963938 as libc::c_ulonglong,
    3180013070471143 as libc::c_ulonglong,
    1331027634540579 as libc::c_ulonglong,
    552273022992392 as libc::c_ulonglong,
    2858693077461887 as libc::c_ulonglong,
    197914407731510 as libc::c_ulonglong,
    187252310910959 as libc::c_ulonglong,
    4160637171377125 as libc::c_ulonglong,
    3225059526713298 as libc::c_ulonglong,
    2574558217383978 as libc::c_ulonglong,
    249695600622489 as libc::c_ulonglong,
    364988742814327 as libc::c_ulonglong,
    4245298536326258 as libc::c_ulonglong,
    1812464706589342 as libc::c_ulonglong,
    2734857123772998 as libc::c_ulonglong,
    120105577124628 as libc::c_ulonglong,
    160179251271109 as libc::c_ulonglong,
    3604555733307834 as libc::c_ulonglong,
    150380003195715 as libc::c_ulonglong,
    1574304909935121 as libc::c_ulonglong,
    142190285600761 as libc::c_ulonglong,
    1835385847725651 as libc::c_ulonglong,
    3168087139615901 as libc::c_ulonglong,
    3201434861713736 as libc::c_ulonglong,
    741757984537760 as libc::c_ulonglong,
    163585009419543 as libc::c_ulonglong,
    3837997981109783 as libc::c_ulonglong,
    3771946407870997 as libc::c_ulonglong,
    2867641360295452 as libc::c_ulonglong,
    3097548691501578 as libc::c_ulonglong,
    124624912142104 as libc::c_ulonglong,
    2729896088769328 as libc::c_ulonglong,
    1087786827035225 as libc::c_ulonglong,
    3934000813818614 as libc::c_ulonglong,
    1176792318645055 as libc::c_ulonglong,
    125311882169270 as libc::c_ulonglong,
    3530709439299502 as libc::c_ulonglong,
    1561477829834527 as libc::c_ulonglong,
    3927894570196761 as libc::c_ulonglong,
    3957765307669212 as libc::c_ulonglong,
    105720519513730 as libc::c_ulonglong,
    3758969845816997 as libc::c_ulonglong,
    2738320452287300 as libc::c_ulonglong,
    2380753632109507 as libc::c_ulonglong,
    2762090901149075 as libc::c_ulonglong,
    123455059136515 as libc::c_ulonglong,
    4222807813169807 as libc::c_ulonglong,
    118064783651432 as libc::c_ulonglong,
    2877694712254934 as libc::c_ulonglong,
    3535027426396448 as libc::c_ulonglong,
    100175663703417 as libc::c_ulonglong,
    3287921121213155 as libc::c_ulonglong,
    4497246481824206 as libc::c_ulonglong,
    1960809949007025 as libc::c_ulonglong,
    3236854264159102 as libc::c_ulonglong,
    35028112623717 as libc::c_ulonglong,
    338838627913273 as libc::c_ulonglong,
    2827531947914645 as libc::c_ulonglong,
    4231826783810670 as libc::c_ulonglong,
    1082490106100389 as libc::c_ulonglong,
    13267544387448 as libc::c_ulonglong,
    4249975884259105 as libc::c_ulonglong,
    2844862161652484 as libc::c_ulonglong,
    262742197948971 as libc::c_ulonglong,
    3525653802457116 as libc::c_ulonglong,
    269963889261701 as libc::c_ulonglong,
    3690062482117102 as libc::c_ulonglong,
    675413453822147 as libc::c_ulonglong,
    2170937868437574 as libc::c_ulonglong,
    2367632187022010 as libc::c_ulonglong,
    214032802409445 as libc::c_ulonglong,
    2054007379612477 as libc::c_ulonglong,
    3558050826739009 as libc::c_ulonglong,
    266827184752634 as libc::c_ulonglong,
    1946520293291195 as libc::c_ulonglong,
    238087872386556 as libc::c_ulonglong,
    490056555385700 as libc::c_ulonglong,
    794405769357386 as libc::c_ulonglong,
    3886901294859702 as libc::c_ulonglong,
    3120414548626348 as libc::c_ulonglong,
    84316625221136 as libc::c_ulonglong,
    223073962531835 as libc::c_ulonglong,
    4280846460577631 as libc::c_ulonglong,
    344296282849308 as libc::c_ulonglong,
    3522116652699457 as libc::c_ulonglong,
    171817232053075 as libc::c_ulonglong,
    3296636283062273 as libc::c_ulonglong,
    3587303364425579 as libc::c_ulonglong,
    1033485783633331 as libc::c_ulonglong,
    3686984130812906 as libc::c_ulonglong,
    268290803650477 as libc::c_ulonglong,
    2803988215834467 as libc::c_ulonglong,
    3821246410529720 as libc::c_ulonglong,
    1077722388925870 as libc::c_ulonglong,
    4187137036866164 as libc::c_ulonglong,
    104696540795905 as libc::c_ulonglong,
    998770003854764 as libc::c_ulonglong,
    3960768137535019 as libc::c_ulonglong,
    4293792474919135 as libc::c_ulonglong,
    3251297981727034 as libc::c_ulonglong,
    192479028790101 as libc::c_ulonglong,
    1175880869349935 as libc::c_ulonglong,
    3506949259311937 as libc::c_ulonglong,
    2161711516160714 as libc::c_ulonglong,
    2506820922270187 as libc::c_ulonglong,
    131002200661047 as libc::c_ulonglong,
    3532399477339994 as libc::c_ulonglong,
    2515815721228719 as libc::c_ulonglong,
    4274974119021502 as libc::c_ulonglong,
    265752394510924 as libc::c_ulonglong,
    163144272153395 as libc::c_ulonglong,
    2824260010502991 as libc::c_ulonglong,
    517077012665142 as libc::c_ulonglong,
    602987073882924 as libc::c_ulonglong,
    2939630061751780 as libc::c_ulonglong,
    59211609557440 as libc::c_ulonglong,
    963423614549333 as libc::c_ulonglong,
    495476232754434 as libc::c_ulonglong,
    94274496109103 as libc::c_ulonglong,
    2245136222990187 as libc::c_ulonglong,
    185414764872288 as libc::c_ulonglong,
    2266067668609289 as libc::c_ulonglong,
    3873978896235927 as libc::c_ulonglong,
    4428283513152105 as libc::c_ulonglong,
    3881481480259312 as libc::c_ulonglong,
    207746202010862 as libc::c_ulonglong,
    1609437858011364 as libc::c_ulonglong,
    477585758421515 as libc::c_ulonglong,
    3850430788664649 as libc::c_ulonglong,
    2682299074459173 as libc::c_ulonglong,
    149439089751274 as libc::c_ulonglong,
    3665760243877698 as libc::c_ulonglong,
    1356661512658931 as libc::c_ulonglong,
    1675903262368322 as libc::c_ulonglong,
    3355649228050892 as libc::c_ulonglong,
    99772108898412 as libc::c_ulonglong,
];
static mut Hacl_K256_PrecompTable_precomp_g_pow2_192_table_w4: [uint64_t; 240] = [
    0 as libc::c_ulonglong,
    0 as libc::c_ulonglong,
    0 as libc::c_ulonglong,
    0 as libc::c_ulonglong,
    0 as libc::c_ulonglong,
    1 as libc::c_ulonglong,
    0 as libc::c_ulonglong,
    0 as libc::c_ulonglong,
    0 as libc::c_ulonglong,
    0 as libc::c_ulonglong,
    0 as libc::c_ulonglong,
    0 as libc::c_ulonglong,
    0 as libc::c_ulonglong,
    0 as libc::c_ulonglong,
    0 as libc::c_ulonglong,
    34056422761564 as libc::c_ulonglong,
    3315864838337811 as libc::c_ulonglong,
    3797032336888745 as libc::c_ulonglong,
    2580641850480806 as libc::c_ulonglong,
    208048944042500 as libc::c_ulonglong,
    1233795288689421 as libc::c_ulonglong,
    1048795233382631 as libc::c_ulonglong,
    646545158071530 as libc::c_ulonglong,
    1816025742137285 as libc::c_ulonglong,
    12245672982162 as libc::c_ulonglong,
    2119364213800870 as libc::c_ulonglong,
    2034960311715107 as libc::c_ulonglong,
    3172697815804487 as libc::c_ulonglong,
    4185144850224160 as libc::c_ulonglong,
    2792055915674 as libc::c_ulonglong,
    795534452139321 as libc::c_ulonglong,
    3647836177838185 as libc::c_ulonglong,
    2681403398797991 as libc::c_ulonglong,
    3149264270306207 as libc::c_ulonglong,
    278704080615511 as libc::c_ulonglong,
    2752552368344718 as libc::c_ulonglong,
    1363840972378818 as libc::c_ulonglong,
    1877521512083293 as libc::c_ulonglong,
    1862111388059470 as libc::c_ulonglong,
    36200324115014 as libc::c_ulonglong,
    4183622899327217 as libc::c_ulonglong,
    747381675363076 as libc::c_ulonglong,
    2772916395314624 as libc::c_ulonglong,
    833767013119965 as libc::c_ulonglong,
    246274452928088 as libc::c_ulonglong,
    1526238021297781 as libc::c_ulonglong,
    3327534966022747 as libc::c_ulonglong,
    1169012581910517 as libc::c_ulonglong,
    4430894603030025 as libc::c_ulonglong,
    149242742442115 as libc::c_ulonglong,
    1002569704307172 as libc::c_ulonglong,
    2763252093432365 as libc::c_ulonglong,
    3037748497732938 as libc::c_ulonglong,
    2329811173939457 as libc::c_ulonglong,
    270769113180752 as libc::c_ulonglong,
    4344092461623432 as libc::c_ulonglong,
    892200524589382 as libc::c_ulonglong,
    2511418516713970 as libc::c_ulonglong,
    103575031265398 as libc::c_ulonglong,
    183736033430252 as libc::c_ulonglong,
    583003071257308 as libc::c_ulonglong,
    3357167344738425 as libc::c_ulonglong,
    4038099763242651 as libc::c_ulonglong,
    1776250620957255 as libc::c_ulonglong,
    51334115864192 as libc::c_ulonglong,
    2616405698969611 as libc::c_ulonglong,
    1196364755910565 as libc::c_ulonglong,
    3135228056210500 as libc::c_ulonglong,
    533729417611761 as libc::c_ulonglong,
    86564351229326 as libc::c_ulonglong,
    98936129527281 as libc::c_ulonglong,
    4425305036630677 as libc::c_ulonglong,
    2980296390253408 as libc::c_ulonglong,
    2487091677325739 as libc::c_ulonglong,
    10501977234280 as libc::c_ulonglong,
    1805646499831077 as libc::c_ulonglong,
    3120615962395477 as libc::c_ulonglong,
    3634629685307533 as libc::c_ulonglong,
    3009632755291436 as libc::c_ulonglong,
    16794051906523 as libc::c_ulonglong,
    2465481597883214 as libc::c_ulonglong,
    211492787490403 as libc::c_ulonglong,
    1120942867046103 as libc::c_ulonglong,
    486438308572108 as libc::c_ulonglong,
    76058986271771 as libc::c_ulonglong,
    2435216584587357 as libc::c_ulonglong,
    3076359381968283 as libc::c_ulonglong,
    1071594491489655 as libc::c_ulonglong,
    3148707450339154 as libc::c_ulonglong,
    249332205737851 as libc::c_ulonglong,
    4171051176626809 as libc::c_ulonglong,
    3165176227956388 as libc::c_ulonglong,
    2400901591835233 as libc::c_ulonglong,
    1435783621333022 as libc::c_ulonglong,
    20312753440321 as libc::c_ulonglong,
    1767293887448005 as libc::c_ulonglong,
    685150647587522 as libc::c_ulonglong,
    2957187934449906 as libc::c_ulonglong,
    382661319140439 as libc::c_ulonglong,
    177583591139601 as libc::c_ulonglong,
    2083572648630743 as libc::c_ulonglong,
    1083410277889419 as libc::c_ulonglong,
    4267902097868310 as libc::c_ulonglong,
    679989918385081 as libc::c_ulonglong,
    123155311554032 as libc::c_ulonglong,
    2830267662472020 as libc::c_ulonglong,
    4476040509735924 as libc::c_ulonglong,
    526697201585144 as libc::c_ulonglong,
    3465306430573135 as libc::c_ulonglong,
    2296616218591 as libc::c_ulonglong,
    1270626872734279 as libc::c_ulonglong,
    1049740198790549 as libc::c_ulonglong,
    4197567214843444 as libc::c_ulonglong,
    1962225231320591 as libc::c_ulonglong,
    186125026796856 as libc::c_ulonglong,
    737027567341142 as libc::c_ulonglong,
    4364616098174 as libc::c_ulonglong,
    3618884818756660 as libc::c_ulonglong,
    1236837563717668 as libc::c_ulonglong,
    162873772439548 as libc::c_ulonglong,
    3081542470065122 as libc::c_ulonglong,
    910331750163991 as libc::c_ulonglong,
    2110498143869827 as libc::c_ulonglong,
    3208473121852657 as libc::c_ulonglong,
    94687786224509 as libc::c_ulonglong,
    4113309027567819 as libc::c_ulonglong,
    4272179438357536 as libc::c_ulonglong,
    1857418654076140 as libc::c_ulonglong,
    1672678841741004 as libc::c_ulonglong,
    94482160248411 as libc::c_ulonglong,
    1928652436799020 as libc::c_ulonglong,
    1750866462381515 as libc::c_ulonglong,
    4048060485672270 as libc::c_ulonglong,
    4006680581258587 as libc::c_ulonglong,
    14850434761312 as libc::c_ulonglong,
    2828734997081648 as libc::c_ulonglong,
    1975589525873972 as libc::c_ulonglong,
    3724347738416009 as libc::c_ulonglong,
    597163266689736 as libc::c_ulonglong,
    14568362978551 as libc::c_ulonglong,
    2203865455839744 as libc::c_ulonglong,
    2237034958890595 as libc::c_ulonglong,
    1863572986731818 as libc::c_ulonglong,
    2329774560279041 as libc::c_ulonglong,
    245105447642201 as libc::c_ulonglong,
    2179697447864822 as libc::c_ulonglong,
    1769609498189882 as libc::c_ulonglong,
    1916950746430931 as libc::c_ulonglong,
    847019613787312 as libc::c_ulonglong,
    163210606565100 as libc::c_ulonglong,
    3658248417400062 as libc::c_ulonglong,
    717138296045881 as libc::c_ulonglong,
    42531212306121 as libc::c_ulonglong,
    1040915917097532 as libc::c_ulonglong,
    77364489101310 as libc::c_ulonglong,
    539253504015590 as libc::c_ulonglong,
    732690726289841 as libc::c_ulonglong,
    3401622034697806 as libc::c_ulonglong,
    2864593278358513 as libc::c_ulonglong,
    142611941887017 as libc::c_ulonglong,
    536364617506702 as libc::c_ulonglong,
    845071859974284 as libc::c_ulonglong,
    4461787417089721 as libc::c_ulonglong,
    2633811871939723 as libc::c_ulonglong,
    113619731985610 as libc::c_ulonglong,
    2535870015489566 as libc::c_ulonglong,
    2146224665077830 as libc::c_ulonglong,
    2593725534662047 as libc::c_ulonglong,
    1332349537449710 as libc::c_ulonglong,
    153375287068096 as libc::c_ulonglong,
    3689977177165276 as libc::c_ulonglong,
    3631865615314120 as libc::c_ulonglong,
    184644878348929 as libc::c_ulonglong,
    2220481726602813 as libc::c_ulonglong,
    204002551273091 as libc::c_ulonglong,
    3022560051766785 as libc::c_ulonglong,
    3125940458001213 as libc::c_ulonglong,
    4258299086906325 as libc::c_ulonglong,
    1072471915162030 as libc::c_ulonglong,
    2797562724530 as libc::c_ulonglong,
    3974298156223059 as libc::c_ulonglong,
    1624778551002554 as libc::c_ulonglong,
    3490703864485971 as libc::c_ulonglong,
    2533877484212458 as libc::c_ulonglong,
    176107782538555 as libc::c_ulonglong,
    4275987398312137 as libc::c_ulonglong,
    4397120757693722 as libc::c_ulonglong,
    3001292763847390 as libc::c_ulonglong,
    1556490837621310 as libc::c_ulonglong,
    70442953037671 as libc::c_ulonglong,
    1558915972545974 as libc::c_ulonglong,
    744724505252845 as libc::c_ulonglong,
    2697230204313363 as libc::c_ulonglong,
    3495671924212144 as libc::c_ulonglong,
    95744296878924 as libc::c_ulonglong,
    1508848630912047 as libc::c_ulonglong,
    4163599342850968 as libc::c_ulonglong,
    1234988733935901 as libc::c_ulonglong,
    3789722472212706 as libc::c_ulonglong,
    219522007052022 as libc::c_ulonglong,
    2106597506701262 as libc::c_ulonglong,
    3231115099832239 as libc::c_ulonglong,
    1296436890593905 as libc::c_ulonglong,
    1016795619587656 as libc::c_ulonglong,
    231150565033388 as libc::c_ulonglong,
    4205501688458754 as libc::c_ulonglong,
    2271569140386062 as libc::c_ulonglong,
    3421769599058157 as libc::c_ulonglong,
    4118408853784554 as libc::c_ulonglong,
    276709341465173 as libc::c_ulonglong,
    2681340614854362 as libc::c_ulonglong,
    2514413365628788 as libc::c_ulonglong,
    62294545067341 as libc::c_ulonglong,
    277610220069365 as libc::c_ulonglong,
    252463150123799 as libc::c_ulonglong,
    2547353593759399 as libc::c_ulonglong,
    1857438147448607 as libc::c_ulonglong,
    2964811969681256 as libc::c_ulonglong,
    3303706463835387 as libc::c_ulonglong,
    248936570980853 as libc::c_ulonglong,
    3208982702478009 as libc::c_ulonglong,
    2518671051730787 as libc::c_ulonglong,
    727433853033835 as libc::c_ulonglong,
    1290389308223446 as libc::c_ulonglong,
    220742793981035 as libc::c_ulonglong,
    3851225361654709 as libc::c_ulonglong,
    2307489307934273 as libc::c_ulonglong,
    1151710489948266 as libc::c_ulonglong,
    289775285210516 as libc::c_ulonglong,
    222685002397295 as libc::c_ulonglong,
    1222117478082108 as libc::c_ulonglong,
    2822029169395728 as libc::c_ulonglong,
    1172146252219882 as libc::c_ulonglong,
    2626108105510259 as libc::c_ulonglong,
    209803527887167 as libc::c_ulonglong,
    2718831919953281 as libc::c_ulonglong,
    4348638387588593 as libc::c_ulonglong,
    3761438313263183 as libc::c_ulonglong,
    13169515318095 as libc::c_ulonglong,
    212893621229476 as libc::c_ulonglong,
];
static mut Hacl_K256_PrecompTable_precomp_basepoint_table_w5: [uint64_t; 480] = [
    0 as libc::c_ulonglong,
    0 as libc::c_ulonglong,
    0 as libc::c_ulonglong,
    0 as libc::c_ulonglong,
    0 as libc::c_ulonglong,
    1 as libc::c_ulonglong,
    0 as libc::c_ulonglong,
    0 as libc::c_ulonglong,
    0 as libc::c_ulonglong,
    0 as libc::c_ulonglong,
    0 as libc::c_ulonglong,
    0 as libc::c_ulonglong,
    0 as libc::c_ulonglong,
    0 as libc::c_ulonglong,
    0 as libc::c_ulonglong,
    705178180786072 as libc::c_ulonglong,
    3855836460717471 as libc::c_ulonglong,
    4089131105950716 as libc::c_ulonglong,
    3301581525494108 as libc::c_ulonglong,
    133858670344668 as libc::c_ulonglong,
    2199641648059576 as libc::c_ulonglong,
    1278080618437060 as libc::c_ulonglong,
    3959378566518708 as libc::c_ulonglong,
    3455034269351872 as libc::c_ulonglong,
    79417610544803 as libc::c_ulonglong,
    1 as libc::c_ulonglong,
    0 as libc::c_ulonglong,
    0 as libc::c_ulonglong,
    0 as libc::c_ulonglong,
    0 as libc::c_ulonglong,
    1282049064345544 as libc::c_ulonglong,
    971732600440099 as libc::c_ulonglong,
    1014594595727339 as libc::c_ulonglong,
    4392159187541980 as libc::c_ulonglong,
    268327875692285 as libc::c_ulonglong,
    2411661712280539 as libc::c_ulonglong,
    1092576199280126 as libc::c_ulonglong,
    4328619610718051 as libc::c_ulonglong,
    3535440816471627 as libc::c_ulonglong,
    95182251488556 as libc::c_ulonglong,
    1893725512243753 as libc::c_ulonglong,
    3619861457111820 as libc::c_ulonglong,
    879374960417905 as libc::c_ulonglong,
    2868056058129113 as libc::c_ulonglong,
    273195291893682 as libc::c_ulonglong,
    2044797305960112 as libc::c_ulonglong,
    2357106853933780 as libc::c_ulonglong,
    3563112438336058 as libc::c_ulonglong,
    2430811541762558 as libc::c_ulonglong,
    106443809495428 as libc::c_ulonglong,
    2231357633909668 as libc::c_ulonglong,
    3641705835951936 as libc::c_ulonglong,
    80642569314189 as libc::c_ulonglong,
    2254841882373268 as libc::c_ulonglong,
    149848031966573 as libc::c_ulonglong,
    2304615661367764 as libc::c_ulonglong,
    2410957403736446 as libc::c_ulonglong,
    2712754805859804 as libc::c_ulonglong,
    2440183877540536 as libc::c_ulonglong,
    99784623895865 as libc::c_ulonglong,
    3667773127482758 as libc::c_ulonglong,
    1354899394473308 as libc::c_ulonglong,
    3636602998800808 as libc::c_ulonglong,
    2709296679846364 as libc::c_ulonglong,
    7253362091963 as libc::c_ulonglong,
    3585950735562744 as libc::c_ulonglong,
    935775991758415 as libc::c_ulonglong,
    4108078106735201 as libc::c_ulonglong,
    556081800336307 as libc::c_ulonglong,
    229585977163057 as libc::c_ulonglong,
    4055594186679801 as libc::c_ulonglong,
    1767681004944933 as libc::c_ulonglong,
    1432634922083242 as libc::c_ulonglong,
    534935602949197 as libc::c_ulonglong,
    251753159522567 as libc::c_ulonglong,
    2846474078499321 as libc::c_ulonglong,
    4488649590348702 as libc::c_ulonglong,
    2437476916025038 as libc::c_ulonglong,
    3040577412822874 as libc::c_ulonglong,
    79405234918614 as libc::c_ulonglong,
    3030621226551508 as libc::c_ulonglong,
    2801117003929806 as libc::c_ulonglong,
    1642927515498422 as libc::c_ulonglong,
    2802725079726297 as libc::c_ulonglong,
    8472780626107 as libc::c_ulonglong,
    866068070352655 as libc::c_ulonglong,
    188080768545106 as libc::c_ulonglong,
    2152119998903058 as libc::c_ulonglong,
    3391239985029665 as libc::c_ulonglong,
    23820026013564 as libc::c_ulonglong,
    2965064154891949 as libc::c_ulonglong,
    1846516097921398 as libc::c_ulonglong,
    4418379948133146 as libc::c_ulonglong,
    3137755426942400 as libc::c_ulonglong,
    47705291301781 as libc::c_ulonglong,
    4278533051105665 as libc::c_ulonglong,
    3453643211214931 as libc::c_ulonglong,
    3379734319145156 as libc::c_ulonglong,
    3762442192097039 as libc::c_ulonglong,
    40243003528694 as libc::c_ulonglong,
    4063448994211201 as libc::c_ulonglong,
    5697015368785 as libc::c_ulonglong,
    1006545411838613 as libc::c_ulonglong,
    4242291693755210 as libc::c_ulonglong,
    135184629190512 as libc::c_ulonglong,
    264898689131035 as libc::c_ulonglong,
    611796474823597 as libc::c_ulonglong,
    3255382250029089 as libc::c_ulonglong,
    3490429246984696 as libc::c_ulonglong,
    236558595864362 as libc::c_ulonglong,
    2055934691551704 as libc::c_ulonglong,
    1487711670114502 as libc::c_ulonglong,
    1823930698221632 as libc::c_ulonglong,
    2130937287438472 as libc::c_ulonglong,
    154610053389779 as libc::c_ulonglong,
    2746573287023216 as libc::c_ulonglong,
    2430987262221221 as libc::c_ulonglong,
    1668741642878689 as libc::c_ulonglong,
    904982541243977 as libc::c_ulonglong,
    56087343124948 as libc::c_ulonglong,
    393905062353536 as libc::c_ulonglong,
    412681877350188 as libc::c_ulonglong,
    3153602040979977 as libc::c_ulonglong,
    4466820876224989 as libc::c_ulonglong,
    146579165617857 as libc::c_ulonglong,
    2628741216508991 as libc::c_ulonglong,
    747994231529806 as libc::c_ulonglong,
    750506569317681 as libc::c_ulonglong,
    1887492790748779 as libc::c_ulonglong,
    35259008682771 as libc::c_ulonglong,
    2085116434894208 as libc::c_ulonglong,
    543291398921711 as libc::c_ulonglong,
    1144362007901552 as libc::c_ulonglong,
    679305136036846 as libc::c_ulonglong,
    141090902244489 as libc::c_ulonglong,
    632480954474859 as libc::c_ulonglong,
    2384513102652591 as libc::c_ulonglong,
    2225529790159790 as libc::c_ulonglong,
    692258664851625 as libc::c_ulonglong,
    198681843567699 as libc::c_ulonglong,
    2397092587228181 as libc::c_ulonglong,
    145862822166614 as libc::c_ulonglong,
    196976540479452 as libc::c_ulonglong,
    3321831130141455 as libc::c_ulonglong,
    69266673089832 as libc::c_ulonglong,
    4469644227342284 as libc::c_ulonglong,
    3899271145504796 as libc::c_ulonglong,
    1261890974076660 as libc::c_ulonglong,
    525357673886694 as libc::c_ulonglong,
    182135997828583 as libc::c_ulonglong,
    4292760618810332 as libc::c_ulonglong,
    3404186545541683 as libc::c_ulonglong,
    312297386688768 as libc::c_ulonglong,
    204377466824608 as libc::c_ulonglong,
    230900767857952 as libc::c_ulonglong,
    3871485172339693 as libc::c_ulonglong,
    779449329662955 as libc::c_ulonglong,
    978655822464694 as libc::c_ulonglong,
    2278252139594027 as libc::c_ulonglong,
    104641527040382 as libc::c_ulonglong,
    3528840153625765 as libc::c_ulonglong,
    4484699080275273 as libc::c_ulonglong,
    1463971951102316 as libc::c_ulonglong,
    4013910812844749 as libc::c_ulonglong,
    228915589433620 as libc::c_ulonglong,
    1209641433482461 as libc::c_ulonglong,
    4043178788774759 as libc::c_ulonglong,
    3008668238856634 as libc::c_ulonglong,
    1448425089071412 as libc::c_ulonglong,
    26269719725037 as libc::c_ulonglong,
    3330785027545223 as libc::c_ulonglong,
    852657975349259 as libc::c_ulonglong,
    227245054466105 as libc::c_ulonglong,
    1534632353984777 as libc::c_ulonglong,
    207715098574660 as libc::c_ulonglong,
    3209837527352280 as libc::c_ulonglong,
    4051688046309066 as libc::c_ulonglong,
    3839009590725955 as libc::c_ulonglong,
    1321506437398842 as libc::c_ulonglong,
    68340219159928 as libc::c_ulonglong,
    1806950276956275 as libc::c_ulonglong,
    3923908055275295 as libc::c_ulonglong,
    743963253393575 as libc::c_ulonglong,
    42162407478783 as libc::c_ulonglong,
    261334584474610 as libc::c_ulonglong,
    3728224928885214 as libc::c_ulonglong,
    4004701081842869 as libc::c_ulonglong,
    709043201644674 as libc::c_ulonglong,
    4267294249150171 as libc::c_ulonglong,
    255540582975025 as libc::c_ulonglong,
    875490593722211 as libc::c_ulonglong,
    796393708218375 as libc::c_ulonglong,
    14774425627956 as libc::c_ulonglong,
    1500040516752097 as libc::c_ulonglong,
    141076627721678 as libc::c_ulonglong,
    2634539368480628 as libc::c_ulonglong,
    1106488853550103 as libc::c_ulonglong,
    2346231921151930 as libc::c_ulonglong,
    897108283954283 as libc::c_ulonglong,
    64616679559843 as libc::c_ulonglong,
    400244949840943 as libc::c_ulonglong,
    1731263826831733 as libc::c_ulonglong,
    1649996579904651 as libc::c_ulonglong,
    3643693449640761 as libc::c_ulonglong,
    172543068638991 as libc::c_ulonglong,
    329537981097182 as libc::c_ulonglong,
    2029799860802869 as libc::c_ulonglong,
    4377737515208862 as libc::c_ulonglong,
    29103311051334 as libc::c_ulonglong,
    265583594111499 as libc::c_ulonglong,
    3798074876561255 as libc::c_ulonglong,
    184749333259352 as libc::c_ulonglong,
    3117395073661801 as libc::c_ulonglong,
    3695784565008833 as libc::c_ulonglong,
    64282709896721 as libc::c_ulonglong,
    1618968913246422 as libc::c_ulonglong,
    3185235128095257 as libc::c_ulonglong,
    3288745068118692 as libc::c_ulonglong,
    1963818603508782 as libc::c_ulonglong,
    281054350739495 as libc::c_ulonglong,
    1658639050810346 as libc::c_ulonglong,
    3061097601679552 as libc::c_ulonglong,
    3023781433263746 as libc::c_ulonglong,
    2770283391242475 as libc::c_ulonglong,
    144508864751908 as libc::c_ulonglong,
    173576288079856 as libc::c_ulonglong,
    46114579547054 as libc::c_ulonglong,
    1679480127300211 as libc::c_ulonglong,
    1683062051644007 as libc::c_ulonglong,
    117183826129323 as libc::c_ulonglong,
    1894068608117440 as libc::c_ulonglong,
    3846899838975733 as libc::c_ulonglong,
    4289279019496192 as libc::c_ulonglong,
    176995887914031 as libc::c_ulonglong,
    78074942938713 as libc::c_ulonglong,
    454207263265292 as libc::c_ulonglong,
    972683614054061 as libc::c_ulonglong,
    808474205144361 as libc::c_ulonglong,
    942703935951735 as libc::c_ulonglong,
    134460241077887 as libc::c_ulonglong,
    2104196179349630 as libc::c_ulonglong,
    501632371208418 as libc::c_ulonglong,
    1666838991431177 as libc::c_ulonglong,
    445606193139838 as libc::c_ulonglong,
    73704603396096 as libc::c_ulonglong,
    3140284774064777 as libc::c_ulonglong,
    1356066420820179 as libc::c_ulonglong,
    227054159419281 as libc::c_ulonglong,
    1847611229198687 as libc::c_ulonglong,
    82327838827660 as libc::c_ulonglong,
    3704027573265803 as libc::c_ulonglong,
    1585260489220244 as libc::c_ulonglong,
    4404647914931933 as libc::c_ulonglong,
    2424649827425515 as libc::c_ulonglong,
    206821944206116 as libc::c_ulonglong,
    1508635776287972 as libc::c_ulonglong,
    1933584575629676 as libc::c_ulonglong,
    1903635423783032 as libc::c_ulonglong,
    4193642165165650 as libc::c_ulonglong,
    234321074690644 as libc::c_ulonglong,
    210406774251925 as libc::c_ulonglong,
    1965845668185599 as libc::c_ulonglong,
    3059839433804731 as libc::c_ulonglong,
    1933300510683631 as libc::c_ulonglong,
    150696600689211 as libc::c_ulonglong,
    4069293682158567 as libc::c_ulonglong,
    4346344602660044 as libc::c_ulonglong,
    312200249664561 as libc::c_ulonglong,
    2495020807621840 as libc::c_ulonglong,
    1912707714385 as libc::c_ulonglong,
    299345978159762 as libc::c_ulonglong,
    1164752722686920 as libc::c_ulonglong,
    225322433710338 as libc::c_ulonglong,
    3128747381283759 as libc::c_ulonglong,
    275659067815583 as libc::c_ulonglong,
    1489671057429039 as libc::c_ulonglong,
    1567693343342676 as libc::c_ulonglong,
    921672046098071 as libc::c_ulonglong,
    3707418899384085 as libc::c_ulonglong,
    54646424931593 as libc::c_ulonglong,
    4026733380127147 as libc::c_ulonglong,
    2933435393699231 as libc::c_ulonglong,
    3356593659521967 as libc::c_ulonglong,
    3637750749325529 as libc::c_ulonglong,
    232939412379045 as libc::c_ulonglong,
    2298399636043069 as libc::c_ulonglong,
    270361546063041 as libc::c_ulonglong,
    2523933572551420 as libc::c_ulonglong,
    3456896091572950 as libc::c_ulonglong,
    185447004732850 as libc::c_ulonglong,
    429322937697821 as libc::c_ulonglong,
    2579704215668222 as libc::c_ulonglong,
    695065378803349 as libc::c_ulonglong,
    3987916247731243 as libc::c_ulonglong,
    255159546348233 as libc::c_ulonglong,
    3057777929921282 as libc::c_ulonglong,
    1608970699916312 as libc::c_ulonglong,
    1902369623063807 as libc::c_ulonglong,
    1413619643652777 as libc::c_ulonglong,
    94983996321227 as libc::c_ulonglong,
    2832873179548050 as libc::c_ulonglong,
    4335430233622555 as libc::c_ulonglong,
    1559023976028843 as libc::c_ulonglong,
    3297181988648895 as libc::c_ulonglong,
    100072021232323 as libc::c_ulonglong,
    2124984034109675 as libc::c_ulonglong,
    4501252835618918 as libc::c_ulonglong,
    2053336899483297 as libc::c_ulonglong,
    638807226463876 as libc::c_ulonglong,
    278445213600634 as libc::c_ulonglong,
    2311236445660555 as libc::c_ulonglong,
    303317664040012 as libc::c_ulonglong,
    2659353858089024 as libc::c_ulonglong,
    3598827423980130 as libc::c_ulonglong,
    176059343827873 as libc::c_ulonglong,
    3891639526275437 as libc::c_ulonglong,
    252823982819463 as libc::c_ulonglong,
    3404823300622345 as libc::c_ulonglong,
    2758370772497456 as libc::c_ulonglong,
    91397496598783 as libc::c_ulonglong,
    2248661144141892 as libc::c_ulonglong,
    491087075271969 as libc::c_ulonglong,
    1786344894571315 as libc::c_ulonglong,
    452497694885923 as libc::c_ulonglong,
    34039628873357 as libc::c_ulonglong,
    2116503165025197 as libc::c_ulonglong,
    4436733709429923 as libc::c_ulonglong,
    3045800776819238 as libc::c_ulonglong,
    1385518906078375 as libc::c_ulonglong,
    110495603336764 as libc::c_ulonglong,
    4051447296249587 as libc::c_ulonglong,
    1103557421498625 as libc::c_ulonglong,
    1840785058439622 as libc::c_ulonglong,
    425322753992314 as libc::c_ulonglong,
    98330046771676 as libc::c_ulonglong,
    365407468686431 as libc::c_ulonglong,
    2611246859977123 as libc::c_ulonglong,
    3050253933135339 as libc::c_ulonglong,
    1006482220896688 as libc::c_ulonglong,
    166818196428389 as libc::c_ulonglong,
    3415236093104372 as libc::c_ulonglong,
    1762308883882288 as libc::c_ulonglong,
    1327828123094558 as libc::c_ulonglong,
    3403946425556706 as libc::c_ulonglong,
    96503464455441 as libc::c_ulonglong,
    3893015304031471 as libc::c_ulonglong,
    3740839477490397 as libc::c_ulonglong,
    2411470812852231 as libc::c_ulonglong,
    940927462436211 as libc::c_ulonglong,
    163825285911099 as libc::c_ulonglong,
    1622441495640386 as libc::c_ulonglong,
    850224095680266 as libc::c_ulonglong,
    76199085900939 as libc::c_ulonglong,
    1941852365144042 as libc::c_ulonglong,
    140326673652807 as libc::c_ulonglong,
    3161611011249524 as libc::c_ulonglong,
    317297150009965 as libc::c_ulonglong,
    2145053259340619 as libc::c_ulonglong,
    2180498176457552 as libc::c_ulonglong,
    38457740506224 as libc::c_ulonglong,
    394174899129468 as libc::c_ulonglong,
    2687474560485245 as libc::c_ulonglong,
    1542175980184516 as libc::c_ulonglong,
    1628502671124819 as libc::c_ulonglong,
    48477401124385 as libc::c_ulonglong,
    4474181600025082 as libc::c_ulonglong,
    2142747956365708 as libc::c_ulonglong,
    1638299432475478 as libc::c_ulonglong,
    2005869320353249 as libc::c_ulonglong,
    112292630760956 as libc::c_ulonglong,
    1887521965171588 as libc::c_ulonglong,
    457587531429696 as libc::c_ulonglong,
    840994209504042 as libc::c_ulonglong,
    4268060856325798 as libc::c_ulonglong,
    195597993440388 as libc::c_ulonglong,
    4148484749020338 as libc::c_ulonglong,
    2074885000909672 as libc::c_ulonglong,
    2309839019263165 as libc::c_ulonglong,
    2087616209681024 as libc::c_ulonglong,
    257214370719966 as libc::c_ulonglong,
    2331363508376581 as libc::c_ulonglong,
    1233124357504711 as libc::c_ulonglong,
    2849542202650296 as libc::c_ulonglong,
    3790982825325736 as libc::c_ulonglong,
    13381453503890 as libc::c_ulonglong,
    1665246594531069 as libc::c_ulonglong,
    4165624287443904 as libc::c_ulonglong,
    3418759698027493 as libc::c_ulonglong,
    2118493255117399 as libc::c_ulonglong,
    136249206366067 as libc::c_ulonglong,
    4064050233283309 as libc::c_ulonglong,
    1368779887911300 as libc::c_ulonglong,
    4370550759530269 as libc::c_ulonglong,
    66992990631341 as libc::c_ulonglong,
    84442368922270 as libc::c_ulonglong,
    2139322635321394 as libc::c_ulonglong,
    2076163483726795 as libc::c_ulonglong,
    657097866349103 as libc::c_ulonglong,
    2095579409488071 as libc::c_ulonglong,
    226525774791341 as libc::c_ulonglong,
    4445744257665359 as libc::c_ulonglong,
    2035752839278107 as libc::c_ulonglong,
    1998242662838304 as libc::c_ulonglong,
    1601548415521694 as libc::c_ulonglong,
    151297684296198 as libc::c_ulonglong,
    1350963039017303 as libc::c_ulonglong,
    2624916349548281 as libc::c_ulonglong,
    2018863259670197 as libc::c_ulonglong,
    2717274357461290 as libc::c_ulonglong,
    94024796961533 as libc::c_ulonglong,
    711335520409111 as libc::c_ulonglong,
    4322093765820263 as libc::c_ulonglong,
    2041650358174649 as libc::c_ulonglong,
    3439791603157577 as libc::c_ulonglong,
    179292018616267 as libc::c_ulonglong,
    2436436921286669 as libc::c_ulonglong,
    3905268797208340 as libc::c_ulonglong,
    2829194895162985 as libc::c_ulonglong,
    1355175382191543 as libc::c_ulonglong,
    55128779761539 as libc::c_ulonglong,
    2648428998786922 as libc::c_ulonglong,
    869805912573515 as libc::c_ulonglong,
    3706708942847864 as libc::c_ulonglong,
    2785288916584667 as libc::c_ulonglong,
    37156862850147 as libc::c_ulonglong,
    1422245336293228 as libc::c_ulonglong,
    4497066058933021 as libc::c_ulonglong,
    85588912978349 as libc::c_ulonglong,
    2616252221194611 as libc::c_ulonglong,
    53506393720989 as libc::c_ulonglong,
    3727539190732644 as libc::c_ulonglong,
    872132446545237 as libc::c_ulonglong,
    933583590986077 as libc::c_ulonglong,
    3794591170581203 as libc::c_ulonglong,
    167875550514069 as libc::c_ulonglong,
    2267466834993297 as libc::c_ulonglong,
    3072652681756816 as libc::c_ulonglong,
    2108499037430803 as libc::c_ulonglong,
    1606735192928366 as libc::c_ulonglong,
    72339568815255 as libc::c_ulonglong,
    3258484260684219 as libc::c_ulonglong,
    3277927277719855 as libc::c_ulonglong,
    2459560373011535 as libc::c_ulonglong,
    1672794293294033 as libc::c_ulonglong,
    227460934880669 as libc::c_ulonglong,
    3702454405413705 as libc::c_ulonglong,
    106168148441676 as libc::c_ulonglong,
    1356617643071159 as libc::c_ulonglong,
    3280896569942762 as libc::c_ulonglong,
    142618711614302 as libc::c_ulonglong,
    4291782740862057 as libc::c_ulonglong,
    4141020884874235 as libc::c_ulonglong,
    3720787221267125 as libc::c_ulonglong,
    552884940089351 as libc::c_ulonglong,
    174626154407180 as libc::c_ulonglong,
    972071013326540 as libc::c_ulonglong,
    4458530419931903 as libc::c_ulonglong,
    4435168973822858 as libc::c_ulonglong,
    1902967548748411 as libc::c_ulonglong,
    53007977605840 as libc::c_ulonglong,
    2453997334323925 as libc::c_ulonglong,
    3653077937283262 as libc::c_ulonglong,
    850660265046356 as libc::c_ulonglong,
    312721924805450 as libc::c_ulonglong,
    268503679240683 as libc::c_ulonglong,
    256960167714122 as libc::c_ulonglong,
    1474492507858350 as libc::c_ulonglong,
    2456345526438488 as libc::c_ulonglong,
    3686029507160255 as libc::c_ulonglong,
    279158933010398 as libc::c_ulonglong,
    3646946293948063 as libc::c_ulonglong,
    704477527214036 as libc::c_ulonglong,
    3387744169891031 as libc::c_ulonglong,
    3772622670980241 as libc::c_ulonglong,
    136368897543304 as libc::c_ulonglong,
    3744894052577607 as libc::c_ulonglong,
    1976007214443430 as libc::c_ulonglong,
    2090045379763451 as libc::c_ulonglong,
    968565474458988 as libc::c_ulonglong,
    234295114806066 as libc::c_ulonglong,
];
#[inline]
unsafe extern "C" fn Hacl_K256_Field_is_felem_zero_vartime(
    mut f: *mut uint64_t,
) -> bool {
    let mut f0: uint64_t = *f.offset(0 as libc::c_uint as isize);
    let mut f1: uint64_t = *f.offset(1 as libc::c_uint as isize);
    let mut f2: uint64_t = *f.offset(2 as libc::c_uint as isize);
    let mut f3: uint64_t = *f.offset(3 as libc::c_uint as isize);
    let mut f4: uint64_t = *f.offset(4 as libc::c_uint as isize);
    return f0 == 0 as libc::c_ulonglong && f1 == 0 as libc::c_ulonglong
        && f2 == 0 as libc::c_ulonglong && f3 == 0 as libc::c_ulonglong
        && f4 == 0 as libc::c_ulonglong;
}
#[inline]
unsafe extern "C" fn Hacl_K256_Field_is_felem_eq_vartime(
    mut f1: *mut uint64_t,
    mut f2: *mut uint64_t,
) -> bool {
    let mut a0: uint64_t = *f1.offset(0 as libc::c_uint as isize);
    let mut a1: uint64_t = *f1.offset(1 as libc::c_uint as isize);
    let mut a2: uint64_t = *f1.offset(2 as libc::c_uint as isize);
    let mut a3: uint64_t = *f1.offset(3 as libc::c_uint as isize);
    let mut a4: uint64_t = *f1.offset(4 as libc::c_uint as isize);
    let mut b0: uint64_t = *f2.offset(0 as libc::c_uint as isize);
    let mut b1: uint64_t = *f2.offset(1 as libc::c_uint as isize);
    let mut b2: uint64_t = *f2.offset(2 as libc::c_uint as isize);
    let mut b3: uint64_t = *f2.offset(3 as libc::c_uint as isize);
    let mut b4: uint64_t = *f2.offset(4 as libc::c_uint as isize);
    return a0 == b0 && a1 == b1 && a2 == b2 && a3 == b3 && a4 == b4;
}
#[inline]
unsafe extern "C" fn Hacl_K256_Field_is_felem_lt_prime_minus_order_vartime(
    mut f: *mut uint64_t,
) -> bool {
    let mut f0: uint64_t = *f.offset(0 as libc::c_uint as isize);
    let mut f1: uint64_t = *f.offset(1 as libc::c_uint as isize);
    let mut f2: uint64_t = *f.offset(2 as libc::c_uint as isize);
    let mut f3: uint64_t = *f.offset(3 as libc::c_uint as isize);
    let mut f4: uint64_t = *f.offset(4 as libc::c_uint as isize);
    if f4 > 0 as libc::c_ulonglong || f3 > 0 as libc::c_ulonglong {
        return 0 as libc::c_int != 0;
    }
    if f2 < 0x1455123 as libc::c_ulonglong {
        return 1 as libc::c_int != 0;
    }
    if f2 > 0x1455123 as libc::c_ulonglong {
        return 0 as libc::c_int != 0;
    }
    if f1 < 0x1950b75fc4402 as libc::c_ulonglong {
        return 1 as libc::c_int != 0;
    }
    if f1 > 0x1950b75fc4402 as libc::c_ulonglong {
        return 0 as libc::c_int != 0;
    }
    return f0 < 0xda1722fc9baee as libc::c_ulonglong;
}
#[inline]
unsafe extern "C" fn Hacl_K256_Field_load_felem(
    mut f: *mut uint64_t,
    mut b: *mut uint8_t,
) {
    let mut tmp: [uint64_t; 4] = [0 as libc::c_uint as uint64_t, 0, 0, 0];
    let mut i: uint32_t = 0 as libc::c_uint;
    let mut bj: *mut uint8_t = b.offset(i.wrapping_mul(8 as libc::c_uint) as isize);
    let mut u: uint64_t = if 0 != 0 {
        (load64(bj) & 0xff00000000000000 as libc::c_ulonglong) >> 56 as libc::c_int
            | (load64(bj) & 0xff000000000000 as libc::c_ulonglong) >> 40 as libc::c_int
            | (load64(bj) & 0xff0000000000 as libc::c_ulonglong) >> 24 as libc::c_int
            | (load64(bj) & 0xff00000000 as libc::c_ulonglong) >> 8 as libc::c_int
            | (load64(bj) & 0xff000000 as libc::c_ulonglong) << 8 as libc::c_int
            | (load64(bj) & 0xff0000 as libc::c_ulonglong) << 24 as libc::c_int
            | (load64(bj) & 0xff00 as libc::c_ulonglong) << 40 as libc::c_int
            | (load64(bj) & 0xff as libc::c_ulonglong) << 56 as libc::c_int
    } else {
        _OSSwapInt64(load64(bj))
    };
    let mut r: uint64_t = u;
    let mut x: uint64_t = r;
    let mut os: *mut uint64_t = tmp.as_mut_ptr();
    *os.offset(i as isize) = x;
    i = (i as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut bj_0: *mut uint8_t = b.offset(i.wrapping_mul(8 as libc::c_uint) as isize);
    let mut u_0: uint64_t = if 0 != 0 {
        (load64(bj_0) & 0xff00000000000000 as libc::c_ulonglong) >> 56 as libc::c_int
            | (load64(bj_0) & 0xff000000000000 as libc::c_ulonglong) >> 40 as libc::c_int
            | (load64(bj_0) & 0xff0000000000 as libc::c_ulonglong) >> 24 as libc::c_int
            | (load64(bj_0) & 0xff00000000 as libc::c_ulonglong) >> 8 as libc::c_int
            | (load64(bj_0) & 0xff000000 as libc::c_ulonglong) << 8 as libc::c_int
            | (load64(bj_0) & 0xff0000 as libc::c_ulonglong) << 24 as libc::c_int
            | (load64(bj_0) & 0xff00 as libc::c_ulonglong) << 40 as libc::c_int
            | (load64(bj_0) & 0xff as libc::c_ulonglong) << 56 as libc::c_int
    } else {
        _OSSwapInt64(load64(bj_0))
    };
    let mut r_0: uint64_t = u_0;
    let mut x_0: uint64_t = r_0;
    let mut os_0: *mut uint64_t = tmp.as_mut_ptr();
    *os_0.offset(i as isize) = x_0;
    i = (i as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut bj_1: *mut uint8_t = b.offset(i.wrapping_mul(8 as libc::c_uint) as isize);
    let mut u_1: uint64_t = if 0 != 0 {
        (load64(bj_1) & 0xff00000000000000 as libc::c_ulonglong) >> 56 as libc::c_int
            | (load64(bj_1) & 0xff000000000000 as libc::c_ulonglong) >> 40 as libc::c_int
            | (load64(bj_1) & 0xff0000000000 as libc::c_ulonglong) >> 24 as libc::c_int
            | (load64(bj_1) & 0xff00000000 as libc::c_ulonglong) >> 8 as libc::c_int
            | (load64(bj_1) & 0xff000000 as libc::c_ulonglong) << 8 as libc::c_int
            | (load64(bj_1) & 0xff0000 as libc::c_ulonglong) << 24 as libc::c_int
            | (load64(bj_1) & 0xff00 as libc::c_ulonglong) << 40 as libc::c_int
            | (load64(bj_1) & 0xff as libc::c_ulonglong) << 56 as libc::c_int
    } else {
        _OSSwapInt64(load64(bj_1))
    };
    let mut r_1: uint64_t = u_1;
    let mut x_1: uint64_t = r_1;
    let mut os_1: *mut uint64_t = tmp.as_mut_ptr();
    *os_1.offset(i as isize) = x_1;
    i = (i as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut bj_2: *mut uint8_t = b.offset(i.wrapping_mul(8 as libc::c_uint) as isize);
    let mut u_2: uint64_t = if 0 != 0 {
        (load64(bj_2) & 0xff00000000000000 as libc::c_ulonglong) >> 56 as libc::c_int
            | (load64(bj_2) & 0xff000000000000 as libc::c_ulonglong) >> 40 as libc::c_int
            | (load64(bj_2) & 0xff0000000000 as libc::c_ulonglong) >> 24 as libc::c_int
            | (load64(bj_2) & 0xff00000000 as libc::c_ulonglong) >> 8 as libc::c_int
            | (load64(bj_2) & 0xff000000 as libc::c_ulonglong) << 8 as libc::c_int
            | (load64(bj_2) & 0xff0000 as libc::c_ulonglong) << 24 as libc::c_int
            | (load64(bj_2) & 0xff00 as libc::c_ulonglong) << 40 as libc::c_int
            | (load64(bj_2) & 0xff as libc::c_ulonglong) << 56 as libc::c_int
    } else {
        _OSSwapInt64(load64(bj_2))
    };
    let mut r_2: uint64_t = u_2;
    let mut x_2: uint64_t = r_2;
    let mut os_2: *mut uint64_t = tmp.as_mut_ptr();
    *os_2.offset(i as isize) = x_2;
    i = (i as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut s0: uint64_t = tmp[3 as libc::c_uint as usize];
    let mut s1: uint64_t = tmp[2 as libc::c_uint as usize];
    let mut s2: uint64_t = tmp[1 as libc::c_uint as usize];
    let mut s3: uint64_t = tmp[0 as libc::c_uint as usize];
    let mut f00: uint64_t = s0 & 0xfffffffffffff as libc::c_ulonglong;
    let mut f10: uint64_t = s0 >> 52 as libc::c_uint
        | (s1 & 0xffffffffff as libc::c_ulonglong) << 12 as libc::c_uint;
    let mut f20: uint64_t = s1 >> 40 as libc::c_uint
        | (s2 & 0xfffffff as libc::c_ulonglong) << 24 as libc::c_uint;
    let mut f30: uint64_t = s2 >> 28 as libc::c_uint
        | (s3 & 0xffff as libc::c_ulonglong) << 36 as libc::c_uint;
    let mut f40: uint64_t = s3 >> 16 as libc::c_uint;
    let mut f0: uint64_t = f00;
    let mut f1: uint64_t = f10;
    let mut f2: uint64_t = f20;
    let mut f3: uint64_t = f30;
    let mut f4: uint64_t = f40;
    *f.offset(0 as libc::c_uint as isize) = f0;
    *f.offset(1 as libc::c_uint as isize) = f1;
    *f.offset(2 as libc::c_uint as isize) = f2;
    *f.offset(3 as libc::c_uint as isize) = f3;
    *f.offset(4 as libc::c_uint as isize) = f4;
}
#[inline]
unsafe extern "C" fn Hacl_K256_Field_load_felem_lt_prime_vartime(
    mut f: *mut uint64_t,
    mut b: *mut uint8_t,
) -> bool {
    Hacl_K256_Field_load_felem(f, b);
    let mut f0: uint64_t = *f.offset(0 as libc::c_uint as isize);
    let mut f1: uint64_t = *f.offset(1 as libc::c_uint as isize);
    let mut f2: uint64_t = *f.offset(2 as libc::c_uint as isize);
    let mut f3: uint64_t = *f.offset(3 as libc::c_uint as isize);
    let mut f4: uint64_t = *f.offset(4 as libc::c_uint as isize);
    let mut is_ge_p: bool = f0 >= 0xffffefffffc2f as libc::c_ulonglong
        && f1 == 0xfffffffffffff as libc::c_ulonglong
        && f2 == 0xfffffffffffff as libc::c_ulonglong
        && f3 == 0xfffffffffffff as libc::c_ulonglong
        && f4 == 0xffffffffffff as libc::c_ulonglong;
    return !is_ge_p;
}
#[inline]
unsafe extern "C" fn Hacl_K256_Field_store_felem(
    mut b: *mut uint8_t,
    mut f: *mut uint64_t,
) {
    let mut tmp: [uint64_t; 4] = [0 as libc::c_uint as uint64_t, 0, 0, 0];
    let mut f00: uint64_t = *f.offset(0 as libc::c_uint as isize);
    let mut f10: uint64_t = *f.offset(1 as libc::c_uint as isize);
    let mut f20: uint64_t = *f.offset(2 as libc::c_uint as isize);
    let mut f30: uint64_t = *f.offset(3 as libc::c_uint as isize);
    let mut f4: uint64_t = *f.offset(4 as libc::c_uint as isize);
    let mut o0: uint64_t = f00 | f10 << 52 as libc::c_uint;
    let mut o1: uint64_t = f10 >> 12 as libc::c_uint | f20 << 40 as libc::c_uint;
    let mut o2: uint64_t = f20 >> 24 as libc::c_uint | f30 << 28 as libc::c_uint;
    let mut o3: uint64_t = f30 >> 36 as libc::c_uint | f4 << 16 as libc::c_uint;
    let mut f0: uint64_t = o0;
    let mut f1: uint64_t = o1;
    let mut f2: uint64_t = o2;
    let mut f3: uint64_t = o3;
    tmp[0 as libc::c_uint as usize] = f3;
    tmp[1 as libc::c_uint as usize] = f2;
    tmp[2 as libc::c_uint as usize] = f1;
    tmp[3 as libc::c_uint as usize] = f0;
    let mut i: uint32_t = 0 as libc::c_uint;
    store64(
        b.offset(i.wrapping_mul(8 as libc::c_uint) as isize),
        if 0 != 0 {
            (tmp[i as usize] & 0xff00000000000000 as libc::c_ulonglong)
                >> 56 as libc::c_int
                | (tmp[i as usize] & 0xff000000000000 as libc::c_ulonglong)
                    >> 40 as libc::c_int
                | (tmp[i as usize] & 0xff0000000000 as libc::c_ulonglong)
                    >> 24 as libc::c_int
                | (tmp[i as usize] & 0xff00000000 as libc::c_ulonglong)
                    >> 8 as libc::c_int
                | (tmp[i as usize] & 0xff000000 as libc::c_ulonglong) << 8 as libc::c_int
                | (tmp[i as usize] & 0xff0000 as libc::c_ulonglong) << 24 as libc::c_int
                | (tmp[i as usize] & 0xff00 as libc::c_ulonglong) << 40 as libc::c_int
                | (tmp[i as usize] & 0xff as libc::c_ulonglong) << 56 as libc::c_int
        } else {
            _OSSwapInt64(tmp[i as usize])
        },
    );
    i = (i as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    store64(
        b.offset(i.wrapping_mul(8 as libc::c_uint) as isize),
        if 0 != 0 {
            (tmp[i as usize] & 0xff00000000000000 as libc::c_ulonglong)
                >> 56 as libc::c_int
                | (tmp[i as usize] & 0xff000000000000 as libc::c_ulonglong)
                    >> 40 as libc::c_int
                | (tmp[i as usize] & 0xff0000000000 as libc::c_ulonglong)
                    >> 24 as libc::c_int
                | (tmp[i as usize] & 0xff00000000 as libc::c_ulonglong)
                    >> 8 as libc::c_int
                | (tmp[i as usize] & 0xff000000 as libc::c_ulonglong) << 8 as libc::c_int
                | (tmp[i as usize] & 0xff0000 as libc::c_ulonglong) << 24 as libc::c_int
                | (tmp[i as usize] & 0xff00 as libc::c_ulonglong) << 40 as libc::c_int
                | (tmp[i as usize] & 0xff as libc::c_ulonglong) << 56 as libc::c_int
        } else {
            _OSSwapInt64(tmp[i as usize])
        },
    );
    i = (i as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    store64(
        b.offset(i.wrapping_mul(8 as libc::c_uint) as isize),
        if 0 != 0 {
            (tmp[i as usize] & 0xff00000000000000 as libc::c_ulonglong)
                >> 56 as libc::c_int
                | (tmp[i as usize] & 0xff000000000000 as libc::c_ulonglong)
                    >> 40 as libc::c_int
                | (tmp[i as usize] & 0xff0000000000 as libc::c_ulonglong)
                    >> 24 as libc::c_int
                | (tmp[i as usize] & 0xff00000000 as libc::c_ulonglong)
                    >> 8 as libc::c_int
                | (tmp[i as usize] & 0xff000000 as libc::c_ulonglong) << 8 as libc::c_int
                | (tmp[i as usize] & 0xff0000 as libc::c_ulonglong) << 24 as libc::c_int
                | (tmp[i as usize] & 0xff00 as libc::c_ulonglong) << 40 as libc::c_int
                | (tmp[i as usize] & 0xff as libc::c_ulonglong) << 56 as libc::c_int
        } else {
            _OSSwapInt64(tmp[i as usize])
        },
    );
    i = (i as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    store64(
        b.offset(i.wrapping_mul(8 as libc::c_uint) as isize),
        if 0 != 0 {
            (tmp[i as usize] & 0xff00000000000000 as libc::c_ulonglong)
                >> 56 as libc::c_int
                | (tmp[i as usize] & 0xff000000000000 as libc::c_ulonglong)
                    >> 40 as libc::c_int
                | (tmp[i as usize] & 0xff0000000000 as libc::c_ulonglong)
                    >> 24 as libc::c_int
                | (tmp[i as usize] & 0xff00000000 as libc::c_ulonglong)
                    >> 8 as libc::c_int
                | (tmp[i as usize] & 0xff000000 as libc::c_ulonglong) << 8 as libc::c_int
                | (tmp[i as usize] & 0xff0000 as libc::c_ulonglong) << 24 as libc::c_int
                | (tmp[i as usize] & 0xff00 as libc::c_ulonglong) << 40 as libc::c_int
                | (tmp[i as usize] & 0xff as libc::c_ulonglong) << 56 as libc::c_int
        } else {
            _OSSwapInt64(tmp[i as usize])
        },
    );
    i = (i as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
}
#[inline]
unsafe extern "C" fn Hacl_K256_Field_fmul_small_num(
    mut out: *mut uint64_t,
    mut f: *mut uint64_t,
    mut num: uint64_t,
) {
    let mut f00: uint64_t = *f.offset(0 as libc::c_uint as isize);
    let mut f10: uint64_t = *f.offset(1 as libc::c_uint as isize);
    let mut f20: uint64_t = *f.offset(2 as libc::c_uint as isize);
    let mut f30: uint64_t = *f.offset(3 as libc::c_uint as isize);
    let mut f40: uint64_t = *f.offset(4 as libc::c_uint as isize);
    let mut o0: uint64_t = f00 * num;
    let mut o1: uint64_t = f10 * num;
    let mut o2: uint64_t = f20 * num;
    let mut o3: uint64_t = f30 * num;
    let mut o4: uint64_t = f40 * num;
    let mut f0: uint64_t = o0;
    let mut f1: uint64_t = o1;
    let mut f2: uint64_t = o2;
    let mut f3: uint64_t = o3;
    let mut f4: uint64_t = o4;
    *out.offset(0 as libc::c_uint as isize) = f0;
    *out.offset(1 as libc::c_uint as isize) = f1;
    *out.offset(2 as libc::c_uint as isize) = f2;
    *out.offset(3 as libc::c_uint as isize) = f3;
    *out.offset(4 as libc::c_uint as isize) = f4;
}
#[inline]
unsafe extern "C" fn Hacl_K256_Field_fadd(
    mut out: *mut uint64_t,
    mut f1: *mut uint64_t,
    mut f2: *mut uint64_t,
) {
    let mut a0: uint64_t = *f1.offset(0 as libc::c_uint as isize);
    let mut a1: uint64_t = *f1.offset(1 as libc::c_uint as isize);
    let mut a2: uint64_t = *f1.offset(2 as libc::c_uint as isize);
    let mut a3: uint64_t = *f1.offset(3 as libc::c_uint as isize);
    let mut a4: uint64_t = *f1.offset(4 as libc::c_uint as isize);
    let mut b0: uint64_t = *f2.offset(0 as libc::c_uint as isize);
    let mut b1: uint64_t = *f2.offset(1 as libc::c_uint as isize);
    let mut b2: uint64_t = *f2.offset(2 as libc::c_uint as isize);
    let mut b3: uint64_t = *f2.offset(3 as libc::c_uint as isize);
    let mut b4: uint64_t = *f2.offset(4 as libc::c_uint as isize);
    let mut o0: uint64_t = a0.wrapping_add(b0);
    let mut o1: uint64_t = a1.wrapping_add(b1);
    let mut o2: uint64_t = a2.wrapping_add(b2);
    let mut o3: uint64_t = a3.wrapping_add(b3);
    let mut o4: uint64_t = a4.wrapping_add(b4);
    let mut f0: uint64_t = o0;
    let mut f11: uint64_t = o1;
    let mut f21: uint64_t = o2;
    let mut f3: uint64_t = o3;
    let mut f4: uint64_t = o4;
    *out.offset(0 as libc::c_uint as isize) = f0;
    *out.offset(1 as libc::c_uint as isize) = f11;
    *out.offset(2 as libc::c_uint as isize) = f21;
    *out.offset(3 as libc::c_uint as isize) = f3;
    *out.offset(4 as libc::c_uint as isize) = f4;
}
#[inline]
unsafe extern "C" fn Hacl_K256_Field_fsub(
    mut out: *mut uint64_t,
    mut f1: *mut uint64_t,
    mut f2: *mut uint64_t,
    mut x: uint64_t,
) {
    let mut a0: uint64_t = *f1.offset(0 as libc::c_uint as isize);
    let mut a1: uint64_t = *f1.offset(1 as libc::c_uint as isize);
    let mut a2: uint64_t = *f1.offset(2 as libc::c_uint as isize);
    let mut a3: uint64_t = *f1.offset(3 as libc::c_uint as isize);
    let mut a4: uint64_t = *f1.offset(4 as libc::c_uint as isize);
    let mut b0: uint64_t = *f2.offset(0 as libc::c_uint as isize);
    let mut b1: uint64_t = *f2.offset(1 as libc::c_uint as isize);
    let mut b2: uint64_t = *f2.offset(2 as libc::c_uint as isize);
    let mut b3: uint64_t = *f2.offset(3 as libc::c_uint as isize);
    let mut b4: uint64_t = *f2.offset(4 as libc::c_uint as isize);
    let mut r00: uint64_t = (9007190664804446 as libc::c_ulonglong)
        .wrapping_mul(x)
        .wrapping_sub(b0);
    let mut r10: uint64_t = (9007199254740990 as libc::c_ulonglong)
        .wrapping_mul(x)
        .wrapping_sub(b1);
    let mut r20: uint64_t = (9007199254740990 as libc::c_ulonglong)
        .wrapping_mul(x)
        .wrapping_sub(b2);
    let mut r30: uint64_t = (9007199254740990 as libc::c_ulonglong)
        .wrapping_mul(x)
        .wrapping_sub(b3);
    let mut r40: uint64_t = (562949953421310 as libc::c_ulonglong)
        .wrapping_mul(x)
        .wrapping_sub(b4);
    let mut r0: uint64_t = r00;
    let mut r1: uint64_t = r10;
    let mut r2: uint64_t = r20;
    let mut r3: uint64_t = r30;
    let mut r4: uint64_t = r40;
    let mut o0: uint64_t = a0.wrapping_add(r0);
    let mut o1: uint64_t = a1.wrapping_add(r1);
    let mut o2: uint64_t = a2.wrapping_add(r2);
    let mut o3: uint64_t = a3.wrapping_add(r3);
    let mut o4: uint64_t = a4.wrapping_add(r4);
    let mut f0: uint64_t = o0;
    let mut f11: uint64_t = o1;
    let mut f21: uint64_t = o2;
    let mut f3: uint64_t = o3;
    let mut f4: uint64_t = o4;
    *out.offset(0 as libc::c_uint as isize) = f0;
    *out.offset(1 as libc::c_uint as isize) = f11;
    *out.offset(2 as libc::c_uint as isize) = f21;
    *out.offset(3 as libc::c_uint as isize) = f3;
    *out.offset(4 as libc::c_uint as isize) = f4;
}
#[inline]
unsafe extern "C" fn Hacl_K256_Field_fmul(
    mut out: *mut uint64_t,
    mut f1: *mut uint64_t,
    mut f2: *mut uint64_t,
) {
    let mut a0: uint64_t = *f1.offset(0 as libc::c_uint as isize);
    let mut a1: uint64_t = *f1.offset(1 as libc::c_uint as isize);
    let mut a2: uint64_t = *f1.offset(2 as libc::c_uint as isize);
    let mut a3: uint64_t = *f1.offset(3 as libc::c_uint as isize);
    let mut a4: uint64_t = *f1.offset(4 as libc::c_uint as isize);
    let mut b0: uint64_t = *f2.offset(0 as libc::c_uint as isize);
    let mut b1: uint64_t = *f2.offset(1 as libc::c_uint as isize);
    let mut b2: uint64_t = *f2.offset(2 as libc::c_uint as isize);
    let mut b3: uint64_t = *f2.offset(3 as libc::c_uint as isize);
    let mut b4: uint64_t = *f2.offset(4 as libc::c_uint as isize);
    let mut r: uint64_t = 0x1000003d10 as libc::c_ulonglong;
    let mut d0: FStar_UInt128_uint128 = FStar_UInt128_add_mod(
        FStar_UInt128_add_mod(
            FStar_UInt128_add_mod(
                FStar_UInt128_mul_wide(a0, b3),
                FStar_UInt128_mul_wide(a1, b2),
            ),
            FStar_UInt128_mul_wide(a2, b1),
        ),
        FStar_UInt128_mul_wide(a3, b0),
    );
    let mut c0: FStar_UInt128_uint128 = FStar_UInt128_mul_wide(a4, b4);
    let mut d1: FStar_UInt128_uint128 = FStar_UInt128_add_mod(
        d0,
        FStar_UInt128_mul_wide(r, FStar_UInt128_uint128_to_uint64(c0)),
    );
    let mut c1: uint64_t = FStar_UInt128_uint128_to_uint64(
        FStar_UInt128_shift_right(c0, 64 as libc::c_uint),
    );
    let mut t3: uint64_t = FStar_UInt128_uint128_to_uint64(d1)
        & 0xfffffffffffff as libc::c_ulonglong;
    let mut d2: FStar_UInt128_uint128 = FStar_UInt128_shift_right(
        d1,
        52 as libc::c_uint,
    );
    let mut d3: FStar_UInt128_uint128 = FStar_UInt128_add_mod(
        FStar_UInt128_add_mod(
            FStar_UInt128_add_mod(
                FStar_UInt128_add_mod(
                    FStar_UInt128_add_mod(d2, FStar_UInt128_mul_wide(a0, b4)),
                    FStar_UInt128_mul_wide(a1, b3),
                ),
                FStar_UInt128_mul_wide(a2, b2),
            ),
            FStar_UInt128_mul_wide(a3, b1),
        ),
        FStar_UInt128_mul_wide(a4, b0),
    );
    let mut d4: FStar_UInt128_uint128 = FStar_UInt128_add_mod(
        d3,
        FStar_UInt128_mul_wide(r << 12 as libc::c_uint, c1),
    );
    let mut t4: uint64_t = FStar_UInt128_uint128_to_uint64(d4)
        & 0xfffffffffffff as libc::c_ulonglong;
    let mut d5: FStar_UInt128_uint128 = FStar_UInt128_shift_right(
        d4,
        52 as libc::c_uint,
    );
    let mut tx: uint64_t = t4 >> 48 as libc::c_uint;
    let mut t4_: uint64_t = t4 & 0xffffffffffff as libc::c_ulonglong;
    let mut c2: FStar_UInt128_uint128 = FStar_UInt128_mul_wide(a0, b0);
    let mut d6: FStar_UInt128_uint128 = FStar_UInt128_add_mod(
        FStar_UInt128_add_mod(
            FStar_UInt128_add_mod(
                FStar_UInt128_add_mod(d5, FStar_UInt128_mul_wide(a1, b4)),
                FStar_UInt128_mul_wide(a2, b3),
            ),
            FStar_UInt128_mul_wide(a3, b2),
        ),
        FStar_UInt128_mul_wide(a4, b1),
    );
    let mut u0: uint64_t = FStar_UInt128_uint128_to_uint64(d6)
        & 0xfffffffffffff as libc::c_ulonglong;
    let mut d7: FStar_UInt128_uint128 = FStar_UInt128_shift_right(
        d6,
        52 as libc::c_uint,
    );
    let mut u0_: uint64_t = tx | u0 << 4 as libc::c_uint;
    let mut c3: FStar_UInt128_uint128 = FStar_UInt128_add_mod(
        c2,
        FStar_UInt128_mul_wide(u0_, r >> 4 as libc::c_uint),
    );
    let mut r0: uint64_t = FStar_UInt128_uint128_to_uint64(c3)
        & 0xfffffffffffff as libc::c_ulonglong;
    let mut c4: FStar_UInt128_uint128 = FStar_UInt128_shift_right(
        c3,
        52 as libc::c_uint,
    );
    let mut c5: FStar_UInt128_uint128 = FStar_UInt128_add_mod(
        FStar_UInt128_add_mod(c4, FStar_UInt128_mul_wide(a0, b1)),
        FStar_UInt128_mul_wide(a1, b0),
    );
    let mut d8: FStar_UInt128_uint128 = FStar_UInt128_add_mod(
        FStar_UInt128_add_mod(
            FStar_UInt128_add_mod(d7, FStar_UInt128_mul_wide(a2, b4)),
            FStar_UInt128_mul_wide(a3, b3),
        ),
        FStar_UInt128_mul_wide(a4, b2),
    );
    let mut c6: FStar_UInt128_uint128 = FStar_UInt128_add_mod(
        c5,
        FStar_UInt128_mul_wide(
            FStar_UInt128_uint128_to_uint64(d8) & 0xfffffffffffff as libc::c_ulonglong,
            r,
        ),
    );
    let mut d9: FStar_UInt128_uint128 = FStar_UInt128_shift_right(
        d8,
        52 as libc::c_uint,
    );
    let mut r1: uint64_t = FStar_UInt128_uint128_to_uint64(c6)
        & 0xfffffffffffff as libc::c_ulonglong;
    let mut c7: FStar_UInt128_uint128 = FStar_UInt128_shift_right(
        c6,
        52 as libc::c_uint,
    );
    let mut c8: FStar_UInt128_uint128 = FStar_UInt128_add_mod(
        FStar_UInt128_add_mod(
            FStar_UInt128_add_mod(c7, FStar_UInt128_mul_wide(a0, b2)),
            FStar_UInt128_mul_wide(a1, b1),
        ),
        FStar_UInt128_mul_wide(a2, b0),
    );
    let mut d10: FStar_UInt128_uint128 = FStar_UInt128_add_mod(
        FStar_UInt128_add_mod(d9, FStar_UInt128_mul_wide(a3, b4)),
        FStar_UInt128_mul_wide(a4, b3),
    );
    let mut c9: FStar_UInt128_uint128 = FStar_UInt128_add_mod(
        c8,
        FStar_UInt128_mul_wide(r, FStar_UInt128_uint128_to_uint64(d10)),
    );
    let mut d11: uint64_t = FStar_UInt128_uint128_to_uint64(
        FStar_UInt128_shift_right(d10, 64 as libc::c_uint),
    );
    let mut r2: uint64_t = FStar_UInt128_uint128_to_uint64(c9)
        & 0xfffffffffffff as libc::c_ulonglong;
    let mut c10: FStar_UInt128_uint128 = FStar_UInt128_shift_right(
        c9,
        52 as libc::c_uint,
    );
    let mut c11: FStar_UInt128_uint128 = FStar_UInt128_add_mod(
        FStar_UInt128_add_mod(c10, FStar_UInt128_mul_wide(r << 12 as libc::c_uint, d11)),
        FStar_UInt128_uint64_to_uint128(t3),
    );
    let mut r3: uint64_t = FStar_UInt128_uint128_to_uint64(c11)
        & 0xfffffffffffff as libc::c_ulonglong;
    let mut c12: uint64_t = FStar_UInt128_uint128_to_uint64(
        FStar_UInt128_shift_right(c11, 52 as libc::c_uint),
    );
    let mut r4: uint64_t = c12.wrapping_add(t4_);
    let mut f0: uint64_t = r0;
    let mut f11: uint64_t = r1;
    let mut f21: uint64_t = r2;
    let mut f3: uint64_t = r3;
    let mut f4: uint64_t = r4;
    *out.offset(0 as libc::c_uint as isize) = f0;
    *out.offset(1 as libc::c_uint as isize) = f11;
    *out.offset(2 as libc::c_uint as isize) = f21;
    *out.offset(3 as libc::c_uint as isize) = f3;
    *out.offset(4 as libc::c_uint as isize) = f4;
}
#[inline]
unsafe extern "C" fn Hacl_K256_Field_fsqr(mut out: *mut uint64_t, mut f: *mut uint64_t) {
    let mut a0: uint64_t = *f.offset(0 as libc::c_uint as isize);
    let mut a1: uint64_t = *f.offset(1 as libc::c_uint as isize);
    let mut a2: uint64_t = *f.offset(2 as libc::c_uint as isize);
    let mut a3: uint64_t = *f.offset(3 as libc::c_uint as isize);
    let mut a4: uint64_t = *f.offset(4 as libc::c_uint as isize);
    let mut r: uint64_t = 0x1000003d10 as libc::c_ulonglong;
    let mut d0: FStar_UInt128_uint128 = FStar_UInt128_add_mod(
        FStar_UInt128_mul_wide(a0.wrapping_mul(2 as libc::c_ulonglong), a3),
        FStar_UInt128_mul_wide(a1.wrapping_mul(2 as libc::c_ulonglong), a2),
    );
    let mut c0: FStar_UInt128_uint128 = FStar_UInt128_mul_wide(a4, a4);
    let mut d1: FStar_UInt128_uint128 = FStar_UInt128_add_mod(
        d0,
        FStar_UInt128_mul_wide(r, FStar_UInt128_uint128_to_uint64(c0)),
    );
    let mut c1: uint64_t = FStar_UInt128_uint128_to_uint64(
        FStar_UInt128_shift_right(c0, 64 as libc::c_uint),
    );
    let mut t3: uint64_t = FStar_UInt128_uint128_to_uint64(d1)
        & 0xfffffffffffff as libc::c_ulonglong;
    let mut d2: FStar_UInt128_uint128 = FStar_UInt128_shift_right(
        d1,
        52 as libc::c_uint,
    );
    let mut a41: uint64_t = a4.wrapping_mul(2 as libc::c_ulonglong);
    let mut d3: FStar_UInt128_uint128 = FStar_UInt128_add_mod(
        FStar_UInt128_add_mod(
            FStar_UInt128_add_mod(d2, FStar_UInt128_mul_wide(a0, a41)),
            FStar_UInt128_mul_wide(a1.wrapping_mul(2 as libc::c_ulonglong), a3),
        ),
        FStar_UInt128_mul_wide(a2, a2),
    );
    let mut d4: FStar_UInt128_uint128 = FStar_UInt128_add_mod(
        d3,
        FStar_UInt128_mul_wide(r << 12 as libc::c_uint, c1),
    );
    let mut t4: uint64_t = FStar_UInt128_uint128_to_uint64(d4)
        & 0xfffffffffffff as libc::c_ulonglong;
    let mut d5: FStar_UInt128_uint128 = FStar_UInt128_shift_right(
        d4,
        52 as libc::c_uint,
    );
    let mut tx: uint64_t = t4 >> 48 as libc::c_uint;
    let mut t4_: uint64_t = t4 & 0xffffffffffff as libc::c_ulonglong;
    let mut c2: FStar_UInt128_uint128 = FStar_UInt128_mul_wide(a0, a0);
    let mut d6: FStar_UInt128_uint128 = FStar_UInt128_add_mod(
        FStar_UInt128_add_mod(d5, FStar_UInt128_mul_wide(a1, a41)),
        FStar_UInt128_mul_wide(a2.wrapping_mul(2 as libc::c_ulonglong), a3),
    );
    let mut u0: uint64_t = FStar_UInt128_uint128_to_uint64(d6)
        & 0xfffffffffffff as libc::c_ulonglong;
    let mut d7: FStar_UInt128_uint128 = FStar_UInt128_shift_right(
        d6,
        52 as libc::c_uint,
    );
    let mut u0_: uint64_t = tx | u0 << 4 as libc::c_uint;
    let mut c3: FStar_UInt128_uint128 = FStar_UInt128_add_mod(
        c2,
        FStar_UInt128_mul_wide(u0_, r >> 4 as libc::c_uint),
    );
    let mut r0: uint64_t = FStar_UInt128_uint128_to_uint64(c3)
        & 0xfffffffffffff as libc::c_ulonglong;
    let mut c4: FStar_UInt128_uint128 = FStar_UInt128_shift_right(
        c3,
        52 as libc::c_uint,
    );
    let mut a01: uint64_t = a0.wrapping_mul(2 as libc::c_ulonglong);
    let mut c5: FStar_UInt128_uint128 = FStar_UInt128_add_mod(
        c4,
        FStar_UInt128_mul_wide(a01, a1),
    );
    let mut d8: FStar_UInt128_uint128 = FStar_UInt128_add_mod(
        FStar_UInt128_add_mod(d7, FStar_UInt128_mul_wide(a2, a41)),
        FStar_UInt128_mul_wide(a3, a3),
    );
    let mut c6: FStar_UInt128_uint128 = FStar_UInt128_add_mod(
        c5,
        FStar_UInt128_mul_wide(
            FStar_UInt128_uint128_to_uint64(d8) & 0xfffffffffffff as libc::c_ulonglong,
            r,
        ),
    );
    let mut d9: FStar_UInt128_uint128 = FStar_UInt128_shift_right(
        d8,
        52 as libc::c_uint,
    );
    let mut r1: uint64_t = FStar_UInt128_uint128_to_uint64(c6)
        & 0xfffffffffffff as libc::c_ulonglong;
    let mut c7: FStar_UInt128_uint128 = FStar_UInt128_shift_right(
        c6,
        52 as libc::c_uint,
    );
    let mut c8: FStar_UInt128_uint128 = FStar_UInt128_add_mod(
        FStar_UInt128_add_mod(c7, FStar_UInt128_mul_wide(a01, a2)),
        FStar_UInt128_mul_wide(a1, a1),
    );
    let mut d10: FStar_UInt128_uint128 = FStar_UInt128_add_mod(
        d9,
        FStar_UInt128_mul_wide(a3, a41),
    );
    let mut c9: FStar_UInt128_uint128 = FStar_UInt128_add_mod(
        c8,
        FStar_UInt128_mul_wide(r, FStar_UInt128_uint128_to_uint64(d10)),
    );
    let mut d11: uint64_t = FStar_UInt128_uint128_to_uint64(
        FStar_UInt128_shift_right(d10, 64 as libc::c_uint),
    );
    let mut r2: uint64_t = FStar_UInt128_uint128_to_uint64(c9)
        & 0xfffffffffffff as libc::c_ulonglong;
    let mut c10: FStar_UInt128_uint128 = FStar_UInt128_shift_right(
        c9,
        52 as libc::c_uint,
    );
    let mut c11: FStar_UInt128_uint128 = FStar_UInt128_add_mod(
        FStar_UInt128_add_mod(c10, FStar_UInt128_mul_wide(r << 12 as libc::c_uint, d11)),
        FStar_UInt128_uint64_to_uint128(t3),
    );
    let mut r3: uint64_t = FStar_UInt128_uint128_to_uint64(c11)
        & 0xfffffffffffff as libc::c_ulonglong;
    let mut c12: uint64_t = FStar_UInt128_uint128_to_uint64(
        FStar_UInt128_shift_right(c11, 52 as libc::c_uint),
    );
    let mut r4: uint64_t = c12.wrapping_add(t4_);
    let mut f0: uint64_t = r0;
    let mut f1: uint64_t = r1;
    let mut f2: uint64_t = r2;
    let mut f3: uint64_t = r3;
    let mut f4: uint64_t = r4;
    *out.offset(0 as libc::c_uint as isize) = f0;
    *out.offset(1 as libc::c_uint as isize) = f1;
    *out.offset(2 as libc::c_uint as isize) = f2;
    *out.offset(3 as libc::c_uint as isize) = f3;
    *out.offset(4 as libc::c_uint as isize) = f4;
}
#[inline]
unsafe extern "C" fn Hacl_K256_Field_fnormalize_weak(
    mut out: *mut uint64_t,
    mut f: *mut uint64_t,
) {
    let mut t0: uint64_t = *f.offset(0 as libc::c_uint as isize);
    let mut t1: uint64_t = *f.offset(1 as libc::c_uint as isize);
    let mut t2: uint64_t = *f.offset(2 as libc::c_uint as isize);
    let mut t3: uint64_t = *f.offset(3 as libc::c_uint as isize);
    let mut t4: uint64_t = *f.offset(4 as libc::c_uint as isize);
    let mut x0: uint64_t = t4 >> 48 as libc::c_uint;
    let mut t410: uint64_t = t4 & 0xffffffffffff as libc::c_ulonglong;
    let mut x: uint64_t = x0;
    let mut t01: uint64_t = t0;
    let mut t11: uint64_t = t1;
    let mut t21: uint64_t = t2;
    let mut t31: uint64_t = t3;
    let mut t41: uint64_t = t410;
    let mut t02: uint64_t = t01
        .wrapping_add(x.wrapping_mul(0x1000003d1 as libc::c_ulonglong));
    let mut t12: uint64_t = t11.wrapping_add(t02 >> 52 as libc::c_uint);
    let mut t03: uint64_t = t02 & 0xfffffffffffff as libc::c_ulonglong;
    let mut t22: uint64_t = t21.wrapping_add(t12 >> 52 as libc::c_uint);
    let mut t13: uint64_t = t12 & 0xfffffffffffff as libc::c_ulonglong;
    let mut t32: uint64_t = t31.wrapping_add(t22 >> 52 as libc::c_uint);
    let mut t23: uint64_t = t22 & 0xfffffffffffff as libc::c_ulonglong;
    let mut t42: uint64_t = t41.wrapping_add(t32 >> 52 as libc::c_uint);
    let mut t33: uint64_t = t32 & 0xfffffffffffff as libc::c_ulonglong;
    let mut f0: uint64_t = t03;
    let mut f1: uint64_t = t13;
    let mut f2: uint64_t = t23;
    let mut f3: uint64_t = t33;
    let mut f4: uint64_t = t42;
    *out.offset(0 as libc::c_uint as isize) = f0;
    *out.offset(1 as libc::c_uint as isize) = f1;
    *out.offset(2 as libc::c_uint as isize) = f2;
    *out.offset(3 as libc::c_uint as isize) = f3;
    *out.offset(4 as libc::c_uint as isize) = f4;
}
#[inline]
unsafe extern "C" fn Hacl_K256_Field_fnormalize(
    mut out: *mut uint64_t,
    mut f: *mut uint64_t,
) {
    let mut f00: uint64_t = *f.offset(0 as libc::c_uint as isize);
    let mut f10: uint64_t = *f.offset(1 as libc::c_uint as isize);
    let mut f20: uint64_t = *f.offset(2 as libc::c_uint as isize);
    let mut f30: uint64_t = *f.offset(3 as libc::c_uint as isize);
    let mut f40: uint64_t = *f.offset(4 as libc::c_uint as isize);
    let mut x0: uint64_t = f40 >> 48 as libc::c_uint;
    let mut t40: uint64_t = f40 & 0xffffffffffff as libc::c_ulonglong;
    let mut x1: uint64_t = x0;
    let mut t00: uint64_t = f00;
    let mut t10: uint64_t = f10;
    let mut t20: uint64_t = f20;
    let mut t30: uint64_t = f30;
    let mut t42: uint64_t = t40;
    let mut t01: uint64_t = t00
        .wrapping_add(x1.wrapping_mul(0x1000003d1 as libc::c_ulonglong));
    let mut t110: uint64_t = t10.wrapping_add(t01 >> 52 as libc::c_uint);
    let mut t020: uint64_t = t01 & 0xfffffffffffff as libc::c_ulonglong;
    let mut t210: uint64_t = t20.wrapping_add(t110 >> 52 as libc::c_uint);
    let mut t120: uint64_t = t110 & 0xfffffffffffff as libc::c_ulonglong;
    let mut t310: uint64_t = t30.wrapping_add(t210 >> 52 as libc::c_uint);
    let mut t220: uint64_t = t210 & 0xfffffffffffff as libc::c_ulonglong;
    let mut t410: uint64_t = t42.wrapping_add(t310 >> 52 as libc::c_uint);
    let mut t320: uint64_t = t310 & 0xfffffffffffff as libc::c_ulonglong;
    let mut t0: uint64_t = t020;
    let mut t1: uint64_t = t120;
    let mut t2: uint64_t = t220;
    let mut t3: uint64_t = t320;
    let mut t4: uint64_t = t410;
    let mut x2: uint64_t = t4 >> 48 as libc::c_uint;
    let mut t411: uint64_t = t4 & 0xffffffffffff as libc::c_ulonglong;
    let mut x: uint64_t = x2;
    let mut r0: uint64_t = t0;
    let mut r1: uint64_t = t1;
    let mut r2: uint64_t = t2;
    let mut r3: uint64_t = t3;
    let mut r4: uint64_t = t411;
    let mut m4: uint64_t = FStar_UInt64_eq_mask(r4, 0xffffffffffff as libc::c_ulonglong);
    let mut m3: uint64_t = FStar_UInt64_eq_mask(
        r3,
        0xfffffffffffff as libc::c_ulonglong,
    );
    let mut m2: uint64_t = FStar_UInt64_eq_mask(
        r2,
        0xfffffffffffff as libc::c_ulonglong,
    );
    let mut m1: uint64_t = FStar_UInt64_eq_mask(
        r1,
        0xfffffffffffff as libc::c_ulonglong,
    );
    let mut m0: uint64_t = FStar_UInt64_gte_mask(
        r0,
        0xffffefffffc2f as libc::c_ulonglong,
    );
    let mut is_ge_p_m: uint64_t = m0 & m1 & m2 & m3 & m4;
    let mut m_to_one: uint64_t = is_ge_p_m & 1 as libc::c_ulonglong;
    let mut x10: uint64_t = m_to_one | x;
    let mut t010: uint64_t = r0
        .wrapping_add(x10.wrapping_mul(0x1000003d1 as libc::c_ulonglong));
    let mut t11: uint64_t = r1.wrapping_add(t010 >> 52 as libc::c_uint);
    let mut t02: uint64_t = t010 & 0xfffffffffffff as libc::c_ulonglong;
    let mut t21: uint64_t = r2.wrapping_add(t11 >> 52 as libc::c_uint);
    let mut t12: uint64_t = t11 & 0xfffffffffffff as libc::c_ulonglong;
    let mut t31: uint64_t = r3.wrapping_add(t21 >> 52 as libc::c_uint);
    let mut t22: uint64_t = t21 & 0xfffffffffffff as libc::c_ulonglong;
    let mut t41: uint64_t = r4.wrapping_add(t31 >> 52 as libc::c_uint);
    let mut t32: uint64_t = t31 & 0xfffffffffffff as libc::c_ulonglong;
    let mut s0: uint64_t = t02;
    let mut s1: uint64_t = t12;
    let mut s2: uint64_t = t22;
    let mut s3: uint64_t = t32;
    let mut s4: uint64_t = t41;
    let mut t412: uint64_t = s4 & 0xffffffffffff as libc::c_ulonglong;
    let mut k0: uint64_t = s0;
    let mut k1: uint64_t = s1;
    let mut k2: uint64_t = s2;
    let mut k3: uint64_t = s3;
    let mut k4: uint64_t = t412;
    let mut f0: uint64_t = k0;
    let mut f1: uint64_t = k1;
    let mut f2: uint64_t = k2;
    let mut f3: uint64_t = k3;
    let mut f4: uint64_t = k4;
    *out.offset(0 as libc::c_uint as isize) = f0;
    *out.offset(1 as libc::c_uint as isize) = f1;
    *out.offset(2 as libc::c_uint as isize) = f2;
    *out.offset(3 as libc::c_uint as isize) = f3;
    *out.offset(4 as libc::c_uint as isize) = f4;
}
#[inline]
unsafe extern "C" fn Hacl_K256_Field_fnegate_conditional_vartime(
    mut f: *mut uint64_t,
    mut is_negate: bool,
) {
    if is_negate {
        let mut a0: uint64_t = *f.offset(0 as libc::c_uint as isize);
        let mut a1: uint64_t = *f.offset(1 as libc::c_uint as isize);
        let mut a2: uint64_t = *f.offset(2 as libc::c_uint as isize);
        let mut a3: uint64_t = *f.offset(3 as libc::c_uint as isize);
        let mut a4: uint64_t = *f.offset(4 as libc::c_uint as isize);
        let mut r0: uint64_t = (9007190664804446 as libc::c_ulonglong).wrapping_sub(a0);
        let mut r1: uint64_t = (9007199254740990 as libc::c_ulonglong).wrapping_sub(a1);
        let mut r2: uint64_t = (9007199254740990 as libc::c_ulonglong).wrapping_sub(a2);
        let mut r3: uint64_t = (9007199254740990 as libc::c_ulonglong).wrapping_sub(a3);
        let mut r4: uint64_t = (562949953421310 as libc::c_ulonglong).wrapping_sub(a4);
        let mut f0: uint64_t = r0;
        let mut f1: uint64_t = r1;
        let mut f2: uint64_t = r2;
        let mut f3: uint64_t = r3;
        let mut f4: uint64_t = r4;
        *f.offset(0 as libc::c_uint as isize) = f0;
        *f.offset(1 as libc::c_uint as isize) = f1;
        *f.offset(2 as libc::c_uint as isize) = f2;
        *f.offset(3 as libc::c_uint as isize) = f3;
        *f.offset(4 as libc::c_uint as isize) = f4;
        let mut f_copy: [uint64_t; 5] = [0 as libc::c_uint as uint64_t, 0, 0, 0, 0];
        memcpy(
            f_copy.as_mut_ptr() as *mut libc::c_void,
            f as *const libc::c_void,
            (5 as libc::c_uint as libc::c_ulong)
                .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
        );
        Hacl_K256_Field_fnormalize(f, f_copy.as_mut_ptr());
        return;
    }
}
#[inline]
unsafe extern "C" fn Hacl_Impl_K256_Finv_fsquare_times_in_place(
    mut out: *mut uint64_t,
    mut b: uint32_t,
) {
    let mut i: uint32_t = 0 as libc::c_uint;
    while i < b {
        let mut x_copy: [uint64_t; 5] = [0 as libc::c_uint as uint64_t, 0, 0, 0, 0];
        memcpy(
            x_copy.as_mut_ptr() as *mut libc::c_void,
            out as *const libc::c_void,
            (5 as libc::c_uint as libc::c_ulong)
                .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
        );
        Hacl_K256_Field_fsqr(out, x_copy.as_mut_ptr());
        i = i.wrapping_add(1);
        i;
    }
}
#[inline]
unsafe extern "C" fn Hacl_Impl_K256_Finv_fsquare_times(
    mut out: *mut uint64_t,
    mut a: *mut uint64_t,
    mut b: uint32_t,
) {
    memcpy(
        out as *mut libc::c_void,
        a as *const libc::c_void,
        (5 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    let mut i: uint32_t = 0 as libc::c_uint;
    while i < b {
        let mut x_copy: [uint64_t; 5] = [0 as libc::c_uint as uint64_t, 0, 0, 0, 0];
        memcpy(
            x_copy.as_mut_ptr() as *mut libc::c_void,
            out as *const libc::c_void,
            (5 as libc::c_uint as libc::c_ulong)
                .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
        );
        Hacl_K256_Field_fsqr(out, x_copy.as_mut_ptr());
        i = i.wrapping_add(1);
        i;
    }
}
#[inline]
unsafe extern "C" fn Hacl_Impl_K256_Finv_fexp_223_23(
    mut out: *mut uint64_t,
    mut x2: *mut uint64_t,
    mut f: *mut uint64_t,
) {
    let mut x3: [uint64_t; 5] = [0 as libc::c_uint as uint64_t, 0, 0, 0, 0];
    let mut x22: [uint64_t; 5] = [0 as libc::c_uint as uint64_t, 0, 0, 0, 0];
    let mut x44: [uint64_t; 5] = [0 as libc::c_uint as uint64_t, 0, 0, 0, 0];
    let mut x88: [uint64_t; 5] = [0 as libc::c_uint as uint64_t, 0, 0, 0, 0];
    Hacl_Impl_K256_Finv_fsquare_times(x2, f, 1 as libc::c_uint);
    let mut f1_copy: [uint64_t; 5] = [0 as libc::c_uint as uint64_t, 0, 0, 0, 0];
    memcpy(
        f1_copy.as_mut_ptr() as *mut libc::c_void,
        x2 as *const libc::c_void,
        (5 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    Hacl_K256_Field_fmul(x2, f1_copy.as_mut_ptr(), f);
    Hacl_Impl_K256_Finv_fsquare_times(x3.as_mut_ptr(), x2, 1 as libc::c_uint);
    let mut f1_copy0: [uint64_t; 5] = [0 as libc::c_uint as uint64_t, 0, 0, 0, 0];
    memcpy(
        f1_copy0.as_mut_ptr() as *mut libc::c_void,
        x3.as_mut_ptr() as *const libc::c_void,
        (5 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    Hacl_K256_Field_fmul(x3.as_mut_ptr(), f1_copy0.as_mut_ptr(), f);
    Hacl_Impl_K256_Finv_fsquare_times(out, x3.as_mut_ptr(), 3 as libc::c_uint);
    let mut f1_copy1: [uint64_t; 5] = [0 as libc::c_uint as uint64_t, 0, 0, 0, 0];
    memcpy(
        f1_copy1.as_mut_ptr() as *mut libc::c_void,
        out as *const libc::c_void,
        (5 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    Hacl_K256_Field_fmul(out, f1_copy1.as_mut_ptr(), x3.as_mut_ptr());
    Hacl_Impl_K256_Finv_fsquare_times_in_place(out, 3 as libc::c_uint);
    let mut f1_copy2: [uint64_t; 5] = [0 as libc::c_uint as uint64_t, 0, 0, 0, 0];
    memcpy(
        f1_copy2.as_mut_ptr() as *mut libc::c_void,
        out as *const libc::c_void,
        (5 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    Hacl_K256_Field_fmul(out, f1_copy2.as_mut_ptr(), x3.as_mut_ptr());
    Hacl_Impl_K256_Finv_fsquare_times_in_place(out, 2 as libc::c_uint);
    let mut f1_copy3: [uint64_t; 5] = [0 as libc::c_uint as uint64_t, 0, 0, 0, 0];
    memcpy(
        f1_copy3.as_mut_ptr() as *mut libc::c_void,
        out as *const libc::c_void,
        (5 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    Hacl_K256_Field_fmul(out, f1_copy3.as_mut_ptr(), x2);
    Hacl_Impl_K256_Finv_fsquare_times(x22.as_mut_ptr(), out, 11 as libc::c_uint);
    let mut f1_copy4: [uint64_t; 5] = [0 as libc::c_uint as uint64_t, 0, 0, 0, 0];
    memcpy(
        f1_copy4.as_mut_ptr() as *mut libc::c_void,
        x22.as_mut_ptr() as *const libc::c_void,
        (5 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    Hacl_K256_Field_fmul(x22.as_mut_ptr(), f1_copy4.as_mut_ptr(), out);
    Hacl_Impl_K256_Finv_fsquare_times(
        x44.as_mut_ptr(),
        x22.as_mut_ptr(),
        22 as libc::c_uint,
    );
    let mut f1_copy5: [uint64_t; 5] = [0 as libc::c_uint as uint64_t, 0, 0, 0, 0];
    memcpy(
        f1_copy5.as_mut_ptr() as *mut libc::c_void,
        x44.as_mut_ptr() as *const libc::c_void,
        (5 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    Hacl_K256_Field_fmul(x44.as_mut_ptr(), f1_copy5.as_mut_ptr(), x22.as_mut_ptr());
    Hacl_Impl_K256_Finv_fsquare_times(
        x88.as_mut_ptr(),
        x44.as_mut_ptr(),
        44 as libc::c_uint,
    );
    let mut f1_copy6: [uint64_t; 5] = [0 as libc::c_uint as uint64_t, 0, 0, 0, 0];
    memcpy(
        f1_copy6.as_mut_ptr() as *mut libc::c_void,
        x88.as_mut_ptr() as *const libc::c_void,
        (5 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    Hacl_K256_Field_fmul(x88.as_mut_ptr(), f1_copy6.as_mut_ptr(), x44.as_mut_ptr());
    Hacl_Impl_K256_Finv_fsquare_times(out, x88.as_mut_ptr(), 88 as libc::c_uint);
    let mut f1_copy7: [uint64_t; 5] = [0 as libc::c_uint as uint64_t, 0, 0, 0, 0];
    memcpy(
        f1_copy7.as_mut_ptr() as *mut libc::c_void,
        out as *const libc::c_void,
        (5 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    Hacl_K256_Field_fmul(out, f1_copy7.as_mut_ptr(), x88.as_mut_ptr());
    Hacl_Impl_K256_Finv_fsquare_times_in_place(out, 44 as libc::c_uint);
    let mut f1_copy8: [uint64_t; 5] = [0 as libc::c_uint as uint64_t, 0, 0, 0, 0];
    memcpy(
        f1_copy8.as_mut_ptr() as *mut libc::c_void,
        out as *const libc::c_void,
        (5 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    Hacl_K256_Field_fmul(out, f1_copy8.as_mut_ptr(), x44.as_mut_ptr());
    Hacl_Impl_K256_Finv_fsquare_times_in_place(out, 3 as libc::c_uint);
    let mut f1_copy9: [uint64_t; 5] = [0 as libc::c_uint as uint64_t, 0, 0, 0, 0];
    memcpy(
        f1_copy9.as_mut_ptr() as *mut libc::c_void,
        out as *const libc::c_void,
        (5 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    Hacl_K256_Field_fmul(out, f1_copy9.as_mut_ptr(), x3.as_mut_ptr());
    Hacl_Impl_K256_Finv_fsquare_times_in_place(out, 23 as libc::c_uint);
    let mut f1_copy10: [uint64_t; 5] = [0 as libc::c_uint as uint64_t, 0, 0, 0, 0];
    memcpy(
        f1_copy10.as_mut_ptr() as *mut libc::c_void,
        out as *const libc::c_void,
        (5 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    Hacl_K256_Field_fmul(out, f1_copy10.as_mut_ptr(), x22.as_mut_ptr());
}
#[inline]
unsafe extern "C" fn Hacl_Impl_K256_Finv_finv(
    mut out: *mut uint64_t,
    mut f: *mut uint64_t,
) {
    let mut x2: [uint64_t; 5] = [0 as libc::c_uint as uint64_t, 0, 0, 0, 0];
    Hacl_Impl_K256_Finv_fexp_223_23(out, x2.as_mut_ptr(), f);
    Hacl_Impl_K256_Finv_fsquare_times_in_place(out, 5 as libc::c_uint);
    let mut f1_copy: [uint64_t; 5] = [0 as libc::c_uint as uint64_t, 0, 0, 0, 0];
    memcpy(
        f1_copy.as_mut_ptr() as *mut libc::c_void,
        out as *const libc::c_void,
        (5 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    Hacl_K256_Field_fmul(out, f1_copy.as_mut_ptr(), f);
    Hacl_Impl_K256_Finv_fsquare_times_in_place(out, 3 as libc::c_uint);
    let mut f1_copy0: [uint64_t; 5] = [0 as libc::c_uint as uint64_t, 0, 0, 0, 0];
    memcpy(
        f1_copy0.as_mut_ptr() as *mut libc::c_void,
        out as *const libc::c_void,
        (5 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    Hacl_K256_Field_fmul(out, f1_copy0.as_mut_ptr(), x2.as_mut_ptr());
    Hacl_Impl_K256_Finv_fsquare_times_in_place(out, 2 as libc::c_uint);
    let mut f1_copy1: [uint64_t; 5] = [0 as libc::c_uint as uint64_t, 0, 0, 0, 0];
    memcpy(
        f1_copy1.as_mut_ptr() as *mut libc::c_void,
        out as *const libc::c_void,
        (5 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    Hacl_K256_Field_fmul(out, f1_copy1.as_mut_ptr(), f);
}
#[inline]
unsafe extern "C" fn Hacl_Impl_K256_Finv_fsqrt(
    mut out: *mut uint64_t,
    mut f: *mut uint64_t,
) {
    let mut x2: [uint64_t; 5] = [0 as libc::c_uint as uint64_t, 0, 0, 0, 0];
    Hacl_Impl_K256_Finv_fexp_223_23(out, x2.as_mut_ptr(), f);
    Hacl_Impl_K256_Finv_fsquare_times_in_place(out, 6 as libc::c_uint);
    let mut f1_copy: [uint64_t; 5] = [0 as libc::c_uint as uint64_t, 0, 0, 0, 0];
    memcpy(
        f1_copy.as_mut_ptr() as *mut libc::c_void,
        out as *const libc::c_void,
        (5 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    Hacl_K256_Field_fmul(out, f1_copy.as_mut_ptr(), x2.as_mut_ptr());
    Hacl_Impl_K256_Finv_fsquare_times_in_place(out, 2 as libc::c_uint);
}
#[inline]
unsafe extern "C" fn Hacl_IntTypes_Intrinsics_128_add_carry_u64(
    mut cin: uint64_t,
    mut x: uint64_t,
    mut y: uint64_t,
    mut r: *mut uint64_t,
) -> uint64_t {
    let mut res: FStar_UInt128_uint128 = FStar_UInt128_add_mod(
        FStar_UInt128_add_mod(
            FStar_UInt128_uint64_to_uint128(x),
            FStar_UInt128_uint64_to_uint128(cin),
        ),
        FStar_UInt128_uint64_to_uint128(y),
    );
    let mut c: uint64_t = FStar_UInt128_uint128_to_uint64(
        FStar_UInt128_shift_right(res, 64 as libc::c_uint),
    );
    *r.offset(0 as libc::c_uint as isize) = FStar_UInt128_uint128_to_uint64(res);
    return c;
}
#[inline]
unsafe extern "C" fn Hacl_IntTypes_Intrinsics_128_sub_borrow_u64(
    mut cin: uint64_t,
    mut x: uint64_t,
    mut y: uint64_t,
    mut r: *mut uint64_t,
) -> uint64_t {
    let mut res: FStar_UInt128_uint128 = FStar_UInt128_sub_mod(
        FStar_UInt128_sub_mod(
            FStar_UInt128_uint64_to_uint128(x),
            FStar_UInt128_uint64_to_uint128(y),
        ),
        FStar_UInt128_uint64_to_uint128(cin),
    );
    let mut c: uint64_t = FStar_UInt128_uint128_to_uint64(
        FStar_UInt128_shift_right(res, 64 as libc::c_uint),
    ) & 1 as libc::c_ulonglong;
    *r.offset(0 as libc::c_uint as isize) = FStar_UInt128_uint128_to_uint64(res);
    return c;
}
#[inline]
unsafe extern "C" fn Hacl_Bignum_Base_mul_wide_add2_u64(
    mut a: uint64_t,
    mut b: uint64_t,
    mut c_in: uint64_t,
    mut out: *mut uint64_t,
) -> uint64_t {
    let mut out0: uint64_t = *out.offset(0 as libc::c_uint as isize);
    let mut res: FStar_UInt128_uint128 = FStar_UInt128_add(
        FStar_UInt128_add(
            FStar_UInt128_mul_wide(a, b),
            FStar_UInt128_uint64_to_uint128(c_in),
        ),
        FStar_UInt128_uint64_to_uint128(out0),
    );
    *out.offset(0 as libc::c_uint as isize) = FStar_UInt128_uint128_to_uint64(res);
    return FStar_UInt128_uint128_to_uint64(
        FStar_UInt128_shift_right(res, 64 as libc::c_uint),
    );
}
#[inline]
unsafe extern "C" fn Hacl_Bignum_Lib_bn_get_bits_u64(
    mut len: uint32_t,
    mut b: *mut uint64_t,
    mut i: uint32_t,
    mut l: uint32_t,
) -> uint64_t {
    let mut i1: uint32_t = i.wrapping_div(64 as libc::c_uint);
    let mut j: uint32_t = i.wrapping_rem(64 as libc::c_uint);
    let mut p1: uint64_t = *b.offset(i1 as isize) >> j;
    let mut ite: uint64_t = 0;
    if i1.wrapping_add(1 as libc::c_uint) < len && (0 as libc::c_uint) < j {
        ite = p1
            | *b.offset(i1.wrapping_add(1 as libc::c_uint) as isize)
                << (64 as libc::c_uint).wrapping_sub(j);
    } else {
        ite = p1;
    }
    return ite & ((1 as libc::c_ulonglong) << l).wrapping_sub(1 as libc::c_ulonglong);
}
#[inline]
unsafe extern "C" fn Hacl_Bignum_Addition_bn_add_eq_len_u64(
    mut aLen: uint32_t,
    mut a: *mut uint64_t,
    mut b: *mut uint64_t,
    mut res: *mut uint64_t,
) -> uint64_t {
    let mut c: uint64_t = 0 as libc::c_ulonglong;
    let mut i: uint32_t = 0 as libc::c_uint;
    while i < aLen.wrapping_div(4 as libc::c_uint) {
        let mut t1: uint64_t = *a.offset((4 as libc::c_uint).wrapping_mul(i) as isize);
        let mut t20: uint64_t = *b.offset((4 as libc::c_uint).wrapping_mul(i) as isize);
        let mut res_i0: *mut uint64_t = res
            .offset((4 as libc::c_uint).wrapping_mul(i) as isize);
        c = Hacl_IntTypes_Intrinsics_128_add_carry_u64(c, t1, t20, res_i0);
        let mut t10: uint64_t = *a
            .offset(
                (4 as libc::c_uint).wrapping_mul(i).wrapping_add(1 as libc::c_uint)
                    as isize,
            );
        let mut t21: uint64_t = *b
            .offset(
                (4 as libc::c_uint).wrapping_mul(i).wrapping_add(1 as libc::c_uint)
                    as isize,
            );
        let mut res_i1: *mut uint64_t = res
            .offset((4 as libc::c_uint).wrapping_mul(i) as isize)
            .offset(1 as libc::c_uint as isize);
        c = Hacl_IntTypes_Intrinsics_128_add_carry_u64(c, t10, t21, res_i1);
        let mut t11: uint64_t = *a
            .offset(
                (4 as libc::c_uint).wrapping_mul(i).wrapping_add(2 as libc::c_uint)
                    as isize,
            );
        let mut t22: uint64_t = *b
            .offset(
                (4 as libc::c_uint).wrapping_mul(i).wrapping_add(2 as libc::c_uint)
                    as isize,
            );
        let mut res_i2: *mut uint64_t = res
            .offset((4 as libc::c_uint).wrapping_mul(i) as isize)
            .offset(2 as libc::c_uint as isize);
        c = Hacl_IntTypes_Intrinsics_128_add_carry_u64(c, t11, t22, res_i2);
        let mut t12: uint64_t = *a
            .offset(
                (4 as libc::c_uint).wrapping_mul(i).wrapping_add(3 as libc::c_uint)
                    as isize,
            );
        let mut t2: uint64_t = *b
            .offset(
                (4 as libc::c_uint).wrapping_mul(i).wrapping_add(3 as libc::c_uint)
                    as isize,
            );
        let mut res_i: *mut uint64_t = res
            .offset((4 as libc::c_uint).wrapping_mul(i) as isize)
            .offset(3 as libc::c_uint as isize);
        c = Hacl_IntTypes_Intrinsics_128_add_carry_u64(c, t12, t2, res_i);
        i = i.wrapping_add(1);
        i;
    }
    let mut i_0: uint32_t = aLen
        .wrapping_div(4 as libc::c_uint)
        .wrapping_mul(4 as libc::c_uint);
    while i_0 < aLen {
        let mut t1_0: uint64_t = *a.offset(i_0 as isize);
        let mut t2_0: uint64_t = *b.offset(i_0 as isize);
        let mut res_i_0: *mut uint64_t = res.offset(i_0 as isize);
        c = Hacl_IntTypes_Intrinsics_128_add_carry_u64(c, t1_0, t2_0, res_i_0);
        i_0 = i_0.wrapping_add(1);
        i_0;
    }
    return c;
}
#[inline]
unsafe extern "C" fn bn_add_sa(
    mut aLen: uint32_t,
    mut bLen: uint32_t,
    mut b: *mut uint64_t,
    mut res: *mut uint64_t,
) -> uint64_t {
    let mut res0: *mut uint64_t = res;
    let mut c0: uint64_t = 0 as libc::c_ulonglong;
    let mut i: uint32_t = 0 as libc::c_uint;
    while i < bLen.wrapping_div(4 as libc::c_uint) {
        let mut t1: uint64_t = *res0
            .offset((4 as libc::c_uint).wrapping_mul(i) as isize);
        let mut t20: uint64_t = *b.offset((4 as libc::c_uint).wrapping_mul(i) as isize);
        let mut res_i0: *mut uint64_t = res0
            .offset((4 as libc::c_uint).wrapping_mul(i) as isize);
        c0 = Hacl_IntTypes_Intrinsics_128_add_carry_u64(c0, t1, t20, res_i0);
        let mut t10: uint64_t = *res0
            .offset(
                (4 as libc::c_uint).wrapping_mul(i).wrapping_add(1 as libc::c_uint)
                    as isize,
            );
        let mut t21: uint64_t = *b
            .offset(
                (4 as libc::c_uint).wrapping_mul(i).wrapping_add(1 as libc::c_uint)
                    as isize,
            );
        let mut res_i1: *mut uint64_t = res0
            .offset((4 as libc::c_uint).wrapping_mul(i) as isize)
            .offset(1 as libc::c_uint as isize);
        c0 = Hacl_IntTypes_Intrinsics_128_add_carry_u64(c0, t10, t21, res_i1);
        let mut t11: uint64_t = *res0
            .offset(
                (4 as libc::c_uint).wrapping_mul(i).wrapping_add(2 as libc::c_uint)
                    as isize,
            );
        let mut t22: uint64_t = *b
            .offset(
                (4 as libc::c_uint).wrapping_mul(i).wrapping_add(2 as libc::c_uint)
                    as isize,
            );
        let mut res_i2: *mut uint64_t = res0
            .offset((4 as libc::c_uint).wrapping_mul(i) as isize)
            .offset(2 as libc::c_uint as isize);
        c0 = Hacl_IntTypes_Intrinsics_128_add_carry_u64(c0, t11, t22, res_i2);
        let mut t12: uint64_t = *res0
            .offset(
                (4 as libc::c_uint).wrapping_mul(i).wrapping_add(3 as libc::c_uint)
                    as isize,
            );
        let mut t2: uint64_t = *b
            .offset(
                (4 as libc::c_uint).wrapping_mul(i).wrapping_add(3 as libc::c_uint)
                    as isize,
            );
        let mut res_i: *mut uint64_t = res0
            .offset((4 as libc::c_uint).wrapping_mul(i) as isize)
            .offset(3 as libc::c_uint as isize);
        c0 = Hacl_IntTypes_Intrinsics_128_add_carry_u64(c0, t12, t2, res_i);
        i = i.wrapping_add(1);
        i;
    }
    let mut i_0: uint32_t = bLen
        .wrapping_div(4 as libc::c_uint)
        .wrapping_mul(4 as libc::c_uint);
    while i_0 < bLen {
        let mut t1_0: uint64_t = *res0.offset(i_0 as isize);
        let mut t2_0: uint64_t = *b.offset(i_0 as isize);
        let mut res_i_0: *mut uint64_t = res0.offset(i_0 as isize);
        c0 = Hacl_IntTypes_Intrinsics_128_add_carry_u64(c0, t1_0, t2_0, res_i_0);
        i_0 = i_0.wrapping_add(1);
        i_0;
    }
    let mut c00: uint64_t = c0;
    if bLen < aLen {
        let mut res1: *mut uint64_t = res.offset(bLen as isize);
        let mut c: uint64_t = c00;
        let mut i_1: uint32_t = 0 as libc::c_uint;
        while i_1 < aLen.wrapping_sub(bLen).wrapping_div(4 as libc::c_uint) {
            let mut t1_1: uint64_t = *res1
                .offset((4 as libc::c_uint).wrapping_mul(i_1) as isize);
            let mut res_i0_0: *mut uint64_t = res1
                .offset((4 as libc::c_uint).wrapping_mul(i_1) as isize);
            c = Hacl_IntTypes_Intrinsics_128_add_carry_u64(
                c,
                t1_1,
                0 as libc::c_ulonglong,
                res_i0_0,
            );
            let mut t10_0: uint64_t = *res1
                .offset(
                    (4 as libc::c_uint).wrapping_mul(i_1).wrapping_add(1 as libc::c_uint)
                        as isize,
                );
            let mut res_i1_0: *mut uint64_t = res1
                .offset((4 as libc::c_uint).wrapping_mul(i_1) as isize)
                .offset(1 as libc::c_uint as isize);
            c = Hacl_IntTypes_Intrinsics_128_add_carry_u64(
                c,
                t10_0,
                0 as libc::c_ulonglong,
                res_i1_0,
            );
            let mut t11_0: uint64_t = *res1
                .offset(
                    (4 as libc::c_uint).wrapping_mul(i_1).wrapping_add(2 as libc::c_uint)
                        as isize,
                );
            let mut res_i2_0: *mut uint64_t = res1
                .offset((4 as libc::c_uint).wrapping_mul(i_1) as isize)
                .offset(2 as libc::c_uint as isize);
            c = Hacl_IntTypes_Intrinsics_128_add_carry_u64(
                c,
                t11_0,
                0 as libc::c_ulonglong,
                res_i2_0,
            );
            let mut t12_0: uint64_t = *res1
                .offset(
                    (4 as libc::c_uint).wrapping_mul(i_1).wrapping_add(3 as libc::c_uint)
                        as isize,
                );
            let mut res_i_1: *mut uint64_t = res1
                .offset((4 as libc::c_uint).wrapping_mul(i_1) as isize)
                .offset(3 as libc::c_uint as isize);
            c = Hacl_IntTypes_Intrinsics_128_add_carry_u64(
                c,
                t12_0,
                0 as libc::c_ulonglong,
                res_i_1,
            );
            i_1 = i_1.wrapping_add(1);
            i_1;
        }
        let mut i_2: uint32_t = aLen
            .wrapping_sub(bLen)
            .wrapping_div(4 as libc::c_uint)
            .wrapping_mul(4 as libc::c_uint);
        while i_2 < aLen.wrapping_sub(bLen) {
            let mut t1_2: uint64_t = *res1.offset(i_2 as isize);
            let mut res_i_2: *mut uint64_t = res1.offset(i_2 as isize);
            c = Hacl_IntTypes_Intrinsics_128_add_carry_u64(
                c,
                t1_2,
                0 as libc::c_ulonglong,
                res_i_2,
            );
            i_2 = i_2.wrapping_add(1);
            i_2;
        }
        let mut c1: uint64_t = c;
        return c1;
    }
    return c00;
}
unsafe extern "C" fn add4(
    mut a: *mut uint64_t,
    mut b: *mut uint64_t,
    mut res: *mut uint64_t,
) -> uint64_t {
    let mut c: uint64_t = 0 as libc::c_ulonglong;
    let mut t1: uint64_t = *a
        .offset((4 as libc::c_uint).wrapping_mul(0 as libc::c_uint) as isize);
    let mut t20: uint64_t = *b
        .offset((4 as libc::c_uint).wrapping_mul(0 as libc::c_uint) as isize);
    let mut res_i0: *mut uint64_t = res
        .offset((4 as libc::c_uint).wrapping_mul(0 as libc::c_uint) as isize);
    c = Hacl_IntTypes_Intrinsics_128_add_carry_u64(c, t1, t20, res_i0);
    let mut t10: uint64_t = *a
        .offset(
            (4 as libc::c_uint)
                .wrapping_mul(0 as libc::c_uint)
                .wrapping_add(1 as libc::c_uint) as isize,
        );
    let mut t21: uint64_t = *b
        .offset(
            (4 as libc::c_uint)
                .wrapping_mul(0 as libc::c_uint)
                .wrapping_add(1 as libc::c_uint) as isize,
        );
    let mut res_i1: *mut uint64_t = res
        .offset((4 as libc::c_uint).wrapping_mul(0 as libc::c_uint) as isize)
        .offset(1 as libc::c_uint as isize);
    c = Hacl_IntTypes_Intrinsics_128_add_carry_u64(c, t10, t21, res_i1);
    let mut t11: uint64_t = *a
        .offset(
            (4 as libc::c_uint)
                .wrapping_mul(0 as libc::c_uint)
                .wrapping_add(2 as libc::c_uint) as isize,
        );
    let mut t22: uint64_t = *b
        .offset(
            (4 as libc::c_uint)
                .wrapping_mul(0 as libc::c_uint)
                .wrapping_add(2 as libc::c_uint) as isize,
        );
    let mut res_i2: *mut uint64_t = res
        .offset((4 as libc::c_uint).wrapping_mul(0 as libc::c_uint) as isize)
        .offset(2 as libc::c_uint as isize);
    c = Hacl_IntTypes_Intrinsics_128_add_carry_u64(c, t11, t22, res_i2);
    let mut t12: uint64_t = *a
        .offset(
            (4 as libc::c_uint)
                .wrapping_mul(0 as libc::c_uint)
                .wrapping_add(3 as libc::c_uint) as isize,
        );
    let mut t2: uint64_t = *b
        .offset(
            (4 as libc::c_uint)
                .wrapping_mul(0 as libc::c_uint)
                .wrapping_add(3 as libc::c_uint) as isize,
        );
    let mut res_i: *mut uint64_t = res
        .offset((4 as libc::c_uint).wrapping_mul(0 as libc::c_uint) as isize)
        .offset(3 as libc::c_uint as isize);
    c = Hacl_IntTypes_Intrinsics_128_add_carry_u64(c, t12, t2, res_i);
    return c;
}
unsafe extern "C" fn add_mod4(
    mut n: *mut uint64_t,
    mut a: *mut uint64_t,
    mut b: *mut uint64_t,
    mut res: *mut uint64_t,
) {
    let mut c0: uint64_t = 0 as libc::c_ulonglong;
    let mut t1: uint64_t = *a
        .offset((4 as libc::c_uint).wrapping_mul(0 as libc::c_uint) as isize);
    let mut t20: uint64_t = *b
        .offset((4 as libc::c_uint).wrapping_mul(0 as libc::c_uint) as isize);
    let mut res_i0: *mut uint64_t = res
        .offset((4 as libc::c_uint).wrapping_mul(0 as libc::c_uint) as isize);
    c0 = Hacl_IntTypes_Intrinsics_128_add_carry_u64(c0, t1, t20, res_i0);
    let mut t10: uint64_t = *a
        .offset(
            (4 as libc::c_uint)
                .wrapping_mul(0 as libc::c_uint)
                .wrapping_add(1 as libc::c_uint) as isize,
        );
    let mut t21: uint64_t = *b
        .offset(
            (4 as libc::c_uint)
                .wrapping_mul(0 as libc::c_uint)
                .wrapping_add(1 as libc::c_uint) as isize,
        );
    let mut res_i1: *mut uint64_t = res
        .offset((4 as libc::c_uint).wrapping_mul(0 as libc::c_uint) as isize)
        .offset(1 as libc::c_uint as isize);
    c0 = Hacl_IntTypes_Intrinsics_128_add_carry_u64(c0, t10, t21, res_i1);
    let mut t11: uint64_t = *a
        .offset(
            (4 as libc::c_uint)
                .wrapping_mul(0 as libc::c_uint)
                .wrapping_add(2 as libc::c_uint) as isize,
        );
    let mut t22: uint64_t = *b
        .offset(
            (4 as libc::c_uint)
                .wrapping_mul(0 as libc::c_uint)
                .wrapping_add(2 as libc::c_uint) as isize,
        );
    let mut res_i2: *mut uint64_t = res
        .offset((4 as libc::c_uint).wrapping_mul(0 as libc::c_uint) as isize)
        .offset(2 as libc::c_uint as isize);
    c0 = Hacl_IntTypes_Intrinsics_128_add_carry_u64(c0, t11, t22, res_i2);
    let mut t12: uint64_t = *a
        .offset(
            (4 as libc::c_uint)
                .wrapping_mul(0 as libc::c_uint)
                .wrapping_add(3 as libc::c_uint) as isize,
        );
    let mut t2: uint64_t = *b
        .offset(
            (4 as libc::c_uint)
                .wrapping_mul(0 as libc::c_uint)
                .wrapping_add(3 as libc::c_uint) as isize,
        );
    let mut res_i: *mut uint64_t = res
        .offset((4 as libc::c_uint).wrapping_mul(0 as libc::c_uint) as isize)
        .offset(3 as libc::c_uint as isize);
    c0 = Hacl_IntTypes_Intrinsics_128_add_carry_u64(c0, t12, t2, res_i);
    let mut c00: uint64_t = c0;
    let mut tmp: [uint64_t; 4] = [0 as libc::c_uint as uint64_t, 0, 0, 0];
    let mut c: uint64_t = 0 as libc::c_ulonglong;
    let mut t1_0: uint64_t = *res
        .offset((4 as libc::c_uint).wrapping_mul(0 as libc::c_uint) as isize);
    let mut t20_0: uint64_t = *n
        .offset((4 as libc::c_uint).wrapping_mul(0 as libc::c_uint) as isize);
    let mut res_i0_0: *mut uint64_t = tmp
        .as_mut_ptr()
        .offset((4 as libc::c_uint).wrapping_mul(0 as libc::c_uint) as isize);
    c = Hacl_IntTypes_Intrinsics_128_sub_borrow_u64(c, t1_0, t20_0, res_i0_0);
    let mut t10_0: uint64_t = *res
        .offset(
            (4 as libc::c_uint)
                .wrapping_mul(0 as libc::c_uint)
                .wrapping_add(1 as libc::c_uint) as isize,
        );
    let mut t21_0: uint64_t = *n
        .offset(
            (4 as libc::c_uint)
                .wrapping_mul(0 as libc::c_uint)
                .wrapping_add(1 as libc::c_uint) as isize,
        );
    let mut res_i1_0: *mut uint64_t = tmp
        .as_mut_ptr()
        .offset((4 as libc::c_uint).wrapping_mul(0 as libc::c_uint) as isize)
        .offset(1 as libc::c_uint as isize);
    c = Hacl_IntTypes_Intrinsics_128_sub_borrow_u64(c, t10_0, t21_0, res_i1_0);
    let mut t11_0: uint64_t = *res
        .offset(
            (4 as libc::c_uint)
                .wrapping_mul(0 as libc::c_uint)
                .wrapping_add(2 as libc::c_uint) as isize,
        );
    let mut t22_0: uint64_t = *n
        .offset(
            (4 as libc::c_uint)
                .wrapping_mul(0 as libc::c_uint)
                .wrapping_add(2 as libc::c_uint) as isize,
        );
    let mut res_i2_0: *mut uint64_t = tmp
        .as_mut_ptr()
        .offset((4 as libc::c_uint).wrapping_mul(0 as libc::c_uint) as isize)
        .offset(2 as libc::c_uint as isize);
    c = Hacl_IntTypes_Intrinsics_128_sub_borrow_u64(c, t11_0, t22_0, res_i2_0);
    let mut t12_0: uint64_t = *res
        .offset(
            (4 as libc::c_uint)
                .wrapping_mul(0 as libc::c_uint)
                .wrapping_add(3 as libc::c_uint) as isize,
        );
    let mut t2_0: uint64_t = *n
        .offset(
            (4 as libc::c_uint)
                .wrapping_mul(0 as libc::c_uint)
                .wrapping_add(3 as libc::c_uint) as isize,
        );
    let mut res_i_0: *mut uint64_t = tmp
        .as_mut_ptr()
        .offset((4 as libc::c_uint).wrapping_mul(0 as libc::c_uint) as isize)
        .offset(3 as libc::c_uint as isize);
    c = Hacl_IntTypes_Intrinsics_128_sub_borrow_u64(c, t12_0, t2_0, res_i_0);
    let mut c1: uint64_t = c;
    let mut c2: uint64_t = c00.wrapping_sub(c1);
    let mut i: uint32_t = 0 as libc::c_uint;
    let mut x: uint64_t = c2 & *res.offset(i as isize) | !c2 & tmp[i as usize];
    let mut os: *mut uint64_t = res;
    *os.offset(i as isize) = x;
    i = (i as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut x_0: uint64_t = c2 & *res.offset(i as isize) | !c2 & tmp[i as usize];
    let mut os_0: *mut uint64_t = res;
    *os_0.offset(i as isize) = x_0;
    i = (i as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut x_1: uint64_t = c2 & *res.offset(i as isize) | !c2 & tmp[i as usize];
    let mut os_1: *mut uint64_t = res;
    *os_1.offset(i as isize) = x_1;
    i = (i as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut x_2: uint64_t = c2 & *res.offset(i as isize) | !c2 & tmp[i as usize];
    let mut os_2: *mut uint64_t = res;
    *os_2.offset(i as isize) = x_2;
    i = (i as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
}
unsafe extern "C" fn sub_mod4(
    mut n: *mut uint64_t,
    mut a: *mut uint64_t,
    mut b: *mut uint64_t,
    mut res: *mut uint64_t,
) {
    let mut c0: uint64_t = 0 as libc::c_ulonglong;
    let mut t1: uint64_t = *a
        .offset((4 as libc::c_uint).wrapping_mul(0 as libc::c_uint) as isize);
    let mut t20: uint64_t = *b
        .offset((4 as libc::c_uint).wrapping_mul(0 as libc::c_uint) as isize);
    let mut res_i0: *mut uint64_t = res
        .offset((4 as libc::c_uint).wrapping_mul(0 as libc::c_uint) as isize);
    c0 = Hacl_IntTypes_Intrinsics_128_sub_borrow_u64(c0, t1, t20, res_i0);
    let mut t10: uint64_t = *a
        .offset(
            (4 as libc::c_uint)
                .wrapping_mul(0 as libc::c_uint)
                .wrapping_add(1 as libc::c_uint) as isize,
        );
    let mut t21: uint64_t = *b
        .offset(
            (4 as libc::c_uint)
                .wrapping_mul(0 as libc::c_uint)
                .wrapping_add(1 as libc::c_uint) as isize,
        );
    let mut res_i1: *mut uint64_t = res
        .offset((4 as libc::c_uint).wrapping_mul(0 as libc::c_uint) as isize)
        .offset(1 as libc::c_uint as isize);
    c0 = Hacl_IntTypes_Intrinsics_128_sub_borrow_u64(c0, t10, t21, res_i1);
    let mut t11: uint64_t = *a
        .offset(
            (4 as libc::c_uint)
                .wrapping_mul(0 as libc::c_uint)
                .wrapping_add(2 as libc::c_uint) as isize,
        );
    let mut t22: uint64_t = *b
        .offset(
            (4 as libc::c_uint)
                .wrapping_mul(0 as libc::c_uint)
                .wrapping_add(2 as libc::c_uint) as isize,
        );
    let mut res_i2: *mut uint64_t = res
        .offset((4 as libc::c_uint).wrapping_mul(0 as libc::c_uint) as isize)
        .offset(2 as libc::c_uint as isize);
    c0 = Hacl_IntTypes_Intrinsics_128_sub_borrow_u64(c0, t11, t22, res_i2);
    let mut t12: uint64_t = *a
        .offset(
            (4 as libc::c_uint)
                .wrapping_mul(0 as libc::c_uint)
                .wrapping_add(3 as libc::c_uint) as isize,
        );
    let mut t2: uint64_t = *b
        .offset(
            (4 as libc::c_uint)
                .wrapping_mul(0 as libc::c_uint)
                .wrapping_add(3 as libc::c_uint) as isize,
        );
    let mut res_i: *mut uint64_t = res
        .offset((4 as libc::c_uint).wrapping_mul(0 as libc::c_uint) as isize)
        .offset(3 as libc::c_uint as isize);
    c0 = Hacl_IntTypes_Intrinsics_128_sub_borrow_u64(c0, t12, t2, res_i);
    let mut c00: uint64_t = c0;
    let mut tmp: [uint64_t; 4] = [0 as libc::c_uint as uint64_t, 0, 0, 0];
    let mut c: uint64_t = 0 as libc::c_ulonglong;
    let mut t1_0: uint64_t = *res
        .offset((4 as libc::c_uint).wrapping_mul(0 as libc::c_uint) as isize);
    let mut t20_0: uint64_t = *n
        .offset((4 as libc::c_uint).wrapping_mul(0 as libc::c_uint) as isize);
    let mut res_i0_0: *mut uint64_t = tmp
        .as_mut_ptr()
        .offset((4 as libc::c_uint).wrapping_mul(0 as libc::c_uint) as isize);
    c = Hacl_IntTypes_Intrinsics_128_add_carry_u64(c, t1_0, t20_0, res_i0_0);
    let mut t10_0: uint64_t = *res
        .offset(
            (4 as libc::c_uint)
                .wrapping_mul(0 as libc::c_uint)
                .wrapping_add(1 as libc::c_uint) as isize,
        );
    let mut t21_0: uint64_t = *n
        .offset(
            (4 as libc::c_uint)
                .wrapping_mul(0 as libc::c_uint)
                .wrapping_add(1 as libc::c_uint) as isize,
        );
    let mut res_i1_0: *mut uint64_t = tmp
        .as_mut_ptr()
        .offset((4 as libc::c_uint).wrapping_mul(0 as libc::c_uint) as isize)
        .offset(1 as libc::c_uint as isize);
    c = Hacl_IntTypes_Intrinsics_128_add_carry_u64(c, t10_0, t21_0, res_i1_0);
    let mut t11_0: uint64_t = *res
        .offset(
            (4 as libc::c_uint)
                .wrapping_mul(0 as libc::c_uint)
                .wrapping_add(2 as libc::c_uint) as isize,
        );
    let mut t22_0: uint64_t = *n
        .offset(
            (4 as libc::c_uint)
                .wrapping_mul(0 as libc::c_uint)
                .wrapping_add(2 as libc::c_uint) as isize,
        );
    let mut res_i2_0: *mut uint64_t = tmp
        .as_mut_ptr()
        .offset((4 as libc::c_uint).wrapping_mul(0 as libc::c_uint) as isize)
        .offset(2 as libc::c_uint as isize);
    c = Hacl_IntTypes_Intrinsics_128_add_carry_u64(c, t11_0, t22_0, res_i2_0);
    let mut t12_0: uint64_t = *res
        .offset(
            (4 as libc::c_uint)
                .wrapping_mul(0 as libc::c_uint)
                .wrapping_add(3 as libc::c_uint) as isize,
        );
    let mut t2_0: uint64_t = *n
        .offset(
            (4 as libc::c_uint)
                .wrapping_mul(0 as libc::c_uint)
                .wrapping_add(3 as libc::c_uint) as isize,
        );
    let mut res_i_0: *mut uint64_t = tmp
        .as_mut_ptr()
        .offset((4 as libc::c_uint).wrapping_mul(0 as libc::c_uint) as isize)
        .offset(3 as libc::c_uint as isize);
    c = Hacl_IntTypes_Intrinsics_128_add_carry_u64(c, t12_0, t2_0, res_i_0);
    let mut c1: uint64_t = c;
    let mut c2: uint64_t = (0 as libc::c_ulonglong).wrapping_sub(c00);
    let mut i: uint32_t = 0 as libc::c_uint;
    let mut x: uint64_t = c2 & tmp[i as usize] | !c2 & *res.offset(i as isize);
    let mut os: *mut uint64_t = res;
    *os.offset(i as isize) = x;
    i = (i as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut x_0: uint64_t = c2 & tmp[i as usize] | !c2 & *res.offset(i as isize);
    let mut os_0: *mut uint64_t = res;
    *os_0.offset(i as isize) = x_0;
    i = (i as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut x_1: uint64_t = c2 & tmp[i as usize] | !c2 & *res.offset(i as isize);
    let mut os_1: *mut uint64_t = res;
    *os_1.offset(i as isize) = x_1;
    i = (i as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut x_2: uint64_t = c2 & tmp[i as usize] | !c2 & *res.offset(i as isize);
    let mut os_2: *mut uint64_t = res;
    *os_2.offset(i as isize) = x_2;
    i = (i as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
}
unsafe extern "C" fn mul4(
    mut a: *mut uint64_t,
    mut b: *mut uint64_t,
    mut res: *mut uint64_t,
) {
    memset(
        res as *mut libc::c_void,
        0 as libc::c_uint as libc::c_int,
        (8 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    let mut i0: uint32_t = 0 as libc::c_uint;
    let mut bj: uint64_t = *b.offset(i0 as isize);
    let mut res_j: *mut uint64_t = res.offset(i0 as isize);
    let mut c: uint64_t = 0 as libc::c_ulonglong;
    let mut a_i: uint64_t = *a
        .offset((4 as libc::c_uint).wrapping_mul(0 as libc::c_uint) as isize);
    let mut res_i0: *mut uint64_t = res_j
        .offset((4 as libc::c_uint).wrapping_mul(0 as libc::c_uint) as isize);
    c = Hacl_Bignum_Base_mul_wide_add2_u64(a_i, bj, c, res_i0);
    let mut a_i0: uint64_t = *a
        .offset(
            (4 as libc::c_uint)
                .wrapping_mul(0 as libc::c_uint)
                .wrapping_add(1 as libc::c_uint) as isize,
        );
    let mut res_i1: *mut uint64_t = res_j
        .offset((4 as libc::c_uint).wrapping_mul(0 as libc::c_uint) as isize)
        .offset(1 as libc::c_uint as isize);
    c = Hacl_Bignum_Base_mul_wide_add2_u64(a_i0, bj, c, res_i1);
    let mut a_i1: uint64_t = *a
        .offset(
            (4 as libc::c_uint)
                .wrapping_mul(0 as libc::c_uint)
                .wrapping_add(2 as libc::c_uint) as isize,
        );
    let mut res_i2: *mut uint64_t = res_j
        .offset((4 as libc::c_uint).wrapping_mul(0 as libc::c_uint) as isize)
        .offset(2 as libc::c_uint as isize);
    c = Hacl_Bignum_Base_mul_wide_add2_u64(a_i1, bj, c, res_i2);
    let mut a_i2: uint64_t = *a
        .offset(
            (4 as libc::c_uint)
                .wrapping_mul(0 as libc::c_uint)
                .wrapping_add(3 as libc::c_uint) as isize,
        );
    let mut res_i: *mut uint64_t = res_j
        .offset((4 as libc::c_uint).wrapping_mul(0 as libc::c_uint) as isize)
        .offset(3 as libc::c_uint as isize);
    c = Hacl_Bignum_Base_mul_wide_add2_u64(a_i2, bj, c, res_i);
    let mut r: uint64_t = c;
    *res.offset((4 as libc::c_uint).wrapping_add(i0) as isize) = r;
    i0 = (i0 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut bj_0: uint64_t = *b.offset(i0 as isize);
    let mut res_j_0: *mut uint64_t = res.offset(i0 as isize);
    let mut c_0: uint64_t = 0 as libc::c_ulonglong;
    let mut a_i_0: uint64_t = *a
        .offset((4 as libc::c_uint).wrapping_mul(0 as libc::c_uint) as isize);
    let mut res_i0_0: *mut uint64_t = res_j_0
        .offset((4 as libc::c_uint).wrapping_mul(0 as libc::c_uint) as isize);
    c_0 = Hacl_Bignum_Base_mul_wide_add2_u64(a_i_0, bj_0, c_0, res_i0_0);
    let mut a_i0_0: uint64_t = *a
        .offset(
            (4 as libc::c_uint)
                .wrapping_mul(0 as libc::c_uint)
                .wrapping_add(1 as libc::c_uint) as isize,
        );
    let mut res_i1_0: *mut uint64_t = res_j_0
        .offset((4 as libc::c_uint).wrapping_mul(0 as libc::c_uint) as isize)
        .offset(1 as libc::c_uint as isize);
    c_0 = Hacl_Bignum_Base_mul_wide_add2_u64(a_i0_0, bj_0, c_0, res_i1_0);
    let mut a_i1_0: uint64_t = *a
        .offset(
            (4 as libc::c_uint)
                .wrapping_mul(0 as libc::c_uint)
                .wrapping_add(2 as libc::c_uint) as isize,
        );
    let mut res_i2_0: *mut uint64_t = res_j_0
        .offset((4 as libc::c_uint).wrapping_mul(0 as libc::c_uint) as isize)
        .offset(2 as libc::c_uint as isize);
    c_0 = Hacl_Bignum_Base_mul_wide_add2_u64(a_i1_0, bj_0, c_0, res_i2_0);
    let mut a_i2_0: uint64_t = *a
        .offset(
            (4 as libc::c_uint)
                .wrapping_mul(0 as libc::c_uint)
                .wrapping_add(3 as libc::c_uint) as isize,
        );
    let mut res_i_0: *mut uint64_t = res_j_0
        .offset((4 as libc::c_uint).wrapping_mul(0 as libc::c_uint) as isize)
        .offset(3 as libc::c_uint as isize);
    c_0 = Hacl_Bignum_Base_mul_wide_add2_u64(a_i2_0, bj_0, c_0, res_i_0);
    let mut r_0: uint64_t = c_0;
    *res.offset((4 as libc::c_uint).wrapping_add(i0) as isize) = r_0;
    i0 = (i0 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut bj_1: uint64_t = *b.offset(i0 as isize);
    let mut res_j_1: *mut uint64_t = res.offset(i0 as isize);
    let mut c_1: uint64_t = 0 as libc::c_ulonglong;
    let mut a_i_1: uint64_t = *a
        .offset((4 as libc::c_uint).wrapping_mul(0 as libc::c_uint) as isize);
    let mut res_i0_1: *mut uint64_t = res_j_1
        .offset((4 as libc::c_uint).wrapping_mul(0 as libc::c_uint) as isize);
    c_1 = Hacl_Bignum_Base_mul_wide_add2_u64(a_i_1, bj_1, c_1, res_i0_1);
    let mut a_i0_1: uint64_t = *a
        .offset(
            (4 as libc::c_uint)
                .wrapping_mul(0 as libc::c_uint)
                .wrapping_add(1 as libc::c_uint) as isize,
        );
    let mut res_i1_1: *mut uint64_t = res_j_1
        .offset((4 as libc::c_uint).wrapping_mul(0 as libc::c_uint) as isize)
        .offset(1 as libc::c_uint as isize);
    c_1 = Hacl_Bignum_Base_mul_wide_add2_u64(a_i0_1, bj_1, c_1, res_i1_1);
    let mut a_i1_1: uint64_t = *a
        .offset(
            (4 as libc::c_uint)
                .wrapping_mul(0 as libc::c_uint)
                .wrapping_add(2 as libc::c_uint) as isize,
        );
    let mut res_i2_1: *mut uint64_t = res_j_1
        .offset((4 as libc::c_uint).wrapping_mul(0 as libc::c_uint) as isize)
        .offset(2 as libc::c_uint as isize);
    c_1 = Hacl_Bignum_Base_mul_wide_add2_u64(a_i1_1, bj_1, c_1, res_i2_1);
    let mut a_i2_1: uint64_t = *a
        .offset(
            (4 as libc::c_uint)
                .wrapping_mul(0 as libc::c_uint)
                .wrapping_add(3 as libc::c_uint) as isize,
        );
    let mut res_i_1: *mut uint64_t = res_j_1
        .offset((4 as libc::c_uint).wrapping_mul(0 as libc::c_uint) as isize)
        .offset(3 as libc::c_uint as isize);
    c_1 = Hacl_Bignum_Base_mul_wide_add2_u64(a_i2_1, bj_1, c_1, res_i_1);
    let mut r_1: uint64_t = c_1;
    *res.offset((4 as libc::c_uint).wrapping_add(i0) as isize) = r_1;
    i0 = (i0 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut bj_2: uint64_t = *b.offset(i0 as isize);
    let mut res_j_2: *mut uint64_t = res.offset(i0 as isize);
    let mut c_2: uint64_t = 0 as libc::c_ulonglong;
    let mut a_i_2: uint64_t = *a
        .offset((4 as libc::c_uint).wrapping_mul(0 as libc::c_uint) as isize);
    let mut res_i0_2: *mut uint64_t = res_j_2
        .offset((4 as libc::c_uint).wrapping_mul(0 as libc::c_uint) as isize);
    c_2 = Hacl_Bignum_Base_mul_wide_add2_u64(a_i_2, bj_2, c_2, res_i0_2);
    let mut a_i0_2: uint64_t = *a
        .offset(
            (4 as libc::c_uint)
                .wrapping_mul(0 as libc::c_uint)
                .wrapping_add(1 as libc::c_uint) as isize,
        );
    let mut res_i1_2: *mut uint64_t = res_j_2
        .offset((4 as libc::c_uint).wrapping_mul(0 as libc::c_uint) as isize)
        .offset(1 as libc::c_uint as isize);
    c_2 = Hacl_Bignum_Base_mul_wide_add2_u64(a_i0_2, bj_2, c_2, res_i1_2);
    let mut a_i1_2: uint64_t = *a
        .offset(
            (4 as libc::c_uint)
                .wrapping_mul(0 as libc::c_uint)
                .wrapping_add(2 as libc::c_uint) as isize,
        );
    let mut res_i2_2: *mut uint64_t = res_j_2
        .offset((4 as libc::c_uint).wrapping_mul(0 as libc::c_uint) as isize)
        .offset(2 as libc::c_uint as isize);
    c_2 = Hacl_Bignum_Base_mul_wide_add2_u64(a_i1_2, bj_2, c_2, res_i2_2);
    let mut a_i2_2: uint64_t = *a
        .offset(
            (4 as libc::c_uint)
                .wrapping_mul(0 as libc::c_uint)
                .wrapping_add(3 as libc::c_uint) as isize,
        );
    let mut res_i_2: *mut uint64_t = res_j_2
        .offset((4 as libc::c_uint).wrapping_mul(0 as libc::c_uint) as isize)
        .offset(3 as libc::c_uint as isize);
    c_2 = Hacl_Bignum_Base_mul_wide_add2_u64(a_i2_2, bj_2, c_2, res_i_2);
    let mut r_2: uint64_t = c_2;
    *res.offset((4 as libc::c_uint).wrapping_add(i0) as isize) = r_2;
    i0 = (i0 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
}
unsafe extern "C" fn sqr4(mut a: *mut uint64_t, mut res: *mut uint64_t) {
    memset(
        res as *mut libc::c_void,
        0 as libc::c_uint as libc::c_int,
        (8 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    let mut i0: uint32_t = 0 as libc::c_uint;
    let mut a_j: uint64_t = *a.offset(i0 as isize);
    let mut ab: *mut uint64_t = a;
    let mut res_j: *mut uint64_t = res.offset(i0 as isize);
    let mut c: uint64_t = 0 as libc::c_ulonglong;
    let mut i: uint32_t = 0 as libc::c_uint;
    while i < i0.wrapping_div(4 as libc::c_uint) {
        let mut a_i: uint64_t = *ab.offset((4 as libc::c_uint).wrapping_mul(i) as isize);
        let mut res_i0: *mut uint64_t = res_j
            .offset((4 as libc::c_uint).wrapping_mul(i) as isize);
        c = Hacl_Bignum_Base_mul_wide_add2_u64(a_i, a_j, c, res_i0);
        let mut a_i0: uint64_t = *ab
            .offset(
                (4 as libc::c_uint).wrapping_mul(i).wrapping_add(1 as libc::c_uint)
                    as isize,
            );
        let mut res_i1: *mut uint64_t = res_j
            .offset((4 as libc::c_uint).wrapping_mul(i) as isize)
            .offset(1 as libc::c_uint as isize);
        c = Hacl_Bignum_Base_mul_wide_add2_u64(a_i0, a_j, c, res_i1);
        let mut a_i1: uint64_t = *ab
            .offset(
                (4 as libc::c_uint).wrapping_mul(i).wrapping_add(2 as libc::c_uint)
                    as isize,
            );
        let mut res_i2: *mut uint64_t = res_j
            .offset((4 as libc::c_uint).wrapping_mul(i) as isize)
            .offset(2 as libc::c_uint as isize);
        c = Hacl_Bignum_Base_mul_wide_add2_u64(a_i1, a_j, c, res_i2);
        let mut a_i2: uint64_t = *ab
            .offset(
                (4 as libc::c_uint).wrapping_mul(i).wrapping_add(3 as libc::c_uint)
                    as isize,
            );
        let mut res_i: *mut uint64_t = res_j
            .offset((4 as libc::c_uint).wrapping_mul(i) as isize)
            .offset(3 as libc::c_uint as isize);
        c = Hacl_Bignum_Base_mul_wide_add2_u64(a_i2, a_j, c, res_i);
        i = i.wrapping_add(1);
        i;
    }
    let mut i_0: uint32_t = i0
        .wrapping_div(4 as libc::c_uint)
        .wrapping_mul(4 as libc::c_uint);
    while i_0 < i0 {
        let mut a_i_0: uint64_t = *ab.offset(i_0 as isize);
        let mut res_i_0: *mut uint64_t = res_j.offset(i_0 as isize);
        c = Hacl_Bignum_Base_mul_wide_add2_u64(a_i_0, a_j, c, res_i_0);
        i_0 = i_0.wrapping_add(1);
        i_0;
    }
    let mut r: uint64_t = c;
    *res.offset(i0.wrapping_add(i0) as isize) = r;
    i0 = (i0 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut a_j_0: uint64_t = *a.offset(i0 as isize);
    let mut ab_0: *mut uint64_t = a;
    let mut res_j_0: *mut uint64_t = res.offset(i0 as isize);
    let mut c_0: uint64_t = 0 as libc::c_ulonglong;
    let mut i_1: uint32_t = 0 as libc::c_uint;
    while i_1 < i0.wrapping_div(4 as libc::c_uint) {
        let mut a_i_1: uint64_t = *ab_0
            .offset((4 as libc::c_uint).wrapping_mul(i_1) as isize);
        let mut res_i0_0: *mut uint64_t = res_j_0
            .offset((4 as libc::c_uint).wrapping_mul(i_1) as isize);
        c_0 = Hacl_Bignum_Base_mul_wide_add2_u64(a_i_1, a_j_0, c_0, res_i0_0);
        let mut a_i0_0: uint64_t = *ab_0
            .offset(
                (4 as libc::c_uint).wrapping_mul(i_1).wrapping_add(1 as libc::c_uint)
                    as isize,
            );
        let mut res_i1_0: *mut uint64_t = res_j_0
            .offset((4 as libc::c_uint).wrapping_mul(i_1) as isize)
            .offset(1 as libc::c_uint as isize);
        c_0 = Hacl_Bignum_Base_mul_wide_add2_u64(a_i0_0, a_j_0, c_0, res_i1_0);
        let mut a_i1_0: uint64_t = *ab_0
            .offset(
                (4 as libc::c_uint).wrapping_mul(i_1).wrapping_add(2 as libc::c_uint)
                    as isize,
            );
        let mut res_i2_0: *mut uint64_t = res_j_0
            .offset((4 as libc::c_uint).wrapping_mul(i_1) as isize)
            .offset(2 as libc::c_uint as isize);
        c_0 = Hacl_Bignum_Base_mul_wide_add2_u64(a_i1_0, a_j_0, c_0, res_i2_0);
        let mut a_i2_0: uint64_t = *ab_0
            .offset(
                (4 as libc::c_uint).wrapping_mul(i_1).wrapping_add(3 as libc::c_uint)
                    as isize,
            );
        let mut res_i_1: *mut uint64_t = res_j_0
            .offset((4 as libc::c_uint).wrapping_mul(i_1) as isize)
            .offset(3 as libc::c_uint as isize);
        c_0 = Hacl_Bignum_Base_mul_wide_add2_u64(a_i2_0, a_j_0, c_0, res_i_1);
        i_1 = i_1.wrapping_add(1);
        i_1;
    }
    let mut i_2: uint32_t = i0
        .wrapping_div(4 as libc::c_uint)
        .wrapping_mul(4 as libc::c_uint);
    while i_2 < i0 {
        let mut a_i_2: uint64_t = *ab_0.offset(i_2 as isize);
        let mut res_i_2: *mut uint64_t = res_j_0.offset(i_2 as isize);
        c_0 = Hacl_Bignum_Base_mul_wide_add2_u64(a_i_2, a_j_0, c_0, res_i_2);
        i_2 = i_2.wrapping_add(1);
        i_2;
    }
    let mut r_0: uint64_t = c_0;
    *res.offset(i0.wrapping_add(i0) as isize) = r_0;
    i0 = (i0 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut a_j_1: uint64_t = *a.offset(i0 as isize);
    let mut ab_1: *mut uint64_t = a;
    let mut res_j_1: *mut uint64_t = res.offset(i0 as isize);
    let mut c_1: uint64_t = 0 as libc::c_ulonglong;
    let mut i_3: uint32_t = 0 as libc::c_uint;
    while i_3 < i0.wrapping_div(4 as libc::c_uint) {
        let mut a_i_3: uint64_t = *ab_1
            .offset((4 as libc::c_uint).wrapping_mul(i_3) as isize);
        let mut res_i0_1: *mut uint64_t = res_j_1
            .offset((4 as libc::c_uint).wrapping_mul(i_3) as isize);
        c_1 = Hacl_Bignum_Base_mul_wide_add2_u64(a_i_3, a_j_1, c_1, res_i0_1);
        let mut a_i0_1: uint64_t = *ab_1
            .offset(
                (4 as libc::c_uint).wrapping_mul(i_3).wrapping_add(1 as libc::c_uint)
                    as isize,
            );
        let mut res_i1_1: *mut uint64_t = res_j_1
            .offset((4 as libc::c_uint).wrapping_mul(i_3) as isize)
            .offset(1 as libc::c_uint as isize);
        c_1 = Hacl_Bignum_Base_mul_wide_add2_u64(a_i0_1, a_j_1, c_1, res_i1_1);
        let mut a_i1_1: uint64_t = *ab_1
            .offset(
                (4 as libc::c_uint).wrapping_mul(i_3).wrapping_add(2 as libc::c_uint)
                    as isize,
            );
        let mut res_i2_1: *mut uint64_t = res_j_1
            .offset((4 as libc::c_uint).wrapping_mul(i_3) as isize)
            .offset(2 as libc::c_uint as isize);
        c_1 = Hacl_Bignum_Base_mul_wide_add2_u64(a_i1_1, a_j_1, c_1, res_i2_1);
        let mut a_i2_1: uint64_t = *ab_1
            .offset(
                (4 as libc::c_uint).wrapping_mul(i_3).wrapping_add(3 as libc::c_uint)
                    as isize,
            );
        let mut res_i_3: *mut uint64_t = res_j_1
            .offset((4 as libc::c_uint).wrapping_mul(i_3) as isize)
            .offset(3 as libc::c_uint as isize);
        c_1 = Hacl_Bignum_Base_mul_wide_add2_u64(a_i2_1, a_j_1, c_1, res_i_3);
        i_3 = i_3.wrapping_add(1);
        i_3;
    }
    let mut i_4: uint32_t = i0
        .wrapping_div(4 as libc::c_uint)
        .wrapping_mul(4 as libc::c_uint);
    while i_4 < i0 {
        let mut a_i_4: uint64_t = *ab_1.offset(i_4 as isize);
        let mut res_i_4: *mut uint64_t = res_j_1.offset(i_4 as isize);
        c_1 = Hacl_Bignum_Base_mul_wide_add2_u64(a_i_4, a_j_1, c_1, res_i_4);
        i_4 = i_4.wrapping_add(1);
        i_4;
    }
    let mut r_1: uint64_t = c_1;
    *res.offset(i0.wrapping_add(i0) as isize) = r_1;
    i0 = (i0 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut a_j_2: uint64_t = *a.offset(i0 as isize);
    let mut ab_2: *mut uint64_t = a;
    let mut res_j_2: *mut uint64_t = res.offset(i0 as isize);
    let mut c_2: uint64_t = 0 as libc::c_ulonglong;
    let mut i_5: uint32_t = 0 as libc::c_uint;
    while i_5 < i0.wrapping_div(4 as libc::c_uint) {
        let mut a_i_5: uint64_t = *ab_2
            .offset((4 as libc::c_uint).wrapping_mul(i_5) as isize);
        let mut res_i0_2: *mut uint64_t = res_j_2
            .offset((4 as libc::c_uint).wrapping_mul(i_5) as isize);
        c_2 = Hacl_Bignum_Base_mul_wide_add2_u64(a_i_5, a_j_2, c_2, res_i0_2);
        let mut a_i0_2: uint64_t = *ab_2
            .offset(
                (4 as libc::c_uint).wrapping_mul(i_5).wrapping_add(1 as libc::c_uint)
                    as isize,
            );
        let mut res_i1_2: *mut uint64_t = res_j_2
            .offset((4 as libc::c_uint).wrapping_mul(i_5) as isize)
            .offset(1 as libc::c_uint as isize);
        c_2 = Hacl_Bignum_Base_mul_wide_add2_u64(a_i0_2, a_j_2, c_2, res_i1_2);
        let mut a_i1_2: uint64_t = *ab_2
            .offset(
                (4 as libc::c_uint).wrapping_mul(i_5).wrapping_add(2 as libc::c_uint)
                    as isize,
            );
        let mut res_i2_2: *mut uint64_t = res_j_2
            .offset((4 as libc::c_uint).wrapping_mul(i_5) as isize)
            .offset(2 as libc::c_uint as isize);
        c_2 = Hacl_Bignum_Base_mul_wide_add2_u64(a_i1_2, a_j_2, c_2, res_i2_2);
        let mut a_i2_2: uint64_t = *ab_2
            .offset(
                (4 as libc::c_uint).wrapping_mul(i_5).wrapping_add(3 as libc::c_uint)
                    as isize,
            );
        let mut res_i_5: *mut uint64_t = res_j_2
            .offset((4 as libc::c_uint).wrapping_mul(i_5) as isize)
            .offset(3 as libc::c_uint as isize);
        c_2 = Hacl_Bignum_Base_mul_wide_add2_u64(a_i2_2, a_j_2, c_2, res_i_5);
        i_5 = i_5.wrapping_add(1);
        i_5;
    }
    let mut i_6: uint32_t = i0
        .wrapping_div(4 as libc::c_uint)
        .wrapping_mul(4 as libc::c_uint);
    while i_6 < i0 {
        let mut a_i_6: uint64_t = *ab_2.offset(i_6 as isize);
        let mut res_i_6: *mut uint64_t = res_j_2.offset(i_6 as isize);
        c_2 = Hacl_Bignum_Base_mul_wide_add2_u64(a_i_6, a_j_2, c_2, res_i_6);
        i_6 = i_6.wrapping_add(1);
        i_6;
    }
    let mut r_2: uint64_t = c_2;
    *res.offset(i0.wrapping_add(i0) as isize) = r_2;
    i0 = (i0 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut a_copy0: [uint64_t; 8] = [
        0 as libc::c_uint as uint64_t,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
    ];
    let mut b_copy0: [uint64_t; 8] = [
        0 as libc::c_uint as uint64_t,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
    ];
    memcpy(
        a_copy0.as_mut_ptr() as *mut libc::c_void,
        res as *const libc::c_void,
        (8 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    memcpy(
        b_copy0.as_mut_ptr() as *mut libc::c_void,
        res as *const libc::c_void,
        (8 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    let mut r_3: uint64_t = Hacl_Bignum_Addition_bn_add_eq_len_u64(
        8 as libc::c_uint,
        a_copy0.as_mut_ptr(),
        b_copy0.as_mut_ptr(),
        res,
    );
    let mut c0: uint64_t = r_3;
    let mut tmp: [uint64_t; 8] = [0 as libc::c_uint as uint64_t, 0, 0, 0, 0, 0, 0, 0];
    let mut i_7: uint32_t = 0 as libc::c_uint;
    let mut res1: FStar_UInt128_uint128 = FStar_UInt128_mul_wide(
        *a.offset(i_7 as isize),
        *a.offset(i_7 as isize),
    );
    let mut hi: uint64_t = FStar_UInt128_uint128_to_uint64(
        FStar_UInt128_shift_right(res1, 64 as libc::c_uint),
    );
    let mut lo: uint64_t = FStar_UInt128_uint128_to_uint64(res1);
    tmp[(2 as libc::c_uint).wrapping_mul(i_7) as usize] = lo;
    tmp[(2 as libc::c_uint).wrapping_mul(i_7).wrapping_add(1 as libc::c_uint)
        as usize] = hi;
    i_7 = (i_7 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut res1_0: FStar_UInt128_uint128 = FStar_UInt128_mul_wide(
        *a.offset(i_7 as isize),
        *a.offset(i_7 as isize),
    );
    let mut hi_0: uint64_t = FStar_UInt128_uint128_to_uint64(
        FStar_UInt128_shift_right(res1_0, 64 as libc::c_uint),
    );
    let mut lo_0: uint64_t = FStar_UInt128_uint128_to_uint64(res1_0);
    tmp[(2 as libc::c_uint).wrapping_mul(i_7) as usize] = lo_0;
    tmp[(2 as libc::c_uint).wrapping_mul(i_7).wrapping_add(1 as libc::c_uint)
        as usize] = hi_0;
    i_7 = (i_7 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut res1_1: FStar_UInt128_uint128 = FStar_UInt128_mul_wide(
        *a.offset(i_7 as isize),
        *a.offset(i_7 as isize),
    );
    let mut hi_1: uint64_t = FStar_UInt128_uint128_to_uint64(
        FStar_UInt128_shift_right(res1_1, 64 as libc::c_uint),
    );
    let mut lo_1: uint64_t = FStar_UInt128_uint128_to_uint64(res1_1);
    tmp[(2 as libc::c_uint).wrapping_mul(i_7) as usize] = lo_1;
    tmp[(2 as libc::c_uint).wrapping_mul(i_7).wrapping_add(1 as libc::c_uint)
        as usize] = hi_1;
    i_7 = (i_7 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut res1_2: FStar_UInt128_uint128 = FStar_UInt128_mul_wide(
        *a.offset(i_7 as isize),
        *a.offset(i_7 as isize),
    );
    let mut hi_2: uint64_t = FStar_UInt128_uint128_to_uint64(
        FStar_UInt128_shift_right(res1_2, 64 as libc::c_uint),
    );
    let mut lo_2: uint64_t = FStar_UInt128_uint128_to_uint64(res1_2);
    tmp[(2 as libc::c_uint).wrapping_mul(i_7) as usize] = lo_2;
    tmp[(2 as libc::c_uint).wrapping_mul(i_7).wrapping_add(1 as libc::c_uint)
        as usize] = hi_2;
    i_7 = (i_7 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut a_copy: [uint64_t; 8] = [0 as libc::c_uint as uint64_t, 0, 0, 0, 0, 0, 0, 0];
    let mut b_copy: [uint64_t; 8] = [0 as libc::c_uint as uint64_t, 0, 0, 0, 0, 0, 0, 0];
    memcpy(
        a_copy.as_mut_ptr() as *mut libc::c_void,
        res as *const libc::c_void,
        (8 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    memcpy(
        b_copy.as_mut_ptr() as *mut libc::c_void,
        tmp.as_mut_ptr() as *const libc::c_void,
        (8 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    let mut r0: uint64_t = Hacl_Bignum_Addition_bn_add_eq_len_u64(
        8 as libc::c_uint,
        a_copy.as_mut_ptr(),
        b_copy.as_mut_ptr(),
        res,
    );
    let mut c1: uint64_t = r0;
}
#[inline]
unsafe extern "C" fn is_qelem_zero(mut f: *mut uint64_t) -> uint64_t {
    let mut bn_zero: [uint64_t; 4] = [0 as libc::c_uint as uint64_t, 0, 0, 0];
    let mut mask: uint64_t = 0xffffffffffffffff as libc::c_ulonglong;
    let mut i: uint32_t = 0 as libc::c_uint;
    let mut uu____0: uint64_t = FStar_UInt64_eq_mask(
        *f.offset(i as isize),
        bn_zero[i as usize],
    );
    mask = uu____0 & mask;
    i = (i as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut uu____0_0: uint64_t = FStar_UInt64_eq_mask(
        *f.offset(i as isize),
        bn_zero[i as usize],
    );
    mask = uu____0_0 & mask;
    i = (i as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut uu____0_1: uint64_t = FStar_UInt64_eq_mask(
        *f.offset(i as isize),
        bn_zero[i as usize],
    );
    mask = uu____0_1 & mask;
    i = (i as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut uu____0_2: uint64_t = FStar_UInt64_eq_mask(
        *f.offset(i as isize),
        bn_zero[i as usize],
    );
    mask = uu____0_2 & mask;
    i = (i as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut mask1: uint64_t = mask;
    let mut res: uint64_t = mask1;
    return res;
}
#[inline]
unsafe extern "C" fn is_qelem_zero_vartime(mut f: *mut uint64_t) -> bool {
    let mut f0: uint64_t = *f.offset(0 as libc::c_uint as isize);
    let mut f1: uint64_t = *f.offset(1 as libc::c_uint as isize);
    let mut f2: uint64_t = *f.offset(2 as libc::c_uint as isize);
    let mut f3: uint64_t = *f.offset(3 as libc::c_uint as isize);
    return f0 == 0 as libc::c_ulonglong && f1 == 0 as libc::c_ulonglong
        && f2 == 0 as libc::c_ulonglong && f3 == 0 as libc::c_ulonglong;
}
#[inline]
unsafe extern "C" fn load_qelem_check(
    mut f: *mut uint64_t,
    mut b: *mut uint8_t,
) -> uint64_t {
    let mut n: [uint64_t; 4] = [0 as libc::c_uint as uint64_t, 0, 0, 0];
    n[0 as libc::c_uint as usize] = 0xbfd25e8cd0364141 as libc::c_ulonglong;
    n[1 as libc::c_uint as usize] = 0xbaaedce6af48a03b as libc::c_ulonglong;
    n[2 as libc::c_uint as usize] = 0xfffffffffffffffe as libc::c_ulonglong;
    n[3 as libc::c_uint as usize] = 0xffffffffffffffff as libc::c_ulonglong;
    let mut i: uint32_t = 0 as libc::c_uint;
    let mut u: uint64_t = if 0 != 0 {
        (load64(
            b
                .offset(
                    (4 as libc::c_uint)
                        .wrapping_sub(i)
                        .wrapping_sub(1 as libc::c_uint)
                        .wrapping_mul(8 as libc::c_uint) as isize,
                ),
        ) & 0xff00000000000000 as libc::c_ulonglong) >> 56 as libc::c_int
            | (load64(
                b
                    .offset(
                        (4 as libc::c_uint)
                            .wrapping_sub(i)
                            .wrapping_sub(1 as libc::c_uint)
                            .wrapping_mul(8 as libc::c_uint) as isize,
                    ),
            ) & 0xff000000000000 as libc::c_ulonglong) >> 40 as libc::c_int
            | (load64(
                b
                    .offset(
                        (4 as libc::c_uint)
                            .wrapping_sub(i)
                            .wrapping_sub(1 as libc::c_uint)
                            .wrapping_mul(8 as libc::c_uint) as isize,
                    ),
            ) & 0xff0000000000 as libc::c_ulonglong) >> 24 as libc::c_int
            | (load64(
                b
                    .offset(
                        (4 as libc::c_uint)
                            .wrapping_sub(i)
                            .wrapping_sub(1 as libc::c_uint)
                            .wrapping_mul(8 as libc::c_uint) as isize,
                    ),
            ) & 0xff00000000 as libc::c_ulonglong) >> 8 as libc::c_int
            | (load64(
                b
                    .offset(
                        (4 as libc::c_uint)
                            .wrapping_sub(i)
                            .wrapping_sub(1 as libc::c_uint)
                            .wrapping_mul(8 as libc::c_uint) as isize,
                    ),
            ) & 0xff000000 as libc::c_ulonglong) << 8 as libc::c_int
            | (load64(
                b
                    .offset(
                        (4 as libc::c_uint)
                            .wrapping_sub(i)
                            .wrapping_sub(1 as libc::c_uint)
                            .wrapping_mul(8 as libc::c_uint) as isize,
                    ),
            ) & 0xff0000 as libc::c_ulonglong) << 24 as libc::c_int
            | (load64(
                b
                    .offset(
                        (4 as libc::c_uint)
                            .wrapping_sub(i)
                            .wrapping_sub(1 as libc::c_uint)
                            .wrapping_mul(8 as libc::c_uint) as isize,
                    ),
            ) & 0xff00 as libc::c_ulonglong) << 40 as libc::c_int
            | (load64(
                b
                    .offset(
                        (4 as libc::c_uint)
                            .wrapping_sub(i)
                            .wrapping_sub(1 as libc::c_uint)
                            .wrapping_mul(8 as libc::c_uint) as isize,
                    ),
            ) & 0xff as libc::c_ulonglong) << 56 as libc::c_int
    } else {
        _OSSwapInt64(
            load64(
                b
                    .offset(
                        (4 as libc::c_uint)
                            .wrapping_sub(i)
                            .wrapping_sub(1 as libc::c_uint)
                            .wrapping_mul(8 as libc::c_uint) as isize,
                    ),
            ),
        )
    };
    let mut x: uint64_t = u;
    let mut os: *mut uint64_t = f;
    *os.offset(i as isize) = x;
    i = (i as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut u_0: uint64_t = if 0 != 0 {
        (load64(
            b
                .offset(
                    (4 as libc::c_uint)
                        .wrapping_sub(i)
                        .wrapping_sub(1 as libc::c_uint)
                        .wrapping_mul(8 as libc::c_uint) as isize,
                ),
        ) & 0xff00000000000000 as libc::c_ulonglong) >> 56 as libc::c_int
            | (load64(
                b
                    .offset(
                        (4 as libc::c_uint)
                            .wrapping_sub(i)
                            .wrapping_sub(1 as libc::c_uint)
                            .wrapping_mul(8 as libc::c_uint) as isize,
                    ),
            ) & 0xff000000000000 as libc::c_ulonglong) >> 40 as libc::c_int
            | (load64(
                b
                    .offset(
                        (4 as libc::c_uint)
                            .wrapping_sub(i)
                            .wrapping_sub(1 as libc::c_uint)
                            .wrapping_mul(8 as libc::c_uint) as isize,
                    ),
            ) & 0xff0000000000 as libc::c_ulonglong) >> 24 as libc::c_int
            | (load64(
                b
                    .offset(
                        (4 as libc::c_uint)
                            .wrapping_sub(i)
                            .wrapping_sub(1 as libc::c_uint)
                            .wrapping_mul(8 as libc::c_uint) as isize,
                    ),
            ) & 0xff00000000 as libc::c_ulonglong) >> 8 as libc::c_int
            | (load64(
                b
                    .offset(
                        (4 as libc::c_uint)
                            .wrapping_sub(i)
                            .wrapping_sub(1 as libc::c_uint)
                            .wrapping_mul(8 as libc::c_uint) as isize,
                    ),
            ) & 0xff000000 as libc::c_ulonglong) << 8 as libc::c_int
            | (load64(
                b
                    .offset(
                        (4 as libc::c_uint)
                            .wrapping_sub(i)
                            .wrapping_sub(1 as libc::c_uint)
                            .wrapping_mul(8 as libc::c_uint) as isize,
                    ),
            ) & 0xff0000 as libc::c_ulonglong) << 24 as libc::c_int
            | (load64(
                b
                    .offset(
                        (4 as libc::c_uint)
                            .wrapping_sub(i)
                            .wrapping_sub(1 as libc::c_uint)
                            .wrapping_mul(8 as libc::c_uint) as isize,
                    ),
            ) & 0xff00 as libc::c_ulonglong) << 40 as libc::c_int
            | (load64(
                b
                    .offset(
                        (4 as libc::c_uint)
                            .wrapping_sub(i)
                            .wrapping_sub(1 as libc::c_uint)
                            .wrapping_mul(8 as libc::c_uint) as isize,
                    ),
            ) & 0xff as libc::c_ulonglong) << 56 as libc::c_int
    } else {
        _OSSwapInt64(
            load64(
                b
                    .offset(
                        (4 as libc::c_uint)
                            .wrapping_sub(i)
                            .wrapping_sub(1 as libc::c_uint)
                            .wrapping_mul(8 as libc::c_uint) as isize,
                    ),
            ),
        )
    };
    let mut x_0: uint64_t = u_0;
    let mut os_0: *mut uint64_t = f;
    *os_0.offset(i as isize) = x_0;
    i = (i as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut u_1: uint64_t = if 0 != 0 {
        (load64(
            b
                .offset(
                    (4 as libc::c_uint)
                        .wrapping_sub(i)
                        .wrapping_sub(1 as libc::c_uint)
                        .wrapping_mul(8 as libc::c_uint) as isize,
                ),
        ) & 0xff00000000000000 as libc::c_ulonglong) >> 56 as libc::c_int
            | (load64(
                b
                    .offset(
                        (4 as libc::c_uint)
                            .wrapping_sub(i)
                            .wrapping_sub(1 as libc::c_uint)
                            .wrapping_mul(8 as libc::c_uint) as isize,
                    ),
            ) & 0xff000000000000 as libc::c_ulonglong) >> 40 as libc::c_int
            | (load64(
                b
                    .offset(
                        (4 as libc::c_uint)
                            .wrapping_sub(i)
                            .wrapping_sub(1 as libc::c_uint)
                            .wrapping_mul(8 as libc::c_uint) as isize,
                    ),
            ) & 0xff0000000000 as libc::c_ulonglong) >> 24 as libc::c_int
            | (load64(
                b
                    .offset(
                        (4 as libc::c_uint)
                            .wrapping_sub(i)
                            .wrapping_sub(1 as libc::c_uint)
                            .wrapping_mul(8 as libc::c_uint) as isize,
                    ),
            ) & 0xff00000000 as libc::c_ulonglong) >> 8 as libc::c_int
            | (load64(
                b
                    .offset(
                        (4 as libc::c_uint)
                            .wrapping_sub(i)
                            .wrapping_sub(1 as libc::c_uint)
                            .wrapping_mul(8 as libc::c_uint) as isize,
                    ),
            ) & 0xff000000 as libc::c_ulonglong) << 8 as libc::c_int
            | (load64(
                b
                    .offset(
                        (4 as libc::c_uint)
                            .wrapping_sub(i)
                            .wrapping_sub(1 as libc::c_uint)
                            .wrapping_mul(8 as libc::c_uint) as isize,
                    ),
            ) & 0xff0000 as libc::c_ulonglong) << 24 as libc::c_int
            | (load64(
                b
                    .offset(
                        (4 as libc::c_uint)
                            .wrapping_sub(i)
                            .wrapping_sub(1 as libc::c_uint)
                            .wrapping_mul(8 as libc::c_uint) as isize,
                    ),
            ) & 0xff00 as libc::c_ulonglong) << 40 as libc::c_int
            | (load64(
                b
                    .offset(
                        (4 as libc::c_uint)
                            .wrapping_sub(i)
                            .wrapping_sub(1 as libc::c_uint)
                            .wrapping_mul(8 as libc::c_uint) as isize,
                    ),
            ) & 0xff as libc::c_ulonglong) << 56 as libc::c_int
    } else {
        _OSSwapInt64(
            load64(
                b
                    .offset(
                        (4 as libc::c_uint)
                            .wrapping_sub(i)
                            .wrapping_sub(1 as libc::c_uint)
                            .wrapping_mul(8 as libc::c_uint) as isize,
                    ),
            ),
        )
    };
    let mut x_1: uint64_t = u_1;
    let mut os_1: *mut uint64_t = f;
    *os_1.offset(i as isize) = x_1;
    i = (i as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut u_2: uint64_t = if 0 != 0 {
        (load64(
            b
                .offset(
                    (4 as libc::c_uint)
                        .wrapping_sub(i)
                        .wrapping_sub(1 as libc::c_uint)
                        .wrapping_mul(8 as libc::c_uint) as isize,
                ),
        ) & 0xff00000000000000 as libc::c_ulonglong) >> 56 as libc::c_int
            | (load64(
                b
                    .offset(
                        (4 as libc::c_uint)
                            .wrapping_sub(i)
                            .wrapping_sub(1 as libc::c_uint)
                            .wrapping_mul(8 as libc::c_uint) as isize,
                    ),
            ) & 0xff000000000000 as libc::c_ulonglong) >> 40 as libc::c_int
            | (load64(
                b
                    .offset(
                        (4 as libc::c_uint)
                            .wrapping_sub(i)
                            .wrapping_sub(1 as libc::c_uint)
                            .wrapping_mul(8 as libc::c_uint) as isize,
                    ),
            ) & 0xff0000000000 as libc::c_ulonglong) >> 24 as libc::c_int
            | (load64(
                b
                    .offset(
                        (4 as libc::c_uint)
                            .wrapping_sub(i)
                            .wrapping_sub(1 as libc::c_uint)
                            .wrapping_mul(8 as libc::c_uint) as isize,
                    ),
            ) & 0xff00000000 as libc::c_ulonglong) >> 8 as libc::c_int
            | (load64(
                b
                    .offset(
                        (4 as libc::c_uint)
                            .wrapping_sub(i)
                            .wrapping_sub(1 as libc::c_uint)
                            .wrapping_mul(8 as libc::c_uint) as isize,
                    ),
            ) & 0xff000000 as libc::c_ulonglong) << 8 as libc::c_int
            | (load64(
                b
                    .offset(
                        (4 as libc::c_uint)
                            .wrapping_sub(i)
                            .wrapping_sub(1 as libc::c_uint)
                            .wrapping_mul(8 as libc::c_uint) as isize,
                    ),
            ) & 0xff0000 as libc::c_ulonglong) << 24 as libc::c_int
            | (load64(
                b
                    .offset(
                        (4 as libc::c_uint)
                            .wrapping_sub(i)
                            .wrapping_sub(1 as libc::c_uint)
                            .wrapping_mul(8 as libc::c_uint) as isize,
                    ),
            ) & 0xff00 as libc::c_ulonglong) << 40 as libc::c_int
            | (load64(
                b
                    .offset(
                        (4 as libc::c_uint)
                            .wrapping_sub(i)
                            .wrapping_sub(1 as libc::c_uint)
                            .wrapping_mul(8 as libc::c_uint) as isize,
                    ),
            ) & 0xff as libc::c_ulonglong) << 56 as libc::c_int
    } else {
        _OSSwapInt64(
            load64(
                b
                    .offset(
                        (4 as libc::c_uint)
                            .wrapping_sub(i)
                            .wrapping_sub(1 as libc::c_uint)
                            .wrapping_mul(8 as libc::c_uint) as isize,
                    ),
            ),
        )
    };
    let mut x_2: uint64_t = u_2;
    let mut os_2: *mut uint64_t = f;
    *os_2.offset(i as isize) = x_2;
    i = (i as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut is_zero: uint64_t = is_qelem_zero(f);
    let mut acc: uint64_t = 0 as libc::c_ulonglong;
    let mut i_0: uint32_t = 0 as libc::c_uint;
    let mut beq: uint64_t = FStar_UInt64_eq_mask(
        *f.offset(i_0 as isize),
        n[i_0 as usize],
    );
    let mut blt: uint64_t = !FStar_UInt64_gte_mask(
        *f.offset(i_0 as isize),
        n[i_0 as usize],
    );
    acc = beq & acc | !beq & blt;
    i_0 = (i_0 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut beq_0: uint64_t = FStar_UInt64_eq_mask(
        *f.offset(i_0 as isize),
        n[i_0 as usize],
    );
    let mut blt_0: uint64_t = !FStar_UInt64_gte_mask(
        *f.offset(i_0 as isize),
        n[i_0 as usize],
    );
    acc = beq_0 & acc | !beq_0 & blt_0;
    i_0 = (i_0 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut beq_1: uint64_t = FStar_UInt64_eq_mask(
        *f.offset(i_0 as isize),
        n[i_0 as usize],
    );
    let mut blt_1: uint64_t = !FStar_UInt64_gte_mask(
        *f.offset(i_0 as isize),
        n[i_0 as usize],
    );
    acc = beq_1 & acc | !beq_1 & blt_1;
    i_0 = (i_0 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut beq_2: uint64_t = FStar_UInt64_eq_mask(
        *f.offset(i_0 as isize),
        n[i_0 as usize],
    );
    let mut blt_2: uint64_t = !FStar_UInt64_gte_mask(
        *f.offset(i_0 as isize),
        n[i_0 as usize],
    );
    acc = beq_2 & acc | !beq_2 & blt_2;
    i_0 = (i_0 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut is_lt_q: uint64_t = acc;
    return !is_zero & is_lt_q;
}
#[inline]
unsafe extern "C" fn load_qelem_vartime(
    mut f: *mut uint64_t,
    mut b: *mut uint8_t,
) -> bool {
    let mut i: uint32_t = 0 as libc::c_uint;
    let mut u: uint64_t = if 0 != 0 {
        (load64(
            b
                .offset(
                    (4 as libc::c_uint)
                        .wrapping_sub(i)
                        .wrapping_sub(1 as libc::c_uint)
                        .wrapping_mul(8 as libc::c_uint) as isize,
                ),
        ) & 0xff00000000000000 as libc::c_ulonglong) >> 56 as libc::c_int
            | (load64(
                b
                    .offset(
                        (4 as libc::c_uint)
                            .wrapping_sub(i)
                            .wrapping_sub(1 as libc::c_uint)
                            .wrapping_mul(8 as libc::c_uint) as isize,
                    ),
            ) & 0xff000000000000 as libc::c_ulonglong) >> 40 as libc::c_int
            | (load64(
                b
                    .offset(
                        (4 as libc::c_uint)
                            .wrapping_sub(i)
                            .wrapping_sub(1 as libc::c_uint)
                            .wrapping_mul(8 as libc::c_uint) as isize,
                    ),
            ) & 0xff0000000000 as libc::c_ulonglong) >> 24 as libc::c_int
            | (load64(
                b
                    .offset(
                        (4 as libc::c_uint)
                            .wrapping_sub(i)
                            .wrapping_sub(1 as libc::c_uint)
                            .wrapping_mul(8 as libc::c_uint) as isize,
                    ),
            ) & 0xff00000000 as libc::c_ulonglong) >> 8 as libc::c_int
            | (load64(
                b
                    .offset(
                        (4 as libc::c_uint)
                            .wrapping_sub(i)
                            .wrapping_sub(1 as libc::c_uint)
                            .wrapping_mul(8 as libc::c_uint) as isize,
                    ),
            ) & 0xff000000 as libc::c_ulonglong) << 8 as libc::c_int
            | (load64(
                b
                    .offset(
                        (4 as libc::c_uint)
                            .wrapping_sub(i)
                            .wrapping_sub(1 as libc::c_uint)
                            .wrapping_mul(8 as libc::c_uint) as isize,
                    ),
            ) & 0xff0000 as libc::c_ulonglong) << 24 as libc::c_int
            | (load64(
                b
                    .offset(
                        (4 as libc::c_uint)
                            .wrapping_sub(i)
                            .wrapping_sub(1 as libc::c_uint)
                            .wrapping_mul(8 as libc::c_uint) as isize,
                    ),
            ) & 0xff00 as libc::c_ulonglong) << 40 as libc::c_int
            | (load64(
                b
                    .offset(
                        (4 as libc::c_uint)
                            .wrapping_sub(i)
                            .wrapping_sub(1 as libc::c_uint)
                            .wrapping_mul(8 as libc::c_uint) as isize,
                    ),
            ) & 0xff as libc::c_ulonglong) << 56 as libc::c_int
    } else {
        _OSSwapInt64(
            load64(
                b
                    .offset(
                        (4 as libc::c_uint)
                            .wrapping_sub(i)
                            .wrapping_sub(1 as libc::c_uint)
                            .wrapping_mul(8 as libc::c_uint) as isize,
                    ),
            ),
        )
    };
    let mut x: uint64_t = u;
    let mut os: *mut uint64_t = f;
    *os.offset(i as isize) = x;
    i = (i as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut u_0: uint64_t = if 0 != 0 {
        (load64(
            b
                .offset(
                    (4 as libc::c_uint)
                        .wrapping_sub(i)
                        .wrapping_sub(1 as libc::c_uint)
                        .wrapping_mul(8 as libc::c_uint) as isize,
                ),
        ) & 0xff00000000000000 as libc::c_ulonglong) >> 56 as libc::c_int
            | (load64(
                b
                    .offset(
                        (4 as libc::c_uint)
                            .wrapping_sub(i)
                            .wrapping_sub(1 as libc::c_uint)
                            .wrapping_mul(8 as libc::c_uint) as isize,
                    ),
            ) & 0xff000000000000 as libc::c_ulonglong) >> 40 as libc::c_int
            | (load64(
                b
                    .offset(
                        (4 as libc::c_uint)
                            .wrapping_sub(i)
                            .wrapping_sub(1 as libc::c_uint)
                            .wrapping_mul(8 as libc::c_uint) as isize,
                    ),
            ) & 0xff0000000000 as libc::c_ulonglong) >> 24 as libc::c_int
            | (load64(
                b
                    .offset(
                        (4 as libc::c_uint)
                            .wrapping_sub(i)
                            .wrapping_sub(1 as libc::c_uint)
                            .wrapping_mul(8 as libc::c_uint) as isize,
                    ),
            ) & 0xff00000000 as libc::c_ulonglong) >> 8 as libc::c_int
            | (load64(
                b
                    .offset(
                        (4 as libc::c_uint)
                            .wrapping_sub(i)
                            .wrapping_sub(1 as libc::c_uint)
                            .wrapping_mul(8 as libc::c_uint) as isize,
                    ),
            ) & 0xff000000 as libc::c_ulonglong) << 8 as libc::c_int
            | (load64(
                b
                    .offset(
                        (4 as libc::c_uint)
                            .wrapping_sub(i)
                            .wrapping_sub(1 as libc::c_uint)
                            .wrapping_mul(8 as libc::c_uint) as isize,
                    ),
            ) & 0xff0000 as libc::c_ulonglong) << 24 as libc::c_int
            | (load64(
                b
                    .offset(
                        (4 as libc::c_uint)
                            .wrapping_sub(i)
                            .wrapping_sub(1 as libc::c_uint)
                            .wrapping_mul(8 as libc::c_uint) as isize,
                    ),
            ) & 0xff00 as libc::c_ulonglong) << 40 as libc::c_int
            | (load64(
                b
                    .offset(
                        (4 as libc::c_uint)
                            .wrapping_sub(i)
                            .wrapping_sub(1 as libc::c_uint)
                            .wrapping_mul(8 as libc::c_uint) as isize,
                    ),
            ) & 0xff as libc::c_ulonglong) << 56 as libc::c_int
    } else {
        _OSSwapInt64(
            load64(
                b
                    .offset(
                        (4 as libc::c_uint)
                            .wrapping_sub(i)
                            .wrapping_sub(1 as libc::c_uint)
                            .wrapping_mul(8 as libc::c_uint) as isize,
                    ),
            ),
        )
    };
    let mut x_0: uint64_t = u_0;
    let mut os_0: *mut uint64_t = f;
    *os_0.offset(i as isize) = x_0;
    i = (i as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut u_1: uint64_t = if 0 != 0 {
        (load64(
            b
                .offset(
                    (4 as libc::c_uint)
                        .wrapping_sub(i)
                        .wrapping_sub(1 as libc::c_uint)
                        .wrapping_mul(8 as libc::c_uint) as isize,
                ),
        ) & 0xff00000000000000 as libc::c_ulonglong) >> 56 as libc::c_int
            | (load64(
                b
                    .offset(
                        (4 as libc::c_uint)
                            .wrapping_sub(i)
                            .wrapping_sub(1 as libc::c_uint)
                            .wrapping_mul(8 as libc::c_uint) as isize,
                    ),
            ) & 0xff000000000000 as libc::c_ulonglong) >> 40 as libc::c_int
            | (load64(
                b
                    .offset(
                        (4 as libc::c_uint)
                            .wrapping_sub(i)
                            .wrapping_sub(1 as libc::c_uint)
                            .wrapping_mul(8 as libc::c_uint) as isize,
                    ),
            ) & 0xff0000000000 as libc::c_ulonglong) >> 24 as libc::c_int
            | (load64(
                b
                    .offset(
                        (4 as libc::c_uint)
                            .wrapping_sub(i)
                            .wrapping_sub(1 as libc::c_uint)
                            .wrapping_mul(8 as libc::c_uint) as isize,
                    ),
            ) & 0xff00000000 as libc::c_ulonglong) >> 8 as libc::c_int
            | (load64(
                b
                    .offset(
                        (4 as libc::c_uint)
                            .wrapping_sub(i)
                            .wrapping_sub(1 as libc::c_uint)
                            .wrapping_mul(8 as libc::c_uint) as isize,
                    ),
            ) & 0xff000000 as libc::c_ulonglong) << 8 as libc::c_int
            | (load64(
                b
                    .offset(
                        (4 as libc::c_uint)
                            .wrapping_sub(i)
                            .wrapping_sub(1 as libc::c_uint)
                            .wrapping_mul(8 as libc::c_uint) as isize,
                    ),
            ) & 0xff0000 as libc::c_ulonglong) << 24 as libc::c_int
            | (load64(
                b
                    .offset(
                        (4 as libc::c_uint)
                            .wrapping_sub(i)
                            .wrapping_sub(1 as libc::c_uint)
                            .wrapping_mul(8 as libc::c_uint) as isize,
                    ),
            ) & 0xff00 as libc::c_ulonglong) << 40 as libc::c_int
            | (load64(
                b
                    .offset(
                        (4 as libc::c_uint)
                            .wrapping_sub(i)
                            .wrapping_sub(1 as libc::c_uint)
                            .wrapping_mul(8 as libc::c_uint) as isize,
                    ),
            ) & 0xff as libc::c_ulonglong) << 56 as libc::c_int
    } else {
        _OSSwapInt64(
            load64(
                b
                    .offset(
                        (4 as libc::c_uint)
                            .wrapping_sub(i)
                            .wrapping_sub(1 as libc::c_uint)
                            .wrapping_mul(8 as libc::c_uint) as isize,
                    ),
            ),
        )
    };
    let mut x_1: uint64_t = u_1;
    let mut os_1: *mut uint64_t = f;
    *os_1.offset(i as isize) = x_1;
    i = (i as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut u_2: uint64_t = if 0 != 0 {
        (load64(
            b
                .offset(
                    (4 as libc::c_uint)
                        .wrapping_sub(i)
                        .wrapping_sub(1 as libc::c_uint)
                        .wrapping_mul(8 as libc::c_uint) as isize,
                ),
        ) & 0xff00000000000000 as libc::c_ulonglong) >> 56 as libc::c_int
            | (load64(
                b
                    .offset(
                        (4 as libc::c_uint)
                            .wrapping_sub(i)
                            .wrapping_sub(1 as libc::c_uint)
                            .wrapping_mul(8 as libc::c_uint) as isize,
                    ),
            ) & 0xff000000000000 as libc::c_ulonglong) >> 40 as libc::c_int
            | (load64(
                b
                    .offset(
                        (4 as libc::c_uint)
                            .wrapping_sub(i)
                            .wrapping_sub(1 as libc::c_uint)
                            .wrapping_mul(8 as libc::c_uint) as isize,
                    ),
            ) & 0xff0000000000 as libc::c_ulonglong) >> 24 as libc::c_int
            | (load64(
                b
                    .offset(
                        (4 as libc::c_uint)
                            .wrapping_sub(i)
                            .wrapping_sub(1 as libc::c_uint)
                            .wrapping_mul(8 as libc::c_uint) as isize,
                    ),
            ) & 0xff00000000 as libc::c_ulonglong) >> 8 as libc::c_int
            | (load64(
                b
                    .offset(
                        (4 as libc::c_uint)
                            .wrapping_sub(i)
                            .wrapping_sub(1 as libc::c_uint)
                            .wrapping_mul(8 as libc::c_uint) as isize,
                    ),
            ) & 0xff000000 as libc::c_ulonglong) << 8 as libc::c_int
            | (load64(
                b
                    .offset(
                        (4 as libc::c_uint)
                            .wrapping_sub(i)
                            .wrapping_sub(1 as libc::c_uint)
                            .wrapping_mul(8 as libc::c_uint) as isize,
                    ),
            ) & 0xff0000 as libc::c_ulonglong) << 24 as libc::c_int
            | (load64(
                b
                    .offset(
                        (4 as libc::c_uint)
                            .wrapping_sub(i)
                            .wrapping_sub(1 as libc::c_uint)
                            .wrapping_mul(8 as libc::c_uint) as isize,
                    ),
            ) & 0xff00 as libc::c_ulonglong) << 40 as libc::c_int
            | (load64(
                b
                    .offset(
                        (4 as libc::c_uint)
                            .wrapping_sub(i)
                            .wrapping_sub(1 as libc::c_uint)
                            .wrapping_mul(8 as libc::c_uint) as isize,
                    ),
            ) & 0xff as libc::c_ulonglong) << 56 as libc::c_int
    } else {
        _OSSwapInt64(
            load64(
                b
                    .offset(
                        (4 as libc::c_uint)
                            .wrapping_sub(i)
                            .wrapping_sub(1 as libc::c_uint)
                            .wrapping_mul(8 as libc::c_uint) as isize,
                    ),
            ),
        )
    };
    let mut x_2: uint64_t = u_2;
    let mut os_2: *mut uint64_t = f;
    *os_2.offset(i as isize) = x_2;
    i = (i as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut is_zero: bool = is_qelem_zero_vartime(f);
    let mut a0: uint64_t = *f.offset(0 as libc::c_uint as isize);
    let mut a1: uint64_t = *f.offset(1 as libc::c_uint as isize);
    let mut a2: uint64_t = *f.offset(2 as libc::c_uint as isize);
    let mut a3: uint64_t = *f.offset(3 as libc::c_uint as isize);
    let mut is_lt_q_b: bool = false;
    if a3 < 0xffffffffffffffff as libc::c_ulonglong
        || a2 < 0xfffffffffffffffe as libc::c_ulonglong
    {
        is_lt_q_b = 1 as libc::c_int != 0;
    } else if a2 > 0xfffffffffffffffe as libc::c_ulonglong {
        is_lt_q_b = 0 as libc::c_int != 0;
    } else if a1 < 0xbaaedce6af48a03b as libc::c_ulonglong {
        is_lt_q_b = 1 as libc::c_int != 0;
    } else if a1 > 0xbaaedce6af48a03b as libc::c_ulonglong {
        is_lt_q_b = 0 as libc::c_int != 0;
    } else {
        is_lt_q_b = a0 < 0xbfd25e8cd0364141 as libc::c_ulonglong;
    }
    return !is_zero && is_lt_q_b as libc::c_int != 0;
}
#[inline]
unsafe extern "C" fn modq_short(mut out: *mut uint64_t, mut a: *mut uint64_t) {
    let mut tmp: [uint64_t; 4] = [0 as libc::c_uint as uint64_t, 0, 0, 0];
    tmp[0 as libc::c_uint as usize] = 0x402da1732fc9bebf as libc::c_ulonglong;
    tmp[1 as libc::c_uint as usize] = 0x4551231950b75fc4 as libc::c_ulonglong;
    tmp[2 as libc::c_uint as usize] = 0x1 as libc::c_ulonglong;
    tmp[3 as libc::c_uint as usize] = 0 as libc::c_ulonglong;
    let mut c: uint64_t = add4(a, tmp.as_mut_ptr(), out);
    let mut mask: uint64_t = (0 as libc::c_ulonglong).wrapping_sub(c);
    let mut i: uint32_t = 0 as libc::c_uint;
    let mut x: uint64_t = mask & *out.offset(i as isize) | !mask & *a.offset(i as isize);
    let mut os: *mut uint64_t = out;
    *os.offset(i as isize) = x;
    i = (i as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut x_0: uint64_t = mask & *out.offset(i as isize)
        | !mask & *a.offset(i as isize);
    let mut os_0: *mut uint64_t = out;
    *os_0.offset(i as isize) = x_0;
    i = (i as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut x_1: uint64_t = mask & *out.offset(i as isize)
        | !mask & *a.offset(i as isize);
    let mut os_1: *mut uint64_t = out;
    *os_1.offset(i as isize) = x_1;
    i = (i as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut x_2: uint64_t = mask & *out.offset(i as isize)
        | !mask & *a.offset(i as isize);
    let mut os_2: *mut uint64_t = out;
    *os_2.offset(i as isize) = x_2;
    i = (i as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
}
#[inline]
unsafe extern "C" fn load_qelem_modq(mut f: *mut uint64_t, mut b: *mut uint8_t) {
    let mut tmp: [uint64_t; 4] = [0 as libc::c_uint as uint64_t, 0, 0, 0];
    let mut i: uint32_t = 0 as libc::c_uint;
    let mut u: uint64_t = if 0 != 0 {
        (load64(
            b
                .offset(
                    (4 as libc::c_uint)
                        .wrapping_sub(i)
                        .wrapping_sub(1 as libc::c_uint)
                        .wrapping_mul(8 as libc::c_uint) as isize,
                ),
        ) & 0xff00000000000000 as libc::c_ulonglong) >> 56 as libc::c_int
            | (load64(
                b
                    .offset(
                        (4 as libc::c_uint)
                            .wrapping_sub(i)
                            .wrapping_sub(1 as libc::c_uint)
                            .wrapping_mul(8 as libc::c_uint) as isize,
                    ),
            ) & 0xff000000000000 as libc::c_ulonglong) >> 40 as libc::c_int
            | (load64(
                b
                    .offset(
                        (4 as libc::c_uint)
                            .wrapping_sub(i)
                            .wrapping_sub(1 as libc::c_uint)
                            .wrapping_mul(8 as libc::c_uint) as isize,
                    ),
            ) & 0xff0000000000 as libc::c_ulonglong) >> 24 as libc::c_int
            | (load64(
                b
                    .offset(
                        (4 as libc::c_uint)
                            .wrapping_sub(i)
                            .wrapping_sub(1 as libc::c_uint)
                            .wrapping_mul(8 as libc::c_uint) as isize,
                    ),
            ) & 0xff00000000 as libc::c_ulonglong) >> 8 as libc::c_int
            | (load64(
                b
                    .offset(
                        (4 as libc::c_uint)
                            .wrapping_sub(i)
                            .wrapping_sub(1 as libc::c_uint)
                            .wrapping_mul(8 as libc::c_uint) as isize,
                    ),
            ) & 0xff000000 as libc::c_ulonglong) << 8 as libc::c_int
            | (load64(
                b
                    .offset(
                        (4 as libc::c_uint)
                            .wrapping_sub(i)
                            .wrapping_sub(1 as libc::c_uint)
                            .wrapping_mul(8 as libc::c_uint) as isize,
                    ),
            ) & 0xff0000 as libc::c_ulonglong) << 24 as libc::c_int
            | (load64(
                b
                    .offset(
                        (4 as libc::c_uint)
                            .wrapping_sub(i)
                            .wrapping_sub(1 as libc::c_uint)
                            .wrapping_mul(8 as libc::c_uint) as isize,
                    ),
            ) & 0xff00 as libc::c_ulonglong) << 40 as libc::c_int
            | (load64(
                b
                    .offset(
                        (4 as libc::c_uint)
                            .wrapping_sub(i)
                            .wrapping_sub(1 as libc::c_uint)
                            .wrapping_mul(8 as libc::c_uint) as isize,
                    ),
            ) & 0xff as libc::c_ulonglong) << 56 as libc::c_int
    } else {
        _OSSwapInt64(
            load64(
                b
                    .offset(
                        (4 as libc::c_uint)
                            .wrapping_sub(i)
                            .wrapping_sub(1 as libc::c_uint)
                            .wrapping_mul(8 as libc::c_uint) as isize,
                    ),
            ),
        )
    };
    let mut x: uint64_t = u;
    let mut os: *mut uint64_t = f;
    *os.offset(i as isize) = x;
    i = (i as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut u_0: uint64_t = if 0 != 0 {
        (load64(
            b
                .offset(
                    (4 as libc::c_uint)
                        .wrapping_sub(i)
                        .wrapping_sub(1 as libc::c_uint)
                        .wrapping_mul(8 as libc::c_uint) as isize,
                ),
        ) & 0xff00000000000000 as libc::c_ulonglong) >> 56 as libc::c_int
            | (load64(
                b
                    .offset(
                        (4 as libc::c_uint)
                            .wrapping_sub(i)
                            .wrapping_sub(1 as libc::c_uint)
                            .wrapping_mul(8 as libc::c_uint) as isize,
                    ),
            ) & 0xff000000000000 as libc::c_ulonglong) >> 40 as libc::c_int
            | (load64(
                b
                    .offset(
                        (4 as libc::c_uint)
                            .wrapping_sub(i)
                            .wrapping_sub(1 as libc::c_uint)
                            .wrapping_mul(8 as libc::c_uint) as isize,
                    ),
            ) & 0xff0000000000 as libc::c_ulonglong) >> 24 as libc::c_int
            | (load64(
                b
                    .offset(
                        (4 as libc::c_uint)
                            .wrapping_sub(i)
                            .wrapping_sub(1 as libc::c_uint)
                            .wrapping_mul(8 as libc::c_uint) as isize,
                    ),
            ) & 0xff00000000 as libc::c_ulonglong) >> 8 as libc::c_int
            | (load64(
                b
                    .offset(
                        (4 as libc::c_uint)
                            .wrapping_sub(i)
                            .wrapping_sub(1 as libc::c_uint)
                            .wrapping_mul(8 as libc::c_uint) as isize,
                    ),
            ) & 0xff000000 as libc::c_ulonglong) << 8 as libc::c_int
            | (load64(
                b
                    .offset(
                        (4 as libc::c_uint)
                            .wrapping_sub(i)
                            .wrapping_sub(1 as libc::c_uint)
                            .wrapping_mul(8 as libc::c_uint) as isize,
                    ),
            ) & 0xff0000 as libc::c_ulonglong) << 24 as libc::c_int
            | (load64(
                b
                    .offset(
                        (4 as libc::c_uint)
                            .wrapping_sub(i)
                            .wrapping_sub(1 as libc::c_uint)
                            .wrapping_mul(8 as libc::c_uint) as isize,
                    ),
            ) & 0xff00 as libc::c_ulonglong) << 40 as libc::c_int
            | (load64(
                b
                    .offset(
                        (4 as libc::c_uint)
                            .wrapping_sub(i)
                            .wrapping_sub(1 as libc::c_uint)
                            .wrapping_mul(8 as libc::c_uint) as isize,
                    ),
            ) & 0xff as libc::c_ulonglong) << 56 as libc::c_int
    } else {
        _OSSwapInt64(
            load64(
                b
                    .offset(
                        (4 as libc::c_uint)
                            .wrapping_sub(i)
                            .wrapping_sub(1 as libc::c_uint)
                            .wrapping_mul(8 as libc::c_uint) as isize,
                    ),
            ),
        )
    };
    let mut x_0: uint64_t = u_0;
    let mut os_0: *mut uint64_t = f;
    *os_0.offset(i as isize) = x_0;
    i = (i as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut u_1: uint64_t = if 0 != 0 {
        (load64(
            b
                .offset(
                    (4 as libc::c_uint)
                        .wrapping_sub(i)
                        .wrapping_sub(1 as libc::c_uint)
                        .wrapping_mul(8 as libc::c_uint) as isize,
                ),
        ) & 0xff00000000000000 as libc::c_ulonglong) >> 56 as libc::c_int
            | (load64(
                b
                    .offset(
                        (4 as libc::c_uint)
                            .wrapping_sub(i)
                            .wrapping_sub(1 as libc::c_uint)
                            .wrapping_mul(8 as libc::c_uint) as isize,
                    ),
            ) & 0xff000000000000 as libc::c_ulonglong) >> 40 as libc::c_int
            | (load64(
                b
                    .offset(
                        (4 as libc::c_uint)
                            .wrapping_sub(i)
                            .wrapping_sub(1 as libc::c_uint)
                            .wrapping_mul(8 as libc::c_uint) as isize,
                    ),
            ) & 0xff0000000000 as libc::c_ulonglong) >> 24 as libc::c_int
            | (load64(
                b
                    .offset(
                        (4 as libc::c_uint)
                            .wrapping_sub(i)
                            .wrapping_sub(1 as libc::c_uint)
                            .wrapping_mul(8 as libc::c_uint) as isize,
                    ),
            ) & 0xff00000000 as libc::c_ulonglong) >> 8 as libc::c_int
            | (load64(
                b
                    .offset(
                        (4 as libc::c_uint)
                            .wrapping_sub(i)
                            .wrapping_sub(1 as libc::c_uint)
                            .wrapping_mul(8 as libc::c_uint) as isize,
                    ),
            ) & 0xff000000 as libc::c_ulonglong) << 8 as libc::c_int
            | (load64(
                b
                    .offset(
                        (4 as libc::c_uint)
                            .wrapping_sub(i)
                            .wrapping_sub(1 as libc::c_uint)
                            .wrapping_mul(8 as libc::c_uint) as isize,
                    ),
            ) & 0xff0000 as libc::c_ulonglong) << 24 as libc::c_int
            | (load64(
                b
                    .offset(
                        (4 as libc::c_uint)
                            .wrapping_sub(i)
                            .wrapping_sub(1 as libc::c_uint)
                            .wrapping_mul(8 as libc::c_uint) as isize,
                    ),
            ) & 0xff00 as libc::c_ulonglong) << 40 as libc::c_int
            | (load64(
                b
                    .offset(
                        (4 as libc::c_uint)
                            .wrapping_sub(i)
                            .wrapping_sub(1 as libc::c_uint)
                            .wrapping_mul(8 as libc::c_uint) as isize,
                    ),
            ) & 0xff as libc::c_ulonglong) << 56 as libc::c_int
    } else {
        _OSSwapInt64(
            load64(
                b
                    .offset(
                        (4 as libc::c_uint)
                            .wrapping_sub(i)
                            .wrapping_sub(1 as libc::c_uint)
                            .wrapping_mul(8 as libc::c_uint) as isize,
                    ),
            ),
        )
    };
    let mut x_1: uint64_t = u_1;
    let mut os_1: *mut uint64_t = f;
    *os_1.offset(i as isize) = x_1;
    i = (i as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut u_2: uint64_t = if 0 != 0 {
        (load64(
            b
                .offset(
                    (4 as libc::c_uint)
                        .wrapping_sub(i)
                        .wrapping_sub(1 as libc::c_uint)
                        .wrapping_mul(8 as libc::c_uint) as isize,
                ),
        ) & 0xff00000000000000 as libc::c_ulonglong) >> 56 as libc::c_int
            | (load64(
                b
                    .offset(
                        (4 as libc::c_uint)
                            .wrapping_sub(i)
                            .wrapping_sub(1 as libc::c_uint)
                            .wrapping_mul(8 as libc::c_uint) as isize,
                    ),
            ) & 0xff000000000000 as libc::c_ulonglong) >> 40 as libc::c_int
            | (load64(
                b
                    .offset(
                        (4 as libc::c_uint)
                            .wrapping_sub(i)
                            .wrapping_sub(1 as libc::c_uint)
                            .wrapping_mul(8 as libc::c_uint) as isize,
                    ),
            ) & 0xff0000000000 as libc::c_ulonglong) >> 24 as libc::c_int
            | (load64(
                b
                    .offset(
                        (4 as libc::c_uint)
                            .wrapping_sub(i)
                            .wrapping_sub(1 as libc::c_uint)
                            .wrapping_mul(8 as libc::c_uint) as isize,
                    ),
            ) & 0xff00000000 as libc::c_ulonglong) >> 8 as libc::c_int
            | (load64(
                b
                    .offset(
                        (4 as libc::c_uint)
                            .wrapping_sub(i)
                            .wrapping_sub(1 as libc::c_uint)
                            .wrapping_mul(8 as libc::c_uint) as isize,
                    ),
            ) & 0xff000000 as libc::c_ulonglong) << 8 as libc::c_int
            | (load64(
                b
                    .offset(
                        (4 as libc::c_uint)
                            .wrapping_sub(i)
                            .wrapping_sub(1 as libc::c_uint)
                            .wrapping_mul(8 as libc::c_uint) as isize,
                    ),
            ) & 0xff0000 as libc::c_ulonglong) << 24 as libc::c_int
            | (load64(
                b
                    .offset(
                        (4 as libc::c_uint)
                            .wrapping_sub(i)
                            .wrapping_sub(1 as libc::c_uint)
                            .wrapping_mul(8 as libc::c_uint) as isize,
                    ),
            ) & 0xff00 as libc::c_ulonglong) << 40 as libc::c_int
            | (load64(
                b
                    .offset(
                        (4 as libc::c_uint)
                            .wrapping_sub(i)
                            .wrapping_sub(1 as libc::c_uint)
                            .wrapping_mul(8 as libc::c_uint) as isize,
                    ),
            ) & 0xff as libc::c_ulonglong) << 56 as libc::c_int
    } else {
        _OSSwapInt64(
            load64(
                b
                    .offset(
                        (4 as libc::c_uint)
                            .wrapping_sub(i)
                            .wrapping_sub(1 as libc::c_uint)
                            .wrapping_mul(8 as libc::c_uint) as isize,
                    ),
            ),
        )
    };
    let mut x_2: uint64_t = u_2;
    let mut os_2: *mut uint64_t = f;
    *os_2.offset(i as isize) = x_2;
    i = (i as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    memcpy(
        tmp.as_mut_ptr() as *mut libc::c_void,
        f as *const libc::c_void,
        (4 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    modq_short(f, tmp.as_mut_ptr());
}
#[inline]
unsafe extern "C" fn store_qelem(mut b: *mut uint8_t, mut f: *mut uint64_t) {
    let mut tmp: [uint8_t; 32] = [
        0 as libc::c_uint as uint8_t,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
    ];
    let mut i: uint32_t = 0 as libc::c_uint;
    store64(
        b.offset(i.wrapping_mul(8 as libc::c_uint) as isize),
        if 0 != 0 {
            (*f
                .offset(
                    (4 as libc::c_uint).wrapping_sub(i).wrapping_sub(1 as libc::c_uint)
                        as isize,
                ) & 0xff00000000000000 as libc::c_ulonglong) >> 56 as libc::c_int
                | (*f
                    .offset(
                        (4 as libc::c_uint)
                            .wrapping_sub(i)
                            .wrapping_sub(1 as libc::c_uint) as isize,
                    ) & 0xff000000000000 as libc::c_ulonglong) >> 40 as libc::c_int
                | (*f
                    .offset(
                        (4 as libc::c_uint)
                            .wrapping_sub(i)
                            .wrapping_sub(1 as libc::c_uint) as isize,
                    ) & 0xff0000000000 as libc::c_ulonglong) >> 24 as libc::c_int
                | (*f
                    .offset(
                        (4 as libc::c_uint)
                            .wrapping_sub(i)
                            .wrapping_sub(1 as libc::c_uint) as isize,
                    ) & 0xff00000000 as libc::c_ulonglong) >> 8 as libc::c_int
                | (*f
                    .offset(
                        (4 as libc::c_uint)
                            .wrapping_sub(i)
                            .wrapping_sub(1 as libc::c_uint) as isize,
                    ) & 0xff000000 as libc::c_ulonglong) << 8 as libc::c_int
                | (*f
                    .offset(
                        (4 as libc::c_uint)
                            .wrapping_sub(i)
                            .wrapping_sub(1 as libc::c_uint) as isize,
                    ) & 0xff0000 as libc::c_ulonglong) << 24 as libc::c_int
                | (*f
                    .offset(
                        (4 as libc::c_uint)
                            .wrapping_sub(i)
                            .wrapping_sub(1 as libc::c_uint) as isize,
                    ) & 0xff00 as libc::c_ulonglong) << 40 as libc::c_int
                | (*f
                    .offset(
                        (4 as libc::c_uint)
                            .wrapping_sub(i)
                            .wrapping_sub(1 as libc::c_uint) as isize,
                    ) & 0xff as libc::c_ulonglong) << 56 as libc::c_int
        } else {
            _OSSwapInt64(
                *f
                    .offset(
                        (4 as libc::c_uint)
                            .wrapping_sub(i)
                            .wrapping_sub(1 as libc::c_uint) as isize,
                    ),
            )
        },
    );
    i = (i as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    store64(
        b.offset(i.wrapping_mul(8 as libc::c_uint) as isize),
        if 0 != 0 {
            (*f
                .offset(
                    (4 as libc::c_uint).wrapping_sub(i).wrapping_sub(1 as libc::c_uint)
                        as isize,
                ) & 0xff00000000000000 as libc::c_ulonglong) >> 56 as libc::c_int
                | (*f
                    .offset(
                        (4 as libc::c_uint)
                            .wrapping_sub(i)
                            .wrapping_sub(1 as libc::c_uint) as isize,
                    ) & 0xff000000000000 as libc::c_ulonglong) >> 40 as libc::c_int
                | (*f
                    .offset(
                        (4 as libc::c_uint)
                            .wrapping_sub(i)
                            .wrapping_sub(1 as libc::c_uint) as isize,
                    ) & 0xff0000000000 as libc::c_ulonglong) >> 24 as libc::c_int
                | (*f
                    .offset(
                        (4 as libc::c_uint)
                            .wrapping_sub(i)
                            .wrapping_sub(1 as libc::c_uint) as isize,
                    ) & 0xff00000000 as libc::c_ulonglong) >> 8 as libc::c_int
                | (*f
                    .offset(
                        (4 as libc::c_uint)
                            .wrapping_sub(i)
                            .wrapping_sub(1 as libc::c_uint) as isize,
                    ) & 0xff000000 as libc::c_ulonglong) << 8 as libc::c_int
                | (*f
                    .offset(
                        (4 as libc::c_uint)
                            .wrapping_sub(i)
                            .wrapping_sub(1 as libc::c_uint) as isize,
                    ) & 0xff0000 as libc::c_ulonglong) << 24 as libc::c_int
                | (*f
                    .offset(
                        (4 as libc::c_uint)
                            .wrapping_sub(i)
                            .wrapping_sub(1 as libc::c_uint) as isize,
                    ) & 0xff00 as libc::c_ulonglong) << 40 as libc::c_int
                | (*f
                    .offset(
                        (4 as libc::c_uint)
                            .wrapping_sub(i)
                            .wrapping_sub(1 as libc::c_uint) as isize,
                    ) & 0xff as libc::c_ulonglong) << 56 as libc::c_int
        } else {
            _OSSwapInt64(
                *f
                    .offset(
                        (4 as libc::c_uint)
                            .wrapping_sub(i)
                            .wrapping_sub(1 as libc::c_uint) as isize,
                    ),
            )
        },
    );
    i = (i as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    store64(
        b.offset(i.wrapping_mul(8 as libc::c_uint) as isize),
        if 0 != 0 {
            (*f
                .offset(
                    (4 as libc::c_uint).wrapping_sub(i).wrapping_sub(1 as libc::c_uint)
                        as isize,
                ) & 0xff00000000000000 as libc::c_ulonglong) >> 56 as libc::c_int
                | (*f
                    .offset(
                        (4 as libc::c_uint)
                            .wrapping_sub(i)
                            .wrapping_sub(1 as libc::c_uint) as isize,
                    ) & 0xff000000000000 as libc::c_ulonglong) >> 40 as libc::c_int
                | (*f
                    .offset(
                        (4 as libc::c_uint)
                            .wrapping_sub(i)
                            .wrapping_sub(1 as libc::c_uint) as isize,
                    ) & 0xff0000000000 as libc::c_ulonglong) >> 24 as libc::c_int
                | (*f
                    .offset(
                        (4 as libc::c_uint)
                            .wrapping_sub(i)
                            .wrapping_sub(1 as libc::c_uint) as isize,
                    ) & 0xff00000000 as libc::c_ulonglong) >> 8 as libc::c_int
                | (*f
                    .offset(
                        (4 as libc::c_uint)
                            .wrapping_sub(i)
                            .wrapping_sub(1 as libc::c_uint) as isize,
                    ) & 0xff000000 as libc::c_ulonglong) << 8 as libc::c_int
                | (*f
                    .offset(
                        (4 as libc::c_uint)
                            .wrapping_sub(i)
                            .wrapping_sub(1 as libc::c_uint) as isize,
                    ) & 0xff0000 as libc::c_ulonglong) << 24 as libc::c_int
                | (*f
                    .offset(
                        (4 as libc::c_uint)
                            .wrapping_sub(i)
                            .wrapping_sub(1 as libc::c_uint) as isize,
                    ) & 0xff00 as libc::c_ulonglong) << 40 as libc::c_int
                | (*f
                    .offset(
                        (4 as libc::c_uint)
                            .wrapping_sub(i)
                            .wrapping_sub(1 as libc::c_uint) as isize,
                    ) & 0xff as libc::c_ulonglong) << 56 as libc::c_int
        } else {
            _OSSwapInt64(
                *f
                    .offset(
                        (4 as libc::c_uint)
                            .wrapping_sub(i)
                            .wrapping_sub(1 as libc::c_uint) as isize,
                    ),
            )
        },
    );
    i = (i as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    store64(
        b.offset(i.wrapping_mul(8 as libc::c_uint) as isize),
        if 0 != 0 {
            (*f
                .offset(
                    (4 as libc::c_uint).wrapping_sub(i).wrapping_sub(1 as libc::c_uint)
                        as isize,
                ) & 0xff00000000000000 as libc::c_ulonglong) >> 56 as libc::c_int
                | (*f
                    .offset(
                        (4 as libc::c_uint)
                            .wrapping_sub(i)
                            .wrapping_sub(1 as libc::c_uint) as isize,
                    ) & 0xff000000000000 as libc::c_ulonglong) >> 40 as libc::c_int
                | (*f
                    .offset(
                        (4 as libc::c_uint)
                            .wrapping_sub(i)
                            .wrapping_sub(1 as libc::c_uint) as isize,
                    ) & 0xff0000000000 as libc::c_ulonglong) >> 24 as libc::c_int
                | (*f
                    .offset(
                        (4 as libc::c_uint)
                            .wrapping_sub(i)
                            .wrapping_sub(1 as libc::c_uint) as isize,
                    ) & 0xff00000000 as libc::c_ulonglong) >> 8 as libc::c_int
                | (*f
                    .offset(
                        (4 as libc::c_uint)
                            .wrapping_sub(i)
                            .wrapping_sub(1 as libc::c_uint) as isize,
                    ) & 0xff000000 as libc::c_ulonglong) << 8 as libc::c_int
                | (*f
                    .offset(
                        (4 as libc::c_uint)
                            .wrapping_sub(i)
                            .wrapping_sub(1 as libc::c_uint) as isize,
                    ) & 0xff0000 as libc::c_ulonglong) << 24 as libc::c_int
                | (*f
                    .offset(
                        (4 as libc::c_uint)
                            .wrapping_sub(i)
                            .wrapping_sub(1 as libc::c_uint) as isize,
                    ) & 0xff00 as libc::c_ulonglong) << 40 as libc::c_int
                | (*f
                    .offset(
                        (4 as libc::c_uint)
                            .wrapping_sub(i)
                            .wrapping_sub(1 as libc::c_uint) as isize,
                    ) & 0xff as libc::c_ulonglong) << 56 as libc::c_int
        } else {
            _OSSwapInt64(
                *f
                    .offset(
                        (4 as libc::c_uint)
                            .wrapping_sub(i)
                            .wrapping_sub(1 as libc::c_uint) as isize,
                    ),
            )
        },
    );
    i = (i as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
}
#[inline]
unsafe extern "C" fn qadd(
    mut out: *mut uint64_t,
    mut f1: *mut uint64_t,
    mut f2: *mut uint64_t,
) {
    let mut n: [uint64_t; 4] = [0 as libc::c_uint as uint64_t, 0, 0, 0];
    n[0 as libc::c_uint as usize] = 0xbfd25e8cd0364141 as libc::c_ulonglong;
    n[1 as libc::c_uint as usize] = 0xbaaedce6af48a03b as libc::c_ulonglong;
    n[2 as libc::c_uint as usize] = 0xfffffffffffffffe as libc::c_ulonglong;
    n[3 as libc::c_uint as usize] = 0xffffffffffffffff as libc::c_ulonglong;
    add_mod4(n.as_mut_ptr(), f1, f2, out);
}
#[inline]
unsafe extern "C" fn mul_pow2_256_minus_q_add(
    mut len: uint32_t,
    mut resLen: uint32_t,
    mut t01: *mut uint64_t,
    mut a: *mut uint64_t,
    mut e: *mut uint64_t,
    mut res: *mut uint64_t,
) -> uint64_t {
    if len.wrapping_add(2 as libc::c_uint) as size_t
        > (18446744073709551615 as libc::c_ulong)
            .wrapping_div(::core::mem::size_of::<uint64_t>() as libc::c_ulong)
    {
        printf(
            b"Maximum allocatable size exceeded, aborting before overflow at %s:%d\n\0"
                as *const u8 as *const libc::c_char,
            b"Hacl_K256_ECDSA.c\0" as *const u8 as *const libc::c_char,
            465 as libc::c_int,
        );
        exit(253 as libc::c_int);
    }
    let vla = len.wrapping_add(2 as libc::c_uint) as usize;
    let mut tmp: Vec::<uint64_t> = ::std::vec::from_elem(0, vla);
    memset(
        tmp.as_mut_ptr() as *mut libc::c_void,
        0 as libc::c_uint as libc::c_int,
        (len.wrapping_add(2 as libc::c_uint) as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    memset(
        tmp.as_mut_ptr() as *mut libc::c_void,
        0 as libc::c_uint as libc::c_int,
        (len.wrapping_add(2 as libc::c_uint) as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    let mut i0: uint32_t = 0 as libc::c_uint;
    let mut bj: uint64_t = *t01.offset(i0 as isize);
    let mut res_j: *mut uint64_t = tmp.as_mut_ptr().offset(i0 as isize);
    let mut c: uint64_t = 0 as libc::c_ulonglong;
    let mut i: uint32_t = 0 as libc::c_uint;
    while i < len.wrapping_div(4 as libc::c_uint) {
        let mut a_i: uint64_t = *a.offset((4 as libc::c_uint).wrapping_mul(i) as isize);
        let mut res_i0: *mut uint64_t = res_j
            .offset((4 as libc::c_uint).wrapping_mul(i) as isize);
        c = Hacl_Bignum_Base_mul_wide_add2_u64(a_i, bj, c, res_i0);
        let mut a_i0: uint64_t = *a
            .offset(
                (4 as libc::c_uint).wrapping_mul(i).wrapping_add(1 as libc::c_uint)
                    as isize,
            );
        let mut res_i1: *mut uint64_t = res_j
            .offset((4 as libc::c_uint).wrapping_mul(i) as isize)
            .offset(1 as libc::c_uint as isize);
        c = Hacl_Bignum_Base_mul_wide_add2_u64(a_i0, bj, c, res_i1);
        let mut a_i1: uint64_t = *a
            .offset(
                (4 as libc::c_uint).wrapping_mul(i).wrapping_add(2 as libc::c_uint)
                    as isize,
            );
        let mut res_i2: *mut uint64_t = res_j
            .offset((4 as libc::c_uint).wrapping_mul(i) as isize)
            .offset(2 as libc::c_uint as isize);
        c = Hacl_Bignum_Base_mul_wide_add2_u64(a_i1, bj, c, res_i2);
        let mut a_i2: uint64_t = *a
            .offset(
                (4 as libc::c_uint).wrapping_mul(i).wrapping_add(3 as libc::c_uint)
                    as isize,
            );
        let mut res_i: *mut uint64_t = res_j
            .offset((4 as libc::c_uint).wrapping_mul(i) as isize)
            .offset(3 as libc::c_uint as isize);
        c = Hacl_Bignum_Base_mul_wide_add2_u64(a_i2, bj, c, res_i);
        i = i.wrapping_add(1);
        i;
    }
    let mut i_0: uint32_t = len
        .wrapping_div(4 as libc::c_uint)
        .wrapping_mul(4 as libc::c_uint);
    while i_0 < len {
        let mut a_i_0: uint64_t = *a.offset(i_0 as isize);
        let mut res_i_0: *mut uint64_t = res_j.offset(i_0 as isize);
        c = Hacl_Bignum_Base_mul_wide_add2_u64(a_i_0, bj, c, res_i_0);
        i_0 = i_0.wrapping_add(1);
        i_0;
    }
    let mut r: uint64_t = c;
    *tmp.as_mut_ptr().offset(len.wrapping_add(i0) as isize) = r;
    i0 = (i0 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut bj_0: uint64_t = *t01.offset(i0 as isize);
    let mut res_j_0: *mut uint64_t = tmp.as_mut_ptr().offset(i0 as isize);
    let mut c_0: uint64_t = 0 as libc::c_ulonglong;
    let mut i_1: uint32_t = 0 as libc::c_uint;
    while i_1 < len.wrapping_div(4 as libc::c_uint) {
        let mut a_i_1: uint64_t = *a
            .offset((4 as libc::c_uint).wrapping_mul(i_1) as isize);
        let mut res_i0_0: *mut uint64_t = res_j_0
            .offset((4 as libc::c_uint).wrapping_mul(i_1) as isize);
        c_0 = Hacl_Bignum_Base_mul_wide_add2_u64(a_i_1, bj_0, c_0, res_i0_0);
        let mut a_i0_0: uint64_t = *a
            .offset(
                (4 as libc::c_uint).wrapping_mul(i_1).wrapping_add(1 as libc::c_uint)
                    as isize,
            );
        let mut res_i1_0: *mut uint64_t = res_j_0
            .offset((4 as libc::c_uint).wrapping_mul(i_1) as isize)
            .offset(1 as libc::c_uint as isize);
        c_0 = Hacl_Bignum_Base_mul_wide_add2_u64(a_i0_0, bj_0, c_0, res_i1_0);
        let mut a_i1_0: uint64_t = *a
            .offset(
                (4 as libc::c_uint).wrapping_mul(i_1).wrapping_add(2 as libc::c_uint)
                    as isize,
            );
        let mut res_i2_0: *mut uint64_t = res_j_0
            .offset((4 as libc::c_uint).wrapping_mul(i_1) as isize)
            .offset(2 as libc::c_uint as isize);
        c_0 = Hacl_Bignum_Base_mul_wide_add2_u64(a_i1_0, bj_0, c_0, res_i2_0);
        let mut a_i2_0: uint64_t = *a
            .offset(
                (4 as libc::c_uint).wrapping_mul(i_1).wrapping_add(3 as libc::c_uint)
                    as isize,
            );
        let mut res_i_1: *mut uint64_t = res_j_0
            .offset((4 as libc::c_uint).wrapping_mul(i_1) as isize)
            .offset(3 as libc::c_uint as isize);
        c_0 = Hacl_Bignum_Base_mul_wide_add2_u64(a_i2_0, bj_0, c_0, res_i_1);
        i_1 = i_1.wrapping_add(1);
        i_1;
    }
    let mut i_2: uint32_t = len
        .wrapping_div(4 as libc::c_uint)
        .wrapping_mul(4 as libc::c_uint);
    while i_2 < len {
        let mut a_i_2: uint64_t = *a.offset(i_2 as isize);
        let mut res_i_2: *mut uint64_t = res_j_0.offset(i_2 as isize);
        c_0 = Hacl_Bignum_Base_mul_wide_add2_u64(a_i_2, bj_0, c_0, res_i_2);
        i_2 = i_2.wrapping_add(1);
        i_2;
    }
    let mut r_0: uint64_t = c_0;
    *tmp.as_mut_ptr().offset(len.wrapping_add(i0) as isize) = r_0;
    i0 = (i0 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    memcpy(
        res.offset(2 as libc::c_uint as isize) as *mut libc::c_void,
        a as *const libc::c_void,
        (len as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    bn_add_sa(resLen, len.wrapping_add(2 as libc::c_uint), tmp.as_mut_ptr(), res);
    let mut c_1: uint64_t = bn_add_sa(resLen, 4 as libc::c_uint, e, res);
    return c_1;
}
#[inline]
unsafe extern "C" fn modq(mut out: *mut uint64_t, mut a: *mut uint64_t) {
    let mut r: [uint64_t; 4] = [0 as libc::c_uint as uint64_t, 0, 0, 0];
    let mut tmp: [uint64_t; 4] = [0 as libc::c_uint as uint64_t, 0, 0, 0];
    tmp[0 as libc::c_uint as usize] = 0x402da1732fc9bebf as libc::c_ulonglong;
    tmp[1 as libc::c_uint as usize] = 0x4551231950b75fc4 as libc::c_ulonglong;
    tmp[2 as libc::c_uint as usize] = 0x1 as libc::c_ulonglong;
    tmp[3 as libc::c_uint as usize] = 0 as libc::c_ulonglong;
    let mut t01: *mut uint64_t = tmp.as_mut_ptr();
    let mut m: [uint64_t; 7] = [0 as libc::c_uint as uint64_t, 0, 0, 0, 0, 0, 0];
    let mut p: [uint64_t; 5] = [0 as libc::c_uint as uint64_t, 0, 0, 0, 0];
    let mut a0: *mut uint64_t = a;
    let mut a1: *mut uint64_t = a.offset(4 as libc::c_uint as isize);
    let mut c0: uint64_t = mul_pow2_256_minus_q_add(
        4 as libc::c_uint,
        7 as libc::c_uint,
        t01,
        a1,
        a0,
        m.as_mut_ptr(),
    );
    let mut m0: *mut uint64_t = m.as_mut_ptr();
    let mut m1: *mut uint64_t = m.as_mut_ptr().offset(4 as libc::c_uint as isize);
    let mut c10: uint64_t = mul_pow2_256_minus_q_add(
        3 as libc::c_uint,
        5 as libc::c_uint,
        t01,
        m1,
        m0,
        p.as_mut_ptr(),
    );
    let mut p0: *mut uint64_t = p.as_mut_ptr();
    let mut p1: *mut uint64_t = p.as_mut_ptr().offset(4 as libc::c_uint as isize);
    let mut c2: uint64_t = mul_pow2_256_minus_q_add(
        1 as libc::c_uint,
        4 as libc::c_uint,
        t01,
        p1,
        p0,
        r.as_mut_ptr(),
    );
    let mut c00: uint64_t = c2;
    let mut c1: uint64_t = add4(r.as_mut_ptr(), tmp.as_mut_ptr(), out);
    let mut mask: uint64_t = (0 as libc::c_ulonglong).wrapping_sub(c00.wrapping_add(c1));
    let mut i: uint32_t = 0 as libc::c_uint;
    let mut x: uint64_t = mask & *out.offset(i as isize) | !mask & r[i as usize];
    let mut os: *mut uint64_t = out;
    *os.offset(i as isize) = x;
    i = (i as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut x_0: uint64_t = mask & *out.offset(i as isize) | !mask & r[i as usize];
    let mut os_0: *mut uint64_t = out;
    *os_0.offset(i as isize) = x_0;
    i = (i as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut x_1: uint64_t = mask & *out.offset(i as isize) | !mask & r[i as usize];
    let mut os_1: *mut uint64_t = out;
    *os_1.offset(i as isize) = x_1;
    i = (i as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut x_2: uint64_t = mask & *out.offset(i as isize) | !mask & r[i as usize];
    let mut os_2: *mut uint64_t = out;
    *os_2.offset(i as isize) = x_2;
    i = (i as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
}
#[inline]
unsafe extern "C" fn qmul(
    mut out: *mut uint64_t,
    mut f1: *mut uint64_t,
    mut f2: *mut uint64_t,
) {
    let mut tmp: [uint64_t; 8] = [0 as libc::c_uint as uint64_t, 0, 0, 0, 0, 0, 0, 0];
    mul4(f1, f2, tmp.as_mut_ptr());
    modq(out, tmp.as_mut_ptr());
}
#[inline]
unsafe extern "C" fn qsqr(mut out: *mut uint64_t, mut f: *mut uint64_t) {
    let mut tmp: [uint64_t; 8] = [0 as libc::c_uint as uint64_t, 0, 0, 0, 0, 0, 0, 0];
    sqr4(f, tmp.as_mut_ptr());
    modq(out, tmp.as_mut_ptr());
}
#[inline]
unsafe extern "C" fn qnegate_conditional_vartime(
    mut f: *mut uint64_t,
    mut is_negate: bool,
) {
    let mut n: [uint64_t; 4] = [0 as libc::c_uint as uint64_t, 0, 0, 0];
    n[0 as libc::c_uint as usize] = 0xbfd25e8cd0364141 as libc::c_ulonglong;
    n[1 as libc::c_uint as usize] = 0xbaaedce6af48a03b as libc::c_ulonglong;
    n[2 as libc::c_uint as usize] = 0xfffffffffffffffe as libc::c_ulonglong;
    n[3 as libc::c_uint as usize] = 0xffffffffffffffff as libc::c_ulonglong;
    let mut zero: [uint64_t; 4] = [0 as libc::c_uint as uint64_t, 0, 0, 0];
    if is_negate {
        let mut b_copy: [uint64_t; 4] = [0 as libc::c_uint as uint64_t, 0, 0, 0];
        memcpy(
            b_copy.as_mut_ptr() as *mut libc::c_void,
            f as *const libc::c_void,
            (4 as libc::c_uint as libc::c_ulong)
                .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
        );
        sub_mod4(n.as_mut_ptr(), zero.as_mut_ptr(), b_copy.as_mut_ptr(), f);
    }
}
#[inline]
unsafe extern "C" fn is_qelem_le_q_halved_vartime(mut f: *mut uint64_t) -> bool {
    let mut a0: uint64_t = *f.offset(0 as libc::c_uint as isize);
    let mut a1: uint64_t = *f.offset(1 as libc::c_uint as isize);
    let mut a2: uint64_t = *f.offset(2 as libc::c_uint as isize);
    let mut a3: uint64_t = *f.offset(3 as libc::c_uint as isize);
    if a3 < 0x7fffffffffffffff as libc::c_ulonglong {
        return 1 as libc::c_int != 0;
    }
    if a3 > 0x7fffffffffffffff as libc::c_ulonglong {
        return 0 as libc::c_int != 0;
    }
    if a2 < 0xffffffffffffffff as libc::c_ulonglong
        || a1 < 0x5d576e7357a4501d as libc::c_ulonglong
    {
        return 1 as libc::c_int != 0;
    }
    if a1 > 0x5d576e7357a4501d as libc::c_ulonglong {
        return 0 as libc::c_int != 0;
    }
    return a0 <= 0xdfe92f46681b20a0 as libc::c_ulonglong;
}
#[inline]
unsafe extern "C" fn qmul_shift_384(
    mut res: *mut uint64_t,
    mut a: *mut uint64_t,
    mut b: *mut uint64_t,
) {
    let mut l: [uint64_t; 8] = [0 as libc::c_uint as uint64_t, 0, 0, 0, 0, 0, 0, 0];
    mul4(a, b, l.as_mut_ptr());
    let mut res_b_padded: [uint64_t; 4] = [0 as libc::c_uint as uint64_t, 0, 0, 0];
    memcpy(
        res_b_padded.as_mut_ptr() as *mut libc::c_void,
        l.as_mut_ptr().offset(6 as libc::c_uint as isize) as *const libc::c_void,
        (2 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    let mut c0: uint64_t = Hacl_IntTypes_Intrinsics_128_add_carry_u64(
        0 as libc::c_ulonglong,
        res_b_padded[0 as libc::c_uint as usize],
        1 as libc::c_ulonglong,
        res,
    );
    let mut a1: *mut uint64_t = res_b_padded
        .as_mut_ptr()
        .offset(1 as libc::c_uint as isize);
    let mut res1: *mut uint64_t = res.offset(1 as libc::c_uint as isize);
    let mut c: uint64_t = c0;
    let mut i: uint32_t = 0 as libc::c_uint;
    let mut t1: uint64_t = *a1.offset(i as isize);
    let mut res_i: *mut uint64_t = res1.offset(i as isize);
    c = Hacl_IntTypes_Intrinsics_128_add_carry_u64(c, t1, 0 as libc::c_ulonglong, res_i);
    i = (i as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut t1_0: uint64_t = *a1.offset(i as isize);
    let mut res_i_0: *mut uint64_t = res1.offset(i as isize);
    c = Hacl_IntTypes_Intrinsics_128_add_carry_u64(
        c,
        t1_0,
        0 as libc::c_ulonglong,
        res_i_0,
    );
    i = (i as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut t1_1: uint64_t = *a1.offset(i as isize);
    let mut res_i_1: *mut uint64_t = res1.offset(i as isize);
    c = Hacl_IntTypes_Intrinsics_128_add_carry_u64(
        c,
        t1_1,
        0 as libc::c_ulonglong,
        res_i_1,
    );
    i = (i as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut c1: uint64_t = c;
    let mut flag: uint64_t = l[5 as libc::c_uint as usize] >> 63 as libc::c_uint;
    let mut mask: uint64_t = (0 as libc::c_ulonglong).wrapping_sub(flag);
    let mut i_0: uint32_t = 0 as libc::c_uint;
    let mut x: uint64_t = mask & *res.offset(i_0 as isize)
        | !mask & res_b_padded[i_0 as usize];
    let mut os: *mut uint64_t = res;
    *os.offset(i_0 as isize) = x;
    i_0 = (i_0 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut x_0: uint64_t = mask & *res.offset(i_0 as isize)
        | !mask & res_b_padded[i_0 as usize];
    let mut os_0: *mut uint64_t = res;
    *os_0.offset(i_0 as isize) = x_0;
    i_0 = (i_0 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut x_1: uint64_t = mask & *res.offset(i_0 as isize)
        | !mask & res_b_padded[i_0 as usize];
    let mut os_1: *mut uint64_t = res;
    *os_1.offset(i_0 as isize) = x_1;
    i_0 = (i_0 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut x_2: uint64_t = mask & *res.offset(i_0 as isize)
        | !mask & res_b_padded[i_0 as usize];
    let mut os_2: *mut uint64_t = res;
    *os_2.offset(i_0 as isize) = x_2;
    i_0 = (i_0 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
}
#[inline]
unsafe extern "C" fn qsquare_times_in_place(mut out: *mut uint64_t, mut b: uint32_t) {
    let mut i: uint32_t = 0 as libc::c_uint;
    while i < b {
        let mut f_copy: [uint64_t; 4] = [0 as libc::c_uint as uint64_t, 0, 0, 0];
        memcpy(
            f_copy.as_mut_ptr() as *mut libc::c_void,
            out as *const libc::c_void,
            (4 as libc::c_uint as libc::c_ulong)
                .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
        );
        qsqr(out, f_copy.as_mut_ptr());
        i = i.wrapping_add(1);
        i;
    }
}
#[inline]
unsafe extern "C" fn qsquare_times(
    mut out: *mut uint64_t,
    mut a: *mut uint64_t,
    mut b: uint32_t,
) {
    memcpy(
        out as *mut libc::c_void,
        a as *const libc::c_void,
        (4 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    let mut i: uint32_t = 0 as libc::c_uint;
    while i < b {
        let mut f_copy: [uint64_t; 4] = [0 as libc::c_uint as uint64_t, 0, 0, 0];
        memcpy(
            f_copy.as_mut_ptr() as *mut libc::c_void,
            out as *const libc::c_void,
            (4 as libc::c_uint as libc::c_ulong)
                .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
        );
        qsqr(out, f_copy.as_mut_ptr());
        i = i.wrapping_add(1);
        i;
    }
}
#[inline]
unsafe extern "C" fn qinv(mut out: *mut uint64_t, mut f: *mut uint64_t) {
    let mut x_10: [uint64_t; 4] = [0 as libc::c_uint as uint64_t, 0, 0, 0];
    let mut x_11: [uint64_t; 4] = [0 as libc::c_uint as uint64_t, 0, 0, 0];
    let mut x_101: [uint64_t; 4] = [0 as libc::c_uint as uint64_t, 0, 0, 0];
    let mut x_111: [uint64_t; 4] = [0 as libc::c_uint as uint64_t, 0, 0, 0];
    let mut x_1001: [uint64_t; 4] = [0 as libc::c_uint as uint64_t, 0, 0, 0];
    let mut x_1011: [uint64_t; 4] = [0 as libc::c_uint as uint64_t, 0, 0, 0];
    let mut x_1101: [uint64_t; 4] = [0 as libc::c_uint as uint64_t, 0, 0, 0];
    qsquare_times(x_10.as_mut_ptr(), f, 1 as libc::c_uint);
    qmul(x_11.as_mut_ptr(), x_10.as_mut_ptr(), f);
    qmul(x_101.as_mut_ptr(), x_10.as_mut_ptr(), x_11.as_mut_ptr());
    qmul(x_111.as_mut_ptr(), x_10.as_mut_ptr(), x_101.as_mut_ptr());
    qmul(x_1001.as_mut_ptr(), x_10.as_mut_ptr(), x_111.as_mut_ptr());
    qmul(x_1011.as_mut_ptr(), x_10.as_mut_ptr(), x_1001.as_mut_ptr());
    qmul(x_1101.as_mut_ptr(), x_10.as_mut_ptr(), x_1011.as_mut_ptr());
    let mut x6: [uint64_t; 4] = [0 as libc::c_uint as uint64_t, 0, 0, 0];
    let mut x8: [uint64_t; 4] = [0 as libc::c_uint as uint64_t, 0, 0, 0];
    let mut x14: [uint64_t; 4] = [0 as libc::c_uint as uint64_t, 0, 0, 0];
    qsquare_times(x6.as_mut_ptr(), x_1101.as_mut_ptr(), 2 as libc::c_uint);
    let mut f1_copy0: [uint64_t; 4] = [0 as libc::c_uint as uint64_t, 0, 0, 0];
    memcpy(
        f1_copy0.as_mut_ptr() as *mut libc::c_void,
        x6.as_mut_ptr() as *const libc::c_void,
        (4 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    qmul(x6.as_mut_ptr(), f1_copy0.as_mut_ptr(), x_1011.as_mut_ptr());
    qsquare_times(x8.as_mut_ptr(), x6.as_mut_ptr(), 2 as libc::c_uint);
    let mut f1_copy1: [uint64_t; 4] = [0 as libc::c_uint as uint64_t, 0, 0, 0];
    memcpy(
        f1_copy1.as_mut_ptr() as *mut libc::c_void,
        x8.as_mut_ptr() as *const libc::c_void,
        (4 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    qmul(x8.as_mut_ptr(), f1_copy1.as_mut_ptr(), x_11.as_mut_ptr());
    qsquare_times(x14.as_mut_ptr(), x8.as_mut_ptr(), 6 as libc::c_uint);
    let mut f1_copy2: [uint64_t; 4] = [0 as libc::c_uint as uint64_t, 0, 0, 0];
    memcpy(
        f1_copy2.as_mut_ptr() as *mut libc::c_void,
        x14.as_mut_ptr() as *const libc::c_void,
        (4 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    qmul(x14.as_mut_ptr(), f1_copy2.as_mut_ptr(), x6.as_mut_ptr());
    let mut x56: [uint64_t; 4] = [0 as libc::c_uint as uint64_t, 0, 0, 0];
    qsquare_times(out, x14.as_mut_ptr(), 14 as libc::c_uint);
    let mut f1_copy: [uint64_t; 4] = [0 as libc::c_uint as uint64_t, 0, 0, 0];
    memcpy(
        f1_copy.as_mut_ptr() as *mut libc::c_void,
        out as *const libc::c_void,
        (4 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    qmul(out, f1_copy.as_mut_ptr(), x14.as_mut_ptr());
    qsquare_times(x56.as_mut_ptr(), out, 28 as libc::c_uint);
    let mut f1_copy3: [uint64_t; 4] = [0 as libc::c_uint as uint64_t, 0, 0, 0];
    memcpy(
        f1_copy3.as_mut_ptr() as *mut libc::c_void,
        x56.as_mut_ptr() as *const libc::c_void,
        (4 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    qmul(x56.as_mut_ptr(), f1_copy3.as_mut_ptr(), out);
    qsquare_times(out, x56.as_mut_ptr(), 56 as libc::c_uint);
    let mut f1_copy4: [uint64_t; 4] = [0 as libc::c_uint as uint64_t, 0, 0, 0];
    memcpy(
        f1_copy4.as_mut_ptr() as *mut libc::c_void,
        out as *const libc::c_void,
        (4 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    qmul(out, f1_copy4.as_mut_ptr(), x56.as_mut_ptr());
    qsquare_times_in_place(out, 14 as libc::c_uint);
    let mut f1_copy5: [uint64_t; 4] = [0 as libc::c_uint as uint64_t, 0, 0, 0];
    memcpy(
        f1_copy5.as_mut_ptr() as *mut libc::c_void,
        out as *const libc::c_void,
        (4 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    qmul(out, f1_copy5.as_mut_ptr(), x14.as_mut_ptr());
    qsquare_times_in_place(out, 3 as libc::c_uint);
    let mut f1_copy6: [uint64_t; 4] = [0 as libc::c_uint as uint64_t, 0, 0, 0];
    memcpy(
        f1_copy6.as_mut_ptr() as *mut libc::c_void,
        out as *const libc::c_void,
        (4 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    qmul(out, f1_copy6.as_mut_ptr(), x_101.as_mut_ptr());
    qsquare_times_in_place(out, 4 as libc::c_uint);
    let mut f1_copy7: [uint64_t; 4] = [0 as libc::c_uint as uint64_t, 0, 0, 0];
    memcpy(
        f1_copy7.as_mut_ptr() as *mut libc::c_void,
        out as *const libc::c_void,
        (4 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    qmul(out, f1_copy7.as_mut_ptr(), x_111.as_mut_ptr());
    qsquare_times_in_place(out, 4 as libc::c_uint);
    let mut f1_copy8: [uint64_t; 4] = [0 as libc::c_uint as uint64_t, 0, 0, 0];
    memcpy(
        f1_copy8.as_mut_ptr() as *mut libc::c_void,
        out as *const libc::c_void,
        (4 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    qmul(out, f1_copy8.as_mut_ptr(), x_101.as_mut_ptr());
    qsquare_times_in_place(out, 5 as libc::c_uint);
    let mut f1_copy9: [uint64_t; 4] = [0 as libc::c_uint as uint64_t, 0, 0, 0];
    memcpy(
        f1_copy9.as_mut_ptr() as *mut libc::c_void,
        out as *const libc::c_void,
        (4 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    qmul(out, f1_copy9.as_mut_ptr(), x_1011.as_mut_ptr());
    qsquare_times_in_place(out, 4 as libc::c_uint);
    let mut f1_copy10: [uint64_t; 4] = [0 as libc::c_uint as uint64_t, 0, 0, 0];
    memcpy(
        f1_copy10.as_mut_ptr() as *mut libc::c_void,
        out as *const libc::c_void,
        (4 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    qmul(out, f1_copy10.as_mut_ptr(), x_1011.as_mut_ptr());
    qsquare_times_in_place(out, 4 as libc::c_uint);
    let mut f1_copy11: [uint64_t; 4] = [0 as libc::c_uint as uint64_t, 0, 0, 0];
    memcpy(
        f1_copy11.as_mut_ptr() as *mut libc::c_void,
        out as *const libc::c_void,
        (4 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    qmul(out, f1_copy11.as_mut_ptr(), x_111.as_mut_ptr());
    qsquare_times_in_place(out, 5 as libc::c_uint);
    let mut f1_copy12: [uint64_t; 4] = [0 as libc::c_uint as uint64_t, 0, 0, 0];
    memcpy(
        f1_copy12.as_mut_ptr() as *mut libc::c_void,
        out as *const libc::c_void,
        (4 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    qmul(out, f1_copy12.as_mut_ptr(), x_111.as_mut_ptr());
    qsquare_times_in_place(out, 6 as libc::c_uint);
    let mut f1_copy13: [uint64_t; 4] = [0 as libc::c_uint as uint64_t, 0, 0, 0];
    memcpy(
        f1_copy13.as_mut_ptr() as *mut libc::c_void,
        out as *const libc::c_void,
        (4 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    qmul(out, f1_copy13.as_mut_ptr(), x_1101.as_mut_ptr());
    qsquare_times_in_place(out, 4 as libc::c_uint);
    let mut f1_copy14: [uint64_t; 4] = [0 as libc::c_uint as uint64_t, 0, 0, 0];
    memcpy(
        f1_copy14.as_mut_ptr() as *mut libc::c_void,
        out as *const libc::c_void,
        (4 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    qmul(out, f1_copy14.as_mut_ptr(), x_101.as_mut_ptr());
    qsquare_times_in_place(out, 3 as libc::c_uint);
    let mut f1_copy15: [uint64_t; 4] = [0 as libc::c_uint as uint64_t, 0, 0, 0];
    memcpy(
        f1_copy15.as_mut_ptr() as *mut libc::c_void,
        out as *const libc::c_void,
        (4 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    qmul(out, f1_copy15.as_mut_ptr(), x_111.as_mut_ptr());
    qsquare_times_in_place(out, 5 as libc::c_uint);
    let mut f1_copy16: [uint64_t; 4] = [0 as libc::c_uint as uint64_t, 0, 0, 0];
    memcpy(
        f1_copy16.as_mut_ptr() as *mut libc::c_void,
        out as *const libc::c_void,
        (4 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    qmul(out, f1_copy16.as_mut_ptr(), x_1001.as_mut_ptr());
    qsquare_times_in_place(out, 6 as libc::c_uint);
    let mut f1_copy17: [uint64_t; 4] = [0 as libc::c_uint as uint64_t, 0, 0, 0];
    memcpy(
        f1_copy17.as_mut_ptr() as *mut libc::c_void,
        out as *const libc::c_void,
        (4 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    qmul(out, f1_copy17.as_mut_ptr(), x_101.as_mut_ptr());
    qsquare_times_in_place(out, 10 as libc::c_uint);
    let mut f1_copy18: [uint64_t; 4] = [0 as libc::c_uint as uint64_t, 0, 0, 0];
    memcpy(
        f1_copy18.as_mut_ptr() as *mut libc::c_void,
        out as *const libc::c_void,
        (4 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    qmul(out, f1_copy18.as_mut_ptr(), x_111.as_mut_ptr());
    qsquare_times_in_place(out, 4 as libc::c_uint);
    let mut f1_copy19: [uint64_t; 4] = [0 as libc::c_uint as uint64_t, 0, 0, 0];
    memcpy(
        f1_copy19.as_mut_ptr() as *mut libc::c_void,
        out as *const libc::c_void,
        (4 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    qmul(out, f1_copy19.as_mut_ptr(), x_111.as_mut_ptr());
    qsquare_times_in_place(out, 9 as libc::c_uint);
    let mut f1_copy20: [uint64_t; 4] = [0 as libc::c_uint as uint64_t, 0, 0, 0];
    memcpy(
        f1_copy20.as_mut_ptr() as *mut libc::c_void,
        out as *const libc::c_void,
        (4 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    qmul(out, f1_copy20.as_mut_ptr(), x8.as_mut_ptr());
    qsquare_times_in_place(out, 5 as libc::c_uint);
    let mut f1_copy21: [uint64_t; 4] = [0 as libc::c_uint as uint64_t, 0, 0, 0];
    memcpy(
        f1_copy21.as_mut_ptr() as *mut libc::c_void,
        out as *const libc::c_void,
        (4 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    qmul(out, f1_copy21.as_mut_ptr(), x_1001.as_mut_ptr());
    qsquare_times_in_place(out, 6 as libc::c_uint);
    let mut f1_copy22: [uint64_t; 4] = [0 as libc::c_uint as uint64_t, 0, 0, 0];
    memcpy(
        f1_copy22.as_mut_ptr() as *mut libc::c_void,
        out as *const libc::c_void,
        (4 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    qmul(out, f1_copy22.as_mut_ptr(), x_1011.as_mut_ptr());
    qsquare_times_in_place(out, 4 as libc::c_uint);
    let mut f1_copy23: [uint64_t; 4] = [0 as libc::c_uint as uint64_t, 0, 0, 0];
    memcpy(
        f1_copy23.as_mut_ptr() as *mut libc::c_void,
        out as *const libc::c_void,
        (4 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    qmul(out, f1_copy23.as_mut_ptr(), x_1101.as_mut_ptr());
    qsquare_times_in_place(out, 5 as libc::c_uint);
    let mut f1_copy24: [uint64_t; 4] = [0 as libc::c_uint as uint64_t, 0, 0, 0];
    memcpy(
        f1_copy24.as_mut_ptr() as *mut libc::c_void,
        out as *const libc::c_void,
        (4 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    qmul(out, f1_copy24.as_mut_ptr(), x_11.as_mut_ptr());
    qsquare_times_in_place(out, 6 as libc::c_uint);
    let mut f1_copy25: [uint64_t; 4] = [0 as libc::c_uint as uint64_t, 0, 0, 0];
    memcpy(
        f1_copy25.as_mut_ptr() as *mut libc::c_void,
        out as *const libc::c_void,
        (4 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    qmul(out, f1_copy25.as_mut_ptr(), x_1101.as_mut_ptr());
    qsquare_times_in_place(out, 10 as libc::c_uint);
    let mut f1_copy26: [uint64_t; 4] = [0 as libc::c_uint as uint64_t, 0, 0, 0];
    memcpy(
        f1_copy26.as_mut_ptr() as *mut libc::c_void,
        out as *const libc::c_void,
        (4 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    qmul(out, f1_copy26.as_mut_ptr(), x_1101.as_mut_ptr());
    qsquare_times_in_place(out, 4 as libc::c_uint);
    let mut f1_copy27: [uint64_t; 4] = [0 as libc::c_uint as uint64_t, 0, 0, 0];
    memcpy(
        f1_copy27.as_mut_ptr() as *mut libc::c_void,
        out as *const libc::c_void,
        (4 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    qmul(out, f1_copy27.as_mut_ptr(), x_1001.as_mut_ptr());
    qsquare_times_in_place(out, 6 as libc::c_uint);
    let mut f1_copy28: [uint64_t; 4] = [0 as libc::c_uint as uint64_t, 0, 0, 0];
    memcpy(
        f1_copy28.as_mut_ptr() as *mut libc::c_void,
        out as *const libc::c_void,
        (4 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    qmul(out, f1_copy28.as_mut_ptr(), f);
    qsquare_times_in_place(out, 8 as libc::c_uint);
    let mut f1_copy29: [uint64_t; 4] = [0 as libc::c_uint as uint64_t, 0, 0, 0];
    memcpy(
        f1_copy29.as_mut_ptr() as *mut libc::c_void,
        out as *const libc::c_void,
        (4 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    qmul(out, f1_copy29.as_mut_ptr(), x6.as_mut_ptr());
}
#[no_mangle]
pub unsafe extern "C" fn Hacl_Impl_K256_Point_make_point_at_inf(mut p: *mut uint64_t) {
    let mut px: *mut uint64_t = p;
    let mut py: *mut uint64_t = p.offset(5 as libc::c_uint as isize);
    let mut pz: *mut uint64_t = p.offset(10 as libc::c_uint as isize);
    memset(
        px as *mut libc::c_void,
        0 as libc::c_uint as libc::c_int,
        (5 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    memset(
        py as *mut libc::c_void,
        0 as libc::c_uint as libc::c_int,
        (5 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    *py.offset(0 as libc::c_uint as isize) = 1 as libc::c_ulonglong;
    memset(
        pz as *mut libc::c_void,
        0 as libc::c_uint as libc::c_int,
        (5 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
}
#[inline]
unsafe extern "C" fn to_aff_point(mut p_aff: *mut uint64_t, mut p: *mut uint64_t) {
    let mut x: *mut uint64_t = p_aff;
    let mut y: *mut uint64_t = p_aff.offset(5 as libc::c_uint as isize);
    let mut x1: *mut uint64_t = p;
    let mut y1: *mut uint64_t = p.offset(5 as libc::c_uint as isize);
    let mut z1: *mut uint64_t = p.offset(10 as libc::c_uint as isize);
    let mut zinv: [uint64_t; 5] = [0 as libc::c_uint as uint64_t, 0, 0, 0, 0];
    Hacl_Impl_K256_Finv_finv(zinv.as_mut_ptr(), z1);
    Hacl_K256_Field_fmul(x, x1, zinv.as_mut_ptr());
    Hacl_K256_Field_fmul(y, y1, zinv.as_mut_ptr());
    let mut f_copy: [uint64_t; 5] = [0 as libc::c_uint as uint64_t, 0, 0, 0, 0];
    memcpy(
        f_copy.as_mut_ptr() as *mut libc::c_void,
        x as *const libc::c_void,
        (5 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    Hacl_K256_Field_fnormalize(x, f_copy.as_mut_ptr());
    let mut f_copy0: [uint64_t; 5] = [0 as libc::c_uint as uint64_t, 0, 0, 0, 0];
    memcpy(
        f_copy0.as_mut_ptr() as *mut libc::c_void,
        y as *const libc::c_void,
        (5 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    Hacl_K256_Field_fnormalize(y, f_copy0.as_mut_ptr());
}
#[inline]
unsafe extern "C" fn to_aff_point_x(mut x: *mut uint64_t, mut p: *mut uint64_t) {
    let mut x1: *mut uint64_t = p;
    let mut z1: *mut uint64_t = p.offset(10 as libc::c_uint as isize);
    let mut zinv: [uint64_t; 5] = [0 as libc::c_uint as uint64_t, 0, 0, 0, 0];
    Hacl_Impl_K256_Finv_finv(zinv.as_mut_ptr(), z1);
    Hacl_K256_Field_fmul(x, x1, zinv.as_mut_ptr());
    let mut f_copy: [uint64_t; 5] = [0 as libc::c_uint as uint64_t, 0, 0, 0, 0];
    memcpy(
        f_copy.as_mut_ptr() as *mut libc::c_void,
        x as *const libc::c_void,
        (5 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    Hacl_K256_Field_fnormalize(x, f_copy.as_mut_ptr());
}
#[inline]
unsafe extern "C" fn is_on_curve_vartime(mut p: *mut uint64_t) -> bool {
    let mut y2_exp: [uint64_t; 5] = [0 as libc::c_uint as uint64_t, 0, 0, 0, 0];
    let mut x: *mut uint64_t = p;
    let mut y: *mut uint64_t = p.offset(5 as libc::c_uint as isize);
    let mut b: [uint64_t; 5] = [0 as libc::c_uint as uint64_t, 0, 0, 0, 0];
    b[0 as libc::c_uint as usize] = 0x7 as libc::c_ulonglong;
    b[1 as libc::c_uint as usize] = 0 as libc::c_ulonglong;
    b[2 as libc::c_uint as usize] = 0 as libc::c_ulonglong;
    b[3 as libc::c_uint as usize] = 0 as libc::c_ulonglong;
    b[4 as libc::c_uint as usize] = 0 as libc::c_ulonglong;
    Hacl_K256_Field_fsqr(y2_exp.as_mut_ptr(), x);
    let mut f1_copy: [uint64_t; 5] = [0 as libc::c_uint as uint64_t, 0, 0, 0, 0];
    memcpy(
        f1_copy.as_mut_ptr() as *mut libc::c_void,
        y2_exp.as_mut_ptr() as *const libc::c_void,
        (5 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    Hacl_K256_Field_fmul(y2_exp.as_mut_ptr(), f1_copy.as_mut_ptr(), x);
    let mut f1_copy0: [uint64_t; 5] = [0 as libc::c_uint as uint64_t, 0, 0, 0, 0];
    memcpy(
        f1_copy0.as_mut_ptr() as *mut libc::c_void,
        y2_exp.as_mut_ptr() as *const libc::c_void,
        (5 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    Hacl_K256_Field_fadd(y2_exp.as_mut_ptr(), f1_copy0.as_mut_ptr(), b.as_mut_ptr());
    let mut f_copy0: [uint64_t; 5] = [0 as libc::c_uint as uint64_t, 0, 0, 0, 0];
    memcpy(
        f_copy0.as_mut_ptr() as *mut libc::c_void,
        y2_exp.as_mut_ptr() as *const libc::c_void,
        (5 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    Hacl_K256_Field_fnormalize(y2_exp.as_mut_ptr(), f_copy0.as_mut_ptr());
    let mut y2_comp: [uint64_t; 5] = [0 as libc::c_uint as uint64_t, 0, 0, 0, 0];
    Hacl_K256_Field_fsqr(y2_comp.as_mut_ptr(), y);
    let mut f_copy: [uint64_t; 5] = [0 as libc::c_uint as uint64_t, 0, 0, 0, 0];
    memcpy(
        f_copy.as_mut_ptr() as *mut libc::c_void,
        y2_comp.as_mut_ptr() as *const libc::c_void,
        (5 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    Hacl_K256_Field_fnormalize(y2_comp.as_mut_ptr(), f_copy.as_mut_ptr());
    let mut res: bool = Hacl_K256_Field_is_felem_eq_vartime(
        y2_exp.as_mut_ptr(),
        y2_comp.as_mut_ptr(),
    );
    let mut res0: bool = res;
    return res0;
}
#[no_mangle]
pub unsafe extern "C" fn Hacl_Impl_K256_Point_point_negate(
    mut out: *mut uint64_t,
    mut p: *mut uint64_t,
) {
    let mut px: *mut uint64_t = p;
    let mut py: *mut uint64_t = p.offset(5 as libc::c_uint as isize);
    let mut pz: *mut uint64_t = p.offset(10 as libc::c_uint as isize);
    let mut ox: *mut uint64_t = out;
    let mut oy: *mut uint64_t = out.offset(5 as libc::c_uint as isize);
    let mut oz: *mut uint64_t = out.offset(10 as libc::c_uint as isize);
    *ox.offset(0 as libc::c_uint as isize) = *px.offset(0 as libc::c_uint as isize);
    *ox.offset(1 as libc::c_uint as isize) = *px.offset(1 as libc::c_uint as isize);
    *ox.offset(2 as libc::c_uint as isize) = *px.offset(2 as libc::c_uint as isize);
    *ox.offset(3 as libc::c_uint as isize) = *px.offset(3 as libc::c_uint as isize);
    *ox.offset(4 as libc::c_uint as isize) = *px.offset(4 as libc::c_uint as isize);
    *oz.offset(0 as libc::c_uint as isize) = *pz.offset(0 as libc::c_uint as isize);
    *oz.offset(1 as libc::c_uint as isize) = *pz.offset(1 as libc::c_uint as isize);
    *oz.offset(2 as libc::c_uint as isize) = *pz.offset(2 as libc::c_uint as isize);
    *oz.offset(3 as libc::c_uint as isize) = *pz.offset(3 as libc::c_uint as isize);
    *oz.offset(4 as libc::c_uint as isize) = *pz.offset(4 as libc::c_uint as isize);
    let mut a0: uint64_t = *py.offset(0 as libc::c_uint as isize);
    let mut a1: uint64_t = *py.offset(1 as libc::c_uint as isize);
    let mut a2: uint64_t = *py.offset(2 as libc::c_uint as isize);
    let mut a3: uint64_t = *py.offset(3 as libc::c_uint as isize);
    let mut a4: uint64_t = *py.offset(4 as libc::c_uint as isize);
    let mut r0: uint64_t = (18014381329608892 as libc::c_ulonglong).wrapping_sub(a0);
    let mut r1: uint64_t = (18014398509481980 as libc::c_ulonglong).wrapping_sub(a1);
    let mut r2: uint64_t = (18014398509481980 as libc::c_ulonglong).wrapping_sub(a2);
    let mut r3: uint64_t = (18014398509481980 as libc::c_ulonglong).wrapping_sub(a3);
    let mut r4: uint64_t = (1125899906842620 as libc::c_ulonglong).wrapping_sub(a4);
    let mut f0: uint64_t = r0;
    let mut f1: uint64_t = r1;
    let mut f2: uint64_t = r2;
    let mut f3: uint64_t = r3;
    let mut f4: uint64_t = r4;
    *oy.offset(0 as libc::c_uint as isize) = f0;
    *oy.offset(1 as libc::c_uint as isize) = f1;
    *oy.offset(2 as libc::c_uint as isize) = f2;
    *oy.offset(3 as libc::c_uint as isize) = f3;
    *oy.offset(4 as libc::c_uint as isize) = f4;
    let mut f_copy: [uint64_t; 5] = [0 as libc::c_uint as uint64_t, 0, 0, 0, 0];
    memcpy(
        f_copy.as_mut_ptr() as *mut libc::c_void,
        oy as *const libc::c_void,
        (5 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    Hacl_K256_Field_fnormalize_weak(oy, f_copy.as_mut_ptr());
}
#[inline]
unsafe extern "C" fn point_negate_conditional_vartime(
    mut p: *mut uint64_t,
    mut is_negate: bool,
) {
    if is_negate {
        let mut p_copy: [uint64_t; 15] = [
            0 as libc::c_uint as uint64_t,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
        ];
        memcpy(
            p_copy.as_mut_ptr() as *mut libc::c_void,
            p as *const libc::c_void,
            (15 as libc::c_uint as libc::c_ulong)
                .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
        );
        Hacl_Impl_K256_Point_point_negate(p, p_copy.as_mut_ptr());
        return;
    }
}
#[inline]
unsafe extern "C" fn aff_point_store(mut out: *mut uint8_t, mut p: *mut uint64_t) {
    let mut px: *mut uint64_t = p;
    let mut py: *mut uint64_t = p.offset(5 as libc::c_uint as isize);
    Hacl_K256_Field_store_felem(out, px);
    Hacl_K256_Field_store_felem(out.offset(32 as libc::c_uint as isize), py);
}
#[no_mangle]
pub unsafe extern "C" fn Hacl_Impl_K256_Point_point_store(
    mut out: *mut uint8_t,
    mut p: *mut uint64_t,
) {
    let mut p_aff: [uint64_t; 10] = [
        0 as libc::c_uint as uint64_t,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
    ];
    to_aff_point(p_aff.as_mut_ptr(), p);
    aff_point_store(out, p_aff.as_mut_ptr());
}
#[no_mangle]
pub unsafe extern "C" fn Hacl_Impl_K256_Point_aff_point_load_vartime(
    mut p: *mut uint64_t,
    mut b: *mut uint8_t,
) -> bool {
    let mut px: *mut uint8_t = b;
    let mut py: *mut uint8_t = b.offset(32 as libc::c_uint as isize);
    let mut bn_px: *mut uint64_t = p;
    let mut bn_py: *mut uint64_t = p.offset(5 as libc::c_uint as isize);
    let mut is_x_valid: bool = Hacl_K256_Field_load_felem_lt_prime_vartime(bn_px, px);
    let mut is_y_valid: bool = Hacl_K256_Field_load_felem_lt_prime_vartime(bn_py, py);
    if is_x_valid as libc::c_int != 0 && is_y_valid as libc::c_int != 0 {
        return is_on_curve_vartime(p);
    }
    return 0 as libc::c_int != 0;
}
#[inline]
unsafe extern "C" fn load_point_vartime(
    mut p: *mut uint64_t,
    mut b: *mut uint8_t,
) -> bool {
    let mut p_aff: [uint64_t; 10] = [
        0 as libc::c_uint as uint64_t,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
    ];
    let mut res: bool = Hacl_Impl_K256_Point_aff_point_load_vartime(
        p_aff.as_mut_ptr(),
        b,
    );
    if res {
        let mut x: *mut uint64_t = p_aff.as_mut_ptr();
        let mut y: *mut uint64_t = p_aff.as_mut_ptr().offset(5 as libc::c_uint as isize);
        let mut x1: *mut uint64_t = p;
        let mut y1: *mut uint64_t = p.offset(5 as libc::c_uint as isize);
        let mut z1: *mut uint64_t = p.offset(10 as libc::c_uint as isize);
        memcpy(
            x1 as *mut libc::c_void,
            x as *const libc::c_void,
            (5 as libc::c_uint as libc::c_ulong)
                .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
        );
        memcpy(
            y1 as *mut libc::c_void,
            y as *const libc::c_void,
            (5 as libc::c_uint as libc::c_ulong)
                .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
        );
        memset(
            z1 as *mut libc::c_void,
            0 as libc::c_uint as libc::c_int,
            (5 as libc::c_uint as libc::c_ulong)
                .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
        );
        *z1.offset(0 as libc::c_uint as isize) = 1 as libc::c_ulonglong;
    }
    return res;
}
#[inline]
unsafe extern "C" fn aff_point_decompress_vartime(
    mut x: *mut uint64_t,
    mut y: *mut uint64_t,
    mut s: *mut uint8_t,
) -> bool {
    let mut s0: uint8_t = *s.offset(0 as libc::c_uint as isize);
    let mut s01: uint8_t = s0;
    if !(s01 as libc::c_uint == 0x2 as libc::c_uint
        || s01 as libc::c_uint == 0x3 as libc::c_uint)
    {
        return 0 as libc::c_int != 0;
    }
    let mut xb: *mut uint8_t = s.offset(1 as libc::c_uint as isize);
    let mut is_x_valid: bool = Hacl_K256_Field_load_felem_lt_prime_vartime(x, xb);
    let mut is_y_odd: bool = s01 as libc::c_uint == 0x3 as libc::c_uint;
    if !is_x_valid {
        return 0 as libc::c_int != 0;
    }
    let mut y2: [uint64_t; 5] = [0 as libc::c_uint as uint64_t, 0, 0, 0, 0];
    let mut b: [uint64_t; 5] = [0 as libc::c_uint as uint64_t, 0, 0, 0, 0];
    b[0 as libc::c_uint as usize] = 0x7 as libc::c_ulonglong;
    b[1 as libc::c_uint as usize] = 0 as libc::c_ulonglong;
    b[2 as libc::c_uint as usize] = 0 as libc::c_ulonglong;
    b[3 as libc::c_uint as usize] = 0 as libc::c_ulonglong;
    b[4 as libc::c_uint as usize] = 0 as libc::c_ulonglong;
    Hacl_K256_Field_fsqr(y2.as_mut_ptr(), x);
    let mut f1_copy: [uint64_t; 5] = [0 as libc::c_uint as uint64_t, 0, 0, 0, 0];
    memcpy(
        f1_copy.as_mut_ptr() as *mut libc::c_void,
        y2.as_mut_ptr() as *const libc::c_void,
        (5 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    Hacl_K256_Field_fmul(y2.as_mut_ptr(), f1_copy.as_mut_ptr(), x);
    let mut f1_copy0: [uint64_t; 5] = [0 as libc::c_uint as uint64_t, 0, 0, 0, 0];
    memcpy(
        f1_copy0.as_mut_ptr() as *mut libc::c_void,
        y2.as_mut_ptr() as *const libc::c_void,
        (5 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    Hacl_K256_Field_fadd(y2.as_mut_ptr(), f1_copy0.as_mut_ptr(), b.as_mut_ptr());
    let mut f_copy0: [uint64_t; 5] = [0 as libc::c_uint as uint64_t, 0, 0, 0, 0];
    memcpy(
        f_copy0.as_mut_ptr() as *mut libc::c_void,
        y2.as_mut_ptr() as *const libc::c_void,
        (5 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    Hacl_K256_Field_fnormalize(y2.as_mut_ptr(), f_copy0.as_mut_ptr());
    Hacl_Impl_K256_Finv_fsqrt(y, y2.as_mut_ptr());
    let mut f_copy1: [uint64_t; 5] = [0 as libc::c_uint as uint64_t, 0, 0, 0, 0];
    memcpy(
        f_copy1.as_mut_ptr() as *mut libc::c_void,
        y as *const libc::c_void,
        (5 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    Hacl_K256_Field_fnormalize(y, f_copy1.as_mut_ptr());
    let mut y2_comp: [uint64_t; 5] = [0 as libc::c_uint as uint64_t, 0, 0, 0, 0];
    Hacl_K256_Field_fsqr(y2_comp.as_mut_ptr(), y);
    let mut f_copy: [uint64_t; 5] = [0 as libc::c_uint as uint64_t, 0, 0, 0, 0];
    memcpy(
        f_copy.as_mut_ptr() as *mut libc::c_void,
        y2_comp.as_mut_ptr() as *const libc::c_void,
        (5 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    Hacl_K256_Field_fnormalize(y2_comp.as_mut_ptr(), f_copy.as_mut_ptr());
    let mut res: bool = Hacl_K256_Field_is_felem_eq_vartime(
        y2.as_mut_ptr(),
        y2_comp.as_mut_ptr(),
    );
    let mut is_y_valid: bool = res;
    let mut is_y_valid0: bool = is_y_valid;
    if !is_y_valid0 {
        return 0 as libc::c_int != 0;
    }
    let mut x0: uint64_t = *y.offset(0 as libc::c_uint as isize);
    let mut is_y_odd1: bool = x0 & 1 as libc::c_ulonglong == 1 as libc::c_ulonglong;
    Hacl_K256_Field_fnegate_conditional_vartime(
        y,
        is_y_odd1 as libc::c_int != is_y_odd as libc::c_int,
    );
    return 1 as libc::c_int != 0;
}
#[no_mangle]
pub unsafe extern "C" fn Hacl_Impl_K256_PointDouble_point_double(
    mut out: *mut uint64_t,
    mut p: *mut uint64_t,
) {
    let mut tmp: [uint64_t; 25] = [
        0 as libc::c_uint as uint64_t,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
    ];
    let mut x1: *mut uint64_t = p;
    let mut y1: *mut uint64_t = p.offset(5 as libc::c_uint as isize);
    let mut z1: *mut uint64_t = p.offset(10 as libc::c_uint as isize);
    let mut x3: *mut uint64_t = out;
    let mut y3: *mut uint64_t = out.offset(5 as libc::c_uint as isize);
    let mut z3: *mut uint64_t = out.offset(10 as libc::c_uint as isize);
    let mut yy: *mut uint64_t = tmp.as_mut_ptr();
    let mut zz: *mut uint64_t = tmp.as_mut_ptr().offset(5 as libc::c_uint as isize);
    let mut bzz3: *mut uint64_t = tmp.as_mut_ptr().offset(10 as libc::c_uint as isize);
    let mut bzz9: *mut uint64_t = tmp.as_mut_ptr().offset(15 as libc::c_uint as isize);
    let mut tmp1: *mut uint64_t = tmp.as_mut_ptr().offset(20 as libc::c_uint as isize);
    Hacl_K256_Field_fsqr(yy, y1);
    Hacl_K256_Field_fsqr(zz, z1);
    Hacl_K256_Field_fmul_small_num(x3, x1, 2 as libc::c_ulonglong);
    let mut f1_copy: [uint64_t; 5] = [0 as libc::c_uint as uint64_t, 0, 0, 0, 0];
    memcpy(
        f1_copy.as_mut_ptr() as *mut libc::c_void,
        x3 as *const libc::c_void,
        (5 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    Hacl_K256_Field_fmul(x3, f1_copy.as_mut_ptr(), y1);
    Hacl_K256_Field_fmul(tmp1, yy, y1);
    Hacl_K256_Field_fmul(z3, tmp1, z1);
    let mut f_copy: [uint64_t; 5] = [0 as libc::c_uint as uint64_t, 0, 0, 0, 0];
    memcpy(
        f_copy.as_mut_ptr() as *mut libc::c_void,
        z3 as *const libc::c_void,
        (5 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    Hacl_K256_Field_fmul_small_num(z3, f_copy.as_mut_ptr(), 8 as libc::c_ulonglong);
    let mut f_copy1: [uint64_t; 5] = [0 as libc::c_uint as uint64_t, 0, 0, 0, 0];
    memcpy(
        f_copy1.as_mut_ptr() as *mut libc::c_void,
        z3 as *const libc::c_void,
        (5 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    Hacl_K256_Field_fnormalize_weak(z3, f_copy1.as_mut_ptr());
    Hacl_K256_Field_fmul_small_num(bzz3, zz, 21 as libc::c_ulonglong);
    let mut f_copy0: [uint64_t; 5] = [0 as libc::c_uint as uint64_t, 0, 0, 0, 0];
    memcpy(
        f_copy0.as_mut_ptr() as *mut libc::c_void,
        bzz3 as *const libc::c_void,
        (5 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    Hacl_K256_Field_fnormalize_weak(bzz3, f_copy0.as_mut_ptr());
    Hacl_K256_Field_fmul_small_num(bzz9, bzz3, 3 as libc::c_ulonglong);
    let mut f2_copy: [uint64_t; 5] = [0 as libc::c_uint as uint64_t, 0, 0, 0, 0];
    memcpy(
        f2_copy.as_mut_ptr() as *mut libc::c_void,
        bzz9 as *const libc::c_void,
        (5 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    Hacl_K256_Field_fsub(bzz9, yy, f2_copy.as_mut_ptr(), 6 as libc::c_ulonglong);
    Hacl_K256_Field_fadd(tmp1, yy, bzz3);
    let mut f2_copy0: [uint64_t; 5] = [0 as libc::c_uint as uint64_t, 0, 0, 0, 0];
    memcpy(
        f2_copy0.as_mut_ptr() as *mut libc::c_void,
        tmp1 as *const libc::c_void,
        (5 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    Hacl_K256_Field_fmul(tmp1, bzz9, f2_copy0.as_mut_ptr());
    Hacl_K256_Field_fmul(y3, yy, zz);
    let mut f1_copy0: [uint64_t; 5] = [0 as libc::c_uint as uint64_t, 0, 0, 0, 0];
    memcpy(
        f1_copy0.as_mut_ptr() as *mut libc::c_void,
        x3 as *const libc::c_void,
        (5 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    Hacl_K256_Field_fmul(x3, f1_copy0.as_mut_ptr(), bzz9);
    let mut f_copy2: [uint64_t; 5] = [0 as libc::c_uint as uint64_t, 0, 0, 0, 0];
    memcpy(
        f_copy2.as_mut_ptr() as *mut libc::c_void,
        y3 as *const libc::c_void,
        (5 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    Hacl_K256_Field_fmul_small_num(y3, f_copy2.as_mut_ptr(), 168 as libc::c_ulonglong);
    let mut f2_copy1: [uint64_t; 5] = [0 as libc::c_uint as uint64_t, 0, 0, 0, 0];
    memcpy(
        f2_copy1.as_mut_ptr() as *mut libc::c_void,
        y3 as *const libc::c_void,
        (5 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    Hacl_K256_Field_fadd(y3, tmp1, f2_copy1.as_mut_ptr());
    let mut f_copy3: [uint64_t; 5] = [0 as libc::c_uint as uint64_t, 0, 0, 0, 0];
    memcpy(
        f_copy3.as_mut_ptr() as *mut libc::c_void,
        y3 as *const libc::c_void,
        (5 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    Hacl_K256_Field_fnormalize_weak(y3, f_copy3.as_mut_ptr());
}
#[no_mangle]
pub unsafe extern "C" fn Hacl_Impl_K256_PointAdd_point_add(
    mut out: *mut uint64_t,
    mut p: *mut uint64_t,
    mut q: *mut uint64_t,
) {
    let mut tmp: [uint64_t; 45] = [
        0 as libc::c_uint as uint64_t,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
    ];
    let mut x1: *mut uint64_t = p;
    let mut y1: *mut uint64_t = p.offset(5 as libc::c_uint as isize);
    let mut z1: *mut uint64_t = p.offset(10 as libc::c_uint as isize);
    let mut x2: *mut uint64_t = q;
    let mut y2: *mut uint64_t = q.offset(5 as libc::c_uint as isize);
    let mut z2: *mut uint64_t = q.offset(10 as libc::c_uint as isize);
    let mut x3: *mut uint64_t = out;
    let mut y3: *mut uint64_t = out.offset(5 as libc::c_uint as isize);
    let mut z3: *mut uint64_t = out.offset(10 as libc::c_uint as isize);
    let mut xx: *mut uint64_t = tmp.as_mut_ptr();
    let mut yy: *mut uint64_t = tmp.as_mut_ptr().offset(5 as libc::c_uint as isize);
    let mut zz: *mut uint64_t = tmp.as_mut_ptr().offset(10 as libc::c_uint as isize);
    let mut xy_pairs: *mut uint64_t = tmp
        .as_mut_ptr()
        .offset(15 as libc::c_uint as isize);
    let mut yz_pairs: *mut uint64_t = tmp
        .as_mut_ptr()
        .offset(20 as libc::c_uint as isize);
    let mut xz_pairs: *mut uint64_t = tmp
        .as_mut_ptr()
        .offset(25 as libc::c_uint as isize);
    let mut yy_m_bzz3: *mut uint64_t = tmp
        .as_mut_ptr()
        .offset(30 as libc::c_uint as isize);
    let mut yy_p_bzz3: *mut uint64_t = tmp
        .as_mut_ptr()
        .offset(35 as libc::c_uint as isize);
    let mut tmp1: *mut uint64_t = tmp.as_mut_ptr().offset(40 as libc::c_uint as isize);
    Hacl_K256_Field_fmul(xx, x1, x2);
    Hacl_K256_Field_fmul(yy, y1, y2);
    Hacl_K256_Field_fmul(zz, z1, z2);
    Hacl_K256_Field_fadd(xy_pairs, x1, y1);
    Hacl_K256_Field_fadd(tmp1, x2, y2);
    let mut f1_copy: [uint64_t; 5] = [0 as libc::c_uint as uint64_t, 0, 0, 0, 0];
    memcpy(
        f1_copy.as_mut_ptr() as *mut libc::c_void,
        xy_pairs as *const libc::c_void,
        (5 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    Hacl_K256_Field_fmul(xy_pairs, f1_copy.as_mut_ptr(), tmp1);
    Hacl_K256_Field_fadd(tmp1, xx, yy);
    let mut f1_copy0: [uint64_t; 5] = [0 as libc::c_uint as uint64_t, 0, 0, 0, 0];
    memcpy(
        f1_copy0.as_mut_ptr() as *mut libc::c_void,
        xy_pairs as *const libc::c_void,
        (5 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    Hacl_K256_Field_fsub(xy_pairs, f1_copy0.as_mut_ptr(), tmp1, 4 as libc::c_ulonglong);
    Hacl_K256_Field_fadd(yz_pairs, y1, z1);
    Hacl_K256_Field_fadd(tmp1, y2, z2);
    let mut f1_copy1: [uint64_t; 5] = [0 as libc::c_uint as uint64_t, 0, 0, 0, 0];
    memcpy(
        f1_copy1.as_mut_ptr() as *mut libc::c_void,
        yz_pairs as *const libc::c_void,
        (5 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    Hacl_K256_Field_fmul(yz_pairs, f1_copy1.as_mut_ptr(), tmp1);
    Hacl_K256_Field_fadd(tmp1, yy, zz);
    let mut f1_copy2: [uint64_t; 5] = [0 as libc::c_uint as uint64_t, 0, 0, 0, 0];
    memcpy(
        f1_copy2.as_mut_ptr() as *mut libc::c_void,
        yz_pairs as *const libc::c_void,
        (5 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    Hacl_K256_Field_fsub(yz_pairs, f1_copy2.as_mut_ptr(), tmp1, 4 as libc::c_ulonglong);
    Hacl_K256_Field_fadd(xz_pairs, x1, z1);
    Hacl_K256_Field_fadd(tmp1, x2, z2);
    let mut f1_copy3: [uint64_t; 5] = [0 as libc::c_uint as uint64_t, 0, 0, 0, 0];
    memcpy(
        f1_copy3.as_mut_ptr() as *mut libc::c_void,
        xz_pairs as *const libc::c_void,
        (5 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    Hacl_K256_Field_fmul(xz_pairs, f1_copy3.as_mut_ptr(), tmp1);
    Hacl_K256_Field_fadd(tmp1, xx, zz);
    let mut f1_copy4: [uint64_t; 5] = [0 as libc::c_uint as uint64_t, 0, 0, 0, 0];
    memcpy(
        f1_copy4.as_mut_ptr() as *mut libc::c_void,
        xz_pairs as *const libc::c_void,
        (5 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    Hacl_K256_Field_fsub(xz_pairs, f1_copy4.as_mut_ptr(), tmp1, 4 as libc::c_ulonglong);
    Hacl_K256_Field_fmul_small_num(tmp1, zz, 21 as libc::c_ulonglong);
    let mut f_copy: [uint64_t; 5] = [0 as libc::c_uint as uint64_t, 0, 0, 0, 0];
    memcpy(
        f_copy.as_mut_ptr() as *mut libc::c_void,
        tmp1 as *const libc::c_void,
        (5 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    Hacl_K256_Field_fnormalize_weak(tmp1, f_copy.as_mut_ptr());
    Hacl_K256_Field_fsub(yy_m_bzz3, yy, tmp1, 2 as libc::c_ulonglong);
    Hacl_K256_Field_fadd(yy_p_bzz3, yy, tmp1);
    Hacl_K256_Field_fmul_small_num(x3, yz_pairs, 21 as libc::c_ulonglong);
    let mut f_copy0: [uint64_t; 5] = [0 as libc::c_uint as uint64_t, 0, 0, 0, 0];
    memcpy(
        f_copy0.as_mut_ptr() as *mut libc::c_void,
        x3 as *const libc::c_void,
        (5 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    Hacl_K256_Field_fnormalize_weak(x3, f_copy0.as_mut_ptr());
    Hacl_K256_Field_fmul_small_num(z3, xx, 3 as libc::c_ulonglong);
    Hacl_K256_Field_fmul_small_num(y3, z3, 21 as libc::c_ulonglong);
    let mut f_copy1: [uint64_t; 5] = [0 as libc::c_uint as uint64_t, 0, 0, 0, 0];
    memcpy(
        f_copy1.as_mut_ptr() as *mut libc::c_void,
        y3 as *const libc::c_void,
        (5 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    Hacl_K256_Field_fnormalize_weak(y3, f_copy1.as_mut_ptr());
    Hacl_K256_Field_fmul(tmp1, xy_pairs, yy_m_bzz3);
    let mut f1_copy5: [uint64_t; 5] = [0 as libc::c_uint as uint64_t, 0, 0, 0, 0];
    memcpy(
        f1_copy5.as_mut_ptr() as *mut libc::c_void,
        x3 as *const libc::c_void,
        (5 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    Hacl_K256_Field_fmul(x3, f1_copy5.as_mut_ptr(), xz_pairs);
    let mut f2_copy: [uint64_t; 5] = [0 as libc::c_uint as uint64_t, 0, 0, 0, 0];
    memcpy(
        f2_copy.as_mut_ptr() as *mut libc::c_void,
        x3 as *const libc::c_void,
        (5 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    Hacl_K256_Field_fsub(x3, tmp1, f2_copy.as_mut_ptr(), 2 as libc::c_ulonglong);
    let mut f_copy2: [uint64_t; 5] = [0 as libc::c_uint as uint64_t, 0, 0, 0, 0];
    memcpy(
        f_copy2.as_mut_ptr() as *mut libc::c_void,
        x3 as *const libc::c_void,
        (5 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    Hacl_K256_Field_fnormalize_weak(x3, f_copy2.as_mut_ptr());
    Hacl_K256_Field_fmul(tmp1, yy_p_bzz3, yy_m_bzz3);
    let mut f1_copy6: [uint64_t; 5] = [0 as libc::c_uint as uint64_t, 0, 0, 0, 0];
    memcpy(
        f1_copy6.as_mut_ptr() as *mut libc::c_void,
        y3 as *const libc::c_void,
        (5 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    Hacl_K256_Field_fmul(y3, f1_copy6.as_mut_ptr(), xz_pairs);
    let mut f2_copy0: [uint64_t; 5] = [0 as libc::c_uint as uint64_t, 0, 0, 0, 0];
    memcpy(
        f2_copy0.as_mut_ptr() as *mut libc::c_void,
        y3 as *const libc::c_void,
        (5 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    Hacl_K256_Field_fadd(y3, tmp1, f2_copy0.as_mut_ptr());
    let mut f_copy3: [uint64_t; 5] = [0 as libc::c_uint as uint64_t, 0, 0, 0, 0];
    memcpy(
        f_copy3.as_mut_ptr() as *mut libc::c_void,
        y3 as *const libc::c_void,
        (5 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    Hacl_K256_Field_fnormalize_weak(y3, f_copy3.as_mut_ptr());
    Hacl_K256_Field_fmul(tmp1, yz_pairs, yy_p_bzz3);
    let mut f1_copy7: [uint64_t; 5] = [0 as libc::c_uint as uint64_t, 0, 0, 0, 0];
    memcpy(
        f1_copy7.as_mut_ptr() as *mut libc::c_void,
        z3 as *const libc::c_void,
        (5 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    Hacl_K256_Field_fmul(z3, f1_copy7.as_mut_ptr(), xy_pairs);
    let mut f2_copy1: [uint64_t; 5] = [0 as libc::c_uint as uint64_t, 0, 0, 0, 0];
    memcpy(
        f2_copy1.as_mut_ptr() as *mut libc::c_void,
        z3 as *const libc::c_void,
        (5 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    Hacl_K256_Field_fadd(z3, tmp1, f2_copy1.as_mut_ptr());
    let mut f_copy4: [uint64_t; 5] = [0 as libc::c_uint as uint64_t, 0, 0, 0, 0];
    memcpy(
        f_copy4.as_mut_ptr() as *mut libc::c_void,
        z3 as *const libc::c_void,
        (5 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    Hacl_K256_Field_fnormalize_weak(z3, f_copy4.as_mut_ptr());
}
#[inline]
unsafe extern "C" fn scalar_split_lambda(
    mut r1: *mut uint64_t,
    mut r2: *mut uint64_t,
    mut k: *mut uint64_t,
) {
    let mut tmp1: [uint64_t; 4] = [0 as libc::c_uint as uint64_t, 0, 0, 0];
    let mut tmp2: [uint64_t; 4] = [0 as libc::c_uint as uint64_t, 0, 0, 0];
    tmp1[0 as libc::c_uint as usize] = 0xe893209a45dbb031 as libc::c_ulonglong;
    tmp1[1 as libc::c_uint as usize] = 0x3daa8a1471e8ca7f as libc::c_ulonglong;
    tmp1[2 as libc::c_uint as usize] = 0xe86c90e49284eb15 as libc::c_ulonglong;
    tmp1[3 as libc::c_uint as usize] = 0x3086d221a7d46bcd as libc::c_ulonglong;
    tmp2[0 as libc::c_uint as usize] = 0x1571b4ae8ac47f71 as libc::c_ulonglong;
    tmp2[1 as libc::c_uint as usize] = 0x221208ac9df506c6 as libc::c_ulonglong;
    tmp2[2 as libc::c_uint as usize] = 0x6f547fa90abfe4c4 as libc::c_ulonglong;
    tmp2[3 as libc::c_uint as usize] = 0xe4437ed6010e8828 as libc::c_ulonglong;
    qmul_shift_384(r1, k, tmp1.as_mut_ptr());
    qmul_shift_384(r2, k, tmp2.as_mut_ptr());
    tmp1[0 as libc::c_uint as usize] = 0x6f547fa90abfe4c3 as libc::c_ulonglong;
    tmp1[1 as libc::c_uint as usize] = 0xe4437ed6010e8828 as libc::c_ulonglong;
    tmp1[2 as libc::c_uint as usize] = 0 as libc::c_ulonglong;
    tmp1[3 as libc::c_uint as usize] = 0 as libc::c_ulonglong;
    tmp2[0 as libc::c_uint as usize] = 0xd765cda83db1562c as libc::c_ulonglong;
    tmp2[1 as libc::c_uint as usize] = 0x8a280ac50774346d as libc::c_ulonglong;
    tmp2[2 as libc::c_uint as usize] = 0xfffffffffffffffe as libc::c_ulonglong;
    tmp2[3 as libc::c_uint as usize] = 0xffffffffffffffff as libc::c_ulonglong;
    let mut f1_copy: [uint64_t; 4] = [0 as libc::c_uint as uint64_t, 0, 0, 0];
    memcpy(
        f1_copy.as_mut_ptr() as *mut libc::c_void,
        r1 as *const libc::c_void,
        (4 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    qmul(r1, f1_copy.as_mut_ptr(), tmp1.as_mut_ptr());
    let mut f1_copy0: [uint64_t; 4] = [0 as libc::c_uint as uint64_t, 0, 0, 0];
    memcpy(
        f1_copy0.as_mut_ptr() as *mut libc::c_void,
        r2 as *const libc::c_void,
        (4 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    qmul(r2, f1_copy0.as_mut_ptr(), tmp2.as_mut_ptr());
    tmp1[0 as libc::c_uint as usize] = 0xe0cfc810b51283cf as libc::c_ulonglong;
    tmp1[1 as libc::c_uint as usize] = 0xa880b9fc8ec739c2 as libc::c_ulonglong;
    tmp1[2 as libc::c_uint as usize] = 0x5ad9e3fd77ed9ba4 as libc::c_ulonglong;
    tmp1[3 as libc::c_uint as usize] = 0xac9c52b33fa3cf1f as libc::c_ulonglong;
    let mut f2_copy: [uint64_t; 4] = [0 as libc::c_uint as uint64_t, 0, 0, 0];
    memcpy(
        f2_copy.as_mut_ptr() as *mut libc::c_void,
        r2 as *const libc::c_void,
        (4 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    qadd(r2, r1, f2_copy.as_mut_ptr());
    qmul(tmp2.as_mut_ptr(), r2, tmp1.as_mut_ptr());
    qadd(r1, k, tmp2.as_mut_ptr());
}
#[inline]
unsafe extern "C" fn point_mul_lambda(mut res: *mut uint64_t, mut p: *mut uint64_t) {
    let mut rx: *mut uint64_t = res;
    let mut ry: *mut uint64_t = res.offset(5 as libc::c_uint as isize);
    let mut rz: *mut uint64_t = res.offset(10 as libc::c_uint as isize);
    let mut px: *mut uint64_t = p;
    let mut py: *mut uint64_t = p.offset(5 as libc::c_uint as isize);
    let mut pz: *mut uint64_t = p.offset(10 as libc::c_uint as isize);
    let mut beta: [uint64_t; 5] = [0 as libc::c_uint as uint64_t, 0, 0, 0, 0];
    beta[0 as libc::c_uint as usize] = 0x96c28719501ee as libc::c_ulonglong;
    beta[1 as libc::c_uint as usize] = 0x7512f58995c13 as libc::c_ulonglong;
    beta[2 as libc::c_uint as usize] = 0xc3434e99cf049 as libc::c_ulonglong;
    beta[3 as libc::c_uint as usize] = 0x7106e64479ea as libc::c_ulonglong;
    beta[4 as libc::c_uint as usize] = 0x7ae96a2b657c as libc::c_ulonglong;
    Hacl_K256_Field_fmul(rx, beta.as_mut_ptr(), px);
    *ry.offset(0 as libc::c_uint as isize) = *py.offset(0 as libc::c_uint as isize);
    *ry.offset(1 as libc::c_uint as isize) = *py.offset(1 as libc::c_uint as isize);
    *ry.offset(2 as libc::c_uint as isize) = *py.offset(2 as libc::c_uint as isize);
    *ry.offset(3 as libc::c_uint as isize) = *py.offset(3 as libc::c_uint as isize);
    *ry.offset(4 as libc::c_uint as isize) = *py.offset(4 as libc::c_uint as isize);
    *rz.offset(0 as libc::c_uint as isize) = *pz.offset(0 as libc::c_uint as isize);
    *rz.offset(1 as libc::c_uint as isize) = *pz.offset(1 as libc::c_uint as isize);
    *rz.offset(2 as libc::c_uint as isize) = *pz.offset(2 as libc::c_uint as isize);
    *rz.offset(3 as libc::c_uint as isize) = *pz.offset(3 as libc::c_uint as isize);
    *rz.offset(4 as libc::c_uint as isize) = *pz.offset(4 as libc::c_uint as isize);
}
#[inline]
unsafe extern "C" fn point_mul_lambda_inplace(mut res: *mut uint64_t) {
    let mut rx: *mut uint64_t = res;
    let mut beta: [uint64_t; 5] = [0 as libc::c_uint as uint64_t, 0, 0, 0, 0];
    beta[0 as libc::c_uint as usize] = 0x96c28719501ee as libc::c_ulonglong;
    beta[1 as libc::c_uint as usize] = 0x7512f58995c13 as libc::c_ulonglong;
    beta[2 as libc::c_uint as usize] = 0xc3434e99cf049 as libc::c_ulonglong;
    beta[3 as libc::c_uint as usize] = 0x7106e64479ea as libc::c_ulonglong;
    beta[4 as libc::c_uint as usize] = 0x7ae96a2b657c as libc::c_ulonglong;
    let mut f2_copy: [uint64_t; 5] = [0 as libc::c_uint as uint64_t, 0, 0, 0, 0];
    memcpy(
        f2_copy.as_mut_ptr() as *mut libc::c_void,
        rx as *const libc::c_void,
        (5 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    Hacl_K256_Field_fmul(rx, beta.as_mut_ptr(), f2_copy.as_mut_ptr());
}
#[inline]
unsafe extern "C" fn ecmult_endo_split(
    mut r1: *mut uint64_t,
    mut r2: *mut uint64_t,
    mut q1: *mut uint64_t,
    mut q2: *mut uint64_t,
    mut scalar: *mut uint64_t,
    mut q: *mut uint64_t,
) -> __bool_bool {
    scalar_split_lambda(r1, r2, scalar);
    point_mul_lambda(q2, q);
    memcpy(
        q1 as *mut libc::c_void,
        q as *const libc::c_void,
        (15 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    let mut b0: bool = is_qelem_le_q_halved_vartime(r1);
    qnegate_conditional_vartime(r1, !b0);
    point_negate_conditional_vartime(q1, !b0);
    let mut is_high1: bool = !b0;
    let mut b: bool = is_qelem_le_q_halved_vartime(r2);
    qnegate_conditional_vartime(r2, !b);
    point_negate_conditional_vartime(q2, !b);
    let mut is_high2: bool = !b;
    return {
        let mut init = __bool_bool_s {
            fst: is_high1,
            snd: is_high2,
        };
        init
    };
}
#[no_mangle]
pub unsafe extern "C" fn Hacl_Impl_K256_PointMul_point_mul(
    mut out: *mut uint64_t,
    mut scalar: *mut uint64_t,
    mut q: *mut uint64_t,
) {
    let mut table: [uint64_t; 240] = [
        0 as libc::c_uint as uint64_t,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
    ];
    let mut tmp: [uint64_t; 15] = [
        0 as libc::c_uint as uint64_t,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
    ];
    let mut t0: *mut uint64_t = table.as_mut_ptr();
    let mut t1: *mut uint64_t = table.as_mut_ptr().offset(15 as libc::c_uint as isize);
    Hacl_Impl_K256_Point_make_point_at_inf(t0);
    memcpy(
        t1 as *mut libc::c_void,
        q as *const libc::c_void,
        (15 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    let mut i: uint32_t = 0 as libc::c_uint;
    let mut t11: *mut uint64_t = table
        .as_mut_ptr()
        .offset(
            i.wrapping_add(1 as libc::c_uint).wrapping_mul(15 as libc::c_uint) as isize,
        );
    let mut p_copy0: [uint64_t; 15] = [
        0 as libc::c_uint as uint64_t,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
    ];
    memcpy(
        p_copy0.as_mut_ptr() as *mut libc::c_void,
        t11 as *const libc::c_void,
        (15 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    Hacl_Impl_K256_PointDouble_point_double(tmp.as_mut_ptr(), p_copy0.as_mut_ptr());
    memcpy(
        table
            .as_mut_ptr()
            .offset(
                (2 as libc::c_uint)
                    .wrapping_mul(i)
                    .wrapping_add(2 as libc::c_uint)
                    .wrapping_mul(15 as libc::c_uint) as isize,
            ) as *mut libc::c_void,
        tmp.as_mut_ptr() as *const libc::c_void,
        (15 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    let mut t2: *mut uint64_t = table
        .as_mut_ptr()
        .offset(
            (2 as libc::c_uint)
                .wrapping_mul(i)
                .wrapping_add(2 as libc::c_uint)
                .wrapping_mul(15 as libc::c_uint) as isize,
        );
    let mut p_copy: [uint64_t; 15] = [
        0 as libc::c_uint as uint64_t,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
    ];
    memcpy(
        p_copy.as_mut_ptr() as *mut libc::c_void,
        q as *const libc::c_void,
        (15 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    Hacl_Impl_K256_PointAdd_point_add(tmp.as_mut_ptr(), p_copy.as_mut_ptr(), t2);
    memcpy(
        table
            .as_mut_ptr()
            .offset(
                (2 as libc::c_uint)
                    .wrapping_mul(i)
                    .wrapping_add(3 as libc::c_uint)
                    .wrapping_mul(15 as libc::c_uint) as isize,
            ) as *mut libc::c_void,
        tmp.as_mut_ptr() as *const libc::c_void,
        (15 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    i = (i as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut t11_0: *mut uint64_t = table
        .as_mut_ptr()
        .offset(
            i.wrapping_add(1 as libc::c_uint).wrapping_mul(15 as libc::c_uint) as isize,
        );
    let mut p_copy0_0: [uint64_t; 15] = [
        0 as libc::c_uint as uint64_t,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
    ];
    memcpy(
        p_copy0_0.as_mut_ptr() as *mut libc::c_void,
        t11_0 as *const libc::c_void,
        (15 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    Hacl_Impl_K256_PointDouble_point_double(tmp.as_mut_ptr(), p_copy0_0.as_mut_ptr());
    memcpy(
        table
            .as_mut_ptr()
            .offset(
                (2 as libc::c_uint)
                    .wrapping_mul(i)
                    .wrapping_add(2 as libc::c_uint)
                    .wrapping_mul(15 as libc::c_uint) as isize,
            ) as *mut libc::c_void,
        tmp.as_mut_ptr() as *const libc::c_void,
        (15 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    let mut t2_0: *mut uint64_t = table
        .as_mut_ptr()
        .offset(
            (2 as libc::c_uint)
                .wrapping_mul(i)
                .wrapping_add(2 as libc::c_uint)
                .wrapping_mul(15 as libc::c_uint) as isize,
        );
    let mut p_copy_0: [uint64_t; 15] = [
        0 as libc::c_uint as uint64_t,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
    ];
    memcpy(
        p_copy_0.as_mut_ptr() as *mut libc::c_void,
        q as *const libc::c_void,
        (15 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    Hacl_Impl_K256_PointAdd_point_add(tmp.as_mut_ptr(), p_copy_0.as_mut_ptr(), t2_0);
    memcpy(
        table
            .as_mut_ptr()
            .offset(
                (2 as libc::c_uint)
                    .wrapping_mul(i)
                    .wrapping_add(3 as libc::c_uint)
                    .wrapping_mul(15 as libc::c_uint) as isize,
            ) as *mut libc::c_void,
        tmp.as_mut_ptr() as *const libc::c_void,
        (15 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    i = (i as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut t11_1: *mut uint64_t = table
        .as_mut_ptr()
        .offset(
            i.wrapping_add(1 as libc::c_uint).wrapping_mul(15 as libc::c_uint) as isize,
        );
    let mut p_copy0_1: [uint64_t; 15] = [
        0 as libc::c_uint as uint64_t,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
    ];
    memcpy(
        p_copy0_1.as_mut_ptr() as *mut libc::c_void,
        t11_1 as *const libc::c_void,
        (15 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    Hacl_Impl_K256_PointDouble_point_double(tmp.as_mut_ptr(), p_copy0_1.as_mut_ptr());
    memcpy(
        table
            .as_mut_ptr()
            .offset(
                (2 as libc::c_uint)
                    .wrapping_mul(i)
                    .wrapping_add(2 as libc::c_uint)
                    .wrapping_mul(15 as libc::c_uint) as isize,
            ) as *mut libc::c_void,
        tmp.as_mut_ptr() as *const libc::c_void,
        (15 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    let mut t2_1: *mut uint64_t = table
        .as_mut_ptr()
        .offset(
            (2 as libc::c_uint)
                .wrapping_mul(i)
                .wrapping_add(2 as libc::c_uint)
                .wrapping_mul(15 as libc::c_uint) as isize,
        );
    let mut p_copy_1: [uint64_t; 15] = [
        0 as libc::c_uint as uint64_t,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
    ];
    memcpy(
        p_copy_1.as_mut_ptr() as *mut libc::c_void,
        q as *const libc::c_void,
        (15 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    Hacl_Impl_K256_PointAdd_point_add(tmp.as_mut_ptr(), p_copy_1.as_mut_ptr(), t2_1);
    memcpy(
        table
            .as_mut_ptr()
            .offset(
                (2 as libc::c_uint)
                    .wrapping_mul(i)
                    .wrapping_add(3 as libc::c_uint)
                    .wrapping_mul(15 as libc::c_uint) as isize,
            ) as *mut libc::c_void,
        tmp.as_mut_ptr() as *const libc::c_void,
        (15 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    i = (i as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut t11_2: *mut uint64_t = table
        .as_mut_ptr()
        .offset(
            i.wrapping_add(1 as libc::c_uint).wrapping_mul(15 as libc::c_uint) as isize,
        );
    let mut p_copy0_2: [uint64_t; 15] = [
        0 as libc::c_uint as uint64_t,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
    ];
    memcpy(
        p_copy0_2.as_mut_ptr() as *mut libc::c_void,
        t11_2 as *const libc::c_void,
        (15 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    Hacl_Impl_K256_PointDouble_point_double(tmp.as_mut_ptr(), p_copy0_2.as_mut_ptr());
    memcpy(
        table
            .as_mut_ptr()
            .offset(
                (2 as libc::c_uint)
                    .wrapping_mul(i)
                    .wrapping_add(2 as libc::c_uint)
                    .wrapping_mul(15 as libc::c_uint) as isize,
            ) as *mut libc::c_void,
        tmp.as_mut_ptr() as *const libc::c_void,
        (15 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    let mut t2_2: *mut uint64_t = table
        .as_mut_ptr()
        .offset(
            (2 as libc::c_uint)
                .wrapping_mul(i)
                .wrapping_add(2 as libc::c_uint)
                .wrapping_mul(15 as libc::c_uint) as isize,
        );
    let mut p_copy_2: [uint64_t; 15] = [
        0 as libc::c_uint as uint64_t,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
    ];
    memcpy(
        p_copy_2.as_mut_ptr() as *mut libc::c_void,
        q as *const libc::c_void,
        (15 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    Hacl_Impl_K256_PointAdd_point_add(tmp.as_mut_ptr(), p_copy_2.as_mut_ptr(), t2_2);
    memcpy(
        table
            .as_mut_ptr()
            .offset(
                (2 as libc::c_uint)
                    .wrapping_mul(i)
                    .wrapping_add(3 as libc::c_uint)
                    .wrapping_mul(15 as libc::c_uint) as isize,
            ) as *mut libc::c_void,
        tmp.as_mut_ptr() as *const libc::c_void,
        (15 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    i = (i as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut t11_3: *mut uint64_t = table
        .as_mut_ptr()
        .offset(
            i.wrapping_add(1 as libc::c_uint).wrapping_mul(15 as libc::c_uint) as isize,
        );
    let mut p_copy0_3: [uint64_t; 15] = [
        0 as libc::c_uint as uint64_t,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
    ];
    memcpy(
        p_copy0_3.as_mut_ptr() as *mut libc::c_void,
        t11_3 as *const libc::c_void,
        (15 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    Hacl_Impl_K256_PointDouble_point_double(tmp.as_mut_ptr(), p_copy0_3.as_mut_ptr());
    memcpy(
        table
            .as_mut_ptr()
            .offset(
                (2 as libc::c_uint)
                    .wrapping_mul(i)
                    .wrapping_add(2 as libc::c_uint)
                    .wrapping_mul(15 as libc::c_uint) as isize,
            ) as *mut libc::c_void,
        tmp.as_mut_ptr() as *const libc::c_void,
        (15 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    let mut t2_3: *mut uint64_t = table
        .as_mut_ptr()
        .offset(
            (2 as libc::c_uint)
                .wrapping_mul(i)
                .wrapping_add(2 as libc::c_uint)
                .wrapping_mul(15 as libc::c_uint) as isize,
        );
    let mut p_copy_3: [uint64_t; 15] = [
        0 as libc::c_uint as uint64_t,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
    ];
    memcpy(
        p_copy_3.as_mut_ptr() as *mut libc::c_void,
        q as *const libc::c_void,
        (15 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    Hacl_Impl_K256_PointAdd_point_add(tmp.as_mut_ptr(), p_copy_3.as_mut_ptr(), t2_3);
    memcpy(
        table
            .as_mut_ptr()
            .offset(
                (2 as libc::c_uint)
                    .wrapping_mul(i)
                    .wrapping_add(3 as libc::c_uint)
                    .wrapping_mul(15 as libc::c_uint) as isize,
            ) as *mut libc::c_void,
        tmp.as_mut_ptr() as *const libc::c_void,
        (15 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    i = (i as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut t11_4: *mut uint64_t = table
        .as_mut_ptr()
        .offset(
            i.wrapping_add(1 as libc::c_uint).wrapping_mul(15 as libc::c_uint) as isize,
        );
    let mut p_copy0_4: [uint64_t; 15] = [
        0 as libc::c_uint as uint64_t,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
    ];
    memcpy(
        p_copy0_4.as_mut_ptr() as *mut libc::c_void,
        t11_4 as *const libc::c_void,
        (15 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    Hacl_Impl_K256_PointDouble_point_double(tmp.as_mut_ptr(), p_copy0_4.as_mut_ptr());
    memcpy(
        table
            .as_mut_ptr()
            .offset(
                (2 as libc::c_uint)
                    .wrapping_mul(i)
                    .wrapping_add(2 as libc::c_uint)
                    .wrapping_mul(15 as libc::c_uint) as isize,
            ) as *mut libc::c_void,
        tmp.as_mut_ptr() as *const libc::c_void,
        (15 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    let mut t2_4: *mut uint64_t = table
        .as_mut_ptr()
        .offset(
            (2 as libc::c_uint)
                .wrapping_mul(i)
                .wrapping_add(2 as libc::c_uint)
                .wrapping_mul(15 as libc::c_uint) as isize,
        );
    let mut p_copy_4: [uint64_t; 15] = [
        0 as libc::c_uint as uint64_t,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
    ];
    memcpy(
        p_copy_4.as_mut_ptr() as *mut libc::c_void,
        q as *const libc::c_void,
        (15 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    Hacl_Impl_K256_PointAdd_point_add(tmp.as_mut_ptr(), p_copy_4.as_mut_ptr(), t2_4);
    memcpy(
        table
            .as_mut_ptr()
            .offset(
                (2 as libc::c_uint)
                    .wrapping_mul(i)
                    .wrapping_add(3 as libc::c_uint)
                    .wrapping_mul(15 as libc::c_uint) as isize,
            ) as *mut libc::c_void,
        tmp.as_mut_ptr() as *const libc::c_void,
        (15 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    i = (i as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut t11_5: *mut uint64_t = table
        .as_mut_ptr()
        .offset(
            i.wrapping_add(1 as libc::c_uint).wrapping_mul(15 as libc::c_uint) as isize,
        );
    let mut p_copy0_5: [uint64_t; 15] = [
        0 as libc::c_uint as uint64_t,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
    ];
    memcpy(
        p_copy0_5.as_mut_ptr() as *mut libc::c_void,
        t11_5 as *const libc::c_void,
        (15 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    Hacl_Impl_K256_PointDouble_point_double(tmp.as_mut_ptr(), p_copy0_5.as_mut_ptr());
    memcpy(
        table
            .as_mut_ptr()
            .offset(
                (2 as libc::c_uint)
                    .wrapping_mul(i)
                    .wrapping_add(2 as libc::c_uint)
                    .wrapping_mul(15 as libc::c_uint) as isize,
            ) as *mut libc::c_void,
        tmp.as_mut_ptr() as *const libc::c_void,
        (15 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    let mut t2_5: *mut uint64_t = table
        .as_mut_ptr()
        .offset(
            (2 as libc::c_uint)
                .wrapping_mul(i)
                .wrapping_add(2 as libc::c_uint)
                .wrapping_mul(15 as libc::c_uint) as isize,
        );
    let mut p_copy_5: [uint64_t; 15] = [
        0 as libc::c_uint as uint64_t,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
    ];
    memcpy(
        p_copy_5.as_mut_ptr() as *mut libc::c_void,
        q as *const libc::c_void,
        (15 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    Hacl_Impl_K256_PointAdd_point_add(tmp.as_mut_ptr(), p_copy_5.as_mut_ptr(), t2_5);
    memcpy(
        table
            .as_mut_ptr()
            .offset(
                (2 as libc::c_uint)
                    .wrapping_mul(i)
                    .wrapping_add(3 as libc::c_uint)
                    .wrapping_mul(15 as libc::c_uint) as isize,
            ) as *mut libc::c_void,
        tmp.as_mut_ptr() as *const libc::c_void,
        (15 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    i = (i as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    Hacl_Impl_K256_Point_make_point_at_inf(out);
    let mut tmp0: [uint64_t; 15] = [
        0 as libc::c_uint as uint64_t,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
    ];
    let mut i0: uint32_t = 0 as libc::c_uint;
    while i0 < 64 as libc::c_uint {
        let mut i_0: uint32_t = 0 as libc::c_uint;
        let mut p_copy_6: [uint64_t; 15] = [
            0 as libc::c_uint as uint64_t,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
        ];
        memcpy(
            p_copy_6.as_mut_ptr() as *mut libc::c_void,
            out as *const libc::c_void,
            (15 as libc::c_uint as libc::c_ulong)
                .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
        );
        Hacl_Impl_K256_PointDouble_point_double(out, p_copy_6.as_mut_ptr());
        i_0 = (i_0 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut p_copy_7: [uint64_t; 15] = [
            0 as libc::c_uint as uint64_t,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
        ];
        memcpy(
            p_copy_7.as_mut_ptr() as *mut libc::c_void,
            out as *const libc::c_void,
            (15 as libc::c_uint as libc::c_ulong)
                .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
        );
        Hacl_Impl_K256_PointDouble_point_double(out, p_copy_7.as_mut_ptr());
        i_0 = (i_0 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut p_copy_8: [uint64_t; 15] = [
            0 as libc::c_uint as uint64_t,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
        ];
        memcpy(
            p_copy_8.as_mut_ptr() as *mut libc::c_void,
            out as *const libc::c_void,
            (15 as libc::c_uint as libc::c_ulong)
                .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
        );
        Hacl_Impl_K256_PointDouble_point_double(out, p_copy_8.as_mut_ptr());
        i_0 = (i_0 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut p_copy_9: [uint64_t; 15] = [
            0 as libc::c_uint as uint64_t,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
        ];
        memcpy(
            p_copy_9.as_mut_ptr() as *mut libc::c_void,
            out as *const libc::c_void,
            (15 as libc::c_uint as libc::c_ulong)
                .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
        );
        Hacl_Impl_K256_PointDouble_point_double(out, p_copy_9.as_mut_ptr());
        i_0 = (i_0 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut k: uint32_t = (256 as libc::c_uint)
            .wrapping_sub((4 as libc::c_uint).wrapping_mul(i0))
            .wrapping_sub(4 as libc::c_uint);
        let mut bits_l: uint64_t = Hacl_Bignum_Lib_bn_get_bits_u64(
            4 as libc::c_uint,
            scalar,
            k,
            4 as libc::c_uint,
        );
        memcpy(
            tmp0.as_mut_ptr() as *mut libc::c_void,
            table.as_mut_ptr() as *const libc::c_void,
            (15 as libc::c_uint as libc::c_ulong)
                .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
        );
        let mut i1: uint32_t = 0 as libc::c_uint;
        let mut c: uint64_t = FStar_UInt64_eq_mask(
            bits_l,
            i1.wrapping_add(1 as libc::c_uint) as uint64_t,
        );
        let mut res_j: *const uint64_t = table
            .as_mut_ptr()
            .offset(
                i1.wrapping_add(1 as libc::c_uint).wrapping_mul(15 as libc::c_uint)
                    as isize,
            );
        let mut i_1: uint32_t = 0 as libc::c_uint;
        let mut x: uint64_t = c & *res_j.offset(i_1 as isize) | !c & tmp0[i_1 as usize];
        let mut os: *mut uint64_t = tmp0.as_mut_ptr();
        *os.offset(i_1 as isize) = x;
        i_1 = (i_1 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_0: uint64_t = c & *res_j.offset(i_1 as isize)
            | !c & tmp0[i_1 as usize];
        let mut os_0: *mut uint64_t = tmp0.as_mut_ptr();
        *os_0.offset(i_1 as isize) = x_0;
        i_1 = (i_1 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_1: uint64_t = c & *res_j.offset(i_1 as isize)
            | !c & tmp0[i_1 as usize];
        let mut os_1: *mut uint64_t = tmp0.as_mut_ptr();
        *os_1.offset(i_1 as isize) = x_1;
        i_1 = (i_1 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_2: uint64_t = c & *res_j.offset(i_1 as isize)
            | !c & tmp0[i_1 as usize];
        let mut os_2: *mut uint64_t = tmp0.as_mut_ptr();
        *os_2.offset(i_1 as isize) = x_2;
        i_1 = (i_1 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_3: uint64_t = c & *res_j.offset(i_1 as isize)
            | !c & tmp0[i_1 as usize];
        let mut os_3: *mut uint64_t = tmp0.as_mut_ptr();
        *os_3.offset(i_1 as isize) = x_3;
        i_1 = (i_1 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_4: uint64_t = c & *res_j.offset(i_1 as isize)
            | !c & tmp0[i_1 as usize];
        let mut os_4: *mut uint64_t = tmp0.as_mut_ptr();
        *os_4.offset(i_1 as isize) = x_4;
        i_1 = (i_1 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_5: uint64_t = c & *res_j.offset(i_1 as isize)
            | !c & tmp0[i_1 as usize];
        let mut os_5: *mut uint64_t = tmp0.as_mut_ptr();
        *os_5.offset(i_1 as isize) = x_5;
        i_1 = (i_1 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_6: uint64_t = c & *res_j.offset(i_1 as isize)
            | !c & tmp0[i_1 as usize];
        let mut os_6: *mut uint64_t = tmp0.as_mut_ptr();
        *os_6.offset(i_1 as isize) = x_6;
        i_1 = (i_1 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_7: uint64_t = c & *res_j.offset(i_1 as isize)
            | !c & tmp0[i_1 as usize];
        let mut os_7: *mut uint64_t = tmp0.as_mut_ptr();
        *os_7.offset(i_1 as isize) = x_7;
        i_1 = (i_1 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_8: uint64_t = c & *res_j.offset(i_1 as isize)
            | !c & tmp0[i_1 as usize];
        let mut os_8: *mut uint64_t = tmp0.as_mut_ptr();
        *os_8.offset(i_1 as isize) = x_8;
        i_1 = (i_1 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_9: uint64_t = c & *res_j.offset(i_1 as isize)
            | !c & tmp0[i_1 as usize];
        let mut os_9: *mut uint64_t = tmp0.as_mut_ptr();
        *os_9.offset(i_1 as isize) = x_9;
        i_1 = (i_1 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_10: uint64_t = c & *res_j.offset(i_1 as isize)
            | !c & tmp0[i_1 as usize];
        let mut os_10: *mut uint64_t = tmp0.as_mut_ptr();
        *os_10.offset(i_1 as isize) = x_10;
        i_1 = (i_1 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_11: uint64_t = c & *res_j.offset(i_1 as isize)
            | !c & tmp0[i_1 as usize];
        let mut os_11: *mut uint64_t = tmp0.as_mut_ptr();
        *os_11.offset(i_1 as isize) = x_11;
        i_1 = (i_1 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_12: uint64_t = c & *res_j.offset(i_1 as isize)
            | !c & tmp0[i_1 as usize];
        let mut os_12: *mut uint64_t = tmp0.as_mut_ptr();
        *os_12.offset(i_1 as isize) = x_12;
        i_1 = (i_1 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_13: uint64_t = c & *res_j.offset(i_1 as isize)
            | !c & tmp0[i_1 as usize];
        let mut os_13: *mut uint64_t = tmp0.as_mut_ptr();
        *os_13.offset(i_1 as isize) = x_13;
        i_1 = (i_1 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        i1 = (i1 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut c_0: uint64_t = FStar_UInt64_eq_mask(
            bits_l,
            i1.wrapping_add(1 as libc::c_uint) as uint64_t,
        );
        let mut res_j_0: *const uint64_t = table
            .as_mut_ptr()
            .offset(
                i1.wrapping_add(1 as libc::c_uint).wrapping_mul(15 as libc::c_uint)
                    as isize,
            );
        let mut i_2: uint32_t = 0 as libc::c_uint;
        let mut x_14: uint64_t = c_0 & *res_j_0.offset(i_2 as isize)
            | !c_0 & tmp0[i_2 as usize];
        let mut os_14: *mut uint64_t = tmp0.as_mut_ptr();
        *os_14.offset(i_2 as isize) = x_14;
        i_2 = (i_2 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_15: uint64_t = c_0 & *res_j_0.offset(i_2 as isize)
            | !c_0 & tmp0[i_2 as usize];
        let mut os_15: *mut uint64_t = tmp0.as_mut_ptr();
        *os_15.offset(i_2 as isize) = x_15;
        i_2 = (i_2 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_16: uint64_t = c_0 & *res_j_0.offset(i_2 as isize)
            | !c_0 & tmp0[i_2 as usize];
        let mut os_16: *mut uint64_t = tmp0.as_mut_ptr();
        *os_16.offset(i_2 as isize) = x_16;
        i_2 = (i_2 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_17: uint64_t = c_0 & *res_j_0.offset(i_2 as isize)
            | !c_0 & tmp0[i_2 as usize];
        let mut os_17: *mut uint64_t = tmp0.as_mut_ptr();
        *os_17.offset(i_2 as isize) = x_17;
        i_2 = (i_2 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_18: uint64_t = c_0 & *res_j_0.offset(i_2 as isize)
            | !c_0 & tmp0[i_2 as usize];
        let mut os_18: *mut uint64_t = tmp0.as_mut_ptr();
        *os_18.offset(i_2 as isize) = x_18;
        i_2 = (i_2 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_19: uint64_t = c_0 & *res_j_0.offset(i_2 as isize)
            | !c_0 & tmp0[i_2 as usize];
        let mut os_19: *mut uint64_t = tmp0.as_mut_ptr();
        *os_19.offset(i_2 as isize) = x_19;
        i_2 = (i_2 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_20: uint64_t = c_0 & *res_j_0.offset(i_2 as isize)
            | !c_0 & tmp0[i_2 as usize];
        let mut os_20: *mut uint64_t = tmp0.as_mut_ptr();
        *os_20.offset(i_2 as isize) = x_20;
        i_2 = (i_2 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_21: uint64_t = c_0 & *res_j_0.offset(i_2 as isize)
            | !c_0 & tmp0[i_2 as usize];
        let mut os_21: *mut uint64_t = tmp0.as_mut_ptr();
        *os_21.offset(i_2 as isize) = x_21;
        i_2 = (i_2 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_22: uint64_t = c_0 & *res_j_0.offset(i_2 as isize)
            | !c_0 & tmp0[i_2 as usize];
        let mut os_22: *mut uint64_t = tmp0.as_mut_ptr();
        *os_22.offset(i_2 as isize) = x_22;
        i_2 = (i_2 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_23: uint64_t = c_0 & *res_j_0.offset(i_2 as isize)
            | !c_0 & tmp0[i_2 as usize];
        let mut os_23: *mut uint64_t = tmp0.as_mut_ptr();
        *os_23.offset(i_2 as isize) = x_23;
        i_2 = (i_2 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_24: uint64_t = c_0 & *res_j_0.offset(i_2 as isize)
            | !c_0 & tmp0[i_2 as usize];
        let mut os_24: *mut uint64_t = tmp0.as_mut_ptr();
        *os_24.offset(i_2 as isize) = x_24;
        i_2 = (i_2 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_25: uint64_t = c_0 & *res_j_0.offset(i_2 as isize)
            | !c_0 & tmp0[i_2 as usize];
        let mut os_25: *mut uint64_t = tmp0.as_mut_ptr();
        *os_25.offset(i_2 as isize) = x_25;
        i_2 = (i_2 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_26: uint64_t = c_0 & *res_j_0.offset(i_2 as isize)
            | !c_0 & tmp0[i_2 as usize];
        let mut os_26: *mut uint64_t = tmp0.as_mut_ptr();
        *os_26.offset(i_2 as isize) = x_26;
        i_2 = (i_2 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_27: uint64_t = c_0 & *res_j_0.offset(i_2 as isize)
            | !c_0 & tmp0[i_2 as usize];
        let mut os_27: *mut uint64_t = tmp0.as_mut_ptr();
        *os_27.offset(i_2 as isize) = x_27;
        i_2 = (i_2 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_28: uint64_t = c_0 & *res_j_0.offset(i_2 as isize)
            | !c_0 & tmp0[i_2 as usize];
        let mut os_28: *mut uint64_t = tmp0.as_mut_ptr();
        *os_28.offset(i_2 as isize) = x_28;
        i_2 = (i_2 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        i1 = (i1 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut c_1: uint64_t = FStar_UInt64_eq_mask(
            bits_l,
            i1.wrapping_add(1 as libc::c_uint) as uint64_t,
        );
        let mut res_j_1: *const uint64_t = table
            .as_mut_ptr()
            .offset(
                i1.wrapping_add(1 as libc::c_uint).wrapping_mul(15 as libc::c_uint)
                    as isize,
            );
        let mut i_3: uint32_t = 0 as libc::c_uint;
        let mut x_29: uint64_t = c_1 & *res_j_1.offset(i_3 as isize)
            | !c_1 & tmp0[i_3 as usize];
        let mut os_29: *mut uint64_t = tmp0.as_mut_ptr();
        *os_29.offset(i_3 as isize) = x_29;
        i_3 = (i_3 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_30: uint64_t = c_1 & *res_j_1.offset(i_3 as isize)
            | !c_1 & tmp0[i_3 as usize];
        let mut os_30: *mut uint64_t = tmp0.as_mut_ptr();
        *os_30.offset(i_3 as isize) = x_30;
        i_3 = (i_3 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_31: uint64_t = c_1 & *res_j_1.offset(i_3 as isize)
            | !c_1 & tmp0[i_3 as usize];
        let mut os_31: *mut uint64_t = tmp0.as_mut_ptr();
        *os_31.offset(i_3 as isize) = x_31;
        i_3 = (i_3 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_32: uint64_t = c_1 & *res_j_1.offset(i_3 as isize)
            | !c_1 & tmp0[i_3 as usize];
        let mut os_32: *mut uint64_t = tmp0.as_mut_ptr();
        *os_32.offset(i_3 as isize) = x_32;
        i_3 = (i_3 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_33: uint64_t = c_1 & *res_j_1.offset(i_3 as isize)
            | !c_1 & tmp0[i_3 as usize];
        let mut os_33: *mut uint64_t = tmp0.as_mut_ptr();
        *os_33.offset(i_3 as isize) = x_33;
        i_3 = (i_3 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_34: uint64_t = c_1 & *res_j_1.offset(i_3 as isize)
            | !c_1 & tmp0[i_3 as usize];
        let mut os_34: *mut uint64_t = tmp0.as_mut_ptr();
        *os_34.offset(i_3 as isize) = x_34;
        i_3 = (i_3 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_35: uint64_t = c_1 & *res_j_1.offset(i_3 as isize)
            | !c_1 & tmp0[i_3 as usize];
        let mut os_35: *mut uint64_t = tmp0.as_mut_ptr();
        *os_35.offset(i_3 as isize) = x_35;
        i_3 = (i_3 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_36: uint64_t = c_1 & *res_j_1.offset(i_3 as isize)
            | !c_1 & tmp0[i_3 as usize];
        let mut os_36: *mut uint64_t = tmp0.as_mut_ptr();
        *os_36.offset(i_3 as isize) = x_36;
        i_3 = (i_3 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_37: uint64_t = c_1 & *res_j_1.offset(i_3 as isize)
            | !c_1 & tmp0[i_3 as usize];
        let mut os_37: *mut uint64_t = tmp0.as_mut_ptr();
        *os_37.offset(i_3 as isize) = x_37;
        i_3 = (i_3 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_38: uint64_t = c_1 & *res_j_1.offset(i_3 as isize)
            | !c_1 & tmp0[i_3 as usize];
        let mut os_38: *mut uint64_t = tmp0.as_mut_ptr();
        *os_38.offset(i_3 as isize) = x_38;
        i_3 = (i_3 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_39: uint64_t = c_1 & *res_j_1.offset(i_3 as isize)
            | !c_1 & tmp0[i_3 as usize];
        let mut os_39: *mut uint64_t = tmp0.as_mut_ptr();
        *os_39.offset(i_3 as isize) = x_39;
        i_3 = (i_3 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_40: uint64_t = c_1 & *res_j_1.offset(i_3 as isize)
            | !c_1 & tmp0[i_3 as usize];
        let mut os_40: *mut uint64_t = tmp0.as_mut_ptr();
        *os_40.offset(i_3 as isize) = x_40;
        i_3 = (i_3 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_41: uint64_t = c_1 & *res_j_1.offset(i_3 as isize)
            | !c_1 & tmp0[i_3 as usize];
        let mut os_41: *mut uint64_t = tmp0.as_mut_ptr();
        *os_41.offset(i_3 as isize) = x_41;
        i_3 = (i_3 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_42: uint64_t = c_1 & *res_j_1.offset(i_3 as isize)
            | !c_1 & tmp0[i_3 as usize];
        let mut os_42: *mut uint64_t = tmp0.as_mut_ptr();
        *os_42.offset(i_3 as isize) = x_42;
        i_3 = (i_3 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_43: uint64_t = c_1 & *res_j_1.offset(i_3 as isize)
            | !c_1 & tmp0[i_3 as usize];
        let mut os_43: *mut uint64_t = tmp0.as_mut_ptr();
        *os_43.offset(i_3 as isize) = x_43;
        i_3 = (i_3 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        i1 = (i1 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut c_2: uint64_t = FStar_UInt64_eq_mask(
            bits_l,
            i1.wrapping_add(1 as libc::c_uint) as uint64_t,
        );
        let mut res_j_2: *const uint64_t = table
            .as_mut_ptr()
            .offset(
                i1.wrapping_add(1 as libc::c_uint).wrapping_mul(15 as libc::c_uint)
                    as isize,
            );
        let mut i_4: uint32_t = 0 as libc::c_uint;
        let mut x_44: uint64_t = c_2 & *res_j_2.offset(i_4 as isize)
            | !c_2 & tmp0[i_4 as usize];
        let mut os_44: *mut uint64_t = tmp0.as_mut_ptr();
        *os_44.offset(i_4 as isize) = x_44;
        i_4 = (i_4 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_45: uint64_t = c_2 & *res_j_2.offset(i_4 as isize)
            | !c_2 & tmp0[i_4 as usize];
        let mut os_45: *mut uint64_t = tmp0.as_mut_ptr();
        *os_45.offset(i_4 as isize) = x_45;
        i_4 = (i_4 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_46: uint64_t = c_2 & *res_j_2.offset(i_4 as isize)
            | !c_2 & tmp0[i_4 as usize];
        let mut os_46: *mut uint64_t = tmp0.as_mut_ptr();
        *os_46.offset(i_4 as isize) = x_46;
        i_4 = (i_4 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_47: uint64_t = c_2 & *res_j_2.offset(i_4 as isize)
            | !c_2 & tmp0[i_4 as usize];
        let mut os_47: *mut uint64_t = tmp0.as_mut_ptr();
        *os_47.offset(i_4 as isize) = x_47;
        i_4 = (i_4 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_48: uint64_t = c_2 & *res_j_2.offset(i_4 as isize)
            | !c_2 & tmp0[i_4 as usize];
        let mut os_48: *mut uint64_t = tmp0.as_mut_ptr();
        *os_48.offset(i_4 as isize) = x_48;
        i_4 = (i_4 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_49: uint64_t = c_2 & *res_j_2.offset(i_4 as isize)
            | !c_2 & tmp0[i_4 as usize];
        let mut os_49: *mut uint64_t = tmp0.as_mut_ptr();
        *os_49.offset(i_4 as isize) = x_49;
        i_4 = (i_4 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_50: uint64_t = c_2 & *res_j_2.offset(i_4 as isize)
            | !c_2 & tmp0[i_4 as usize];
        let mut os_50: *mut uint64_t = tmp0.as_mut_ptr();
        *os_50.offset(i_4 as isize) = x_50;
        i_4 = (i_4 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_51: uint64_t = c_2 & *res_j_2.offset(i_4 as isize)
            | !c_2 & tmp0[i_4 as usize];
        let mut os_51: *mut uint64_t = tmp0.as_mut_ptr();
        *os_51.offset(i_4 as isize) = x_51;
        i_4 = (i_4 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_52: uint64_t = c_2 & *res_j_2.offset(i_4 as isize)
            | !c_2 & tmp0[i_4 as usize];
        let mut os_52: *mut uint64_t = tmp0.as_mut_ptr();
        *os_52.offset(i_4 as isize) = x_52;
        i_4 = (i_4 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_53: uint64_t = c_2 & *res_j_2.offset(i_4 as isize)
            | !c_2 & tmp0[i_4 as usize];
        let mut os_53: *mut uint64_t = tmp0.as_mut_ptr();
        *os_53.offset(i_4 as isize) = x_53;
        i_4 = (i_4 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_54: uint64_t = c_2 & *res_j_2.offset(i_4 as isize)
            | !c_2 & tmp0[i_4 as usize];
        let mut os_54: *mut uint64_t = tmp0.as_mut_ptr();
        *os_54.offset(i_4 as isize) = x_54;
        i_4 = (i_4 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_55: uint64_t = c_2 & *res_j_2.offset(i_4 as isize)
            | !c_2 & tmp0[i_4 as usize];
        let mut os_55: *mut uint64_t = tmp0.as_mut_ptr();
        *os_55.offset(i_4 as isize) = x_55;
        i_4 = (i_4 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_56: uint64_t = c_2 & *res_j_2.offset(i_4 as isize)
            | !c_2 & tmp0[i_4 as usize];
        let mut os_56: *mut uint64_t = tmp0.as_mut_ptr();
        *os_56.offset(i_4 as isize) = x_56;
        i_4 = (i_4 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_57: uint64_t = c_2 & *res_j_2.offset(i_4 as isize)
            | !c_2 & tmp0[i_4 as usize];
        let mut os_57: *mut uint64_t = tmp0.as_mut_ptr();
        *os_57.offset(i_4 as isize) = x_57;
        i_4 = (i_4 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_58: uint64_t = c_2 & *res_j_2.offset(i_4 as isize)
            | !c_2 & tmp0[i_4 as usize];
        let mut os_58: *mut uint64_t = tmp0.as_mut_ptr();
        *os_58.offset(i_4 as isize) = x_58;
        i_4 = (i_4 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        i1 = (i1 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut c_3: uint64_t = FStar_UInt64_eq_mask(
            bits_l,
            i1.wrapping_add(1 as libc::c_uint) as uint64_t,
        );
        let mut res_j_3: *const uint64_t = table
            .as_mut_ptr()
            .offset(
                i1.wrapping_add(1 as libc::c_uint).wrapping_mul(15 as libc::c_uint)
                    as isize,
            );
        let mut i_5: uint32_t = 0 as libc::c_uint;
        let mut x_59: uint64_t = c_3 & *res_j_3.offset(i_5 as isize)
            | !c_3 & tmp0[i_5 as usize];
        let mut os_59: *mut uint64_t = tmp0.as_mut_ptr();
        *os_59.offset(i_5 as isize) = x_59;
        i_5 = (i_5 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_60: uint64_t = c_3 & *res_j_3.offset(i_5 as isize)
            | !c_3 & tmp0[i_5 as usize];
        let mut os_60: *mut uint64_t = tmp0.as_mut_ptr();
        *os_60.offset(i_5 as isize) = x_60;
        i_5 = (i_5 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_61: uint64_t = c_3 & *res_j_3.offset(i_5 as isize)
            | !c_3 & tmp0[i_5 as usize];
        let mut os_61: *mut uint64_t = tmp0.as_mut_ptr();
        *os_61.offset(i_5 as isize) = x_61;
        i_5 = (i_5 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_62: uint64_t = c_3 & *res_j_3.offset(i_5 as isize)
            | !c_3 & tmp0[i_5 as usize];
        let mut os_62: *mut uint64_t = tmp0.as_mut_ptr();
        *os_62.offset(i_5 as isize) = x_62;
        i_5 = (i_5 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_63: uint64_t = c_3 & *res_j_3.offset(i_5 as isize)
            | !c_3 & tmp0[i_5 as usize];
        let mut os_63: *mut uint64_t = tmp0.as_mut_ptr();
        *os_63.offset(i_5 as isize) = x_63;
        i_5 = (i_5 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_64: uint64_t = c_3 & *res_j_3.offset(i_5 as isize)
            | !c_3 & tmp0[i_5 as usize];
        let mut os_64: *mut uint64_t = tmp0.as_mut_ptr();
        *os_64.offset(i_5 as isize) = x_64;
        i_5 = (i_5 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_65: uint64_t = c_3 & *res_j_3.offset(i_5 as isize)
            | !c_3 & tmp0[i_5 as usize];
        let mut os_65: *mut uint64_t = tmp0.as_mut_ptr();
        *os_65.offset(i_5 as isize) = x_65;
        i_5 = (i_5 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_66: uint64_t = c_3 & *res_j_3.offset(i_5 as isize)
            | !c_3 & tmp0[i_5 as usize];
        let mut os_66: *mut uint64_t = tmp0.as_mut_ptr();
        *os_66.offset(i_5 as isize) = x_66;
        i_5 = (i_5 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_67: uint64_t = c_3 & *res_j_3.offset(i_5 as isize)
            | !c_3 & tmp0[i_5 as usize];
        let mut os_67: *mut uint64_t = tmp0.as_mut_ptr();
        *os_67.offset(i_5 as isize) = x_67;
        i_5 = (i_5 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_68: uint64_t = c_3 & *res_j_3.offset(i_5 as isize)
            | !c_3 & tmp0[i_5 as usize];
        let mut os_68: *mut uint64_t = tmp0.as_mut_ptr();
        *os_68.offset(i_5 as isize) = x_68;
        i_5 = (i_5 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_69: uint64_t = c_3 & *res_j_3.offset(i_5 as isize)
            | !c_3 & tmp0[i_5 as usize];
        let mut os_69: *mut uint64_t = tmp0.as_mut_ptr();
        *os_69.offset(i_5 as isize) = x_69;
        i_5 = (i_5 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_70: uint64_t = c_3 & *res_j_3.offset(i_5 as isize)
            | !c_3 & tmp0[i_5 as usize];
        let mut os_70: *mut uint64_t = tmp0.as_mut_ptr();
        *os_70.offset(i_5 as isize) = x_70;
        i_5 = (i_5 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_71: uint64_t = c_3 & *res_j_3.offset(i_5 as isize)
            | !c_3 & tmp0[i_5 as usize];
        let mut os_71: *mut uint64_t = tmp0.as_mut_ptr();
        *os_71.offset(i_5 as isize) = x_71;
        i_5 = (i_5 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_72: uint64_t = c_3 & *res_j_3.offset(i_5 as isize)
            | !c_3 & tmp0[i_5 as usize];
        let mut os_72: *mut uint64_t = tmp0.as_mut_ptr();
        *os_72.offset(i_5 as isize) = x_72;
        i_5 = (i_5 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_73: uint64_t = c_3 & *res_j_3.offset(i_5 as isize)
            | !c_3 & tmp0[i_5 as usize];
        let mut os_73: *mut uint64_t = tmp0.as_mut_ptr();
        *os_73.offset(i_5 as isize) = x_73;
        i_5 = (i_5 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        i1 = (i1 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut c_4: uint64_t = FStar_UInt64_eq_mask(
            bits_l,
            i1.wrapping_add(1 as libc::c_uint) as uint64_t,
        );
        let mut res_j_4: *const uint64_t = table
            .as_mut_ptr()
            .offset(
                i1.wrapping_add(1 as libc::c_uint).wrapping_mul(15 as libc::c_uint)
                    as isize,
            );
        let mut i_6: uint32_t = 0 as libc::c_uint;
        let mut x_74: uint64_t = c_4 & *res_j_4.offset(i_6 as isize)
            | !c_4 & tmp0[i_6 as usize];
        let mut os_74: *mut uint64_t = tmp0.as_mut_ptr();
        *os_74.offset(i_6 as isize) = x_74;
        i_6 = (i_6 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_75: uint64_t = c_4 & *res_j_4.offset(i_6 as isize)
            | !c_4 & tmp0[i_6 as usize];
        let mut os_75: *mut uint64_t = tmp0.as_mut_ptr();
        *os_75.offset(i_6 as isize) = x_75;
        i_6 = (i_6 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_76: uint64_t = c_4 & *res_j_4.offset(i_6 as isize)
            | !c_4 & tmp0[i_6 as usize];
        let mut os_76: *mut uint64_t = tmp0.as_mut_ptr();
        *os_76.offset(i_6 as isize) = x_76;
        i_6 = (i_6 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_77: uint64_t = c_4 & *res_j_4.offset(i_6 as isize)
            | !c_4 & tmp0[i_6 as usize];
        let mut os_77: *mut uint64_t = tmp0.as_mut_ptr();
        *os_77.offset(i_6 as isize) = x_77;
        i_6 = (i_6 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_78: uint64_t = c_4 & *res_j_4.offset(i_6 as isize)
            | !c_4 & tmp0[i_6 as usize];
        let mut os_78: *mut uint64_t = tmp0.as_mut_ptr();
        *os_78.offset(i_6 as isize) = x_78;
        i_6 = (i_6 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_79: uint64_t = c_4 & *res_j_4.offset(i_6 as isize)
            | !c_4 & tmp0[i_6 as usize];
        let mut os_79: *mut uint64_t = tmp0.as_mut_ptr();
        *os_79.offset(i_6 as isize) = x_79;
        i_6 = (i_6 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_80: uint64_t = c_4 & *res_j_4.offset(i_6 as isize)
            | !c_4 & tmp0[i_6 as usize];
        let mut os_80: *mut uint64_t = tmp0.as_mut_ptr();
        *os_80.offset(i_6 as isize) = x_80;
        i_6 = (i_6 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_81: uint64_t = c_4 & *res_j_4.offset(i_6 as isize)
            | !c_4 & tmp0[i_6 as usize];
        let mut os_81: *mut uint64_t = tmp0.as_mut_ptr();
        *os_81.offset(i_6 as isize) = x_81;
        i_6 = (i_6 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_82: uint64_t = c_4 & *res_j_4.offset(i_6 as isize)
            | !c_4 & tmp0[i_6 as usize];
        let mut os_82: *mut uint64_t = tmp0.as_mut_ptr();
        *os_82.offset(i_6 as isize) = x_82;
        i_6 = (i_6 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_83: uint64_t = c_4 & *res_j_4.offset(i_6 as isize)
            | !c_4 & tmp0[i_6 as usize];
        let mut os_83: *mut uint64_t = tmp0.as_mut_ptr();
        *os_83.offset(i_6 as isize) = x_83;
        i_6 = (i_6 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_84: uint64_t = c_4 & *res_j_4.offset(i_6 as isize)
            | !c_4 & tmp0[i_6 as usize];
        let mut os_84: *mut uint64_t = tmp0.as_mut_ptr();
        *os_84.offset(i_6 as isize) = x_84;
        i_6 = (i_6 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_85: uint64_t = c_4 & *res_j_4.offset(i_6 as isize)
            | !c_4 & tmp0[i_6 as usize];
        let mut os_85: *mut uint64_t = tmp0.as_mut_ptr();
        *os_85.offset(i_6 as isize) = x_85;
        i_6 = (i_6 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_86: uint64_t = c_4 & *res_j_4.offset(i_6 as isize)
            | !c_4 & tmp0[i_6 as usize];
        let mut os_86: *mut uint64_t = tmp0.as_mut_ptr();
        *os_86.offset(i_6 as isize) = x_86;
        i_6 = (i_6 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_87: uint64_t = c_4 & *res_j_4.offset(i_6 as isize)
            | !c_4 & tmp0[i_6 as usize];
        let mut os_87: *mut uint64_t = tmp0.as_mut_ptr();
        *os_87.offset(i_6 as isize) = x_87;
        i_6 = (i_6 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_88: uint64_t = c_4 & *res_j_4.offset(i_6 as isize)
            | !c_4 & tmp0[i_6 as usize];
        let mut os_88: *mut uint64_t = tmp0.as_mut_ptr();
        *os_88.offset(i_6 as isize) = x_88;
        i_6 = (i_6 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        i1 = (i1 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut c_5: uint64_t = FStar_UInt64_eq_mask(
            bits_l,
            i1.wrapping_add(1 as libc::c_uint) as uint64_t,
        );
        let mut res_j_5: *const uint64_t = table
            .as_mut_ptr()
            .offset(
                i1.wrapping_add(1 as libc::c_uint).wrapping_mul(15 as libc::c_uint)
                    as isize,
            );
        let mut i_7: uint32_t = 0 as libc::c_uint;
        let mut x_89: uint64_t = c_5 & *res_j_5.offset(i_7 as isize)
            | !c_5 & tmp0[i_7 as usize];
        let mut os_89: *mut uint64_t = tmp0.as_mut_ptr();
        *os_89.offset(i_7 as isize) = x_89;
        i_7 = (i_7 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_90: uint64_t = c_5 & *res_j_5.offset(i_7 as isize)
            | !c_5 & tmp0[i_7 as usize];
        let mut os_90: *mut uint64_t = tmp0.as_mut_ptr();
        *os_90.offset(i_7 as isize) = x_90;
        i_7 = (i_7 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_91: uint64_t = c_5 & *res_j_5.offset(i_7 as isize)
            | !c_5 & tmp0[i_7 as usize];
        let mut os_91: *mut uint64_t = tmp0.as_mut_ptr();
        *os_91.offset(i_7 as isize) = x_91;
        i_7 = (i_7 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_92: uint64_t = c_5 & *res_j_5.offset(i_7 as isize)
            | !c_5 & tmp0[i_7 as usize];
        let mut os_92: *mut uint64_t = tmp0.as_mut_ptr();
        *os_92.offset(i_7 as isize) = x_92;
        i_7 = (i_7 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_93: uint64_t = c_5 & *res_j_5.offset(i_7 as isize)
            | !c_5 & tmp0[i_7 as usize];
        let mut os_93: *mut uint64_t = tmp0.as_mut_ptr();
        *os_93.offset(i_7 as isize) = x_93;
        i_7 = (i_7 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_94: uint64_t = c_5 & *res_j_5.offset(i_7 as isize)
            | !c_5 & tmp0[i_7 as usize];
        let mut os_94: *mut uint64_t = tmp0.as_mut_ptr();
        *os_94.offset(i_7 as isize) = x_94;
        i_7 = (i_7 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_95: uint64_t = c_5 & *res_j_5.offset(i_7 as isize)
            | !c_5 & tmp0[i_7 as usize];
        let mut os_95: *mut uint64_t = tmp0.as_mut_ptr();
        *os_95.offset(i_7 as isize) = x_95;
        i_7 = (i_7 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_96: uint64_t = c_5 & *res_j_5.offset(i_7 as isize)
            | !c_5 & tmp0[i_7 as usize];
        let mut os_96: *mut uint64_t = tmp0.as_mut_ptr();
        *os_96.offset(i_7 as isize) = x_96;
        i_7 = (i_7 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_97: uint64_t = c_5 & *res_j_5.offset(i_7 as isize)
            | !c_5 & tmp0[i_7 as usize];
        let mut os_97: *mut uint64_t = tmp0.as_mut_ptr();
        *os_97.offset(i_7 as isize) = x_97;
        i_7 = (i_7 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_98: uint64_t = c_5 & *res_j_5.offset(i_7 as isize)
            | !c_5 & tmp0[i_7 as usize];
        let mut os_98: *mut uint64_t = tmp0.as_mut_ptr();
        *os_98.offset(i_7 as isize) = x_98;
        i_7 = (i_7 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_99: uint64_t = c_5 & *res_j_5.offset(i_7 as isize)
            | !c_5 & tmp0[i_7 as usize];
        let mut os_99: *mut uint64_t = tmp0.as_mut_ptr();
        *os_99.offset(i_7 as isize) = x_99;
        i_7 = (i_7 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_100: uint64_t = c_5 & *res_j_5.offset(i_7 as isize)
            | !c_5 & tmp0[i_7 as usize];
        let mut os_100: *mut uint64_t = tmp0.as_mut_ptr();
        *os_100.offset(i_7 as isize) = x_100;
        i_7 = (i_7 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_101: uint64_t = c_5 & *res_j_5.offset(i_7 as isize)
            | !c_5 & tmp0[i_7 as usize];
        let mut os_101: *mut uint64_t = tmp0.as_mut_ptr();
        *os_101.offset(i_7 as isize) = x_101;
        i_7 = (i_7 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_102: uint64_t = c_5 & *res_j_5.offset(i_7 as isize)
            | !c_5 & tmp0[i_7 as usize];
        let mut os_102: *mut uint64_t = tmp0.as_mut_ptr();
        *os_102.offset(i_7 as isize) = x_102;
        i_7 = (i_7 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_103: uint64_t = c_5 & *res_j_5.offset(i_7 as isize)
            | !c_5 & tmp0[i_7 as usize];
        let mut os_103: *mut uint64_t = tmp0.as_mut_ptr();
        *os_103.offset(i_7 as isize) = x_103;
        i_7 = (i_7 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        i1 = (i1 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut c_6: uint64_t = FStar_UInt64_eq_mask(
            bits_l,
            i1.wrapping_add(1 as libc::c_uint) as uint64_t,
        );
        let mut res_j_6: *const uint64_t = table
            .as_mut_ptr()
            .offset(
                i1.wrapping_add(1 as libc::c_uint).wrapping_mul(15 as libc::c_uint)
                    as isize,
            );
        let mut i_8: uint32_t = 0 as libc::c_uint;
        let mut x_104: uint64_t = c_6 & *res_j_6.offset(i_8 as isize)
            | !c_6 & tmp0[i_8 as usize];
        let mut os_104: *mut uint64_t = tmp0.as_mut_ptr();
        *os_104.offset(i_8 as isize) = x_104;
        i_8 = (i_8 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_105: uint64_t = c_6 & *res_j_6.offset(i_8 as isize)
            | !c_6 & tmp0[i_8 as usize];
        let mut os_105: *mut uint64_t = tmp0.as_mut_ptr();
        *os_105.offset(i_8 as isize) = x_105;
        i_8 = (i_8 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_106: uint64_t = c_6 & *res_j_6.offset(i_8 as isize)
            | !c_6 & tmp0[i_8 as usize];
        let mut os_106: *mut uint64_t = tmp0.as_mut_ptr();
        *os_106.offset(i_8 as isize) = x_106;
        i_8 = (i_8 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_107: uint64_t = c_6 & *res_j_6.offset(i_8 as isize)
            | !c_6 & tmp0[i_8 as usize];
        let mut os_107: *mut uint64_t = tmp0.as_mut_ptr();
        *os_107.offset(i_8 as isize) = x_107;
        i_8 = (i_8 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_108: uint64_t = c_6 & *res_j_6.offset(i_8 as isize)
            | !c_6 & tmp0[i_8 as usize];
        let mut os_108: *mut uint64_t = tmp0.as_mut_ptr();
        *os_108.offset(i_8 as isize) = x_108;
        i_8 = (i_8 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_109: uint64_t = c_6 & *res_j_6.offset(i_8 as isize)
            | !c_6 & tmp0[i_8 as usize];
        let mut os_109: *mut uint64_t = tmp0.as_mut_ptr();
        *os_109.offset(i_8 as isize) = x_109;
        i_8 = (i_8 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_110: uint64_t = c_6 & *res_j_6.offset(i_8 as isize)
            | !c_6 & tmp0[i_8 as usize];
        let mut os_110: *mut uint64_t = tmp0.as_mut_ptr();
        *os_110.offset(i_8 as isize) = x_110;
        i_8 = (i_8 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_111: uint64_t = c_6 & *res_j_6.offset(i_8 as isize)
            | !c_6 & tmp0[i_8 as usize];
        let mut os_111: *mut uint64_t = tmp0.as_mut_ptr();
        *os_111.offset(i_8 as isize) = x_111;
        i_8 = (i_8 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_112: uint64_t = c_6 & *res_j_6.offset(i_8 as isize)
            | !c_6 & tmp0[i_8 as usize];
        let mut os_112: *mut uint64_t = tmp0.as_mut_ptr();
        *os_112.offset(i_8 as isize) = x_112;
        i_8 = (i_8 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_113: uint64_t = c_6 & *res_j_6.offset(i_8 as isize)
            | !c_6 & tmp0[i_8 as usize];
        let mut os_113: *mut uint64_t = tmp0.as_mut_ptr();
        *os_113.offset(i_8 as isize) = x_113;
        i_8 = (i_8 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_114: uint64_t = c_6 & *res_j_6.offset(i_8 as isize)
            | !c_6 & tmp0[i_8 as usize];
        let mut os_114: *mut uint64_t = tmp0.as_mut_ptr();
        *os_114.offset(i_8 as isize) = x_114;
        i_8 = (i_8 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_115: uint64_t = c_6 & *res_j_6.offset(i_8 as isize)
            | !c_6 & tmp0[i_8 as usize];
        let mut os_115: *mut uint64_t = tmp0.as_mut_ptr();
        *os_115.offset(i_8 as isize) = x_115;
        i_8 = (i_8 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_116: uint64_t = c_6 & *res_j_6.offset(i_8 as isize)
            | !c_6 & tmp0[i_8 as usize];
        let mut os_116: *mut uint64_t = tmp0.as_mut_ptr();
        *os_116.offset(i_8 as isize) = x_116;
        i_8 = (i_8 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_117: uint64_t = c_6 & *res_j_6.offset(i_8 as isize)
            | !c_6 & tmp0[i_8 as usize];
        let mut os_117: *mut uint64_t = tmp0.as_mut_ptr();
        *os_117.offset(i_8 as isize) = x_117;
        i_8 = (i_8 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_118: uint64_t = c_6 & *res_j_6.offset(i_8 as isize)
            | !c_6 & tmp0[i_8 as usize];
        let mut os_118: *mut uint64_t = tmp0.as_mut_ptr();
        *os_118.offset(i_8 as isize) = x_118;
        i_8 = (i_8 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        i1 = (i1 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut c_7: uint64_t = FStar_UInt64_eq_mask(
            bits_l,
            i1.wrapping_add(1 as libc::c_uint) as uint64_t,
        );
        let mut res_j_7: *const uint64_t = table
            .as_mut_ptr()
            .offset(
                i1.wrapping_add(1 as libc::c_uint).wrapping_mul(15 as libc::c_uint)
                    as isize,
            );
        let mut i_9: uint32_t = 0 as libc::c_uint;
        let mut x_119: uint64_t = c_7 & *res_j_7.offset(i_9 as isize)
            | !c_7 & tmp0[i_9 as usize];
        let mut os_119: *mut uint64_t = tmp0.as_mut_ptr();
        *os_119.offset(i_9 as isize) = x_119;
        i_9 = (i_9 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_120: uint64_t = c_7 & *res_j_7.offset(i_9 as isize)
            | !c_7 & tmp0[i_9 as usize];
        let mut os_120: *mut uint64_t = tmp0.as_mut_ptr();
        *os_120.offset(i_9 as isize) = x_120;
        i_9 = (i_9 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_121: uint64_t = c_7 & *res_j_7.offset(i_9 as isize)
            | !c_7 & tmp0[i_9 as usize];
        let mut os_121: *mut uint64_t = tmp0.as_mut_ptr();
        *os_121.offset(i_9 as isize) = x_121;
        i_9 = (i_9 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_122: uint64_t = c_7 & *res_j_7.offset(i_9 as isize)
            | !c_7 & tmp0[i_9 as usize];
        let mut os_122: *mut uint64_t = tmp0.as_mut_ptr();
        *os_122.offset(i_9 as isize) = x_122;
        i_9 = (i_9 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_123: uint64_t = c_7 & *res_j_7.offset(i_9 as isize)
            | !c_7 & tmp0[i_9 as usize];
        let mut os_123: *mut uint64_t = tmp0.as_mut_ptr();
        *os_123.offset(i_9 as isize) = x_123;
        i_9 = (i_9 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_124: uint64_t = c_7 & *res_j_7.offset(i_9 as isize)
            | !c_7 & tmp0[i_9 as usize];
        let mut os_124: *mut uint64_t = tmp0.as_mut_ptr();
        *os_124.offset(i_9 as isize) = x_124;
        i_9 = (i_9 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_125: uint64_t = c_7 & *res_j_7.offset(i_9 as isize)
            | !c_7 & tmp0[i_9 as usize];
        let mut os_125: *mut uint64_t = tmp0.as_mut_ptr();
        *os_125.offset(i_9 as isize) = x_125;
        i_9 = (i_9 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_126: uint64_t = c_7 & *res_j_7.offset(i_9 as isize)
            | !c_7 & tmp0[i_9 as usize];
        let mut os_126: *mut uint64_t = tmp0.as_mut_ptr();
        *os_126.offset(i_9 as isize) = x_126;
        i_9 = (i_9 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_127: uint64_t = c_7 & *res_j_7.offset(i_9 as isize)
            | !c_7 & tmp0[i_9 as usize];
        let mut os_127: *mut uint64_t = tmp0.as_mut_ptr();
        *os_127.offset(i_9 as isize) = x_127;
        i_9 = (i_9 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_128: uint64_t = c_7 & *res_j_7.offset(i_9 as isize)
            | !c_7 & tmp0[i_9 as usize];
        let mut os_128: *mut uint64_t = tmp0.as_mut_ptr();
        *os_128.offset(i_9 as isize) = x_128;
        i_9 = (i_9 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_129: uint64_t = c_7 & *res_j_7.offset(i_9 as isize)
            | !c_7 & tmp0[i_9 as usize];
        let mut os_129: *mut uint64_t = tmp0.as_mut_ptr();
        *os_129.offset(i_9 as isize) = x_129;
        i_9 = (i_9 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_130: uint64_t = c_7 & *res_j_7.offset(i_9 as isize)
            | !c_7 & tmp0[i_9 as usize];
        let mut os_130: *mut uint64_t = tmp0.as_mut_ptr();
        *os_130.offset(i_9 as isize) = x_130;
        i_9 = (i_9 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_131: uint64_t = c_7 & *res_j_7.offset(i_9 as isize)
            | !c_7 & tmp0[i_9 as usize];
        let mut os_131: *mut uint64_t = tmp0.as_mut_ptr();
        *os_131.offset(i_9 as isize) = x_131;
        i_9 = (i_9 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_132: uint64_t = c_7 & *res_j_7.offset(i_9 as isize)
            | !c_7 & tmp0[i_9 as usize];
        let mut os_132: *mut uint64_t = tmp0.as_mut_ptr();
        *os_132.offset(i_9 as isize) = x_132;
        i_9 = (i_9 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_133: uint64_t = c_7 & *res_j_7.offset(i_9 as isize)
            | !c_7 & tmp0[i_9 as usize];
        let mut os_133: *mut uint64_t = tmp0.as_mut_ptr();
        *os_133.offset(i_9 as isize) = x_133;
        i_9 = (i_9 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        i1 = (i1 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut c_8: uint64_t = FStar_UInt64_eq_mask(
            bits_l,
            i1.wrapping_add(1 as libc::c_uint) as uint64_t,
        );
        let mut res_j_8: *const uint64_t = table
            .as_mut_ptr()
            .offset(
                i1.wrapping_add(1 as libc::c_uint).wrapping_mul(15 as libc::c_uint)
                    as isize,
            );
        let mut i_10: uint32_t = 0 as libc::c_uint;
        let mut x_134: uint64_t = c_8 & *res_j_8.offset(i_10 as isize)
            | !c_8 & tmp0[i_10 as usize];
        let mut os_134: *mut uint64_t = tmp0.as_mut_ptr();
        *os_134.offset(i_10 as isize) = x_134;
        i_10 = (i_10 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_135: uint64_t = c_8 & *res_j_8.offset(i_10 as isize)
            | !c_8 & tmp0[i_10 as usize];
        let mut os_135: *mut uint64_t = tmp0.as_mut_ptr();
        *os_135.offset(i_10 as isize) = x_135;
        i_10 = (i_10 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_136: uint64_t = c_8 & *res_j_8.offset(i_10 as isize)
            | !c_8 & tmp0[i_10 as usize];
        let mut os_136: *mut uint64_t = tmp0.as_mut_ptr();
        *os_136.offset(i_10 as isize) = x_136;
        i_10 = (i_10 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_137: uint64_t = c_8 & *res_j_8.offset(i_10 as isize)
            | !c_8 & tmp0[i_10 as usize];
        let mut os_137: *mut uint64_t = tmp0.as_mut_ptr();
        *os_137.offset(i_10 as isize) = x_137;
        i_10 = (i_10 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_138: uint64_t = c_8 & *res_j_8.offset(i_10 as isize)
            | !c_8 & tmp0[i_10 as usize];
        let mut os_138: *mut uint64_t = tmp0.as_mut_ptr();
        *os_138.offset(i_10 as isize) = x_138;
        i_10 = (i_10 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_139: uint64_t = c_8 & *res_j_8.offset(i_10 as isize)
            | !c_8 & tmp0[i_10 as usize];
        let mut os_139: *mut uint64_t = tmp0.as_mut_ptr();
        *os_139.offset(i_10 as isize) = x_139;
        i_10 = (i_10 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_140: uint64_t = c_8 & *res_j_8.offset(i_10 as isize)
            | !c_8 & tmp0[i_10 as usize];
        let mut os_140: *mut uint64_t = tmp0.as_mut_ptr();
        *os_140.offset(i_10 as isize) = x_140;
        i_10 = (i_10 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_141: uint64_t = c_8 & *res_j_8.offset(i_10 as isize)
            | !c_8 & tmp0[i_10 as usize];
        let mut os_141: *mut uint64_t = tmp0.as_mut_ptr();
        *os_141.offset(i_10 as isize) = x_141;
        i_10 = (i_10 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_142: uint64_t = c_8 & *res_j_8.offset(i_10 as isize)
            | !c_8 & tmp0[i_10 as usize];
        let mut os_142: *mut uint64_t = tmp0.as_mut_ptr();
        *os_142.offset(i_10 as isize) = x_142;
        i_10 = (i_10 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_143: uint64_t = c_8 & *res_j_8.offset(i_10 as isize)
            | !c_8 & tmp0[i_10 as usize];
        let mut os_143: *mut uint64_t = tmp0.as_mut_ptr();
        *os_143.offset(i_10 as isize) = x_143;
        i_10 = (i_10 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_144: uint64_t = c_8 & *res_j_8.offset(i_10 as isize)
            | !c_8 & tmp0[i_10 as usize];
        let mut os_144: *mut uint64_t = tmp0.as_mut_ptr();
        *os_144.offset(i_10 as isize) = x_144;
        i_10 = (i_10 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_145: uint64_t = c_8 & *res_j_8.offset(i_10 as isize)
            | !c_8 & tmp0[i_10 as usize];
        let mut os_145: *mut uint64_t = tmp0.as_mut_ptr();
        *os_145.offset(i_10 as isize) = x_145;
        i_10 = (i_10 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_146: uint64_t = c_8 & *res_j_8.offset(i_10 as isize)
            | !c_8 & tmp0[i_10 as usize];
        let mut os_146: *mut uint64_t = tmp0.as_mut_ptr();
        *os_146.offset(i_10 as isize) = x_146;
        i_10 = (i_10 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_147: uint64_t = c_8 & *res_j_8.offset(i_10 as isize)
            | !c_8 & tmp0[i_10 as usize];
        let mut os_147: *mut uint64_t = tmp0.as_mut_ptr();
        *os_147.offset(i_10 as isize) = x_147;
        i_10 = (i_10 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_148: uint64_t = c_8 & *res_j_8.offset(i_10 as isize)
            | !c_8 & tmp0[i_10 as usize];
        let mut os_148: *mut uint64_t = tmp0.as_mut_ptr();
        *os_148.offset(i_10 as isize) = x_148;
        i_10 = (i_10 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        i1 = (i1 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut c_9: uint64_t = FStar_UInt64_eq_mask(
            bits_l,
            i1.wrapping_add(1 as libc::c_uint) as uint64_t,
        );
        let mut res_j_9: *const uint64_t = table
            .as_mut_ptr()
            .offset(
                i1.wrapping_add(1 as libc::c_uint).wrapping_mul(15 as libc::c_uint)
                    as isize,
            );
        let mut i_11: uint32_t = 0 as libc::c_uint;
        let mut x_149: uint64_t = c_9 & *res_j_9.offset(i_11 as isize)
            | !c_9 & tmp0[i_11 as usize];
        let mut os_149: *mut uint64_t = tmp0.as_mut_ptr();
        *os_149.offset(i_11 as isize) = x_149;
        i_11 = (i_11 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_150: uint64_t = c_9 & *res_j_9.offset(i_11 as isize)
            | !c_9 & tmp0[i_11 as usize];
        let mut os_150: *mut uint64_t = tmp0.as_mut_ptr();
        *os_150.offset(i_11 as isize) = x_150;
        i_11 = (i_11 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_151: uint64_t = c_9 & *res_j_9.offset(i_11 as isize)
            | !c_9 & tmp0[i_11 as usize];
        let mut os_151: *mut uint64_t = tmp0.as_mut_ptr();
        *os_151.offset(i_11 as isize) = x_151;
        i_11 = (i_11 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_152: uint64_t = c_9 & *res_j_9.offset(i_11 as isize)
            | !c_9 & tmp0[i_11 as usize];
        let mut os_152: *mut uint64_t = tmp0.as_mut_ptr();
        *os_152.offset(i_11 as isize) = x_152;
        i_11 = (i_11 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_153: uint64_t = c_9 & *res_j_9.offset(i_11 as isize)
            | !c_9 & tmp0[i_11 as usize];
        let mut os_153: *mut uint64_t = tmp0.as_mut_ptr();
        *os_153.offset(i_11 as isize) = x_153;
        i_11 = (i_11 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_154: uint64_t = c_9 & *res_j_9.offset(i_11 as isize)
            | !c_9 & tmp0[i_11 as usize];
        let mut os_154: *mut uint64_t = tmp0.as_mut_ptr();
        *os_154.offset(i_11 as isize) = x_154;
        i_11 = (i_11 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_155: uint64_t = c_9 & *res_j_9.offset(i_11 as isize)
            | !c_9 & tmp0[i_11 as usize];
        let mut os_155: *mut uint64_t = tmp0.as_mut_ptr();
        *os_155.offset(i_11 as isize) = x_155;
        i_11 = (i_11 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_156: uint64_t = c_9 & *res_j_9.offset(i_11 as isize)
            | !c_9 & tmp0[i_11 as usize];
        let mut os_156: *mut uint64_t = tmp0.as_mut_ptr();
        *os_156.offset(i_11 as isize) = x_156;
        i_11 = (i_11 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_157: uint64_t = c_9 & *res_j_9.offset(i_11 as isize)
            | !c_9 & tmp0[i_11 as usize];
        let mut os_157: *mut uint64_t = tmp0.as_mut_ptr();
        *os_157.offset(i_11 as isize) = x_157;
        i_11 = (i_11 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_158: uint64_t = c_9 & *res_j_9.offset(i_11 as isize)
            | !c_9 & tmp0[i_11 as usize];
        let mut os_158: *mut uint64_t = tmp0.as_mut_ptr();
        *os_158.offset(i_11 as isize) = x_158;
        i_11 = (i_11 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_159: uint64_t = c_9 & *res_j_9.offset(i_11 as isize)
            | !c_9 & tmp0[i_11 as usize];
        let mut os_159: *mut uint64_t = tmp0.as_mut_ptr();
        *os_159.offset(i_11 as isize) = x_159;
        i_11 = (i_11 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_160: uint64_t = c_9 & *res_j_9.offset(i_11 as isize)
            | !c_9 & tmp0[i_11 as usize];
        let mut os_160: *mut uint64_t = tmp0.as_mut_ptr();
        *os_160.offset(i_11 as isize) = x_160;
        i_11 = (i_11 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_161: uint64_t = c_9 & *res_j_9.offset(i_11 as isize)
            | !c_9 & tmp0[i_11 as usize];
        let mut os_161: *mut uint64_t = tmp0.as_mut_ptr();
        *os_161.offset(i_11 as isize) = x_161;
        i_11 = (i_11 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_162: uint64_t = c_9 & *res_j_9.offset(i_11 as isize)
            | !c_9 & tmp0[i_11 as usize];
        let mut os_162: *mut uint64_t = tmp0.as_mut_ptr();
        *os_162.offset(i_11 as isize) = x_162;
        i_11 = (i_11 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_163: uint64_t = c_9 & *res_j_9.offset(i_11 as isize)
            | !c_9 & tmp0[i_11 as usize];
        let mut os_163: *mut uint64_t = tmp0.as_mut_ptr();
        *os_163.offset(i_11 as isize) = x_163;
        i_11 = (i_11 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        i1 = (i1 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut c_10: uint64_t = FStar_UInt64_eq_mask(
            bits_l,
            i1.wrapping_add(1 as libc::c_uint) as uint64_t,
        );
        let mut res_j_10: *const uint64_t = table
            .as_mut_ptr()
            .offset(
                i1.wrapping_add(1 as libc::c_uint).wrapping_mul(15 as libc::c_uint)
                    as isize,
            );
        let mut i_12: uint32_t = 0 as libc::c_uint;
        let mut x_164: uint64_t = c_10 & *res_j_10.offset(i_12 as isize)
            | !c_10 & tmp0[i_12 as usize];
        let mut os_164: *mut uint64_t = tmp0.as_mut_ptr();
        *os_164.offset(i_12 as isize) = x_164;
        i_12 = (i_12 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_165: uint64_t = c_10 & *res_j_10.offset(i_12 as isize)
            | !c_10 & tmp0[i_12 as usize];
        let mut os_165: *mut uint64_t = tmp0.as_mut_ptr();
        *os_165.offset(i_12 as isize) = x_165;
        i_12 = (i_12 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_166: uint64_t = c_10 & *res_j_10.offset(i_12 as isize)
            | !c_10 & tmp0[i_12 as usize];
        let mut os_166: *mut uint64_t = tmp0.as_mut_ptr();
        *os_166.offset(i_12 as isize) = x_166;
        i_12 = (i_12 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_167: uint64_t = c_10 & *res_j_10.offset(i_12 as isize)
            | !c_10 & tmp0[i_12 as usize];
        let mut os_167: *mut uint64_t = tmp0.as_mut_ptr();
        *os_167.offset(i_12 as isize) = x_167;
        i_12 = (i_12 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_168: uint64_t = c_10 & *res_j_10.offset(i_12 as isize)
            | !c_10 & tmp0[i_12 as usize];
        let mut os_168: *mut uint64_t = tmp0.as_mut_ptr();
        *os_168.offset(i_12 as isize) = x_168;
        i_12 = (i_12 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_169: uint64_t = c_10 & *res_j_10.offset(i_12 as isize)
            | !c_10 & tmp0[i_12 as usize];
        let mut os_169: *mut uint64_t = tmp0.as_mut_ptr();
        *os_169.offset(i_12 as isize) = x_169;
        i_12 = (i_12 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_170: uint64_t = c_10 & *res_j_10.offset(i_12 as isize)
            | !c_10 & tmp0[i_12 as usize];
        let mut os_170: *mut uint64_t = tmp0.as_mut_ptr();
        *os_170.offset(i_12 as isize) = x_170;
        i_12 = (i_12 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_171: uint64_t = c_10 & *res_j_10.offset(i_12 as isize)
            | !c_10 & tmp0[i_12 as usize];
        let mut os_171: *mut uint64_t = tmp0.as_mut_ptr();
        *os_171.offset(i_12 as isize) = x_171;
        i_12 = (i_12 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_172: uint64_t = c_10 & *res_j_10.offset(i_12 as isize)
            | !c_10 & tmp0[i_12 as usize];
        let mut os_172: *mut uint64_t = tmp0.as_mut_ptr();
        *os_172.offset(i_12 as isize) = x_172;
        i_12 = (i_12 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_173: uint64_t = c_10 & *res_j_10.offset(i_12 as isize)
            | !c_10 & tmp0[i_12 as usize];
        let mut os_173: *mut uint64_t = tmp0.as_mut_ptr();
        *os_173.offset(i_12 as isize) = x_173;
        i_12 = (i_12 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_174: uint64_t = c_10 & *res_j_10.offset(i_12 as isize)
            | !c_10 & tmp0[i_12 as usize];
        let mut os_174: *mut uint64_t = tmp0.as_mut_ptr();
        *os_174.offset(i_12 as isize) = x_174;
        i_12 = (i_12 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_175: uint64_t = c_10 & *res_j_10.offset(i_12 as isize)
            | !c_10 & tmp0[i_12 as usize];
        let mut os_175: *mut uint64_t = tmp0.as_mut_ptr();
        *os_175.offset(i_12 as isize) = x_175;
        i_12 = (i_12 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_176: uint64_t = c_10 & *res_j_10.offset(i_12 as isize)
            | !c_10 & tmp0[i_12 as usize];
        let mut os_176: *mut uint64_t = tmp0.as_mut_ptr();
        *os_176.offset(i_12 as isize) = x_176;
        i_12 = (i_12 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_177: uint64_t = c_10 & *res_j_10.offset(i_12 as isize)
            | !c_10 & tmp0[i_12 as usize];
        let mut os_177: *mut uint64_t = tmp0.as_mut_ptr();
        *os_177.offset(i_12 as isize) = x_177;
        i_12 = (i_12 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_178: uint64_t = c_10 & *res_j_10.offset(i_12 as isize)
            | !c_10 & tmp0[i_12 as usize];
        let mut os_178: *mut uint64_t = tmp0.as_mut_ptr();
        *os_178.offset(i_12 as isize) = x_178;
        i_12 = (i_12 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        i1 = (i1 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut c_11: uint64_t = FStar_UInt64_eq_mask(
            bits_l,
            i1.wrapping_add(1 as libc::c_uint) as uint64_t,
        );
        let mut res_j_11: *const uint64_t = table
            .as_mut_ptr()
            .offset(
                i1.wrapping_add(1 as libc::c_uint).wrapping_mul(15 as libc::c_uint)
                    as isize,
            );
        let mut i_13: uint32_t = 0 as libc::c_uint;
        let mut x_179: uint64_t = c_11 & *res_j_11.offset(i_13 as isize)
            | !c_11 & tmp0[i_13 as usize];
        let mut os_179: *mut uint64_t = tmp0.as_mut_ptr();
        *os_179.offset(i_13 as isize) = x_179;
        i_13 = (i_13 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_180: uint64_t = c_11 & *res_j_11.offset(i_13 as isize)
            | !c_11 & tmp0[i_13 as usize];
        let mut os_180: *mut uint64_t = tmp0.as_mut_ptr();
        *os_180.offset(i_13 as isize) = x_180;
        i_13 = (i_13 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_181: uint64_t = c_11 & *res_j_11.offset(i_13 as isize)
            | !c_11 & tmp0[i_13 as usize];
        let mut os_181: *mut uint64_t = tmp0.as_mut_ptr();
        *os_181.offset(i_13 as isize) = x_181;
        i_13 = (i_13 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_182: uint64_t = c_11 & *res_j_11.offset(i_13 as isize)
            | !c_11 & tmp0[i_13 as usize];
        let mut os_182: *mut uint64_t = tmp0.as_mut_ptr();
        *os_182.offset(i_13 as isize) = x_182;
        i_13 = (i_13 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_183: uint64_t = c_11 & *res_j_11.offset(i_13 as isize)
            | !c_11 & tmp0[i_13 as usize];
        let mut os_183: *mut uint64_t = tmp0.as_mut_ptr();
        *os_183.offset(i_13 as isize) = x_183;
        i_13 = (i_13 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_184: uint64_t = c_11 & *res_j_11.offset(i_13 as isize)
            | !c_11 & tmp0[i_13 as usize];
        let mut os_184: *mut uint64_t = tmp0.as_mut_ptr();
        *os_184.offset(i_13 as isize) = x_184;
        i_13 = (i_13 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_185: uint64_t = c_11 & *res_j_11.offset(i_13 as isize)
            | !c_11 & tmp0[i_13 as usize];
        let mut os_185: *mut uint64_t = tmp0.as_mut_ptr();
        *os_185.offset(i_13 as isize) = x_185;
        i_13 = (i_13 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_186: uint64_t = c_11 & *res_j_11.offset(i_13 as isize)
            | !c_11 & tmp0[i_13 as usize];
        let mut os_186: *mut uint64_t = tmp0.as_mut_ptr();
        *os_186.offset(i_13 as isize) = x_186;
        i_13 = (i_13 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_187: uint64_t = c_11 & *res_j_11.offset(i_13 as isize)
            | !c_11 & tmp0[i_13 as usize];
        let mut os_187: *mut uint64_t = tmp0.as_mut_ptr();
        *os_187.offset(i_13 as isize) = x_187;
        i_13 = (i_13 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_188: uint64_t = c_11 & *res_j_11.offset(i_13 as isize)
            | !c_11 & tmp0[i_13 as usize];
        let mut os_188: *mut uint64_t = tmp0.as_mut_ptr();
        *os_188.offset(i_13 as isize) = x_188;
        i_13 = (i_13 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_189: uint64_t = c_11 & *res_j_11.offset(i_13 as isize)
            | !c_11 & tmp0[i_13 as usize];
        let mut os_189: *mut uint64_t = tmp0.as_mut_ptr();
        *os_189.offset(i_13 as isize) = x_189;
        i_13 = (i_13 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_190: uint64_t = c_11 & *res_j_11.offset(i_13 as isize)
            | !c_11 & tmp0[i_13 as usize];
        let mut os_190: *mut uint64_t = tmp0.as_mut_ptr();
        *os_190.offset(i_13 as isize) = x_190;
        i_13 = (i_13 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_191: uint64_t = c_11 & *res_j_11.offset(i_13 as isize)
            | !c_11 & tmp0[i_13 as usize];
        let mut os_191: *mut uint64_t = tmp0.as_mut_ptr();
        *os_191.offset(i_13 as isize) = x_191;
        i_13 = (i_13 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_192: uint64_t = c_11 & *res_j_11.offset(i_13 as isize)
            | !c_11 & tmp0[i_13 as usize];
        let mut os_192: *mut uint64_t = tmp0.as_mut_ptr();
        *os_192.offset(i_13 as isize) = x_192;
        i_13 = (i_13 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_193: uint64_t = c_11 & *res_j_11.offset(i_13 as isize)
            | !c_11 & tmp0[i_13 as usize];
        let mut os_193: *mut uint64_t = tmp0.as_mut_ptr();
        *os_193.offset(i_13 as isize) = x_193;
        i_13 = (i_13 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        i1 = (i1 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut c_12: uint64_t = FStar_UInt64_eq_mask(
            bits_l,
            i1.wrapping_add(1 as libc::c_uint) as uint64_t,
        );
        let mut res_j_12: *const uint64_t = table
            .as_mut_ptr()
            .offset(
                i1.wrapping_add(1 as libc::c_uint).wrapping_mul(15 as libc::c_uint)
                    as isize,
            );
        let mut i_14: uint32_t = 0 as libc::c_uint;
        let mut x_194: uint64_t = c_12 & *res_j_12.offset(i_14 as isize)
            | !c_12 & tmp0[i_14 as usize];
        let mut os_194: *mut uint64_t = tmp0.as_mut_ptr();
        *os_194.offset(i_14 as isize) = x_194;
        i_14 = (i_14 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_195: uint64_t = c_12 & *res_j_12.offset(i_14 as isize)
            | !c_12 & tmp0[i_14 as usize];
        let mut os_195: *mut uint64_t = tmp0.as_mut_ptr();
        *os_195.offset(i_14 as isize) = x_195;
        i_14 = (i_14 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_196: uint64_t = c_12 & *res_j_12.offset(i_14 as isize)
            | !c_12 & tmp0[i_14 as usize];
        let mut os_196: *mut uint64_t = tmp0.as_mut_ptr();
        *os_196.offset(i_14 as isize) = x_196;
        i_14 = (i_14 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_197: uint64_t = c_12 & *res_j_12.offset(i_14 as isize)
            | !c_12 & tmp0[i_14 as usize];
        let mut os_197: *mut uint64_t = tmp0.as_mut_ptr();
        *os_197.offset(i_14 as isize) = x_197;
        i_14 = (i_14 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_198: uint64_t = c_12 & *res_j_12.offset(i_14 as isize)
            | !c_12 & tmp0[i_14 as usize];
        let mut os_198: *mut uint64_t = tmp0.as_mut_ptr();
        *os_198.offset(i_14 as isize) = x_198;
        i_14 = (i_14 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_199: uint64_t = c_12 & *res_j_12.offset(i_14 as isize)
            | !c_12 & tmp0[i_14 as usize];
        let mut os_199: *mut uint64_t = tmp0.as_mut_ptr();
        *os_199.offset(i_14 as isize) = x_199;
        i_14 = (i_14 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_200: uint64_t = c_12 & *res_j_12.offset(i_14 as isize)
            | !c_12 & tmp0[i_14 as usize];
        let mut os_200: *mut uint64_t = tmp0.as_mut_ptr();
        *os_200.offset(i_14 as isize) = x_200;
        i_14 = (i_14 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_201: uint64_t = c_12 & *res_j_12.offset(i_14 as isize)
            | !c_12 & tmp0[i_14 as usize];
        let mut os_201: *mut uint64_t = tmp0.as_mut_ptr();
        *os_201.offset(i_14 as isize) = x_201;
        i_14 = (i_14 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_202: uint64_t = c_12 & *res_j_12.offset(i_14 as isize)
            | !c_12 & tmp0[i_14 as usize];
        let mut os_202: *mut uint64_t = tmp0.as_mut_ptr();
        *os_202.offset(i_14 as isize) = x_202;
        i_14 = (i_14 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_203: uint64_t = c_12 & *res_j_12.offset(i_14 as isize)
            | !c_12 & tmp0[i_14 as usize];
        let mut os_203: *mut uint64_t = tmp0.as_mut_ptr();
        *os_203.offset(i_14 as isize) = x_203;
        i_14 = (i_14 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_204: uint64_t = c_12 & *res_j_12.offset(i_14 as isize)
            | !c_12 & tmp0[i_14 as usize];
        let mut os_204: *mut uint64_t = tmp0.as_mut_ptr();
        *os_204.offset(i_14 as isize) = x_204;
        i_14 = (i_14 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_205: uint64_t = c_12 & *res_j_12.offset(i_14 as isize)
            | !c_12 & tmp0[i_14 as usize];
        let mut os_205: *mut uint64_t = tmp0.as_mut_ptr();
        *os_205.offset(i_14 as isize) = x_205;
        i_14 = (i_14 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_206: uint64_t = c_12 & *res_j_12.offset(i_14 as isize)
            | !c_12 & tmp0[i_14 as usize];
        let mut os_206: *mut uint64_t = tmp0.as_mut_ptr();
        *os_206.offset(i_14 as isize) = x_206;
        i_14 = (i_14 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_207: uint64_t = c_12 & *res_j_12.offset(i_14 as isize)
            | !c_12 & tmp0[i_14 as usize];
        let mut os_207: *mut uint64_t = tmp0.as_mut_ptr();
        *os_207.offset(i_14 as isize) = x_207;
        i_14 = (i_14 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_208: uint64_t = c_12 & *res_j_12.offset(i_14 as isize)
            | !c_12 & tmp0[i_14 as usize];
        let mut os_208: *mut uint64_t = tmp0.as_mut_ptr();
        *os_208.offset(i_14 as isize) = x_208;
        i_14 = (i_14 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        i1 = (i1 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut c_13: uint64_t = FStar_UInt64_eq_mask(
            bits_l,
            i1.wrapping_add(1 as libc::c_uint) as uint64_t,
        );
        let mut res_j_13: *const uint64_t = table
            .as_mut_ptr()
            .offset(
                i1.wrapping_add(1 as libc::c_uint).wrapping_mul(15 as libc::c_uint)
                    as isize,
            );
        let mut i_15: uint32_t = 0 as libc::c_uint;
        let mut x_209: uint64_t = c_13 & *res_j_13.offset(i_15 as isize)
            | !c_13 & tmp0[i_15 as usize];
        let mut os_209: *mut uint64_t = tmp0.as_mut_ptr();
        *os_209.offset(i_15 as isize) = x_209;
        i_15 = (i_15 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_210: uint64_t = c_13 & *res_j_13.offset(i_15 as isize)
            | !c_13 & tmp0[i_15 as usize];
        let mut os_210: *mut uint64_t = tmp0.as_mut_ptr();
        *os_210.offset(i_15 as isize) = x_210;
        i_15 = (i_15 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_211: uint64_t = c_13 & *res_j_13.offset(i_15 as isize)
            | !c_13 & tmp0[i_15 as usize];
        let mut os_211: *mut uint64_t = tmp0.as_mut_ptr();
        *os_211.offset(i_15 as isize) = x_211;
        i_15 = (i_15 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_212: uint64_t = c_13 & *res_j_13.offset(i_15 as isize)
            | !c_13 & tmp0[i_15 as usize];
        let mut os_212: *mut uint64_t = tmp0.as_mut_ptr();
        *os_212.offset(i_15 as isize) = x_212;
        i_15 = (i_15 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_213: uint64_t = c_13 & *res_j_13.offset(i_15 as isize)
            | !c_13 & tmp0[i_15 as usize];
        let mut os_213: *mut uint64_t = tmp0.as_mut_ptr();
        *os_213.offset(i_15 as isize) = x_213;
        i_15 = (i_15 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_214: uint64_t = c_13 & *res_j_13.offset(i_15 as isize)
            | !c_13 & tmp0[i_15 as usize];
        let mut os_214: *mut uint64_t = tmp0.as_mut_ptr();
        *os_214.offset(i_15 as isize) = x_214;
        i_15 = (i_15 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_215: uint64_t = c_13 & *res_j_13.offset(i_15 as isize)
            | !c_13 & tmp0[i_15 as usize];
        let mut os_215: *mut uint64_t = tmp0.as_mut_ptr();
        *os_215.offset(i_15 as isize) = x_215;
        i_15 = (i_15 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_216: uint64_t = c_13 & *res_j_13.offset(i_15 as isize)
            | !c_13 & tmp0[i_15 as usize];
        let mut os_216: *mut uint64_t = tmp0.as_mut_ptr();
        *os_216.offset(i_15 as isize) = x_216;
        i_15 = (i_15 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_217: uint64_t = c_13 & *res_j_13.offset(i_15 as isize)
            | !c_13 & tmp0[i_15 as usize];
        let mut os_217: *mut uint64_t = tmp0.as_mut_ptr();
        *os_217.offset(i_15 as isize) = x_217;
        i_15 = (i_15 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_218: uint64_t = c_13 & *res_j_13.offset(i_15 as isize)
            | !c_13 & tmp0[i_15 as usize];
        let mut os_218: *mut uint64_t = tmp0.as_mut_ptr();
        *os_218.offset(i_15 as isize) = x_218;
        i_15 = (i_15 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_219: uint64_t = c_13 & *res_j_13.offset(i_15 as isize)
            | !c_13 & tmp0[i_15 as usize];
        let mut os_219: *mut uint64_t = tmp0.as_mut_ptr();
        *os_219.offset(i_15 as isize) = x_219;
        i_15 = (i_15 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_220: uint64_t = c_13 & *res_j_13.offset(i_15 as isize)
            | !c_13 & tmp0[i_15 as usize];
        let mut os_220: *mut uint64_t = tmp0.as_mut_ptr();
        *os_220.offset(i_15 as isize) = x_220;
        i_15 = (i_15 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_221: uint64_t = c_13 & *res_j_13.offset(i_15 as isize)
            | !c_13 & tmp0[i_15 as usize];
        let mut os_221: *mut uint64_t = tmp0.as_mut_ptr();
        *os_221.offset(i_15 as isize) = x_221;
        i_15 = (i_15 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_222: uint64_t = c_13 & *res_j_13.offset(i_15 as isize)
            | !c_13 & tmp0[i_15 as usize];
        let mut os_222: *mut uint64_t = tmp0.as_mut_ptr();
        *os_222.offset(i_15 as isize) = x_222;
        i_15 = (i_15 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_223: uint64_t = c_13 & *res_j_13.offset(i_15 as isize)
            | !c_13 & tmp0[i_15 as usize];
        let mut os_223: *mut uint64_t = tmp0.as_mut_ptr();
        *os_223.offset(i_15 as isize) = x_223;
        i_15 = (i_15 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        i1 = (i1 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut p_copy_10: [uint64_t; 15] = [
            0 as libc::c_uint as uint64_t,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
        ];
        memcpy(
            p_copy_10.as_mut_ptr() as *mut libc::c_void,
            out as *const libc::c_void,
            (15 as libc::c_uint as libc::c_ulong)
                .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
        );
        Hacl_Impl_K256_PointAdd_point_add(
            out,
            p_copy_10.as_mut_ptr(),
            tmp0.as_mut_ptr(),
        );
        i0 = i0.wrapping_add(1);
        i0;
    }
}
#[inline]
unsafe extern "C" fn precomp_get_consttime(
    mut table: *const uint64_t,
    mut bits_l: uint64_t,
    mut tmp: *mut uint64_t,
) {
    memcpy(
        tmp as *mut libc::c_void,
        table as *mut uint64_t as *const libc::c_void,
        (15 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    let mut i0: uint32_t = 0 as libc::c_uint;
    let mut c: uint64_t = FStar_UInt64_eq_mask(
        bits_l,
        i0.wrapping_add(1 as libc::c_uint) as uint64_t,
    );
    let mut res_j: *const uint64_t = table
        .offset(
            i0.wrapping_add(1 as libc::c_uint).wrapping_mul(15 as libc::c_uint) as isize,
        );
    let mut i: uint32_t = 0 as libc::c_uint;
    let mut x: uint64_t = c & *res_j.offset(i as isize) | !c & *tmp.offset(i as isize);
    let mut os: *mut uint64_t = tmp;
    *os.offset(i as isize) = x;
    i = (i as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut x_0: uint64_t = c & *res_j.offset(i as isize) | !c & *tmp.offset(i as isize);
    let mut os_0: *mut uint64_t = tmp;
    *os_0.offset(i as isize) = x_0;
    i = (i as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut x_1: uint64_t = c & *res_j.offset(i as isize) | !c & *tmp.offset(i as isize);
    let mut os_1: *mut uint64_t = tmp;
    *os_1.offset(i as isize) = x_1;
    i = (i as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut x_2: uint64_t = c & *res_j.offset(i as isize) | !c & *tmp.offset(i as isize);
    let mut os_2: *mut uint64_t = tmp;
    *os_2.offset(i as isize) = x_2;
    i = (i as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut x_3: uint64_t = c & *res_j.offset(i as isize) | !c & *tmp.offset(i as isize);
    let mut os_3: *mut uint64_t = tmp;
    *os_3.offset(i as isize) = x_3;
    i = (i as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut x_4: uint64_t = c & *res_j.offset(i as isize) | !c & *tmp.offset(i as isize);
    let mut os_4: *mut uint64_t = tmp;
    *os_4.offset(i as isize) = x_4;
    i = (i as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut x_5: uint64_t = c & *res_j.offset(i as isize) | !c & *tmp.offset(i as isize);
    let mut os_5: *mut uint64_t = tmp;
    *os_5.offset(i as isize) = x_5;
    i = (i as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut x_6: uint64_t = c & *res_j.offset(i as isize) | !c & *tmp.offset(i as isize);
    let mut os_6: *mut uint64_t = tmp;
    *os_6.offset(i as isize) = x_6;
    i = (i as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut x_7: uint64_t = c & *res_j.offset(i as isize) | !c & *tmp.offset(i as isize);
    let mut os_7: *mut uint64_t = tmp;
    *os_7.offset(i as isize) = x_7;
    i = (i as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut x_8: uint64_t = c & *res_j.offset(i as isize) | !c & *tmp.offset(i as isize);
    let mut os_8: *mut uint64_t = tmp;
    *os_8.offset(i as isize) = x_8;
    i = (i as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut x_9: uint64_t = c & *res_j.offset(i as isize) | !c & *tmp.offset(i as isize);
    let mut os_9: *mut uint64_t = tmp;
    *os_9.offset(i as isize) = x_9;
    i = (i as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut x_10: uint64_t = c & *res_j.offset(i as isize)
        | !c & *tmp.offset(i as isize);
    let mut os_10: *mut uint64_t = tmp;
    *os_10.offset(i as isize) = x_10;
    i = (i as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut x_11: uint64_t = c & *res_j.offset(i as isize)
        | !c & *tmp.offset(i as isize);
    let mut os_11: *mut uint64_t = tmp;
    *os_11.offset(i as isize) = x_11;
    i = (i as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut x_12: uint64_t = c & *res_j.offset(i as isize)
        | !c & *tmp.offset(i as isize);
    let mut os_12: *mut uint64_t = tmp;
    *os_12.offset(i as isize) = x_12;
    i = (i as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut x_13: uint64_t = c & *res_j.offset(i as isize)
        | !c & *tmp.offset(i as isize);
    let mut os_13: *mut uint64_t = tmp;
    *os_13.offset(i as isize) = x_13;
    i = (i as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    i0 = (i0 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut c_0: uint64_t = FStar_UInt64_eq_mask(
        bits_l,
        i0.wrapping_add(1 as libc::c_uint) as uint64_t,
    );
    let mut res_j_0: *const uint64_t = table
        .offset(
            i0.wrapping_add(1 as libc::c_uint).wrapping_mul(15 as libc::c_uint) as isize,
        );
    let mut i_0: uint32_t = 0 as libc::c_uint;
    let mut x_14: uint64_t = c_0 & *res_j_0.offset(i_0 as isize)
        | !c_0 & *tmp.offset(i_0 as isize);
    let mut os_14: *mut uint64_t = tmp;
    *os_14.offset(i_0 as isize) = x_14;
    i_0 = (i_0 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut x_15: uint64_t = c_0 & *res_j_0.offset(i_0 as isize)
        | !c_0 & *tmp.offset(i_0 as isize);
    let mut os_15: *mut uint64_t = tmp;
    *os_15.offset(i_0 as isize) = x_15;
    i_0 = (i_0 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut x_16: uint64_t = c_0 & *res_j_0.offset(i_0 as isize)
        | !c_0 & *tmp.offset(i_0 as isize);
    let mut os_16: *mut uint64_t = tmp;
    *os_16.offset(i_0 as isize) = x_16;
    i_0 = (i_0 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut x_17: uint64_t = c_0 & *res_j_0.offset(i_0 as isize)
        | !c_0 & *tmp.offset(i_0 as isize);
    let mut os_17: *mut uint64_t = tmp;
    *os_17.offset(i_0 as isize) = x_17;
    i_0 = (i_0 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut x_18: uint64_t = c_0 & *res_j_0.offset(i_0 as isize)
        | !c_0 & *tmp.offset(i_0 as isize);
    let mut os_18: *mut uint64_t = tmp;
    *os_18.offset(i_0 as isize) = x_18;
    i_0 = (i_0 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut x_19: uint64_t = c_0 & *res_j_0.offset(i_0 as isize)
        | !c_0 & *tmp.offset(i_0 as isize);
    let mut os_19: *mut uint64_t = tmp;
    *os_19.offset(i_0 as isize) = x_19;
    i_0 = (i_0 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut x_20: uint64_t = c_0 & *res_j_0.offset(i_0 as isize)
        | !c_0 & *tmp.offset(i_0 as isize);
    let mut os_20: *mut uint64_t = tmp;
    *os_20.offset(i_0 as isize) = x_20;
    i_0 = (i_0 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut x_21: uint64_t = c_0 & *res_j_0.offset(i_0 as isize)
        | !c_0 & *tmp.offset(i_0 as isize);
    let mut os_21: *mut uint64_t = tmp;
    *os_21.offset(i_0 as isize) = x_21;
    i_0 = (i_0 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut x_22: uint64_t = c_0 & *res_j_0.offset(i_0 as isize)
        | !c_0 & *tmp.offset(i_0 as isize);
    let mut os_22: *mut uint64_t = tmp;
    *os_22.offset(i_0 as isize) = x_22;
    i_0 = (i_0 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut x_23: uint64_t = c_0 & *res_j_0.offset(i_0 as isize)
        | !c_0 & *tmp.offset(i_0 as isize);
    let mut os_23: *mut uint64_t = tmp;
    *os_23.offset(i_0 as isize) = x_23;
    i_0 = (i_0 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut x_24: uint64_t = c_0 & *res_j_0.offset(i_0 as isize)
        | !c_0 & *tmp.offset(i_0 as isize);
    let mut os_24: *mut uint64_t = tmp;
    *os_24.offset(i_0 as isize) = x_24;
    i_0 = (i_0 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut x_25: uint64_t = c_0 & *res_j_0.offset(i_0 as isize)
        | !c_0 & *tmp.offset(i_0 as isize);
    let mut os_25: *mut uint64_t = tmp;
    *os_25.offset(i_0 as isize) = x_25;
    i_0 = (i_0 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut x_26: uint64_t = c_0 & *res_j_0.offset(i_0 as isize)
        | !c_0 & *tmp.offset(i_0 as isize);
    let mut os_26: *mut uint64_t = tmp;
    *os_26.offset(i_0 as isize) = x_26;
    i_0 = (i_0 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut x_27: uint64_t = c_0 & *res_j_0.offset(i_0 as isize)
        | !c_0 & *tmp.offset(i_0 as isize);
    let mut os_27: *mut uint64_t = tmp;
    *os_27.offset(i_0 as isize) = x_27;
    i_0 = (i_0 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut x_28: uint64_t = c_0 & *res_j_0.offset(i_0 as isize)
        | !c_0 & *tmp.offset(i_0 as isize);
    let mut os_28: *mut uint64_t = tmp;
    *os_28.offset(i_0 as isize) = x_28;
    i_0 = (i_0 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    i0 = (i0 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut c_1: uint64_t = FStar_UInt64_eq_mask(
        bits_l,
        i0.wrapping_add(1 as libc::c_uint) as uint64_t,
    );
    let mut res_j_1: *const uint64_t = table
        .offset(
            i0.wrapping_add(1 as libc::c_uint).wrapping_mul(15 as libc::c_uint) as isize,
        );
    let mut i_1: uint32_t = 0 as libc::c_uint;
    let mut x_29: uint64_t = c_1 & *res_j_1.offset(i_1 as isize)
        | !c_1 & *tmp.offset(i_1 as isize);
    let mut os_29: *mut uint64_t = tmp;
    *os_29.offset(i_1 as isize) = x_29;
    i_1 = (i_1 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut x_30: uint64_t = c_1 & *res_j_1.offset(i_1 as isize)
        | !c_1 & *tmp.offset(i_1 as isize);
    let mut os_30: *mut uint64_t = tmp;
    *os_30.offset(i_1 as isize) = x_30;
    i_1 = (i_1 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut x_31: uint64_t = c_1 & *res_j_1.offset(i_1 as isize)
        | !c_1 & *tmp.offset(i_1 as isize);
    let mut os_31: *mut uint64_t = tmp;
    *os_31.offset(i_1 as isize) = x_31;
    i_1 = (i_1 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut x_32: uint64_t = c_1 & *res_j_1.offset(i_1 as isize)
        | !c_1 & *tmp.offset(i_1 as isize);
    let mut os_32: *mut uint64_t = tmp;
    *os_32.offset(i_1 as isize) = x_32;
    i_1 = (i_1 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut x_33: uint64_t = c_1 & *res_j_1.offset(i_1 as isize)
        | !c_1 & *tmp.offset(i_1 as isize);
    let mut os_33: *mut uint64_t = tmp;
    *os_33.offset(i_1 as isize) = x_33;
    i_1 = (i_1 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut x_34: uint64_t = c_1 & *res_j_1.offset(i_1 as isize)
        | !c_1 & *tmp.offset(i_1 as isize);
    let mut os_34: *mut uint64_t = tmp;
    *os_34.offset(i_1 as isize) = x_34;
    i_1 = (i_1 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut x_35: uint64_t = c_1 & *res_j_1.offset(i_1 as isize)
        | !c_1 & *tmp.offset(i_1 as isize);
    let mut os_35: *mut uint64_t = tmp;
    *os_35.offset(i_1 as isize) = x_35;
    i_1 = (i_1 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut x_36: uint64_t = c_1 & *res_j_1.offset(i_1 as isize)
        | !c_1 & *tmp.offset(i_1 as isize);
    let mut os_36: *mut uint64_t = tmp;
    *os_36.offset(i_1 as isize) = x_36;
    i_1 = (i_1 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut x_37: uint64_t = c_1 & *res_j_1.offset(i_1 as isize)
        | !c_1 & *tmp.offset(i_1 as isize);
    let mut os_37: *mut uint64_t = tmp;
    *os_37.offset(i_1 as isize) = x_37;
    i_1 = (i_1 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut x_38: uint64_t = c_1 & *res_j_1.offset(i_1 as isize)
        | !c_1 & *tmp.offset(i_1 as isize);
    let mut os_38: *mut uint64_t = tmp;
    *os_38.offset(i_1 as isize) = x_38;
    i_1 = (i_1 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut x_39: uint64_t = c_1 & *res_j_1.offset(i_1 as isize)
        | !c_1 & *tmp.offset(i_1 as isize);
    let mut os_39: *mut uint64_t = tmp;
    *os_39.offset(i_1 as isize) = x_39;
    i_1 = (i_1 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut x_40: uint64_t = c_1 & *res_j_1.offset(i_1 as isize)
        | !c_1 & *tmp.offset(i_1 as isize);
    let mut os_40: *mut uint64_t = tmp;
    *os_40.offset(i_1 as isize) = x_40;
    i_1 = (i_1 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut x_41: uint64_t = c_1 & *res_j_1.offset(i_1 as isize)
        | !c_1 & *tmp.offset(i_1 as isize);
    let mut os_41: *mut uint64_t = tmp;
    *os_41.offset(i_1 as isize) = x_41;
    i_1 = (i_1 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut x_42: uint64_t = c_1 & *res_j_1.offset(i_1 as isize)
        | !c_1 & *tmp.offset(i_1 as isize);
    let mut os_42: *mut uint64_t = tmp;
    *os_42.offset(i_1 as isize) = x_42;
    i_1 = (i_1 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut x_43: uint64_t = c_1 & *res_j_1.offset(i_1 as isize)
        | !c_1 & *tmp.offset(i_1 as isize);
    let mut os_43: *mut uint64_t = tmp;
    *os_43.offset(i_1 as isize) = x_43;
    i_1 = (i_1 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    i0 = (i0 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut c_2: uint64_t = FStar_UInt64_eq_mask(
        bits_l,
        i0.wrapping_add(1 as libc::c_uint) as uint64_t,
    );
    let mut res_j_2: *const uint64_t = table
        .offset(
            i0.wrapping_add(1 as libc::c_uint).wrapping_mul(15 as libc::c_uint) as isize,
        );
    let mut i_2: uint32_t = 0 as libc::c_uint;
    let mut x_44: uint64_t = c_2 & *res_j_2.offset(i_2 as isize)
        | !c_2 & *tmp.offset(i_2 as isize);
    let mut os_44: *mut uint64_t = tmp;
    *os_44.offset(i_2 as isize) = x_44;
    i_2 = (i_2 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut x_45: uint64_t = c_2 & *res_j_2.offset(i_2 as isize)
        | !c_2 & *tmp.offset(i_2 as isize);
    let mut os_45: *mut uint64_t = tmp;
    *os_45.offset(i_2 as isize) = x_45;
    i_2 = (i_2 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut x_46: uint64_t = c_2 & *res_j_2.offset(i_2 as isize)
        | !c_2 & *tmp.offset(i_2 as isize);
    let mut os_46: *mut uint64_t = tmp;
    *os_46.offset(i_2 as isize) = x_46;
    i_2 = (i_2 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut x_47: uint64_t = c_2 & *res_j_2.offset(i_2 as isize)
        | !c_2 & *tmp.offset(i_2 as isize);
    let mut os_47: *mut uint64_t = tmp;
    *os_47.offset(i_2 as isize) = x_47;
    i_2 = (i_2 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut x_48: uint64_t = c_2 & *res_j_2.offset(i_2 as isize)
        | !c_2 & *tmp.offset(i_2 as isize);
    let mut os_48: *mut uint64_t = tmp;
    *os_48.offset(i_2 as isize) = x_48;
    i_2 = (i_2 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut x_49: uint64_t = c_2 & *res_j_2.offset(i_2 as isize)
        | !c_2 & *tmp.offset(i_2 as isize);
    let mut os_49: *mut uint64_t = tmp;
    *os_49.offset(i_2 as isize) = x_49;
    i_2 = (i_2 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut x_50: uint64_t = c_2 & *res_j_2.offset(i_2 as isize)
        | !c_2 & *tmp.offset(i_2 as isize);
    let mut os_50: *mut uint64_t = tmp;
    *os_50.offset(i_2 as isize) = x_50;
    i_2 = (i_2 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut x_51: uint64_t = c_2 & *res_j_2.offset(i_2 as isize)
        | !c_2 & *tmp.offset(i_2 as isize);
    let mut os_51: *mut uint64_t = tmp;
    *os_51.offset(i_2 as isize) = x_51;
    i_2 = (i_2 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut x_52: uint64_t = c_2 & *res_j_2.offset(i_2 as isize)
        | !c_2 & *tmp.offset(i_2 as isize);
    let mut os_52: *mut uint64_t = tmp;
    *os_52.offset(i_2 as isize) = x_52;
    i_2 = (i_2 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut x_53: uint64_t = c_2 & *res_j_2.offset(i_2 as isize)
        | !c_2 & *tmp.offset(i_2 as isize);
    let mut os_53: *mut uint64_t = tmp;
    *os_53.offset(i_2 as isize) = x_53;
    i_2 = (i_2 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut x_54: uint64_t = c_2 & *res_j_2.offset(i_2 as isize)
        | !c_2 & *tmp.offset(i_2 as isize);
    let mut os_54: *mut uint64_t = tmp;
    *os_54.offset(i_2 as isize) = x_54;
    i_2 = (i_2 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut x_55: uint64_t = c_2 & *res_j_2.offset(i_2 as isize)
        | !c_2 & *tmp.offset(i_2 as isize);
    let mut os_55: *mut uint64_t = tmp;
    *os_55.offset(i_2 as isize) = x_55;
    i_2 = (i_2 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut x_56: uint64_t = c_2 & *res_j_2.offset(i_2 as isize)
        | !c_2 & *tmp.offset(i_2 as isize);
    let mut os_56: *mut uint64_t = tmp;
    *os_56.offset(i_2 as isize) = x_56;
    i_2 = (i_2 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut x_57: uint64_t = c_2 & *res_j_2.offset(i_2 as isize)
        | !c_2 & *tmp.offset(i_2 as isize);
    let mut os_57: *mut uint64_t = tmp;
    *os_57.offset(i_2 as isize) = x_57;
    i_2 = (i_2 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut x_58: uint64_t = c_2 & *res_j_2.offset(i_2 as isize)
        | !c_2 & *tmp.offset(i_2 as isize);
    let mut os_58: *mut uint64_t = tmp;
    *os_58.offset(i_2 as isize) = x_58;
    i_2 = (i_2 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    i0 = (i0 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut c_3: uint64_t = FStar_UInt64_eq_mask(
        bits_l,
        i0.wrapping_add(1 as libc::c_uint) as uint64_t,
    );
    let mut res_j_3: *const uint64_t = table
        .offset(
            i0.wrapping_add(1 as libc::c_uint).wrapping_mul(15 as libc::c_uint) as isize,
        );
    let mut i_3: uint32_t = 0 as libc::c_uint;
    let mut x_59: uint64_t = c_3 & *res_j_3.offset(i_3 as isize)
        | !c_3 & *tmp.offset(i_3 as isize);
    let mut os_59: *mut uint64_t = tmp;
    *os_59.offset(i_3 as isize) = x_59;
    i_3 = (i_3 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut x_60: uint64_t = c_3 & *res_j_3.offset(i_3 as isize)
        | !c_3 & *tmp.offset(i_3 as isize);
    let mut os_60: *mut uint64_t = tmp;
    *os_60.offset(i_3 as isize) = x_60;
    i_3 = (i_3 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut x_61: uint64_t = c_3 & *res_j_3.offset(i_3 as isize)
        | !c_3 & *tmp.offset(i_3 as isize);
    let mut os_61: *mut uint64_t = tmp;
    *os_61.offset(i_3 as isize) = x_61;
    i_3 = (i_3 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut x_62: uint64_t = c_3 & *res_j_3.offset(i_3 as isize)
        | !c_3 & *tmp.offset(i_3 as isize);
    let mut os_62: *mut uint64_t = tmp;
    *os_62.offset(i_3 as isize) = x_62;
    i_3 = (i_3 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut x_63: uint64_t = c_3 & *res_j_3.offset(i_3 as isize)
        | !c_3 & *tmp.offset(i_3 as isize);
    let mut os_63: *mut uint64_t = tmp;
    *os_63.offset(i_3 as isize) = x_63;
    i_3 = (i_3 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut x_64: uint64_t = c_3 & *res_j_3.offset(i_3 as isize)
        | !c_3 & *tmp.offset(i_3 as isize);
    let mut os_64: *mut uint64_t = tmp;
    *os_64.offset(i_3 as isize) = x_64;
    i_3 = (i_3 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut x_65: uint64_t = c_3 & *res_j_3.offset(i_3 as isize)
        | !c_3 & *tmp.offset(i_3 as isize);
    let mut os_65: *mut uint64_t = tmp;
    *os_65.offset(i_3 as isize) = x_65;
    i_3 = (i_3 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut x_66: uint64_t = c_3 & *res_j_3.offset(i_3 as isize)
        | !c_3 & *tmp.offset(i_3 as isize);
    let mut os_66: *mut uint64_t = tmp;
    *os_66.offset(i_3 as isize) = x_66;
    i_3 = (i_3 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut x_67: uint64_t = c_3 & *res_j_3.offset(i_3 as isize)
        | !c_3 & *tmp.offset(i_3 as isize);
    let mut os_67: *mut uint64_t = tmp;
    *os_67.offset(i_3 as isize) = x_67;
    i_3 = (i_3 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut x_68: uint64_t = c_3 & *res_j_3.offset(i_3 as isize)
        | !c_3 & *tmp.offset(i_3 as isize);
    let mut os_68: *mut uint64_t = tmp;
    *os_68.offset(i_3 as isize) = x_68;
    i_3 = (i_3 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut x_69: uint64_t = c_3 & *res_j_3.offset(i_3 as isize)
        | !c_3 & *tmp.offset(i_3 as isize);
    let mut os_69: *mut uint64_t = tmp;
    *os_69.offset(i_3 as isize) = x_69;
    i_3 = (i_3 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut x_70: uint64_t = c_3 & *res_j_3.offset(i_3 as isize)
        | !c_3 & *tmp.offset(i_3 as isize);
    let mut os_70: *mut uint64_t = tmp;
    *os_70.offset(i_3 as isize) = x_70;
    i_3 = (i_3 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut x_71: uint64_t = c_3 & *res_j_3.offset(i_3 as isize)
        | !c_3 & *tmp.offset(i_3 as isize);
    let mut os_71: *mut uint64_t = tmp;
    *os_71.offset(i_3 as isize) = x_71;
    i_3 = (i_3 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut x_72: uint64_t = c_3 & *res_j_3.offset(i_3 as isize)
        | !c_3 & *tmp.offset(i_3 as isize);
    let mut os_72: *mut uint64_t = tmp;
    *os_72.offset(i_3 as isize) = x_72;
    i_3 = (i_3 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut x_73: uint64_t = c_3 & *res_j_3.offset(i_3 as isize)
        | !c_3 & *tmp.offset(i_3 as isize);
    let mut os_73: *mut uint64_t = tmp;
    *os_73.offset(i_3 as isize) = x_73;
    i_3 = (i_3 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    i0 = (i0 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut c_4: uint64_t = FStar_UInt64_eq_mask(
        bits_l,
        i0.wrapping_add(1 as libc::c_uint) as uint64_t,
    );
    let mut res_j_4: *const uint64_t = table
        .offset(
            i0.wrapping_add(1 as libc::c_uint).wrapping_mul(15 as libc::c_uint) as isize,
        );
    let mut i_4: uint32_t = 0 as libc::c_uint;
    let mut x_74: uint64_t = c_4 & *res_j_4.offset(i_4 as isize)
        | !c_4 & *tmp.offset(i_4 as isize);
    let mut os_74: *mut uint64_t = tmp;
    *os_74.offset(i_4 as isize) = x_74;
    i_4 = (i_4 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut x_75: uint64_t = c_4 & *res_j_4.offset(i_4 as isize)
        | !c_4 & *tmp.offset(i_4 as isize);
    let mut os_75: *mut uint64_t = tmp;
    *os_75.offset(i_4 as isize) = x_75;
    i_4 = (i_4 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut x_76: uint64_t = c_4 & *res_j_4.offset(i_4 as isize)
        | !c_4 & *tmp.offset(i_4 as isize);
    let mut os_76: *mut uint64_t = tmp;
    *os_76.offset(i_4 as isize) = x_76;
    i_4 = (i_4 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut x_77: uint64_t = c_4 & *res_j_4.offset(i_4 as isize)
        | !c_4 & *tmp.offset(i_4 as isize);
    let mut os_77: *mut uint64_t = tmp;
    *os_77.offset(i_4 as isize) = x_77;
    i_4 = (i_4 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut x_78: uint64_t = c_4 & *res_j_4.offset(i_4 as isize)
        | !c_4 & *tmp.offset(i_4 as isize);
    let mut os_78: *mut uint64_t = tmp;
    *os_78.offset(i_4 as isize) = x_78;
    i_4 = (i_4 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut x_79: uint64_t = c_4 & *res_j_4.offset(i_4 as isize)
        | !c_4 & *tmp.offset(i_4 as isize);
    let mut os_79: *mut uint64_t = tmp;
    *os_79.offset(i_4 as isize) = x_79;
    i_4 = (i_4 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut x_80: uint64_t = c_4 & *res_j_4.offset(i_4 as isize)
        | !c_4 & *tmp.offset(i_4 as isize);
    let mut os_80: *mut uint64_t = tmp;
    *os_80.offset(i_4 as isize) = x_80;
    i_4 = (i_4 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut x_81: uint64_t = c_4 & *res_j_4.offset(i_4 as isize)
        | !c_4 & *tmp.offset(i_4 as isize);
    let mut os_81: *mut uint64_t = tmp;
    *os_81.offset(i_4 as isize) = x_81;
    i_4 = (i_4 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut x_82: uint64_t = c_4 & *res_j_4.offset(i_4 as isize)
        | !c_4 & *tmp.offset(i_4 as isize);
    let mut os_82: *mut uint64_t = tmp;
    *os_82.offset(i_4 as isize) = x_82;
    i_4 = (i_4 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut x_83: uint64_t = c_4 & *res_j_4.offset(i_4 as isize)
        | !c_4 & *tmp.offset(i_4 as isize);
    let mut os_83: *mut uint64_t = tmp;
    *os_83.offset(i_4 as isize) = x_83;
    i_4 = (i_4 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut x_84: uint64_t = c_4 & *res_j_4.offset(i_4 as isize)
        | !c_4 & *tmp.offset(i_4 as isize);
    let mut os_84: *mut uint64_t = tmp;
    *os_84.offset(i_4 as isize) = x_84;
    i_4 = (i_4 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut x_85: uint64_t = c_4 & *res_j_4.offset(i_4 as isize)
        | !c_4 & *tmp.offset(i_4 as isize);
    let mut os_85: *mut uint64_t = tmp;
    *os_85.offset(i_4 as isize) = x_85;
    i_4 = (i_4 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut x_86: uint64_t = c_4 & *res_j_4.offset(i_4 as isize)
        | !c_4 & *tmp.offset(i_4 as isize);
    let mut os_86: *mut uint64_t = tmp;
    *os_86.offset(i_4 as isize) = x_86;
    i_4 = (i_4 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut x_87: uint64_t = c_4 & *res_j_4.offset(i_4 as isize)
        | !c_4 & *tmp.offset(i_4 as isize);
    let mut os_87: *mut uint64_t = tmp;
    *os_87.offset(i_4 as isize) = x_87;
    i_4 = (i_4 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut x_88: uint64_t = c_4 & *res_j_4.offset(i_4 as isize)
        | !c_4 & *tmp.offset(i_4 as isize);
    let mut os_88: *mut uint64_t = tmp;
    *os_88.offset(i_4 as isize) = x_88;
    i_4 = (i_4 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    i0 = (i0 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut c_5: uint64_t = FStar_UInt64_eq_mask(
        bits_l,
        i0.wrapping_add(1 as libc::c_uint) as uint64_t,
    );
    let mut res_j_5: *const uint64_t = table
        .offset(
            i0.wrapping_add(1 as libc::c_uint).wrapping_mul(15 as libc::c_uint) as isize,
        );
    let mut i_5: uint32_t = 0 as libc::c_uint;
    let mut x_89: uint64_t = c_5 & *res_j_5.offset(i_5 as isize)
        | !c_5 & *tmp.offset(i_5 as isize);
    let mut os_89: *mut uint64_t = tmp;
    *os_89.offset(i_5 as isize) = x_89;
    i_5 = (i_5 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut x_90: uint64_t = c_5 & *res_j_5.offset(i_5 as isize)
        | !c_5 & *tmp.offset(i_5 as isize);
    let mut os_90: *mut uint64_t = tmp;
    *os_90.offset(i_5 as isize) = x_90;
    i_5 = (i_5 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut x_91: uint64_t = c_5 & *res_j_5.offset(i_5 as isize)
        | !c_5 & *tmp.offset(i_5 as isize);
    let mut os_91: *mut uint64_t = tmp;
    *os_91.offset(i_5 as isize) = x_91;
    i_5 = (i_5 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut x_92: uint64_t = c_5 & *res_j_5.offset(i_5 as isize)
        | !c_5 & *tmp.offset(i_5 as isize);
    let mut os_92: *mut uint64_t = tmp;
    *os_92.offset(i_5 as isize) = x_92;
    i_5 = (i_5 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut x_93: uint64_t = c_5 & *res_j_5.offset(i_5 as isize)
        | !c_5 & *tmp.offset(i_5 as isize);
    let mut os_93: *mut uint64_t = tmp;
    *os_93.offset(i_5 as isize) = x_93;
    i_5 = (i_5 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut x_94: uint64_t = c_5 & *res_j_5.offset(i_5 as isize)
        | !c_5 & *tmp.offset(i_5 as isize);
    let mut os_94: *mut uint64_t = tmp;
    *os_94.offset(i_5 as isize) = x_94;
    i_5 = (i_5 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut x_95: uint64_t = c_5 & *res_j_5.offset(i_5 as isize)
        | !c_5 & *tmp.offset(i_5 as isize);
    let mut os_95: *mut uint64_t = tmp;
    *os_95.offset(i_5 as isize) = x_95;
    i_5 = (i_5 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut x_96: uint64_t = c_5 & *res_j_5.offset(i_5 as isize)
        | !c_5 & *tmp.offset(i_5 as isize);
    let mut os_96: *mut uint64_t = tmp;
    *os_96.offset(i_5 as isize) = x_96;
    i_5 = (i_5 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut x_97: uint64_t = c_5 & *res_j_5.offset(i_5 as isize)
        | !c_5 & *tmp.offset(i_5 as isize);
    let mut os_97: *mut uint64_t = tmp;
    *os_97.offset(i_5 as isize) = x_97;
    i_5 = (i_5 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut x_98: uint64_t = c_5 & *res_j_5.offset(i_5 as isize)
        | !c_5 & *tmp.offset(i_5 as isize);
    let mut os_98: *mut uint64_t = tmp;
    *os_98.offset(i_5 as isize) = x_98;
    i_5 = (i_5 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut x_99: uint64_t = c_5 & *res_j_5.offset(i_5 as isize)
        | !c_5 & *tmp.offset(i_5 as isize);
    let mut os_99: *mut uint64_t = tmp;
    *os_99.offset(i_5 as isize) = x_99;
    i_5 = (i_5 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut x_100: uint64_t = c_5 & *res_j_5.offset(i_5 as isize)
        | !c_5 & *tmp.offset(i_5 as isize);
    let mut os_100: *mut uint64_t = tmp;
    *os_100.offset(i_5 as isize) = x_100;
    i_5 = (i_5 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut x_101: uint64_t = c_5 & *res_j_5.offset(i_5 as isize)
        | !c_5 & *tmp.offset(i_5 as isize);
    let mut os_101: *mut uint64_t = tmp;
    *os_101.offset(i_5 as isize) = x_101;
    i_5 = (i_5 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut x_102: uint64_t = c_5 & *res_j_5.offset(i_5 as isize)
        | !c_5 & *tmp.offset(i_5 as isize);
    let mut os_102: *mut uint64_t = tmp;
    *os_102.offset(i_5 as isize) = x_102;
    i_5 = (i_5 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut x_103: uint64_t = c_5 & *res_j_5.offset(i_5 as isize)
        | !c_5 & *tmp.offset(i_5 as isize);
    let mut os_103: *mut uint64_t = tmp;
    *os_103.offset(i_5 as isize) = x_103;
    i_5 = (i_5 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    i0 = (i0 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut c_6: uint64_t = FStar_UInt64_eq_mask(
        bits_l,
        i0.wrapping_add(1 as libc::c_uint) as uint64_t,
    );
    let mut res_j_6: *const uint64_t = table
        .offset(
            i0.wrapping_add(1 as libc::c_uint).wrapping_mul(15 as libc::c_uint) as isize,
        );
    let mut i_6: uint32_t = 0 as libc::c_uint;
    let mut x_104: uint64_t = c_6 & *res_j_6.offset(i_6 as isize)
        | !c_6 & *tmp.offset(i_6 as isize);
    let mut os_104: *mut uint64_t = tmp;
    *os_104.offset(i_6 as isize) = x_104;
    i_6 = (i_6 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut x_105: uint64_t = c_6 & *res_j_6.offset(i_6 as isize)
        | !c_6 & *tmp.offset(i_6 as isize);
    let mut os_105: *mut uint64_t = tmp;
    *os_105.offset(i_6 as isize) = x_105;
    i_6 = (i_6 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut x_106: uint64_t = c_6 & *res_j_6.offset(i_6 as isize)
        | !c_6 & *tmp.offset(i_6 as isize);
    let mut os_106: *mut uint64_t = tmp;
    *os_106.offset(i_6 as isize) = x_106;
    i_6 = (i_6 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut x_107: uint64_t = c_6 & *res_j_6.offset(i_6 as isize)
        | !c_6 & *tmp.offset(i_6 as isize);
    let mut os_107: *mut uint64_t = tmp;
    *os_107.offset(i_6 as isize) = x_107;
    i_6 = (i_6 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut x_108: uint64_t = c_6 & *res_j_6.offset(i_6 as isize)
        | !c_6 & *tmp.offset(i_6 as isize);
    let mut os_108: *mut uint64_t = tmp;
    *os_108.offset(i_6 as isize) = x_108;
    i_6 = (i_6 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut x_109: uint64_t = c_6 & *res_j_6.offset(i_6 as isize)
        | !c_6 & *tmp.offset(i_6 as isize);
    let mut os_109: *mut uint64_t = tmp;
    *os_109.offset(i_6 as isize) = x_109;
    i_6 = (i_6 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut x_110: uint64_t = c_6 & *res_j_6.offset(i_6 as isize)
        | !c_6 & *tmp.offset(i_6 as isize);
    let mut os_110: *mut uint64_t = tmp;
    *os_110.offset(i_6 as isize) = x_110;
    i_6 = (i_6 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut x_111: uint64_t = c_6 & *res_j_6.offset(i_6 as isize)
        | !c_6 & *tmp.offset(i_6 as isize);
    let mut os_111: *mut uint64_t = tmp;
    *os_111.offset(i_6 as isize) = x_111;
    i_6 = (i_6 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut x_112: uint64_t = c_6 & *res_j_6.offset(i_6 as isize)
        | !c_6 & *tmp.offset(i_6 as isize);
    let mut os_112: *mut uint64_t = tmp;
    *os_112.offset(i_6 as isize) = x_112;
    i_6 = (i_6 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut x_113: uint64_t = c_6 & *res_j_6.offset(i_6 as isize)
        | !c_6 & *tmp.offset(i_6 as isize);
    let mut os_113: *mut uint64_t = tmp;
    *os_113.offset(i_6 as isize) = x_113;
    i_6 = (i_6 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut x_114: uint64_t = c_6 & *res_j_6.offset(i_6 as isize)
        | !c_6 & *tmp.offset(i_6 as isize);
    let mut os_114: *mut uint64_t = tmp;
    *os_114.offset(i_6 as isize) = x_114;
    i_6 = (i_6 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut x_115: uint64_t = c_6 & *res_j_6.offset(i_6 as isize)
        | !c_6 & *tmp.offset(i_6 as isize);
    let mut os_115: *mut uint64_t = tmp;
    *os_115.offset(i_6 as isize) = x_115;
    i_6 = (i_6 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut x_116: uint64_t = c_6 & *res_j_6.offset(i_6 as isize)
        | !c_6 & *tmp.offset(i_6 as isize);
    let mut os_116: *mut uint64_t = tmp;
    *os_116.offset(i_6 as isize) = x_116;
    i_6 = (i_6 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut x_117: uint64_t = c_6 & *res_j_6.offset(i_6 as isize)
        | !c_6 & *tmp.offset(i_6 as isize);
    let mut os_117: *mut uint64_t = tmp;
    *os_117.offset(i_6 as isize) = x_117;
    i_6 = (i_6 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut x_118: uint64_t = c_6 & *res_j_6.offset(i_6 as isize)
        | !c_6 & *tmp.offset(i_6 as isize);
    let mut os_118: *mut uint64_t = tmp;
    *os_118.offset(i_6 as isize) = x_118;
    i_6 = (i_6 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    i0 = (i0 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut c_7: uint64_t = FStar_UInt64_eq_mask(
        bits_l,
        i0.wrapping_add(1 as libc::c_uint) as uint64_t,
    );
    let mut res_j_7: *const uint64_t = table
        .offset(
            i0.wrapping_add(1 as libc::c_uint).wrapping_mul(15 as libc::c_uint) as isize,
        );
    let mut i_7: uint32_t = 0 as libc::c_uint;
    let mut x_119: uint64_t = c_7 & *res_j_7.offset(i_7 as isize)
        | !c_7 & *tmp.offset(i_7 as isize);
    let mut os_119: *mut uint64_t = tmp;
    *os_119.offset(i_7 as isize) = x_119;
    i_7 = (i_7 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut x_120: uint64_t = c_7 & *res_j_7.offset(i_7 as isize)
        | !c_7 & *tmp.offset(i_7 as isize);
    let mut os_120: *mut uint64_t = tmp;
    *os_120.offset(i_7 as isize) = x_120;
    i_7 = (i_7 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut x_121: uint64_t = c_7 & *res_j_7.offset(i_7 as isize)
        | !c_7 & *tmp.offset(i_7 as isize);
    let mut os_121: *mut uint64_t = tmp;
    *os_121.offset(i_7 as isize) = x_121;
    i_7 = (i_7 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut x_122: uint64_t = c_7 & *res_j_7.offset(i_7 as isize)
        | !c_7 & *tmp.offset(i_7 as isize);
    let mut os_122: *mut uint64_t = tmp;
    *os_122.offset(i_7 as isize) = x_122;
    i_7 = (i_7 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut x_123: uint64_t = c_7 & *res_j_7.offset(i_7 as isize)
        | !c_7 & *tmp.offset(i_7 as isize);
    let mut os_123: *mut uint64_t = tmp;
    *os_123.offset(i_7 as isize) = x_123;
    i_7 = (i_7 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut x_124: uint64_t = c_7 & *res_j_7.offset(i_7 as isize)
        | !c_7 & *tmp.offset(i_7 as isize);
    let mut os_124: *mut uint64_t = tmp;
    *os_124.offset(i_7 as isize) = x_124;
    i_7 = (i_7 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut x_125: uint64_t = c_7 & *res_j_7.offset(i_7 as isize)
        | !c_7 & *tmp.offset(i_7 as isize);
    let mut os_125: *mut uint64_t = tmp;
    *os_125.offset(i_7 as isize) = x_125;
    i_7 = (i_7 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut x_126: uint64_t = c_7 & *res_j_7.offset(i_7 as isize)
        | !c_7 & *tmp.offset(i_7 as isize);
    let mut os_126: *mut uint64_t = tmp;
    *os_126.offset(i_7 as isize) = x_126;
    i_7 = (i_7 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut x_127: uint64_t = c_7 & *res_j_7.offset(i_7 as isize)
        | !c_7 & *tmp.offset(i_7 as isize);
    let mut os_127: *mut uint64_t = tmp;
    *os_127.offset(i_7 as isize) = x_127;
    i_7 = (i_7 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut x_128: uint64_t = c_7 & *res_j_7.offset(i_7 as isize)
        | !c_7 & *tmp.offset(i_7 as isize);
    let mut os_128: *mut uint64_t = tmp;
    *os_128.offset(i_7 as isize) = x_128;
    i_7 = (i_7 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut x_129: uint64_t = c_7 & *res_j_7.offset(i_7 as isize)
        | !c_7 & *tmp.offset(i_7 as isize);
    let mut os_129: *mut uint64_t = tmp;
    *os_129.offset(i_7 as isize) = x_129;
    i_7 = (i_7 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut x_130: uint64_t = c_7 & *res_j_7.offset(i_7 as isize)
        | !c_7 & *tmp.offset(i_7 as isize);
    let mut os_130: *mut uint64_t = tmp;
    *os_130.offset(i_7 as isize) = x_130;
    i_7 = (i_7 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut x_131: uint64_t = c_7 & *res_j_7.offset(i_7 as isize)
        | !c_7 & *tmp.offset(i_7 as isize);
    let mut os_131: *mut uint64_t = tmp;
    *os_131.offset(i_7 as isize) = x_131;
    i_7 = (i_7 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut x_132: uint64_t = c_7 & *res_j_7.offset(i_7 as isize)
        | !c_7 & *tmp.offset(i_7 as isize);
    let mut os_132: *mut uint64_t = tmp;
    *os_132.offset(i_7 as isize) = x_132;
    i_7 = (i_7 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut x_133: uint64_t = c_7 & *res_j_7.offset(i_7 as isize)
        | !c_7 & *tmp.offset(i_7 as isize);
    let mut os_133: *mut uint64_t = tmp;
    *os_133.offset(i_7 as isize) = x_133;
    i_7 = (i_7 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    i0 = (i0 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut c_8: uint64_t = FStar_UInt64_eq_mask(
        bits_l,
        i0.wrapping_add(1 as libc::c_uint) as uint64_t,
    );
    let mut res_j_8: *const uint64_t = table
        .offset(
            i0.wrapping_add(1 as libc::c_uint).wrapping_mul(15 as libc::c_uint) as isize,
        );
    let mut i_8: uint32_t = 0 as libc::c_uint;
    let mut x_134: uint64_t = c_8 & *res_j_8.offset(i_8 as isize)
        | !c_8 & *tmp.offset(i_8 as isize);
    let mut os_134: *mut uint64_t = tmp;
    *os_134.offset(i_8 as isize) = x_134;
    i_8 = (i_8 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut x_135: uint64_t = c_8 & *res_j_8.offset(i_8 as isize)
        | !c_8 & *tmp.offset(i_8 as isize);
    let mut os_135: *mut uint64_t = tmp;
    *os_135.offset(i_8 as isize) = x_135;
    i_8 = (i_8 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut x_136: uint64_t = c_8 & *res_j_8.offset(i_8 as isize)
        | !c_8 & *tmp.offset(i_8 as isize);
    let mut os_136: *mut uint64_t = tmp;
    *os_136.offset(i_8 as isize) = x_136;
    i_8 = (i_8 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut x_137: uint64_t = c_8 & *res_j_8.offset(i_8 as isize)
        | !c_8 & *tmp.offset(i_8 as isize);
    let mut os_137: *mut uint64_t = tmp;
    *os_137.offset(i_8 as isize) = x_137;
    i_8 = (i_8 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut x_138: uint64_t = c_8 & *res_j_8.offset(i_8 as isize)
        | !c_8 & *tmp.offset(i_8 as isize);
    let mut os_138: *mut uint64_t = tmp;
    *os_138.offset(i_8 as isize) = x_138;
    i_8 = (i_8 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut x_139: uint64_t = c_8 & *res_j_8.offset(i_8 as isize)
        | !c_8 & *tmp.offset(i_8 as isize);
    let mut os_139: *mut uint64_t = tmp;
    *os_139.offset(i_8 as isize) = x_139;
    i_8 = (i_8 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut x_140: uint64_t = c_8 & *res_j_8.offset(i_8 as isize)
        | !c_8 & *tmp.offset(i_8 as isize);
    let mut os_140: *mut uint64_t = tmp;
    *os_140.offset(i_8 as isize) = x_140;
    i_8 = (i_8 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut x_141: uint64_t = c_8 & *res_j_8.offset(i_8 as isize)
        | !c_8 & *tmp.offset(i_8 as isize);
    let mut os_141: *mut uint64_t = tmp;
    *os_141.offset(i_8 as isize) = x_141;
    i_8 = (i_8 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut x_142: uint64_t = c_8 & *res_j_8.offset(i_8 as isize)
        | !c_8 & *tmp.offset(i_8 as isize);
    let mut os_142: *mut uint64_t = tmp;
    *os_142.offset(i_8 as isize) = x_142;
    i_8 = (i_8 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut x_143: uint64_t = c_8 & *res_j_8.offset(i_8 as isize)
        | !c_8 & *tmp.offset(i_8 as isize);
    let mut os_143: *mut uint64_t = tmp;
    *os_143.offset(i_8 as isize) = x_143;
    i_8 = (i_8 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut x_144: uint64_t = c_8 & *res_j_8.offset(i_8 as isize)
        | !c_8 & *tmp.offset(i_8 as isize);
    let mut os_144: *mut uint64_t = tmp;
    *os_144.offset(i_8 as isize) = x_144;
    i_8 = (i_8 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut x_145: uint64_t = c_8 & *res_j_8.offset(i_8 as isize)
        | !c_8 & *tmp.offset(i_8 as isize);
    let mut os_145: *mut uint64_t = tmp;
    *os_145.offset(i_8 as isize) = x_145;
    i_8 = (i_8 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut x_146: uint64_t = c_8 & *res_j_8.offset(i_8 as isize)
        | !c_8 & *tmp.offset(i_8 as isize);
    let mut os_146: *mut uint64_t = tmp;
    *os_146.offset(i_8 as isize) = x_146;
    i_8 = (i_8 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut x_147: uint64_t = c_8 & *res_j_8.offset(i_8 as isize)
        | !c_8 & *tmp.offset(i_8 as isize);
    let mut os_147: *mut uint64_t = tmp;
    *os_147.offset(i_8 as isize) = x_147;
    i_8 = (i_8 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut x_148: uint64_t = c_8 & *res_j_8.offset(i_8 as isize)
        | !c_8 & *tmp.offset(i_8 as isize);
    let mut os_148: *mut uint64_t = tmp;
    *os_148.offset(i_8 as isize) = x_148;
    i_8 = (i_8 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    i0 = (i0 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut c_9: uint64_t = FStar_UInt64_eq_mask(
        bits_l,
        i0.wrapping_add(1 as libc::c_uint) as uint64_t,
    );
    let mut res_j_9: *const uint64_t = table
        .offset(
            i0.wrapping_add(1 as libc::c_uint).wrapping_mul(15 as libc::c_uint) as isize,
        );
    let mut i_9: uint32_t = 0 as libc::c_uint;
    let mut x_149: uint64_t = c_9 & *res_j_9.offset(i_9 as isize)
        | !c_9 & *tmp.offset(i_9 as isize);
    let mut os_149: *mut uint64_t = tmp;
    *os_149.offset(i_9 as isize) = x_149;
    i_9 = (i_9 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut x_150: uint64_t = c_9 & *res_j_9.offset(i_9 as isize)
        | !c_9 & *tmp.offset(i_9 as isize);
    let mut os_150: *mut uint64_t = tmp;
    *os_150.offset(i_9 as isize) = x_150;
    i_9 = (i_9 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut x_151: uint64_t = c_9 & *res_j_9.offset(i_9 as isize)
        | !c_9 & *tmp.offset(i_9 as isize);
    let mut os_151: *mut uint64_t = tmp;
    *os_151.offset(i_9 as isize) = x_151;
    i_9 = (i_9 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut x_152: uint64_t = c_9 & *res_j_9.offset(i_9 as isize)
        | !c_9 & *tmp.offset(i_9 as isize);
    let mut os_152: *mut uint64_t = tmp;
    *os_152.offset(i_9 as isize) = x_152;
    i_9 = (i_9 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut x_153: uint64_t = c_9 & *res_j_9.offset(i_9 as isize)
        | !c_9 & *tmp.offset(i_9 as isize);
    let mut os_153: *mut uint64_t = tmp;
    *os_153.offset(i_9 as isize) = x_153;
    i_9 = (i_9 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut x_154: uint64_t = c_9 & *res_j_9.offset(i_9 as isize)
        | !c_9 & *tmp.offset(i_9 as isize);
    let mut os_154: *mut uint64_t = tmp;
    *os_154.offset(i_9 as isize) = x_154;
    i_9 = (i_9 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut x_155: uint64_t = c_9 & *res_j_9.offset(i_9 as isize)
        | !c_9 & *tmp.offset(i_9 as isize);
    let mut os_155: *mut uint64_t = tmp;
    *os_155.offset(i_9 as isize) = x_155;
    i_9 = (i_9 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut x_156: uint64_t = c_9 & *res_j_9.offset(i_9 as isize)
        | !c_9 & *tmp.offset(i_9 as isize);
    let mut os_156: *mut uint64_t = tmp;
    *os_156.offset(i_9 as isize) = x_156;
    i_9 = (i_9 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut x_157: uint64_t = c_9 & *res_j_9.offset(i_9 as isize)
        | !c_9 & *tmp.offset(i_9 as isize);
    let mut os_157: *mut uint64_t = tmp;
    *os_157.offset(i_9 as isize) = x_157;
    i_9 = (i_9 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut x_158: uint64_t = c_9 & *res_j_9.offset(i_9 as isize)
        | !c_9 & *tmp.offset(i_9 as isize);
    let mut os_158: *mut uint64_t = tmp;
    *os_158.offset(i_9 as isize) = x_158;
    i_9 = (i_9 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut x_159: uint64_t = c_9 & *res_j_9.offset(i_9 as isize)
        | !c_9 & *tmp.offset(i_9 as isize);
    let mut os_159: *mut uint64_t = tmp;
    *os_159.offset(i_9 as isize) = x_159;
    i_9 = (i_9 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut x_160: uint64_t = c_9 & *res_j_9.offset(i_9 as isize)
        | !c_9 & *tmp.offset(i_9 as isize);
    let mut os_160: *mut uint64_t = tmp;
    *os_160.offset(i_9 as isize) = x_160;
    i_9 = (i_9 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut x_161: uint64_t = c_9 & *res_j_9.offset(i_9 as isize)
        | !c_9 & *tmp.offset(i_9 as isize);
    let mut os_161: *mut uint64_t = tmp;
    *os_161.offset(i_9 as isize) = x_161;
    i_9 = (i_9 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut x_162: uint64_t = c_9 & *res_j_9.offset(i_9 as isize)
        | !c_9 & *tmp.offset(i_9 as isize);
    let mut os_162: *mut uint64_t = tmp;
    *os_162.offset(i_9 as isize) = x_162;
    i_9 = (i_9 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut x_163: uint64_t = c_9 & *res_j_9.offset(i_9 as isize)
        | !c_9 & *tmp.offset(i_9 as isize);
    let mut os_163: *mut uint64_t = tmp;
    *os_163.offset(i_9 as isize) = x_163;
    i_9 = (i_9 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    i0 = (i0 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut c_10: uint64_t = FStar_UInt64_eq_mask(
        bits_l,
        i0.wrapping_add(1 as libc::c_uint) as uint64_t,
    );
    let mut res_j_10: *const uint64_t = table
        .offset(
            i0.wrapping_add(1 as libc::c_uint).wrapping_mul(15 as libc::c_uint) as isize,
        );
    let mut i_10: uint32_t = 0 as libc::c_uint;
    let mut x_164: uint64_t = c_10 & *res_j_10.offset(i_10 as isize)
        | !c_10 & *tmp.offset(i_10 as isize);
    let mut os_164: *mut uint64_t = tmp;
    *os_164.offset(i_10 as isize) = x_164;
    i_10 = (i_10 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
        as uint32_t;
    let mut x_165: uint64_t = c_10 & *res_j_10.offset(i_10 as isize)
        | !c_10 & *tmp.offset(i_10 as isize);
    let mut os_165: *mut uint64_t = tmp;
    *os_165.offset(i_10 as isize) = x_165;
    i_10 = (i_10 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
        as uint32_t;
    let mut x_166: uint64_t = c_10 & *res_j_10.offset(i_10 as isize)
        | !c_10 & *tmp.offset(i_10 as isize);
    let mut os_166: *mut uint64_t = tmp;
    *os_166.offset(i_10 as isize) = x_166;
    i_10 = (i_10 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
        as uint32_t;
    let mut x_167: uint64_t = c_10 & *res_j_10.offset(i_10 as isize)
        | !c_10 & *tmp.offset(i_10 as isize);
    let mut os_167: *mut uint64_t = tmp;
    *os_167.offset(i_10 as isize) = x_167;
    i_10 = (i_10 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
        as uint32_t;
    let mut x_168: uint64_t = c_10 & *res_j_10.offset(i_10 as isize)
        | !c_10 & *tmp.offset(i_10 as isize);
    let mut os_168: *mut uint64_t = tmp;
    *os_168.offset(i_10 as isize) = x_168;
    i_10 = (i_10 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
        as uint32_t;
    let mut x_169: uint64_t = c_10 & *res_j_10.offset(i_10 as isize)
        | !c_10 & *tmp.offset(i_10 as isize);
    let mut os_169: *mut uint64_t = tmp;
    *os_169.offset(i_10 as isize) = x_169;
    i_10 = (i_10 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
        as uint32_t;
    let mut x_170: uint64_t = c_10 & *res_j_10.offset(i_10 as isize)
        | !c_10 & *tmp.offset(i_10 as isize);
    let mut os_170: *mut uint64_t = tmp;
    *os_170.offset(i_10 as isize) = x_170;
    i_10 = (i_10 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
        as uint32_t;
    let mut x_171: uint64_t = c_10 & *res_j_10.offset(i_10 as isize)
        | !c_10 & *tmp.offset(i_10 as isize);
    let mut os_171: *mut uint64_t = tmp;
    *os_171.offset(i_10 as isize) = x_171;
    i_10 = (i_10 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
        as uint32_t;
    let mut x_172: uint64_t = c_10 & *res_j_10.offset(i_10 as isize)
        | !c_10 & *tmp.offset(i_10 as isize);
    let mut os_172: *mut uint64_t = tmp;
    *os_172.offset(i_10 as isize) = x_172;
    i_10 = (i_10 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
        as uint32_t;
    let mut x_173: uint64_t = c_10 & *res_j_10.offset(i_10 as isize)
        | !c_10 & *tmp.offset(i_10 as isize);
    let mut os_173: *mut uint64_t = tmp;
    *os_173.offset(i_10 as isize) = x_173;
    i_10 = (i_10 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
        as uint32_t;
    let mut x_174: uint64_t = c_10 & *res_j_10.offset(i_10 as isize)
        | !c_10 & *tmp.offset(i_10 as isize);
    let mut os_174: *mut uint64_t = tmp;
    *os_174.offset(i_10 as isize) = x_174;
    i_10 = (i_10 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
        as uint32_t;
    let mut x_175: uint64_t = c_10 & *res_j_10.offset(i_10 as isize)
        | !c_10 & *tmp.offset(i_10 as isize);
    let mut os_175: *mut uint64_t = tmp;
    *os_175.offset(i_10 as isize) = x_175;
    i_10 = (i_10 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
        as uint32_t;
    let mut x_176: uint64_t = c_10 & *res_j_10.offset(i_10 as isize)
        | !c_10 & *tmp.offset(i_10 as isize);
    let mut os_176: *mut uint64_t = tmp;
    *os_176.offset(i_10 as isize) = x_176;
    i_10 = (i_10 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
        as uint32_t;
    let mut x_177: uint64_t = c_10 & *res_j_10.offset(i_10 as isize)
        | !c_10 & *tmp.offset(i_10 as isize);
    let mut os_177: *mut uint64_t = tmp;
    *os_177.offset(i_10 as isize) = x_177;
    i_10 = (i_10 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
        as uint32_t;
    let mut x_178: uint64_t = c_10 & *res_j_10.offset(i_10 as isize)
        | !c_10 & *tmp.offset(i_10 as isize);
    let mut os_178: *mut uint64_t = tmp;
    *os_178.offset(i_10 as isize) = x_178;
    i_10 = (i_10 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
        as uint32_t;
    i0 = (i0 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut c_11: uint64_t = FStar_UInt64_eq_mask(
        bits_l,
        i0.wrapping_add(1 as libc::c_uint) as uint64_t,
    );
    let mut res_j_11: *const uint64_t = table
        .offset(
            i0.wrapping_add(1 as libc::c_uint).wrapping_mul(15 as libc::c_uint) as isize,
        );
    let mut i_11: uint32_t = 0 as libc::c_uint;
    let mut x_179: uint64_t = c_11 & *res_j_11.offset(i_11 as isize)
        | !c_11 & *tmp.offset(i_11 as isize);
    let mut os_179: *mut uint64_t = tmp;
    *os_179.offset(i_11 as isize) = x_179;
    i_11 = (i_11 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
        as uint32_t;
    let mut x_180: uint64_t = c_11 & *res_j_11.offset(i_11 as isize)
        | !c_11 & *tmp.offset(i_11 as isize);
    let mut os_180: *mut uint64_t = tmp;
    *os_180.offset(i_11 as isize) = x_180;
    i_11 = (i_11 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
        as uint32_t;
    let mut x_181: uint64_t = c_11 & *res_j_11.offset(i_11 as isize)
        | !c_11 & *tmp.offset(i_11 as isize);
    let mut os_181: *mut uint64_t = tmp;
    *os_181.offset(i_11 as isize) = x_181;
    i_11 = (i_11 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
        as uint32_t;
    let mut x_182: uint64_t = c_11 & *res_j_11.offset(i_11 as isize)
        | !c_11 & *tmp.offset(i_11 as isize);
    let mut os_182: *mut uint64_t = tmp;
    *os_182.offset(i_11 as isize) = x_182;
    i_11 = (i_11 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
        as uint32_t;
    let mut x_183: uint64_t = c_11 & *res_j_11.offset(i_11 as isize)
        | !c_11 & *tmp.offset(i_11 as isize);
    let mut os_183: *mut uint64_t = tmp;
    *os_183.offset(i_11 as isize) = x_183;
    i_11 = (i_11 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
        as uint32_t;
    let mut x_184: uint64_t = c_11 & *res_j_11.offset(i_11 as isize)
        | !c_11 & *tmp.offset(i_11 as isize);
    let mut os_184: *mut uint64_t = tmp;
    *os_184.offset(i_11 as isize) = x_184;
    i_11 = (i_11 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
        as uint32_t;
    let mut x_185: uint64_t = c_11 & *res_j_11.offset(i_11 as isize)
        | !c_11 & *tmp.offset(i_11 as isize);
    let mut os_185: *mut uint64_t = tmp;
    *os_185.offset(i_11 as isize) = x_185;
    i_11 = (i_11 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
        as uint32_t;
    let mut x_186: uint64_t = c_11 & *res_j_11.offset(i_11 as isize)
        | !c_11 & *tmp.offset(i_11 as isize);
    let mut os_186: *mut uint64_t = tmp;
    *os_186.offset(i_11 as isize) = x_186;
    i_11 = (i_11 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
        as uint32_t;
    let mut x_187: uint64_t = c_11 & *res_j_11.offset(i_11 as isize)
        | !c_11 & *tmp.offset(i_11 as isize);
    let mut os_187: *mut uint64_t = tmp;
    *os_187.offset(i_11 as isize) = x_187;
    i_11 = (i_11 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
        as uint32_t;
    let mut x_188: uint64_t = c_11 & *res_j_11.offset(i_11 as isize)
        | !c_11 & *tmp.offset(i_11 as isize);
    let mut os_188: *mut uint64_t = tmp;
    *os_188.offset(i_11 as isize) = x_188;
    i_11 = (i_11 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
        as uint32_t;
    let mut x_189: uint64_t = c_11 & *res_j_11.offset(i_11 as isize)
        | !c_11 & *tmp.offset(i_11 as isize);
    let mut os_189: *mut uint64_t = tmp;
    *os_189.offset(i_11 as isize) = x_189;
    i_11 = (i_11 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
        as uint32_t;
    let mut x_190: uint64_t = c_11 & *res_j_11.offset(i_11 as isize)
        | !c_11 & *tmp.offset(i_11 as isize);
    let mut os_190: *mut uint64_t = tmp;
    *os_190.offset(i_11 as isize) = x_190;
    i_11 = (i_11 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
        as uint32_t;
    let mut x_191: uint64_t = c_11 & *res_j_11.offset(i_11 as isize)
        | !c_11 & *tmp.offset(i_11 as isize);
    let mut os_191: *mut uint64_t = tmp;
    *os_191.offset(i_11 as isize) = x_191;
    i_11 = (i_11 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
        as uint32_t;
    let mut x_192: uint64_t = c_11 & *res_j_11.offset(i_11 as isize)
        | !c_11 & *tmp.offset(i_11 as isize);
    let mut os_192: *mut uint64_t = tmp;
    *os_192.offset(i_11 as isize) = x_192;
    i_11 = (i_11 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
        as uint32_t;
    let mut x_193: uint64_t = c_11 & *res_j_11.offset(i_11 as isize)
        | !c_11 & *tmp.offset(i_11 as isize);
    let mut os_193: *mut uint64_t = tmp;
    *os_193.offset(i_11 as isize) = x_193;
    i_11 = (i_11 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
        as uint32_t;
    i0 = (i0 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut c_12: uint64_t = FStar_UInt64_eq_mask(
        bits_l,
        i0.wrapping_add(1 as libc::c_uint) as uint64_t,
    );
    let mut res_j_12: *const uint64_t = table
        .offset(
            i0.wrapping_add(1 as libc::c_uint).wrapping_mul(15 as libc::c_uint) as isize,
        );
    let mut i_12: uint32_t = 0 as libc::c_uint;
    let mut x_194: uint64_t = c_12 & *res_j_12.offset(i_12 as isize)
        | !c_12 & *tmp.offset(i_12 as isize);
    let mut os_194: *mut uint64_t = tmp;
    *os_194.offset(i_12 as isize) = x_194;
    i_12 = (i_12 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
        as uint32_t;
    let mut x_195: uint64_t = c_12 & *res_j_12.offset(i_12 as isize)
        | !c_12 & *tmp.offset(i_12 as isize);
    let mut os_195: *mut uint64_t = tmp;
    *os_195.offset(i_12 as isize) = x_195;
    i_12 = (i_12 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
        as uint32_t;
    let mut x_196: uint64_t = c_12 & *res_j_12.offset(i_12 as isize)
        | !c_12 & *tmp.offset(i_12 as isize);
    let mut os_196: *mut uint64_t = tmp;
    *os_196.offset(i_12 as isize) = x_196;
    i_12 = (i_12 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
        as uint32_t;
    let mut x_197: uint64_t = c_12 & *res_j_12.offset(i_12 as isize)
        | !c_12 & *tmp.offset(i_12 as isize);
    let mut os_197: *mut uint64_t = tmp;
    *os_197.offset(i_12 as isize) = x_197;
    i_12 = (i_12 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
        as uint32_t;
    let mut x_198: uint64_t = c_12 & *res_j_12.offset(i_12 as isize)
        | !c_12 & *tmp.offset(i_12 as isize);
    let mut os_198: *mut uint64_t = tmp;
    *os_198.offset(i_12 as isize) = x_198;
    i_12 = (i_12 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
        as uint32_t;
    let mut x_199: uint64_t = c_12 & *res_j_12.offset(i_12 as isize)
        | !c_12 & *tmp.offset(i_12 as isize);
    let mut os_199: *mut uint64_t = tmp;
    *os_199.offset(i_12 as isize) = x_199;
    i_12 = (i_12 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
        as uint32_t;
    let mut x_200: uint64_t = c_12 & *res_j_12.offset(i_12 as isize)
        | !c_12 & *tmp.offset(i_12 as isize);
    let mut os_200: *mut uint64_t = tmp;
    *os_200.offset(i_12 as isize) = x_200;
    i_12 = (i_12 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
        as uint32_t;
    let mut x_201: uint64_t = c_12 & *res_j_12.offset(i_12 as isize)
        | !c_12 & *tmp.offset(i_12 as isize);
    let mut os_201: *mut uint64_t = tmp;
    *os_201.offset(i_12 as isize) = x_201;
    i_12 = (i_12 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
        as uint32_t;
    let mut x_202: uint64_t = c_12 & *res_j_12.offset(i_12 as isize)
        | !c_12 & *tmp.offset(i_12 as isize);
    let mut os_202: *mut uint64_t = tmp;
    *os_202.offset(i_12 as isize) = x_202;
    i_12 = (i_12 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
        as uint32_t;
    let mut x_203: uint64_t = c_12 & *res_j_12.offset(i_12 as isize)
        | !c_12 & *tmp.offset(i_12 as isize);
    let mut os_203: *mut uint64_t = tmp;
    *os_203.offset(i_12 as isize) = x_203;
    i_12 = (i_12 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
        as uint32_t;
    let mut x_204: uint64_t = c_12 & *res_j_12.offset(i_12 as isize)
        | !c_12 & *tmp.offset(i_12 as isize);
    let mut os_204: *mut uint64_t = tmp;
    *os_204.offset(i_12 as isize) = x_204;
    i_12 = (i_12 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
        as uint32_t;
    let mut x_205: uint64_t = c_12 & *res_j_12.offset(i_12 as isize)
        | !c_12 & *tmp.offset(i_12 as isize);
    let mut os_205: *mut uint64_t = tmp;
    *os_205.offset(i_12 as isize) = x_205;
    i_12 = (i_12 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
        as uint32_t;
    let mut x_206: uint64_t = c_12 & *res_j_12.offset(i_12 as isize)
        | !c_12 & *tmp.offset(i_12 as isize);
    let mut os_206: *mut uint64_t = tmp;
    *os_206.offset(i_12 as isize) = x_206;
    i_12 = (i_12 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
        as uint32_t;
    let mut x_207: uint64_t = c_12 & *res_j_12.offset(i_12 as isize)
        | !c_12 & *tmp.offset(i_12 as isize);
    let mut os_207: *mut uint64_t = tmp;
    *os_207.offset(i_12 as isize) = x_207;
    i_12 = (i_12 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
        as uint32_t;
    let mut x_208: uint64_t = c_12 & *res_j_12.offset(i_12 as isize)
        | !c_12 & *tmp.offset(i_12 as isize);
    let mut os_208: *mut uint64_t = tmp;
    *os_208.offset(i_12 as isize) = x_208;
    i_12 = (i_12 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
        as uint32_t;
    i0 = (i0 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut c_13: uint64_t = FStar_UInt64_eq_mask(
        bits_l,
        i0.wrapping_add(1 as libc::c_uint) as uint64_t,
    );
    let mut res_j_13: *const uint64_t = table
        .offset(
            i0.wrapping_add(1 as libc::c_uint).wrapping_mul(15 as libc::c_uint) as isize,
        );
    let mut i_13: uint32_t = 0 as libc::c_uint;
    let mut x_209: uint64_t = c_13 & *res_j_13.offset(i_13 as isize)
        | !c_13 & *tmp.offset(i_13 as isize);
    let mut os_209: *mut uint64_t = tmp;
    *os_209.offset(i_13 as isize) = x_209;
    i_13 = (i_13 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
        as uint32_t;
    let mut x_210: uint64_t = c_13 & *res_j_13.offset(i_13 as isize)
        | !c_13 & *tmp.offset(i_13 as isize);
    let mut os_210: *mut uint64_t = tmp;
    *os_210.offset(i_13 as isize) = x_210;
    i_13 = (i_13 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
        as uint32_t;
    let mut x_211: uint64_t = c_13 & *res_j_13.offset(i_13 as isize)
        | !c_13 & *tmp.offset(i_13 as isize);
    let mut os_211: *mut uint64_t = tmp;
    *os_211.offset(i_13 as isize) = x_211;
    i_13 = (i_13 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
        as uint32_t;
    let mut x_212: uint64_t = c_13 & *res_j_13.offset(i_13 as isize)
        | !c_13 & *tmp.offset(i_13 as isize);
    let mut os_212: *mut uint64_t = tmp;
    *os_212.offset(i_13 as isize) = x_212;
    i_13 = (i_13 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
        as uint32_t;
    let mut x_213: uint64_t = c_13 & *res_j_13.offset(i_13 as isize)
        | !c_13 & *tmp.offset(i_13 as isize);
    let mut os_213: *mut uint64_t = tmp;
    *os_213.offset(i_13 as isize) = x_213;
    i_13 = (i_13 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
        as uint32_t;
    let mut x_214: uint64_t = c_13 & *res_j_13.offset(i_13 as isize)
        | !c_13 & *tmp.offset(i_13 as isize);
    let mut os_214: *mut uint64_t = tmp;
    *os_214.offset(i_13 as isize) = x_214;
    i_13 = (i_13 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
        as uint32_t;
    let mut x_215: uint64_t = c_13 & *res_j_13.offset(i_13 as isize)
        | !c_13 & *tmp.offset(i_13 as isize);
    let mut os_215: *mut uint64_t = tmp;
    *os_215.offset(i_13 as isize) = x_215;
    i_13 = (i_13 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
        as uint32_t;
    let mut x_216: uint64_t = c_13 & *res_j_13.offset(i_13 as isize)
        | !c_13 & *tmp.offset(i_13 as isize);
    let mut os_216: *mut uint64_t = tmp;
    *os_216.offset(i_13 as isize) = x_216;
    i_13 = (i_13 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
        as uint32_t;
    let mut x_217: uint64_t = c_13 & *res_j_13.offset(i_13 as isize)
        | !c_13 & *tmp.offset(i_13 as isize);
    let mut os_217: *mut uint64_t = tmp;
    *os_217.offset(i_13 as isize) = x_217;
    i_13 = (i_13 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
        as uint32_t;
    let mut x_218: uint64_t = c_13 & *res_j_13.offset(i_13 as isize)
        | !c_13 & *tmp.offset(i_13 as isize);
    let mut os_218: *mut uint64_t = tmp;
    *os_218.offset(i_13 as isize) = x_218;
    i_13 = (i_13 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
        as uint32_t;
    let mut x_219: uint64_t = c_13 & *res_j_13.offset(i_13 as isize)
        | !c_13 & *tmp.offset(i_13 as isize);
    let mut os_219: *mut uint64_t = tmp;
    *os_219.offset(i_13 as isize) = x_219;
    i_13 = (i_13 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
        as uint32_t;
    let mut x_220: uint64_t = c_13 & *res_j_13.offset(i_13 as isize)
        | !c_13 & *tmp.offset(i_13 as isize);
    let mut os_220: *mut uint64_t = tmp;
    *os_220.offset(i_13 as isize) = x_220;
    i_13 = (i_13 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
        as uint32_t;
    let mut x_221: uint64_t = c_13 & *res_j_13.offset(i_13 as isize)
        | !c_13 & *tmp.offset(i_13 as isize);
    let mut os_221: *mut uint64_t = tmp;
    *os_221.offset(i_13 as isize) = x_221;
    i_13 = (i_13 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
        as uint32_t;
    let mut x_222: uint64_t = c_13 & *res_j_13.offset(i_13 as isize)
        | !c_13 & *tmp.offset(i_13 as isize);
    let mut os_222: *mut uint64_t = tmp;
    *os_222.offset(i_13 as isize) = x_222;
    i_13 = (i_13 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
        as uint32_t;
    let mut x_223: uint64_t = c_13 & *res_j_13.offset(i_13 as isize)
        | !c_13 & *tmp.offset(i_13 as isize);
    let mut os_223: *mut uint64_t = tmp;
    *os_223.offset(i_13 as isize) = x_223;
    i_13 = (i_13 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
        as uint32_t;
    i0 = (i0 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
}
#[inline]
unsafe extern "C" fn point_mul_g(mut out: *mut uint64_t, mut scalar: *mut uint64_t) {
    let mut q1: [uint64_t; 15] = [
        0 as libc::c_uint as uint64_t,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
    ];
    let mut gx: *mut uint64_t = q1.as_mut_ptr();
    let mut gy: *mut uint64_t = q1.as_mut_ptr().offset(5 as libc::c_uint as isize);
    let mut gz: *mut uint64_t = q1.as_mut_ptr().offset(10 as libc::c_uint as isize);
    *gx.offset(0 as libc::c_uint as isize) = 0x2815b16f81798 as libc::c_ulonglong;
    *gx.offset(1 as libc::c_uint as isize) = 0xdb2dce28d959f as libc::c_ulonglong;
    *gx.offset(2 as libc::c_uint as isize) = 0xe870b07029bfc as libc::c_ulonglong;
    *gx.offset(3 as libc::c_uint as isize) = 0xbbac55a06295c as libc::c_ulonglong;
    *gx.offset(4 as libc::c_uint as isize) = 0x79be667ef9dc as libc::c_ulonglong;
    *gy.offset(0 as libc::c_uint as isize) = 0x7d08ffb10d4b8 as libc::c_ulonglong;
    *gy.offset(1 as libc::c_uint as isize) = 0x48a68554199c4 as libc::c_ulonglong;
    *gy.offset(2 as libc::c_uint as isize) = 0xe1108a8fd17b4 as libc::c_ulonglong;
    *gy.offset(3 as libc::c_uint as isize) = 0xc4655da4fbfc0 as libc::c_ulonglong;
    *gy.offset(4 as libc::c_uint as isize) = 0x483ada7726a3 as libc::c_ulonglong;
    memset(
        gz as *mut libc::c_void,
        0 as libc::c_uint as libc::c_int,
        (5 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    *gz.offset(0 as libc::c_uint as isize) = 1 as libc::c_ulonglong;
    let mut q2: [uint64_t; 15] = [
        4496295042185355 as libc::c_ulonglong,
        3125448202219451 as libc::c_ulonglong,
        1239608518490046 as libc::c_ulonglong,
        2687445637493112 as libc::c_ulonglong,
        77979604880139 as libc::c_ulonglong,
        3360310474215011 as libc::c_ulonglong,
        1216410458165163 as libc::c_ulonglong,
        177901593587973 as libc::c_ulonglong,
        3209978938104985 as libc::c_ulonglong,
        118285133003718 as libc::c_ulonglong,
        434519962075150 as libc::c_ulonglong,
        1114612377498854 as libc::c_ulonglong,
        3488596944003813 as libc::c_ulonglong,
        450716531072892 as libc::c_ulonglong,
        66044973203836 as libc::c_ulonglong,
    ];
    let mut q3: [uint64_t; 15] = [
        1277614565900951 as libc::c_ulonglong,
        378671684419493 as libc::c_ulonglong,
        3176260448102880 as libc::c_ulonglong,
        1575691435565077 as libc::c_ulonglong,
        167304528382180 as libc::c_ulonglong,
        2600787765776588 as libc::c_ulonglong,
        7497946149293 as libc::c_ulonglong,
        2184272641272202 as libc::c_ulonglong,
        2200235265236628 as libc::c_ulonglong,
        265969268774814 as libc::c_ulonglong,
        1913228635640715 as libc::c_ulonglong,
        2831959046949342 as libc::c_ulonglong,
        888030405442963 as libc::c_ulonglong,
        1817092932985033 as libc::c_ulonglong,
        101515844997121 as libc::c_ulonglong,
    ];
    let mut q4: [uint64_t; 15] = [
        34056422761564 as libc::c_ulonglong,
        3315864838337811 as libc::c_ulonglong,
        3797032336888745 as libc::c_ulonglong,
        2580641850480806 as libc::c_ulonglong,
        208048944042500 as libc::c_ulonglong,
        1233795288689421 as libc::c_ulonglong,
        1048795233382631 as libc::c_ulonglong,
        646545158071530 as libc::c_ulonglong,
        1816025742137285 as libc::c_ulonglong,
        12245672982162 as libc::c_ulonglong,
        2119364213800870 as libc::c_ulonglong,
        2034960311715107 as libc::c_ulonglong,
        3172697815804487 as libc::c_ulonglong,
        4185144850224160 as libc::c_ulonglong,
        2792055915674 as libc::c_ulonglong,
    ];
    let mut r1: *mut uint64_t = scalar;
    let mut r2: *mut uint64_t = scalar.offset(1 as libc::c_uint as isize);
    let mut r3: *mut uint64_t = scalar.offset(2 as libc::c_uint as isize);
    let mut r4: *mut uint64_t = scalar.offset(3 as libc::c_uint as isize);
    Hacl_Impl_K256_Point_make_point_at_inf(out);
    let mut tmp: [uint64_t; 15] = [
        0 as libc::c_uint as uint64_t,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
    ];
    let mut i: uint32_t = 0 as libc::c_uint;
    let mut i0: uint32_t = 0 as libc::c_uint;
    let mut p_copy: [uint64_t; 15] = [
        0 as libc::c_uint as uint64_t,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
    ];
    memcpy(
        p_copy.as_mut_ptr() as *mut libc::c_void,
        out as *const libc::c_void,
        (15 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    Hacl_Impl_K256_PointDouble_point_double(out, p_copy.as_mut_ptr());
    i0 = (i0 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut p_copy_0: [uint64_t; 15] = [
        0 as libc::c_uint as uint64_t,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
    ];
    memcpy(
        p_copy_0.as_mut_ptr() as *mut libc::c_void,
        out as *const libc::c_void,
        (15 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    Hacl_Impl_K256_PointDouble_point_double(out, p_copy_0.as_mut_ptr());
    i0 = (i0 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut p_copy_1: [uint64_t; 15] = [
        0 as libc::c_uint as uint64_t,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
    ];
    memcpy(
        p_copy_1.as_mut_ptr() as *mut libc::c_void,
        out as *const libc::c_void,
        (15 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    Hacl_Impl_K256_PointDouble_point_double(out, p_copy_1.as_mut_ptr());
    i0 = (i0 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut p_copy_2: [uint64_t; 15] = [
        0 as libc::c_uint as uint64_t,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
    ];
    memcpy(
        p_copy_2.as_mut_ptr() as *mut libc::c_void,
        out as *const libc::c_void,
        (15 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    Hacl_Impl_K256_PointDouble_point_double(out, p_copy_2.as_mut_ptr());
    i0 = (i0 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut k: uint32_t = (64 as libc::c_uint)
        .wrapping_sub((4 as libc::c_uint).wrapping_mul(i))
        .wrapping_sub(4 as libc::c_uint);
    let mut bits_l: uint64_t = Hacl_Bignum_Lib_bn_get_bits_u64(
        1 as libc::c_uint,
        r4,
        k,
        4 as libc::c_uint,
    );
    precomp_get_consttime(
        Hacl_K256_PrecompTable_precomp_g_pow2_192_table_w4.as_ptr(),
        bits_l,
        tmp.as_mut_ptr(),
    );
    let mut p_copy_3: [uint64_t; 15] = [
        0 as libc::c_uint as uint64_t,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
    ];
    memcpy(
        p_copy_3.as_mut_ptr() as *mut libc::c_void,
        out as *const libc::c_void,
        (15 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    Hacl_Impl_K256_PointAdd_point_add(out, p_copy_3.as_mut_ptr(), tmp.as_mut_ptr());
    let mut k0: uint32_t = (64 as libc::c_uint)
        .wrapping_sub((4 as libc::c_uint).wrapping_mul(i))
        .wrapping_sub(4 as libc::c_uint);
    let mut bits_l0: uint64_t = Hacl_Bignum_Lib_bn_get_bits_u64(
        1 as libc::c_uint,
        r3,
        k0,
        4 as libc::c_uint,
    );
    precomp_get_consttime(
        Hacl_K256_PrecompTable_precomp_g_pow2_128_table_w4.as_ptr(),
        bits_l0,
        tmp.as_mut_ptr(),
    );
    let mut p_copy0: [uint64_t; 15] = [
        0 as libc::c_uint as uint64_t,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
    ];
    memcpy(
        p_copy0.as_mut_ptr() as *mut libc::c_void,
        out as *const libc::c_void,
        (15 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    Hacl_Impl_K256_PointAdd_point_add(out, p_copy0.as_mut_ptr(), tmp.as_mut_ptr());
    let mut k1: uint32_t = (64 as libc::c_uint)
        .wrapping_sub((4 as libc::c_uint).wrapping_mul(i))
        .wrapping_sub(4 as libc::c_uint);
    let mut bits_l1: uint64_t = Hacl_Bignum_Lib_bn_get_bits_u64(
        1 as libc::c_uint,
        r2,
        k1,
        4 as libc::c_uint,
    );
    precomp_get_consttime(
        Hacl_K256_PrecompTable_precomp_g_pow2_64_table_w4.as_ptr(),
        bits_l1,
        tmp.as_mut_ptr(),
    );
    let mut p_copy1: [uint64_t; 15] = [
        0 as libc::c_uint as uint64_t,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
    ];
    memcpy(
        p_copy1.as_mut_ptr() as *mut libc::c_void,
        out as *const libc::c_void,
        (15 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    Hacl_Impl_K256_PointAdd_point_add(out, p_copy1.as_mut_ptr(), tmp.as_mut_ptr());
    let mut k2: uint32_t = (64 as libc::c_uint)
        .wrapping_sub((4 as libc::c_uint).wrapping_mul(i))
        .wrapping_sub(4 as libc::c_uint);
    let mut bits_l2: uint64_t = Hacl_Bignum_Lib_bn_get_bits_u64(
        1 as libc::c_uint,
        r1,
        k2,
        4 as libc::c_uint,
    );
    precomp_get_consttime(
        Hacl_K256_PrecompTable_precomp_basepoint_table_w4.as_ptr(),
        bits_l2,
        tmp.as_mut_ptr(),
    );
    let mut p_copy2: [uint64_t; 15] = [
        0 as libc::c_uint as uint64_t,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
    ];
    memcpy(
        p_copy2.as_mut_ptr() as *mut libc::c_void,
        out as *const libc::c_void,
        (15 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    Hacl_Impl_K256_PointAdd_point_add(out, p_copy2.as_mut_ptr(), tmp.as_mut_ptr());
    i = (i as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut i0_0: uint32_t = 0 as libc::c_uint;
    let mut p_copy_4: [uint64_t; 15] = [
        0 as libc::c_uint as uint64_t,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
    ];
    memcpy(
        p_copy_4.as_mut_ptr() as *mut libc::c_void,
        out as *const libc::c_void,
        (15 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    Hacl_Impl_K256_PointDouble_point_double(out, p_copy_4.as_mut_ptr());
    i0_0 = (i0_0 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
        as uint32_t;
    let mut p_copy_5: [uint64_t; 15] = [
        0 as libc::c_uint as uint64_t,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
    ];
    memcpy(
        p_copy_5.as_mut_ptr() as *mut libc::c_void,
        out as *const libc::c_void,
        (15 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    Hacl_Impl_K256_PointDouble_point_double(out, p_copy_5.as_mut_ptr());
    i0_0 = (i0_0 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
        as uint32_t;
    let mut p_copy_6: [uint64_t; 15] = [
        0 as libc::c_uint as uint64_t,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
    ];
    memcpy(
        p_copy_6.as_mut_ptr() as *mut libc::c_void,
        out as *const libc::c_void,
        (15 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    Hacl_Impl_K256_PointDouble_point_double(out, p_copy_6.as_mut_ptr());
    i0_0 = (i0_0 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
        as uint32_t;
    let mut p_copy_7: [uint64_t; 15] = [
        0 as libc::c_uint as uint64_t,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
    ];
    memcpy(
        p_copy_7.as_mut_ptr() as *mut libc::c_void,
        out as *const libc::c_void,
        (15 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    Hacl_Impl_K256_PointDouble_point_double(out, p_copy_7.as_mut_ptr());
    i0_0 = (i0_0 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
        as uint32_t;
    let mut k_0: uint32_t = (64 as libc::c_uint)
        .wrapping_sub((4 as libc::c_uint).wrapping_mul(i))
        .wrapping_sub(4 as libc::c_uint);
    let mut bits_l_0: uint64_t = Hacl_Bignum_Lib_bn_get_bits_u64(
        1 as libc::c_uint,
        r4,
        k_0,
        4 as libc::c_uint,
    );
    precomp_get_consttime(
        Hacl_K256_PrecompTable_precomp_g_pow2_192_table_w4.as_ptr(),
        bits_l_0,
        tmp.as_mut_ptr(),
    );
    let mut p_copy_8: [uint64_t; 15] = [
        0 as libc::c_uint as uint64_t,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
    ];
    memcpy(
        p_copy_8.as_mut_ptr() as *mut libc::c_void,
        out as *const libc::c_void,
        (15 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    Hacl_Impl_K256_PointAdd_point_add(out, p_copy_8.as_mut_ptr(), tmp.as_mut_ptr());
    let mut k0_0: uint32_t = (64 as libc::c_uint)
        .wrapping_sub((4 as libc::c_uint).wrapping_mul(i))
        .wrapping_sub(4 as libc::c_uint);
    let mut bits_l0_0: uint64_t = Hacl_Bignum_Lib_bn_get_bits_u64(
        1 as libc::c_uint,
        r3,
        k0_0,
        4 as libc::c_uint,
    );
    precomp_get_consttime(
        Hacl_K256_PrecompTable_precomp_g_pow2_128_table_w4.as_ptr(),
        bits_l0_0,
        tmp.as_mut_ptr(),
    );
    let mut p_copy0_0: [uint64_t; 15] = [
        0 as libc::c_uint as uint64_t,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
    ];
    memcpy(
        p_copy0_0.as_mut_ptr() as *mut libc::c_void,
        out as *const libc::c_void,
        (15 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    Hacl_Impl_K256_PointAdd_point_add(out, p_copy0_0.as_mut_ptr(), tmp.as_mut_ptr());
    let mut k1_0: uint32_t = (64 as libc::c_uint)
        .wrapping_sub((4 as libc::c_uint).wrapping_mul(i))
        .wrapping_sub(4 as libc::c_uint);
    let mut bits_l1_0: uint64_t = Hacl_Bignum_Lib_bn_get_bits_u64(
        1 as libc::c_uint,
        r2,
        k1_0,
        4 as libc::c_uint,
    );
    precomp_get_consttime(
        Hacl_K256_PrecompTable_precomp_g_pow2_64_table_w4.as_ptr(),
        bits_l1_0,
        tmp.as_mut_ptr(),
    );
    let mut p_copy1_0: [uint64_t; 15] = [
        0 as libc::c_uint as uint64_t,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
    ];
    memcpy(
        p_copy1_0.as_mut_ptr() as *mut libc::c_void,
        out as *const libc::c_void,
        (15 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    Hacl_Impl_K256_PointAdd_point_add(out, p_copy1_0.as_mut_ptr(), tmp.as_mut_ptr());
    let mut k2_0: uint32_t = (64 as libc::c_uint)
        .wrapping_sub((4 as libc::c_uint).wrapping_mul(i))
        .wrapping_sub(4 as libc::c_uint);
    let mut bits_l2_0: uint64_t = Hacl_Bignum_Lib_bn_get_bits_u64(
        1 as libc::c_uint,
        r1,
        k2_0,
        4 as libc::c_uint,
    );
    precomp_get_consttime(
        Hacl_K256_PrecompTable_precomp_basepoint_table_w4.as_ptr(),
        bits_l2_0,
        tmp.as_mut_ptr(),
    );
    let mut p_copy2_0: [uint64_t; 15] = [
        0 as libc::c_uint as uint64_t,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
    ];
    memcpy(
        p_copy2_0.as_mut_ptr() as *mut libc::c_void,
        out as *const libc::c_void,
        (15 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    Hacl_Impl_K256_PointAdd_point_add(out, p_copy2_0.as_mut_ptr(), tmp.as_mut_ptr());
    i = (i as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut i0_1: uint32_t = 0 as libc::c_uint;
    let mut p_copy_9: [uint64_t; 15] = [
        0 as libc::c_uint as uint64_t,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
    ];
    memcpy(
        p_copy_9.as_mut_ptr() as *mut libc::c_void,
        out as *const libc::c_void,
        (15 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    Hacl_Impl_K256_PointDouble_point_double(out, p_copy_9.as_mut_ptr());
    i0_1 = (i0_1 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
        as uint32_t;
    let mut p_copy_10: [uint64_t; 15] = [
        0 as libc::c_uint as uint64_t,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
    ];
    memcpy(
        p_copy_10.as_mut_ptr() as *mut libc::c_void,
        out as *const libc::c_void,
        (15 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    Hacl_Impl_K256_PointDouble_point_double(out, p_copy_10.as_mut_ptr());
    i0_1 = (i0_1 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
        as uint32_t;
    let mut p_copy_11: [uint64_t; 15] = [
        0 as libc::c_uint as uint64_t,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
    ];
    memcpy(
        p_copy_11.as_mut_ptr() as *mut libc::c_void,
        out as *const libc::c_void,
        (15 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    Hacl_Impl_K256_PointDouble_point_double(out, p_copy_11.as_mut_ptr());
    i0_1 = (i0_1 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
        as uint32_t;
    let mut p_copy_12: [uint64_t; 15] = [
        0 as libc::c_uint as uint64_t,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
    ];
    memcpy(
        p_copy_12.as_mut_ptr() as *mut libc::c_void,
        out as *const libc::c_void,
        (15 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    Hacl_Impl_K256_PointDouble_point_double(out, p_copy_12.as_mut_ptr());
    i0_1 = (i0_1 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
        as uint32_t;
    let mut k_1: uint32_t = (64 as libc::c_uint)
        .wrapping_sub((4 as libc::c_uint).wrapping_mul(i))
        .wrapping_sub(4 as libc::c_uint);
    let mut bits_l_1: uint64_t = Hacl_Bignum_Lib_bn_get_bits_u64(
        1 as libc::c_uint,
        r4,
        k_1,
        4 as libc::c_uint,
    );
    precomp_get_consttime(
        Hacl_K256_PrecompTable_precomp_g_pow2_192_table_w4.as_ptr(),
        bits_l_1,
        tmp.as_mut_ptr(),
    );
    let mut p_copy_13: [uint64_t; 15] = [
        0 as libc::c_uint as uint64_t,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
    ];
    memcpy(
        p_copy_13.as_mut_ptr() as *mut libc::c_void,
        out as *const libc::c_void,
        (15 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    Hacl_Impl_K256_PointAdd_point_add(out, p_copy_13.as_mut_ptr(), tmp.as_mut_ptr());
    let mut k0_1: uint32_t = (64 as libc::c_uint)
        .wrapping_sub((4 as libc::c_uint).wrapping_mul(i))
        .wrapping_sub(4 as libc::c_uint);
    let mut bits_l0_1: uint64_t = Hacl_Bignum_Lib_bn_get_bits_u64(
        1 as libc::c_uint,
        r3,
        k0_1,
        4 as libc::c_uint,
    );
    precomp_get_consttime(
        Hacl_K256_PrecompTable_precomp_g_pow2_128_table_w4.as_ptr(),
        bits_l0_1,
        tmp.as_mut_ptr(),
    );
    let mut p_copy0_1: [uint64_t; 15] = [
        0 as libc::c_uint as uint64_t,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
    ];
    memcpy(
        p_copy0_1.as_mut_ptr() as *mut libc::c_void,
        out as *const libc::c_void,
        (15 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    Hacl_Impl_K256_PointAdd_point_add(out, p_copy0_1.as_mut_ptr(), tmp.as_mut_ptr());
    let mut k1_1: uint32_t = (64 as libc::c_uint)
        .wrapping_sub((4 as libc::c_uint).wrapping_mul(i))
        .wrapping_sub(4 as libc::c_uint);
    let mut bits_l1_1: uint64_t = Hacl_Bignum_Lib_bn_get_bits_u64(
        1 as libc::c_uint,
        r2,
        k1_1,
        4 as libc::c_uint,
    );
    precomp_get_consttime(
        Hacl_K256_PrecompTable_precomp_g_pow2_64_table_w4.as_ptr(),
        bits_l1_1,
        tmp.as_mut_ptr(),
    );
    let mut p_copy1_1: [uint64_t; 15] = [
        0 as libc::c_uint as uint64_t,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
    ];
    memcpy(
        p_copy1_1.as_mut_ptr() as *mut libc::c_void,
        out as *const libc::c_void,
        (15 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    Hacl_Impl_K256_PointAdd_point_add(out, p_copy1_1.as_mut_ptr(), tmp.as_mut_ptr());
    let mut k2_1: uint32_t = (64 as libc::c_uint)
        .wrapping_sub((4 as libc::c_uint).wrapping_mul(i))
        .wrapping_sub(4 as libc::c_uint);
    let mut bits_l2_1: uint64_t = Hacl_Bignum_Lib_bn_get_bits_u64(
        1 as libc::c_uint,
        r1,
        k2_1,
        4 as libc::c_uint,
    );
    precomp_get_consttime(
        Hacl_K256_PrecompTable_precomp_basepoint_table_w4.as_ptr(),
        bits_l2_1,
        tmp.as_mut_ptr(),
    );
    let mut p_copy2_1: [uint64_t; 15] = [
        0 as libc::c_uint as uint64_t,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
    ];
    memcpy(
        p_copy2_1.as_mut_ptr() as *mut libc::c_void,
        out as *const libc::c_void,
        (15 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    Hacl_Impl_K256_PointAdd_point_add(out, p_copy2_1.as_mut_ptr(), tmp.as_mut_ptr());
    i = (i as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut i0_2: uint32_t = 0 as libc::c_uint;
    let mut p_copy_14: [uint64_t; 15] = [
        0 as libc::c_uint as uint64_t,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
    ];
    memcpy(
        p_copy_14.as_mut_ptr() as *mut libc::c_void,
        out as *const libc::c_void,
        (15 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    Hacl_Impl_K256_PointDouble_point_double(out, p_copy_14.as_mut_ptr());
    i0_2 = (i0_2 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
        as uint32_t;
    let mut p_copy_15: [uint64_t; 15] = [
        0 as libc::c_uint as uint64_t,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
    ];
    memcpy(
        p_copy_15.as_mut_ptr() as *mut libc::c_void,
        out as *const libc::c_void,
        (15 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    Hacl_Impl_K256_PointDouble_point_double(out, p_copy_15.as_mut_ptr());
    i0_2 = (i0_2 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
        as uint32_t;
    let mut p_copy_16: [uint64_t; 15] = [
        0 as libc::c_uint as uint64_t,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
    ];
    memcpy(
        p_copy_16.as_mut_ptr() as *mut libc::c_void,
        out as *const libc::c_void,
        (15 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    Hacl_Impl_K256_PointDouble_point_double(out, p_copy_16.as_mut_ptr());
    i0_2 = (i0_2 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
        as uint32_t;
    let mut p_copy_17: [uint64_t; 15] = [
        0 as libc::c_uint as uint64_t,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
    ];
    memcpy(
        p_copy_17.as_mut_ptr() as *mut libc::c_void,
        out as *const libc::c_void,
        (15 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    Hacl_Impl_K256_PointDouble_point_double(out, p_copy_17.as_mut_ptr());
    i0_2 = (i0_2 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
        as uint32_t;
    let mut k_2: uint32_t = (64 as libc::c_uint)
        .wrapping_sub((4 as libc::c_uint).wrapping_mul(i))
        .wrapping_sub(4 as libc::c_uint);
    let mut bits_l_2: uint64_t = Hacl_Bignum_Lib_bn_get_bits_u64(
        1 as libc::c_uint,
        r4,
        k_2,
        4 as libc::c_uint,
    );
    precomp_get_consttime(
        Hacl_K256_PrecompTable_precomp_g_pow2_192_table_w4.as_ptr(),
        bits_l_2,
        tmp.as_mut_ptr(),
    );
    let mut p_copy_18: [uint64_t; 15] = [
        0 as libc::c_uint as uint64_t,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
    ];
    memcpy(
        p_copy_18.as_mut_ptr() as *mut libc::c_void,
        out as *const libc::c_void,
        (15 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    Hacl_Impl_K256_PointAdd_point_add(out, p_copy_18.as_mut_ptr(), tmp.as_mut_ptr());
    let mut k0_2: uint32_t = (64 as libc::c_uint)
        .wrapping_sub((4 as libc::c_uint).wrapping_mul(i))
        .wrapping_sub(4 as libc::c_uint);
    let mut bits_l0_2: uint64_t = Hacl_Bignum_Lib_bn_get_bits_u64(
        1 as libc::c_uint,
        r3,
        k0_2,
        4 as libc::c_uint,
    );
    precomp_get_consttime(
        Hacl_K256_PrecompTable_precomp_g_pow2_128_table_w4.as_ptr(),
        bits_l0_2,
        tmp.as_mut_ptr(),
    );
    let mut p_copy0_2: [uint64_t; 15] = [
        0 as libc::c_uint as uint64_t,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
    ];
    memcpy(
        p_copy0_2.as_mut_ptr() as *mut libc::c_void,
        out as *const libc::c_void,
        (15 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    Hacl_Impl_K256_PointAdd_point_add(out, p_copy0_2.as_mut_ptr(), tmp.as_mut_ptr());
    let mut k1_2: uint32_t = (64 as libc::c_uint)
        .wrapping_sub((4 as libc::c_uint).wrapping_mul(i))
        .wrapping_sub(4 as libc::c_uint);
    let mut bits_l1_2: uint64_t = Hacl_Bignum_Lib_bn_get_bits_u64(
        1 as libc::c_uint,
        r2,
        k1_2,
        4 as libc::c_uint,
    );
    precomp_get_consttime(
        Hacl_K256_PrecompTable_precomp_g_pow2_64_table_w4.as_ptr(),
        bits_l1_2,
        tmp.as_mut_ptr(),
    );
    let mut p_copy1_2: [uint64_t; 15] = [
        0 as libc::c_uint as uint64_t,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
    ];
    memcpy(
        p_copy1_2.as_mut_ptr() as *mut libc::c_void,
        out as *const libc::c_void,
        (15 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    Hacl_Impl_K256_PointAdd_point_add(out, p_copy1_2.as_mut_ptr(), tmp.as_mut_ptr());
    let mut k2_2: uint32_t = (64 as libc::c_uint)
        .wrapping_sub((4 as libc::c_uint).wrapping_mul(i))
        .wrapping_sub(4 as libc::c_uint);
    let mut bits_l2_2: uint64_t = Hacl_Bignum_Lib_bn_get_bits_u64(
        1 as libc::c_uint,
        r1,
        k2_2,
        4 as libc::c_uint,
    );
    precomp_get_consttime(
        Hacl_K256_PrecompTable_precomp_basepoint_table_w4.as_ptr(),
        bits_l2_2,
        tmp.as_mut_ptr(),
    );
    let mut p_copy2_2: [uint64_t; 15] = [
        0 as libc::c_uint as uint64_t,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
    ];
    memcpy(
        p_copy2_2.as_mut_ptr() as *mut libc::c_void,
        out as *const libc::c_void,
        (15 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    Hacl_Impl_K256_PointAdd_point_add(out, p_copy2_2.as_mut_ptr(), tmp.as_mut_ptr());
    i = (i as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut i0_3: uint32_t = 0 as libc::c_uint;
    let mut p_copy_19: [uint64_t; 15] = [
        0 as libc::c_uint as uint64_t,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
    ];
    memcpy(
        p_copy_19.as_mut_ptr() as *mut libc::c_void,
        out as *const libc::c_void,
        (15 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    Hacl_Impl_K256_PointDouble_point_double(out, p_copy_19.as_mut_ptr());
    i0_3 = (i0_3 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
        as uint32_t;
    let mut p_copy_20: [uint64_t; 15] = [
        0 as libc::c_uint as uint64_t,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
    ];
    memcpy(
        p_copy_20.as_mut_ptr() as *mut libc::c_void,
        out as *const libc::c_void,
        (15 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    Hacl_Impl_K256_PointDouble_point_double(out, p_copy_20.as_mut_ptr());
    i0_3 = (i0_3 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
        as uint32_t;
    let mut p_copy_21: [uint64_t; 15] = [
        0 as libc::c_uint as uint64_t,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
    ];
    memcpy(
        p_copy_21.as_mut_ptr() as *mut libc::c_void,
        out as *const libc::c_void,
        (15 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    Hacl_Impl_K256_PointDouble_point_double(out, p_copy_21.as_mut_ptr());
    i0_3 = (i0_3 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
        as uint32_t;
    let mut p_copy_22: [uint64_t; 15] = [
        0 as libc::c_uint as uint64_t,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
    ];
    memcpy(
        p_copy_22.as_mut_ptr() as *mut libc::c_void,
        out as *const libc::c_void,
        (15 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    Hacl_Impl_K256_PointDouble_point_double(out, p_copy_22.as_mut_ptr());
    i0_3 = (i0_3 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
        as uint32_t;
    let mut k_3: uint32_t = (64 as libc::c_uint)
        .wrapping_sub((4 as libc::c_uint).wrapping_mul(i))
        .wrapping_sub(4 as libc::c_uint);
    let mut bits_l_3: uint64_t = Hacl_Bignum_Lib_bn_get_bits_u64(
        1 as libc::c_uint,
        r4,
        k_3,
        4 as libc::c_uint,
    );
    precomp_get_consttime(
        Hacl_K256_PrecompTable_precomp_g_pow2_192_table_w4.as_ptr(),
        bits_l_3,
        tmp.as_mut_ptr(),
    );
    let mut p_copy_23: [uint64_t; 15] = [
        0 as libc::c_uint as uint64_t,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
    ];
    memcpy(
        p_copy_23.as_mut_ptr() as *mut libc::c_void,
        out as *const libc::c_void,
        (15 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    Hacl_Impl_K256_PointAdd_point_add(out, p_copy_23.as_mut_ptr(), tmp.as_mut_ptr());
    let mut k0_3: uint32_t = (64 as libc::c_uint)
        .wrapping_sub((4 as libc::c_uint).wrapping_mul(i))
        .wrapping_sub(4 as libc::c_uint);
    let mut bits_l0_3: uint64_t = Hacl_Bignum_Lib_bn_get_bits_u64(
        1 as libc::c_uint,
        r3,
        k0_3,
        4 as libc::c_uint,
    );
    precomp_get_consttime(
        Hacl_K256_PrecompTable_precomp_g_pow2_128_table_w4.as_ptr(),
        bits_l0_3,
        tmp.as_mut_ptr(),
    );
    let mut p_copy0_3: [uint64_t; 15] = [
        0 as libc::c_uint as uint64_t,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
    ];
    memcpy(
        p_copy0_3.as_mut_ptr() as *mut libc::c_void,
        out as *const libc::c_void,
        (15 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    Hacl_Impl_K256_PointAdd_point_add(out, p_copy0_3.as_mut_ptr(), tmp.as_mut_ptr());
    let mut k1_3: uint32_t = (64 as libc::c_uint)
        .wrapping_sub((4 as libc::c_uint).wrapping_mul(i))
        .wrapping_sub(4 as libc::c_uint);
    let mut bits_l1_3: uint64_t = Hacl_Bignum_Lib_bn_get_bits_u64(
        1 as libc::c_uint,
        r2,
        k1_3,
        4 as libc::c_uint,
    );
    precomp_get_consttime(
        Hacl_K256_PrecompTable_precomp_g_pow2_64_table_w4.as_ptr(),
        bits_l1_3,
        tmp.as_mut_ptr(),
    );
    let mut p_copy1_3: [uint64_t; 15] = [
        0 as libc::c_uint as uint64_t,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
    ];
    memcpy(
        p_copy1_3.as_mut_ptr() as *mut libc::c_void,
        out as *const libc::c_void,
        (15 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    Hacl_Impl_K256_PointAdd_point_add(out, p_copy1_3.as_mut_ptr(), tmp.as_mut_ptr());
    let mut k2_3: uint32_t = (64 as libc::c_uint)
        .wrapping_sub((4 as libc::c_uint).wrapping_mul(i))
        .wrapping_sub(4 as libc::c_uint);
    let mut bits_l2_3: uint64_t = Hacl_Bignum_Lib_bn_get_bits_u64(
        1 as libc::c_uint,
        r1,
        k2_3,
        4 as libc::c_uint,
    );
    precomp_get_consttime(
        Hacl_K256_PrecompTable_precomp_basepoint_table_w4.as_ptr(),
        bits_l2_3,
        tmp.as_mut_ptr(),
    );
    let mut p_copy2_3: [uint64_t; 15] = [
        0 as libc::c_uint as uint64_t,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
    ];
    memcpy(
        p_copy2_3.as_mut_ptr() as *mut libc::c_void,
        out as *const libc::c_void,
        (15 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    Hacl_Impl_K256_PointAdd_point_add(out, p_copy2_3.as_mut_ptr(), tmp.as_mut_ptr());
    i = (i as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut i0_4: uint32_t = 0 as libc::c_uint;
    let mut p_copy_24: [uint64_t; 15] = [
        0 as libc::c_uint as uint64_t,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
    ];
    memcpy(
        p_copy_24.as_mut_ptr() as *mut libc::c_void,
        out as *const libc::c_void,
        (15 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    Hacl_Impl_K256_PointDouble_point_double(out, p_copy_24.as_mut_ptr());
    i0_4 = (i0_4 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
        as uint32_t;
    let mut p_copy_25: [uint64_t; 15] = [
        0 as libc::c_uint as uint64_t,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
    ];
    memcpy(
        p_copy_25.as_mut_ptr() as *mut libc::c_void,
        out as *const libc::c_void,
        (15 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    Hacl_Impl_K256_PointDouble_point_double(out, p_copy_25.as_mut_ptr());
    i0_4 = (i0_4 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
        as uint32_t;
    let mut p_copy_26: [uint64_t; 15] = [
        0 as libc::c_uint as uint64_t,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
    ];
    memcpy(
        p_copy_26.as_mut_ptr() as *mut libc::c_void,
        out as *const libc::c_void,
        (15 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    Hacl_Impl_K256_PointDouble_point_double(out, p_copy_26.as_mut_ptr());
    i0_4 = (i0_4 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
        as uint32_t;
    let mut p_copy_27: [uint64_t; 15] = [
        0 as libc::c_uint as uint64_t,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
    ];
    memcpy(
        p_copy_27.as_mut_ptr() as *mut libc::c_void,
        out as *const libc::c_void,
        (15 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    Hacl_Impl_K256_PointDouble_point_double(out, p_copy_27.as_mut_ptr());
    i0_4 = (i0_4 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
        as uint32_t;
    let mut k_4: uint32_t = (64 as libc::c_uint)
        .wrapping_sub((4 as libc::c_uint).wrapping_mul(i))
        .wrapping_sub(4 as libc::c_uint);
    let mut bits_l_4: uint64_t = Hacl_Bignum_Lib_bn_get_bits_u64(
        1 as libc::c_uint,
        r4,
        k_4,
        4 as libc::c_uint,
    );
    precomp_get_consttime(
        Hacl_K256_PrecompTable_precomp_g_pow2_192_table_w4.as_ptr(),
        bits_l_4,
        tmp.as_mut_ptr(),
    );
    let mut p_copy_28: [uint64_t; 15] = [
        0 as libc::c_uint as uint64_t,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
    ];
    memcpy(
        p_copy_28.as_mut_ptr() as *mut libc::c_void,
        out as *const libc::c_void,
        (15 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    Hacl_Impl_K256_PointAdd_point_add(out, p_copy_28.as_mut_ptr(), tmp.as_mut_ptr());
    let mut k0_4: uint32_t = (64 as libc::c_uint)
        .wrapping_sub((4 as libc::c_uint).wrapping_mul(i))
        .wrapping_sub(4 as libc::c_uint);
    let mut bits_l0_4: uint64_t = Hacl_Bignum_Lib_bn_get_bits_u64(
        1 as libc::c_uint,
        r3,
        k0_4,
        4 as libc::c_uint,
    );
    precomp_get_consttime(
        Hacl_K256_PrecompTable_precomp_g_pow2_128_table_w4.as_ptr(),
        bits_l0_4,
        tmp.as_mut_ptr(),
    );
    let mut p_copy0_4: [uint64_t; 15] = [
        0 as libc::c_uint as uint64_t,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
    ];
    memcpy(
        p_copy0_4.as_mut_ptr() as *mut libc::c_void,
        out as *const libc::c_void,
        (15 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    Hacl_Impl_K256_PointAdd_point_add(out, p_copy0_4.as_mut_ptr(), tmp.as_mut_ptr());
    let mut k1_4: uint32_t = (64 as libc::c_uint)
        .wrapping_sub((4 as libc::c_uint).wrapping_mul(i))
        .wrapping_sub(4 as libc::c_uint);
    let mut bits_l1_4: uint64_t = Hacl_Bignum_Lib_bn_get_bits_u64(
        1 as libc::c_uint,
        r2,
        k1_4,
        4 as libc::c_uint,
    );
    precomp_get_consttime(
        Hacl_K256_PrecompTable_precomp_g_pow2_64_table_w4.as_ptr(),
        bits_l1_4,
        tmp.as_mut_ptr(),
    );
    let mut p_copy1_4: [uint64_t; 15] = [
        0 as libc::c_uint as uint64_t,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
    ];
    memcpy(
        p_copy1_4.as_mut_ptr() as *mut libc::c_void,
        out as *const libc::c_void,
        (15 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    Hacl_Impl_K256_PointAdd_point_add(out, p_copy1_4.as_mut_ptr(), tmp.as_mut_ptr());
    let mut k2_4: uint32_t = (64 as libc::c_uint)
        .wrapping_sub((4 as libc::c_uint).wrapping_mul(i))
        .wrapping_sub(4 as libc::c_uint);
    let mut bits_l2_4: uint64_t = Hacl_Bignum_Lib_bn_get_bits_u64(
        1 as libc::c_uint,
        r1,
        k2_4,
        4 as libc::c_uint,
    );
    precomp_get_consttime(
        Hacl_K256_PrecompTable_precomp_basepoint_table_w4.as_ptr(),
        bits_l2_4,
        tmp.as_mut_ptr(),
    );
    let mut p_copy2_4: [uint64_t; 15] = [
        0 as libc::c_uint as uint64_t,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
    ];
    memcpy(
        p_copy2_4.as_mut_ptr() as *mut libc::c_void,
        out as *const libc::c_void,
        (15 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    Hacl_Impl_K256_PointAdd_point_add(out, p_copy2_4.as_mut_ptr(), tmp.as_mut_ptr());
    i = (i as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut i0_5: uint32_t = 0 as libc::c_uint;
    let mut p_copy_29: [uint64_t; 15] = [
        0 as libc::c_uint as uint64_t,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
    ];
    memcpy(
        p_copy_29.as_mut_ptr() as *mut libc::c_void,
        out as *const libc::c_void,
        (15 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    Hacl_Impl_K256_PointDouble_point_double(out, p_copy_29.as_mut_ptr());
    i0_5 = (i0_5 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
        as uint32_t;
    let mut p_copy_30: [uint64_t; 15] = [
        0 as libc::c_uint as uint64_t,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
    ];
    memcpy(
        p_copy_30.as_mut_ptr() as *mut libc::c_void,
        out as *const libc::c_void,
        (15 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    Hacl_Impl_K256_PointDouble_point_double(out, p_copy_30.as_mut_ptr());
    i0_5 = (i0_5 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
        as uint32_t;
    let mut p_copy_31: [uint64_t; 15] = [
        0 as libc::c_uint as uint64_t,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
    ];
    memcpy(
        p_copy_31.as_mut_ptr() as *mut libc::c_void,
        out as *const libc::c_void,
        (15 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    Hacl_Impl_K256_PointDouble_point_double(out, p_copy_31.as_mut_ptr());
    i0_5 = (i0_5 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
        as uint32_t;
    let mut p_copy_32: [uint64_t; 15] = [
        0 as libc::c_uint as uint64_t,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
    ];
    memcpy(
        p_copy_32.as_mut_ptr() as *mut libc::c_void,
        out as *const libc::c_void,
        (15 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    Hacl_Impl_K256_PointDouble_point_double(out, p_copy_32.as_mut_ptr());
    i0_5 = (i0_5 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
        as uint32_t;
    let mut k_5: uint32_t = (64 as libc::c_uint)
        .wrapping_sub((4 as libc::c_uint).wrapping_mul(i))
        .wrapping_sub(4 as libc::c_uint);
    let mut bits_l_5: uint64_t = Hacl_Bignum_Lib_bn_get_bits_u64(
        1 as libc::c_uint,
        r4,
        k_5,
        4 as libc::c_uint,
    );
    precomp_get_consttime(
        Hacl_K256_PrecompTable_precomp_g_pow2_192_table_w4.as_ptr(),
        bits_l_5,
        tmp.as_mut_ptr(),
    );
    let mut p_copy_33: [uint64_t; 15] = [
        0 as libc::c_uint as uint64_t,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
    ];
    memcpy(
        p_copy_33.as_mut_ptr() as *mut libc::c_void,
        out as *const libc::c_void,
        (15 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    Hacl_Impl_K256_PointAdd_point_add(out, p_copy_33.as_mut_ptr(), tmp.as_mut_ptr());
    let mut k0_5: uint32_t = (64 as libc::c_uint)
        .wrapping_sub((4 as libc::c_uint).wrapping_mul(i))
        .wrapping_sub(4 as libc::c_uint);
    let mut bits_l0_5: uint64_t = Hacl_Bignum_Lib_bn_get_bits_u64(
        1 as libc::c_uint,
        r3,
        k0_5,
        4 as libc::c_uint,
    );
    precomp_get_consttime(
        Hacl_K256_PrecompTable_precomp_g_pow2_128_table_w4.as_ptr(),
        bits_l0_5,
        tmp.as_mut_ptr(),
    );
    let mut p_copy0_5: [uint64_t; 15] = [
        0 as libc::c_uint as uint64_t,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
    ];
    memcpy(
        p_copy0_5.as_mut_ptr() as *mut libc::c_void,
        out as *const libc::c_void,
        (15 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    Hacl_Impl_K256_PointAdd_point_add(out, p_copy0_5.as_mut_ptr(), tmp.as_mut_ptr());
    let mut k1_5: uint32_t = (64 as libc::c_uint)
        .wrapping_sub((4 as libc::c_uint).wrapping_mul(i))
        .wrapping_sub(4 as libc::c_uint);
    let mut bits_l1_5: uint64_t = Hacl_Bignum_Lib_bn_get_bits_u64(
        1 as libc::c_uint,
        r2,
        k1_5,
        4 as libc::c_uint,
    );
    precomp_get_consttime(
        Hacl_K256_PrecompTable_precomp_g_pow2_64_table_w4.as_ptr(),
        bits_l1_5,
        tmp.as_mut_ptr(),
    );
    let mut p_copy1_5: [uint64_t; 15] = [
        0 as libc::c_uint as uint64_t,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
    ];
    memcpy(
        p_copy1_5.as_mut_ptr() as *mut libc::c_void,
        out as *const libc::c_void,
        (15 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    Hacl_Impl_K256_PointAdd_point_add(out, p_copy1_5.as_mut_ptr(), tmp.as_mut_ptr());
    let mut k2_5: uint32_t = (64 as libc::c_uint)
        .wrapping_sub((4 as libc::c_uint).wrapping_mul(i))
        .wrapping_sub(4 as libc::c_uint);
    let mut bits_l2_5: uint64_t = Hacl_Bignum_Lib_bn_get_bits_u64(
        1 as libc::c_uint,
        r1,
        k2_5,
        4 as libc::c_uint,
    );
    precomp_get_consttime(
        Hacl_K256_PrecompTable_precomp_basepoint_table_w4.as_ptr(),
        bits_l2_5,
        tmp.as_mut_ptr(),
    );
    let mut p_copy2_5: [uint64_t; 15] = [
        0 as libc::c_uint as uint64_t,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
    ];
    memcpy(
        p_copy2_5.as_mut_ptr() as *mut libc::c_void,
        out as *const libc::c_void,
        (15 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    Hacl_Impl_K256_PointAdd_point_add(out, p_copy2_5.as_mut_ptr(), tmp.as_mut_ptr());
    i = (i as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut i0_6: uint32_t = 0 as libc::c_uint;
    let mut p_copy_34: [uint64_t; 15] = [
        0 as libc::c_uint as uint64_t,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
    ];
    memcpy(
        p_copy_34.as_mut_ptr() as *mut libc::c_void,
        out as *const libc::c_void,
        (15 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    Hacl_Impl_K256_PointDouble_point_double(out, p_copy_34.as_mut_ptr());
    i0_6 = (i0_6 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
        as uint32_t;
    let mut p_copy_35: [uint64_t; 15] = [
        0 as libc::c_uint as uint64_t,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
    ];
    memcpy(
        p_copy_35.as_mut_ptr() as *mut libc::c_void,
        out as *const libc::c_void,
        (15 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    Hacl_Impl_K256_PointDouble_point_double(out, p_copy_35.as_mut_ptr());
    i0_6 = (i0_6 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
        as uint32_t;
    let mut p_copy_36: [uint64_t; 15] = [
        0 as libc::c_uint as uint64_t,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
    ];
    memcpy(
        p_copy_36.as_mut_ptr() as *mut libc::c_void,
        out as *const libc::c_void,
        (15 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    Hacl_Impl_K256_PointDouble_point_double(out, p_copy_36.as_mut_ptr());
    i0_6 = (i0_6 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
        as uint32_t;
    let mut p_copy_37: [uint64_t; 15] = [
        0 as libc::c_uint as uint64_t,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
    ];
    memcpy(
        p_copy_37.as_mut_ptr() as *mut libc::c_void,
        out as *const libc::c_void,
        (15 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    Hacl_Impl_K256_PointDouble_point_double(out, p_copy_37.as_mut_ptr());
    i0_6 = (i0_6 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
        as uint32_t;
    let mut k_6: uint32_t = (64 as libc::c_uint)
        .wrapping_sub((4 as libc::c_uint).wrapping_mul(i))
        .wrapping_sub(4 as libc::c_uint);
    let mut bits_l_6: uint64_t = Hacl_Bignum_Lib_bn_get_bits_u64(
        1 as libc::c_uint,
        r4,
        k_6,
        4 as libc::c_uint,
    );
    precomp_get_consttime(
        Hacl_K256_PrecompTable_precomp_g_pow2_192_table_w4.as_ptr(),
        bits_l_6,
        tmp.as_mut_ptr(),
    );
    let mut p_copy_38: [uint64_t; 15] = [
        0 as libc::c_uint as uint64_t,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
    ];
    memcpy(
        p_copy_38.as_mut_ptr() as *mut libc::c_void,
        out as *const libc::c_void,
        (15 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    Hacl_Impl_K256_PointAdd_point_add(out, p_copy_38.as_mut_ptr(), tmp.as_mut_ptr());
    let mut k0_6: uint32_t = (64 as libc::c_uint)
        .wrapping_sub((4 as libc::c_uint).wrapping_mul(i))
        .wrapping_sub(4 as libc::c_uint);
    let mut bits_l0_6: uint64_t = Hacl_Bignum_Lib_bn_get_bits_u64(
        1 as libc::c_uint,
        r3,
        k0_6,
        4 as libc::c_uint,
    );
    precomp_get_consttime(
        Hacl_K256_PrecompTable_precomp_g_pow2_128_table_w4.as_ptr(),
        bits_l0_6,
        tmp.as_mut_ptr(),
    );
    let mut p_copy0_6: [uint64_t; 15] = [
        0 as libc::c_uint as uint64_t,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
    ];
    memcpy(
        p_copy0_6.as_mut_ptr() as *mut libc::c_void,
        out as *const libc::c_void,
        (15 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    Hacl_Impl_K256_PointAdd_point_add(out, p_copy0_6.as_mut_ptr(), tmp.as_mut_ptr());
    let mut k1_6: uint32_t = (64 as libc::c_uint)
        .wrapping_sub((4 as libc::c_uint).wrapping_mul(i))
        .wrapping_sub(4 as libc::c_uint);
    let mut bits_l1_6: uint64_t = Hacl_Bignum_Lib_bn_get_bits_u64(
        1 as libc::c_uint,
        r2,
        k1_6,
        4 as libc::c_uint,
    );
    precomp_get_consttime(
        Hacl_K256_PrecompTable_precomp_g_pow2_64_table_w4.as_ptr(),
        bits_l1_6,
        tmp.as_mut_ptr(),
    );
    let mut p_copy1_6: [uint64_t; 15] = [
        0 as libc::c_uint as uint64_t,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
    ];
    memcpy(
        p_copy1_6.as_mut_ptr() as *mut libc::c_void,
        out as *const libc::c_void,
        (15 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    Hacl_Impl_K256_PointAdd_point_add(out, p_copy1_6.as_mut_ptr(), tmp.as_mut_ptr());
    let mut k2_6: uint32_t = (64 as libc::c_uint)
        .wrapping_sub((4 as libc::c_uint).wrapping_mul(i))
        .wrapping_sub(4 as libc::c_uint);
    let mut bits_l2_6: uint64_t = Hacl_Bignum_Lib_bn_get_bits_u64(
        1 as libc::c_uint,
        r1,
        k2_6,
        4 as libc::c_uint,
    );
    precomp_get_consttime(
        Hacl_K256_PrecompTable_precomp_basepoint_table_w4.as_ptr(),
        bits_l2_6,
        tmp.as_mut_ptr(),
    );
    let mut p_copy2_6: [uint64_t; 15] = [
        0 as libc::c_uint as uint64_t,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
    ];
    memcpy(
        p_copy2_6.as_mut_ptr() as *mut libc::c_void,
        out as *const libc::c_void,
        (15 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    Hacl_Impl_K256_PointAdd_point_add(out, p_copy2_6.as_mut_ptr(), tmp.as_mut_ptr());
    i = (i as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut i0_7: uint32_t = 0 as libc::c_uint;
    let mut p_copy_39: [uint64_t; 15] = [
        0 as libc::c_uint as uint64_t,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
    ];
    memcpy(
        p_copy_39.as_mut_ptr() as *mut libc::c_void,
        out as *const libc::c_void,
        (15 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    Hacl_Impl_K256_PointDouble_point_double(out, p_copy_39.as_mut_ptr());
    i0_7 = (i0_7 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
        as uint32_t;
    let mut p_copy_40: [uint64_t; 15] = [
        0 as libc::c_uint as uint64_t,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
    ];
    memcpy(
        p_copy_40.as_mut_ptr() as *mut libc::c_void,
        out as *const libc::c_void,
        (15 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    Hacl_Impl_K256_PointDouble_point_double(out, p_copy_40.as_mut_ptr());
    i0_7 = (i0_7 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
        as uint32_t;
    let mut p_copy_41: [uint64_t; 15] = [
        0 as libc::c_uint as uint64_t,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
    ];
    memcpy(
        p_copy_41.as_mut_ptr() as *mut libc::c_void,
        out as *const libc::c_void,
        (15 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    Hacl_Impl_K256_PointDouble_point_double(out, p_copy_41.as_mut_ptr());
    i0_7 = (i0_7 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
        as uint32_t;
    let mut p_copy_42: [uint64_t; 15] = [
        0 as libc::c_uint as uint64_t,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
    ];
    memcpy(
        p_copy_42.as_mut_ptr() as *mut libc::c_void,
        out as *const libc::c_void,
        (15 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    Hacl_Impl_K256_PointDouble_point_double(out, p_copy_42.as_mut_ptr());
    i0_7 = (i0_7 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
        as uint32_t;
    let mut k_7: uint32_t = (64 as libc::c_uint)
        .wrapping_sub((4 as libc::c_uint).wrapping_mul(i))
        .wrapping_sub(4 as libc::c_uint);
    let mut bits_l_7: uint64_t = Hacl_Bignum_Lib_bn_get_bits_u64(
        1 as libc::c_uint,
        r4,
        k_7,
        4 as libc::c_uint,
    );
    precomp_get_consttime(
        Hacl_K256_PrecompTable_precomp_g_pow2_192_table_w4.as_ptr(),
        bits_l_7,
        tmp.as_mut_ptr(),
    );
    let mut p_copy_43: [uint64_t; 15] = [
        0 as libc::c_uint as uint64_t,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
    ];
    memcpy(
        p_copy_43.as_mut_ptr() as *mut libc::c_void,
        out as *const libc::c_void,
        (15 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    Hacl_Impl_K256_PointAdd_point_add(out, p_copy_43.as_mut_ptr(), tmp.as_mut_ptr());
    let mut k0_7: uint32_t = (64 as libc::c_uint)
        .wrapping_sub((4 as libc::c_uint).wrapping_mul(i))
        .wrapping_sub(4 as libc::c_uint);
    let mut bits_l0_7: uint64_t = Hacl_Bignum_Lib_bn_get_bits_u64(
        1 as libc::c_uint,
        r3,
        k0_7,
        4 as libc::c_uint,
    );
    precomp_get_consttime(
        Hacl_K256_PrecompTable_precomp_g_pow2_128_table_w4.as_ptr(),
        bits_l0_7,
        tmp.as_mut_ptr(),
    );
    let mut p_copy0_7: [uint64_t; 15] = [
        0 as libc::c_uint as uint64_t,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
    ];
    memcpy(
        p_copy0_7.as_mut_ptr() as *mut libc::c_void,
        out as *const libc::c_void,
        (15 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    Hacl_Impl_K256_PointAdd_point_add(out, p_copy0_7.as_mut_ptr(), tmp.as_mut_ptr());
    let mut k1_7: uint32_t = (64 as libc::c_uint)
        .wrapping_sub((4 as libc::c_uint).wrapping_mul(i))
        .wrapping_sub(4 as libc::c_uint);
    let mut bits_l1_7: uint64_t = Hacl_Bignum_Lib_bn_get_bits_u64(
        1 as libc::c_uint,
        r2,
        k1_7,
        4 as libc::c_uint,
    );
    precomp_get_consttime(
        Hacl_K256_PrecompTable_precomp_g_pow2_64_table_w4.as_ptr(),
        bits_l1_7,
        tmp.as_mut_ptr(),
    );
    let mut p_copy1_7: [uint64_t; 15] = [
        0 as libc::c_uint as uint64_t,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
    ];
    memcpy(
        p_copy1_7.as_mut_ptr() as *mut libc::c_void,
        out as *const libc::c_void,
        (15 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    Hacl_Impl_K256_PointAdd_point_add(out, p_copy1_7.as_mut_ptr(), tmp.as_mut_ptr());
    let mut k2_7: uint32_t = (64 as libc::c_uint)
        .wrapping_sub((4 as libc::c_uint).wrapping_mul(i))
        .wrapping_sub(4 as libc::c_uint);
    let mut bits_l2_7: uint64_t = Hacl_Bignum_Lib_bn_get_bits_u64(
        1 as libc::c_uint,
        r1,
        k2_7,
        4 as libc::c_uint,
    );
    precomp_get_consttime(
        Hacl_K256_PrecompTable_precomp_basepoint_table_w4.as_ptr(),
        bits_l2_7,
        tmp.as_mut_ptr(),
    );
    let mut p_copy2_7: [uint64_t; 15] = [
        0 as libc::c_uint as uint64_t,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
    ];
    memcpy(
        p_copy2_7.as_mut_ptr() as *mut libc::c_void,
        out as *const libc::c_void,
        (15 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    Hacl_Impl_K256_PointAdd_point_add(out, p_copy2_7.as_mut_ptr(), tmp.as_mut_ptr());
    i = (i as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut i0_8: uint32_t = 0 as libc::c_uint;
    let mut p_copy_44: [uint64_t; 15] = [
        0 as libc::c_uint as uint64_t,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
    ];
    memcpy(
        p_copy_44.as_mut_ptr() as *mut libc::c_void,
        out as *const libc::c_void,
        (15 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    Hacl_Impl_K256_PointDouble_point_double(out, p_copy_44.as_mut_ptr());
    i0_8 = (i0_8 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
        as uint32_t;
    let mut p_copy_45: [uint64_t; 15] = [
        0 as libc::c_uint as uint64_t,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
    ];
    memcpy(
        p_copy_45.as_mut_ptr() as *mut libc::c_void,
        out as *const libc::c_void,
        (15 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    Hacl_Impl_K256_PointDouble_point_double(out, p_copy_45.as_mut_ptr());
    i0_8 = (i0_8 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
        as uint32_t;
    let mut p_copy_46: [uint64_t; 15] = [
        0 as libc::c_uint as uint64_t,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
    ];
    memcpy(
        p_copy_46.as_mut_ptr() as *mut libc::c_void,
        out as *const libc::c_void,
        (15 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    Hacl_Impl_K256_PointDouble_point_double(out, p_copy_46.as_mut_ptr());
    i0_8 = (i0_8 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
        as uint32_t;
    let mut p_copy_47: [uint64_t; 15] = [
        0 as libc::c_uint as uint64_t,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
    ];
    memcpy(
        p_copy_47.as_mut_ptr() as *mut libc::c_void,
        out as *const libc::c_void,
        (15 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    Hacl_Impl_K256_PointDouble_point_double(out, p_copy_47.as_mut_ptr());
    i0_8 = (i0_8 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
        as uint32_t;
    let mut k_8: uint32_t = (64 as libc::c_uint)
        .wrapping_sub((4 as libc::c_uint).wrapping_mul(i))
        .wrapping_sub(4 as libc::c_uint);
    let mut bits_l_8: uint64_t = Hacl_Bignum_Lib_bn_get_bits_u64(
        1 as libc::c_uint,
        r4,
        k_8,
        4 as libc::c_uint,
    );
    precomp_get_consttime(
        Hacl_K256_PrecompTable_precomp_g_pow2_192_table_w4.as_ptr(),
        bits_l_8,
        tmp.as_mut_ptr(),
    );
    let mut p_copy_48: [uint64_t; 15] = [
        0 as libc::c_uint as uint64_t,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
    ];
    memcpy(
        p_copy_48.as_mut_ptr() as *mut libc::c_void,
        out as *const libc::c_void,
        (15 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    Hacl_Impl_K256_PointAdd_point_add(out, p_copy_48.as_mut_ptr(), tmp.as_mut_ptr());
    let mut k0_8: uint32_t = (64 as libc::c_uint)
        .wrapping_sub((4 as libc::c_uint).wrapping_mul(i))
        .wrapping_sub(4 as libc::c_uint);
    let mut bits_l0_8: uint64_t = Hacl_Bignum_Lib_bn_get_bits_u64(
        1 as libc::c_uint,
        r3,
        k0_8,
        4 as libc::c_uint,
    );
    precomp_get_consttime(
        Hacl_K256_PrecompTable_precomp_g_pow2_128_table_w4.as_ptr(),
        bits_l0_8,
        tmp.as_mut_ptr(),
    );
    let mut p_copy0_8: [uint64_t; 15] = [
        0 as libc::c_uint as uint64_t,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
    ];
    memcpy(
        p_copy0_8.as_mut_ptr() as *mut libc::c_void,
        out as *const libc::c_void,
        (15 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    Hacl_Impl_K256_PointAdd_point_add(out, p_copy0_8.as_mut_ptr(), tmp.as_mut_ptr());
    let mut k1_8: uint32_t = (64 as libc::c_uint)
        .wrapping_sub((4 as libc::c_uint).wrapping_mul(i))
        .wrapping_sub(4 as libc::c_uint);
    let mut bits_l1_8: uint64_t = Hacl_Bignum_Lib_bn_get_bits_u64(
        1 as libc::c_uint,
        r2,
        k1_8,
        4 as libc::c_uint,
    );
    precomp_get_consttime(
        Hacl_K256_PrecompTable_precomp_g_pow2_64_table_w4.as_ptr(),
        bits_l1_8,
        tmp.as_mut_ptr(),
    );
    let mut p_copy1_8: [uint64_t; 15] = [
        0 as libc::c_uint as uint64_t,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
    ];
    memcpy(
        p_copy1_8.as_mut_ptr() as *mut libc::c_void,
        out as *const libc::c_void,
        (15 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    Hacl_Impl_K256_PointAdd_point_add(out, p_copy1_8.as_mut_ptr(), tmp.as_mut_ptr());
    let mut k2_8: uint32_t = (64 as libc::c_uint)
        .wrapping_sub((4 as libc::c_uint).wrapping_mul(i))
        .wrapping_sub(4 as libc::c_uint);
    let mut bits_l2_8: uint64_t = Hacl_Bignum_Lib_bn_get_bits_u64(
        1 as libc::c_uint,
        r1,
        k2_8,
        4 as libc::c_uint,
    );
    precomp_get_consttime(
        Hacl_K256_PrecompTable_precomp_basepoint_table_w4.as_ptr(),
        bits_l2_8,
        tmp.as_mut_ptr(),
    );
    let mut p_copy2_8: [uint64_t; 15] = [
        0 as libc::c_uint as uint64_t,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
    ];
    memcpy(
        p_copy2_8.as_mut_ptr() as *mut libc::c_void,
        out as *const libc::c_void,
        (15 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    Hacl_Impl_K256_PointAdd_point_add(out, p_copy2_8.as_mut_ptr(), tmp.as_mut_ptr());
    i = (i as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut i0_9: uint32_t = 0 as libc::c_uint;
    let mut p_copy_49: [uint64_t; 15] = [
        0 as libc::c_uint as uint64_t,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
    ];
    memcpy(
        p_copy_49.as_mut_ptr() as *mut libc::c_void,
        out as *const libc::c_void,
        (15 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    Hacl_Impl_K256_PointDouble_point_double(out, p_copy_49.as_mut_ptr());
    i0_9 = (i0_9 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
        as uint32_t;
    let mut p_copy_50: [uint64_t; 15] = [
        0 as libc::c_uint as uint64_t,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
    ];
    memcpy(
        p_copy_50.as_mut_ptr() as *mut libc::c_void,
        out as *const libc::c_void,
        (15 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    Hacl_Impl_K256_PointDouble_point_double(out, p_copy_50.as_mut_ptr());
    i0_9 = (i0_9 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
        as uint32_t;
    let mut p_copy_51: [uint64_t; 15] = [
        0 as libc::c_uint as uint64_t,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
    ];
    memcpy(
        p_copy_51.as_mut_ptr() as *mut libc::c_void,
        out as *const libc::c_void,
        (15 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    Hacl_Impl_K256_PointDouble_point_double(out, p_copy_51.as_mut_ptr());
    i0_9 = (i0_9 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
        as uint32_t;
    let mut p_copy_52: [uint64_t; 15] = [
        0 as libc::c_uint as uint64_t,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
    ];
    memcpy(
        p_copy_52.as_mut_ptr() as *mut libc::c_void,
        out as *const libc::c_void,
        (15 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    Hacl_Impl_K256_PointDouble_point_double(out, p_copy_52.as_mut_ptr());
    i0_9 = (i0_9 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
        as uint32_t;
    let mut k_9: uint32_t = (64 as libc::c_uint)
        .wrapping_sub((4 as libc::c_uint).wrapping_mul(i))
        .wrapping_sub(4 as libc::c_uint);
    let mut bits_l_9: uint64_t = Hacl_Bignum_Lib_bn_get_bits_u64(
        1 as libc::c_uint,
        r4,
        k_9,
        4 as libc::c_uint,
    );
    precomp_get_consttime(
        Hacl_K256_PrecompTable_precomp_g_pow2_192_table_w4.as_ptr(),
        bits_l_9,
        tmp.as_mut_ptr(),
    );
    let mut p_copy_53: [uint64_t; 15] = [
        0 as libc::c_uint as uint64_t,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
    ];
    memcpy(
        p_copy_53.as_mut_ptr() as *mut libc::c_void,
        out as *const libc::c_void,
        (15 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    Hacl_Impl_K256_PointAdd_point_add(out, p_copy_53.as_mut_ptr(), tmp.as_mut_ptr());
    let mut k0_9: uint32_t = (64 as libc::c_uint)
        .wrapping_sub((4 as libc::c_uint).wrapping_mul(i))
        .wrapping_sub(4 as libc::c_uint);
    let mut bits_l0_9: uint64_t = Hacl_Bignum_Lib_bn_get_bits_u64(
        1 as libc::c_uint,
        r3,
        k0_9,
        4 as libc::c_uint,
    );
    precomp_get_consttime(
        Hacl_K256_PrecompTable_precomp_g_pow2_128_table_w4.as_ptr(),
        bits_l0_9,
        tmp.as_mut_ptr(),
    );
    let mut p_copy0_9: [uint64_t; 15] = [
        0 as libc::c_uint as uint64_t,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
    ];
    memcpy(
        p_copy0_9.as_mut_ptr() as *mut libc::c_void,
        out as *const libc::c_void,
        (15 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    Hacl_Impl_K256_PointAdd_point_add(out, p_copy0_9.as_mut_ptr(), tmp.as_mut_ptr());
    let mut k1_9: uint32_t = (64 as libc::c_uint)
        .wrapping_sub((4 as libc::c_uint).wrapping_mul(i))
        .wrapping_sub(4 as libc::c_uint);
    let mut bits_l1_9: uint64_t = Hacl_Bignum_Lib_bn_get_bits_u64(
        1 as libc::c_uint,
        r2,
        k1_9,
        4 as libc::c_uint,
    );
    precomp_get_consttime(
        Hacl_K256_PrecompTable_precomp_g_pow2_64_table_w4.as_ptr(),
        bits_l1_9,
        tmp.as_mut_ptr(),
    );
    let mut p_copy1_9: [uint64_t; 15] = [
        0 as libc::c_uint as uint64_t,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
    ];
    memcpy(
        p_copy1_9.as_mut_ptr() as *mut libc::c_void,
        out as *const libc::c_void,
        (15 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    Hacl_Impl_K256_PointAdd_point_add(out, p_copy1_9.as_mut_ptr(), tmp.as_mut_ptr());
    let mut k2_9: uint32_t = (64 as libc::c_uint)
        .wrapping_sub((4 as libc::c_uint).wrapping_mul(i))
        .wrapping_sub(4 as libc::c_uint);
    let mut bits_l2_9: uint64_t = Hacl_Bignum_Lib_bn_get_bits_u64(
        1 as libc::c_uint,
        r1,
        k2_9,
        4 as libc::c_uint,
    );
    precomp_get_consttime(
        Hacl_K256_PrecompTable_precomp_basepoint_table_w4.as_ptr(),
        bits_l2_9,
        tmp.as_mut_ptr(),
    );
    let mut p_copy2_9: [uint64_t; 15] = [
        0 as libc::c_uint as uint64_t,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
    ];
    memcpy(
        p_copy2_9.as_mut_ptr() as *mut libc::c_void,
        out as *const libc::c_void,
        (15 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    Hacl_Impl_K256_PointAdd_point_add(out, p_copy2_9.as_mut_ptr(), tmp.as_mut_ptr());
    i = (i as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut i0_10: uint32_t = 0 as libc::c_uint;
    let mut p_copy_54: [uint64_t; 15] = [
        0 as libc::c_uint as uint64_t,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
    ];
    memcpy(
        p_copy_54.as_mut_ptr() as *mut libc::c_void,
        out as *const libc::c_void,
        (15 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    Hacl_Impl_K256_PointDouble_point_double(out, p_copy_54.as_mut_ptr());
    i0_10 = (i0_10 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
        as uint32_t;
    let mut p_copy_55: [uint64_t; 15] = [
        0 as libc::c_uint as uint64_t,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
    ];
    memcpy(
        p_copy_55.as_mut_ptr() as *mut libc::c_void,
        out as *const libc::c_void,
        (15 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    Hacl_Impl_K256_PointDouble_point_double(out, p_copy_55.as_mut_ptr());
    i0_10 = (i0_10 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
        as uint32_t;
    let mut p_copy_56: [uint64_t; 15] = [
        0 as libc::c_uint as uint64_t,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
    ];
    memcpy(
        p_copy_56.as_mut_ptr() as *mut libc::c_void,
        out as *const libc::c_void,
        (15 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    Hacl_Impl_K256_PointDouble_point_double(out, p_copy_56.as_mut_ptr());
    i0_10 = (i0_10 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
        as uint32_t;
    let mut p_copy_57: [uint64_t; 15] = [
        0 as libc::c_uint as uint64_t,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
    ];
    memcpy(
        p_copy_57.as_mut_ptr() as *mut libc::c_void,
        out as *const libc::c_void,
        (15 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    Hacl_Impl_K256_PointDouble_point_double(out, p_copy_57.as_mut_ptr());
    i0_10 = (i0_10 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
        as uint32_t;
    let mut k_10: uint32_t = (64 as libc::c_uint)
        .wrapping_sub((4 as libc::c_uint).wrapping_mul(i))
        .wrapping_sub(4 as libc::c_uint);
    let mut bits_l_10: uint64_t = Hacl_Bignum_Lib_bn_get_bits_u64(
        1 as libc::c_uint,
        r4,
        k_10,
        4 as libc::c_uint,
    );
    precomp_get_consttime(
        Hacl_K256_PrecompTable_precomp_g_pow2_192_table_w4.as_ptr(),
        bits_l_10,
        tmp.as_mut_ptr(),
    );
    let mut p_copy_58: [uint64_t; 15] = [
        0 as libc::c_uint as uint64_t,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
    ];
    memcpy(
        p_copy_58.as_mut_ptr() as *mut libc::c_void,
        out as *const libc::c_void,
        (15 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    Hacl_Impl_K256_PointAdd_point_add(out, p_copy_58.as_mut_ptr(), tmp.as_mut_ptr());
    let mut k0_10: uint32_t = (64 as libc::c_uint)
        .wrapping_sub((4 as libc::c_uint).wrapping_mul(i))
        .wrapping_sub(4 as libc::c_uint);
    let mut bits_l0_10: uint64_t = Hacl_Bignum_Lib_bn_get_bits_u64(
        1 as libc::c_uint,
        r3,
        k0_10,
        4 as libc::c_uint,
    );
    precomp_get_consttime(
        Hacl_K256_PrecompTable_precomp_g_pow2_128_table_w4.as_ptr(),
        bits_l0_10,
        tmp.as_mut_ptr(),
    );
    let mut p_copy0_10: [uint64_t; 15] = [
        0 as libc::c_uint as uint64_t,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
    ];
    memcpy(
        p_copy0_10.as_mut_ptr() as *mut libc::c_void,
        out as *const libc::c_void,
        (15 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    Hacl_Impl_K256_PointAdd_point_add(out, p_copy0_10.as_mut_ptr(), tmp.as_mut_ptr());
    let mut k1_10: uint32_t = (64 as libc::c_uint)
        .wrapping_sub((4 as libc::c_uint).wrapping_mul(i))
        .wrapping_sub(4 as libc::c_uint);
    let mut bits_l1_10: uint64_t = Hacl_Bignum_Lib_bn_get_bits_u64(
        1 as libc::c_uint,
        r2,
        k1_10,
        4 as libc::c_uint,
    );
    precomp_get_consttime(
        Hacl_K256_PrecompTable_precomp_g_pow2_64_table_w4.as_ptr(),
        bits_l1_10,
        tmp.as_mut_ptr(),
    );
    let mut p_copy1_10: [uint64_t; 15] = [
        0 as libc::c_uint as uint64_t,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
    ];
    memcpy(
        p_copy1_10.as_mut_ptr() as *mut libc::c_void,
        out as *const libc::c_void,
        (15 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    Hacl_Impl_K256_PointAdd_point_add(out, p_copy1_10.as_mut_ptr(), tmp.as_mut_ptr());
    let mut k2_10: uint32_t = (64 as libc::c_uint)
        .wrapping_sub((4 as libc::c_uint).wrapping_mul(i))
        .wrapping_sub(4 as libc::c_uint);
    let mut bits_l2_10: uint64_t = Hacl_Bignum_Lib_bn_get_bits_u64(
        1 as libc::c_uint,
        r1,
        k2_10,
        4 as libc::c_uint,
    );
    precomp_get_consttime(
        Hacl_K256_PrecompTable_precomp_basepoint_table_w4.as_ptr(),
        bits_l2_10,
        tmp.as_mut_ptr(),
    );
    let mut p_copy2_10: [uint64_t; 15] = [
        0 as libc::c_uint as uint64_t,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
    ];
    memcpy(
        p_copy2_10.as_mut_ptr() as *mut libc::c_void,
        out as *const libc::c_void,
        (15 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    Hacl_Impl_K256_PointAdd_point_add(out, p_copy2_10.as_mut_ptr(), tmp.as_mut_ptr());
    i = (i as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut i0_11: uint32_t = 0 as libc::c_uint;
    let mut p_copy_59: [uint64_t; 15] = [
        0 as libc::c_uint as uint64_t,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
    ];
    memcpy(
        p_copy_59.as_mut_ptr() as *mut libc::c_void,
        out as *const libc::c_void,
        (15 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    Hacl_Impl_K256_PointDouble_point_double(out, p_copy_59.as_mut_ptr());
    i0_11 = (i0_11 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
        as uint32_t;
    let mut p_copy_60: [uint64_t; 15] = [
        0 as libc::c_uint as uint64_t,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
    ];
    memcpy(
        p_copy_60.as_mut_ptr() as *mut libc::c_void,
        out as *const libc::c_void,
        (15 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    Hacl_Impl_K256_PointDouble_point_double(out, p_copy_60.as_mut_ptr());
    i0_11 = (i0_11 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
        as uint32_t;
    let mut p_copy_61: [uint64_t; 15] = [
        0 as libc::c_uint as uint64_t,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
    ];
    memcpy(
        p_copy_61.as_mut_ptr() as *mut libc::c_void,
        out as *const libc::c_void,
        (15 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    Hacl_Impl_K256_PointDouble_point_double(out, p_copy_61.as_mut_ptr());
    i0_11 = (i0_11 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
        as uint32_t;
    let mut p_copy_62: [uint64_t; 15] = [
        0 as libc::c_uint as uint64_t,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
    ];
    memcpy(
        p_copy_62.as_mut_ptr() as *mut libc::c_void,
        out as *const libc::c_void,
        (15 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    Hacl_Impl_K256_PointDouble_point_double(out, p_copy_62.as_mut_ptr());
    i0_11 = (i0_11 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
        as uint32_t;
    let mut k_11: uint32_t = (64 as libc::c_uint)
        .wrapping_sub((4 as libc::c_uint).wrapping_mul(i))
        .wrapping_sub(4 as libc::c_uint);
    let mut bits_l_11: uint64_t = Hacl_Bignum_Lib_bn_get_bits_u64(
        1 as libc::c_uint,
        r4,
        k_11,
        4 as libc::c_uint,
    );
    precomp_get_consttime(
        Hacl_K256_PrecompTable_precomp_g_pow2_192_table_w4.as_ptr(),
        bits_l_11,
        tmp.as_mut_ptr(),
    );
    let mut p_copy_63: [uint64_t; 15] = [
        0 as libc::c_uint as uint64_t,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
    ];
    memcpy(
        p_copy_63.as_mut_ptr() as *mut libc::c_void,
        out as *const libc::c_void,
        (15 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    Hacl_Impl_K256_PointAdd_point_add(out, p_copy_63.as_mut_ptr(), tmp.as_mut_ptr());
    let mut k0_11: uint32_t = (64 as libc::c_uint)
        .wrapping_sub((4 as libc::c_uint).wrapping_mul(i))
        .wrapping_sub(4 as libc::c_uint);
    let mut bits_l0_11: uint64_t = Hacl_Bignum_Lib_bn_get_bits_u64(
        1 as libc::c_uint,
        r3,
        k0_11,
        4 as libc::c_uint,
    );
    precomp_get_consttime(
        Hacl_K256_PrecompTable_precomp_g_pow2_128_table_w4.as_ptr(),
        bits_l0_11,
        tmp.as_mut_ptr(),
    );
    let mut p_copy0_11: [uint64_t; 15] = [
        0 as libc::c_uint as uint64_t,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
    ];
    memcpy(
        p_copy0_11.as_mut_ptr() as *mut libc::c_void,
        out as *const libc::c_void,
        (15 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    Hacl_Impl_K256_PointAdd_point_add(out, p_copy0_11.as_mut_ptr(), tmp.as_mut_ptr());
    let mut k1_11: uint32_t = (64 as libc::c_uint)
        .wrapping_sub((4 as libc::c_uint).wrapping_mul(i))
        .wrapping_sub(4 as libc::c_uint);
    let mut bits_l1_11: uint64_t = Hacl_Bignum_Lib_bn_get_bits_u64(
        1 as libc::c_uint,
        r2,
        k1_11,
        4 as libc::c_uint,
    );
    precomp_get_consttime(
        Hacl_K256_PrecompTable_precomp_g_pow2_64_table_w4.as_ptr(),
        bits_l1_11,
        tmp.as_mut_ptr(),
    );
    let mut p_copy1_11: [uint64_t; 15] = [
        0 as libc::c_uint as uint64_t,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
    ];
    memcpy(
        p_copy1_11.as_mut_ptr() as *mut libc::c_void,
        out as *const libc::c_void,
        (15 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    Hacl_Impl_K256_PointAdd_point_add(out, p_copy1_11.as_mut_ptr(), tmp.as_mut_ptr());
    let mut k2_11: uint32_t = (64 as libc::c_uint)
        .wrapping_sub((4 as libc::c_uint).wrapping_mul(i))
        .wrapping_sub(4 as libc::c_uint);
    let mut bits_l2_11: uint64_t = Hacl_Bignum_Lib_bn_get_bits_u64(
        1 as libc::c_uint,
        r1,
        k2_11,
        4 as libc::c_uint,
    );
    precomp_get_consttime(
        Hacl_K256_PrecompTable_precomp_basepoint_table_w4.as_ptr(),
        bits_l2_11,
        tmp.as_mut_ptr(),
    );
    let mut p_copy2_11: [uint64_t; 15] = [
        0 as libc::c_uint as uint64_t,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
    ];
    memcpy(
        p_copy2_11.as_mut_ptr() as *mut libc::c_void,
        out as *const libc::c_void,
        (15 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    Hacl_Impl_K256_PointAdd_point_add(out, p_copy2_11.as_mut_ptr(), tmp.as_mut_ptr());
    i = (i as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut i0_12: uint32_t = 0 as libc::c_uint;
    let mut p_copy_64: [uint64_t; 15] = [
        0 as libc::c_uint as uint64_t,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
    ];
    memcpy(
        p_copy_64.as_mut_ptr() as *mut libc::c_void,
        out as *const libc::c_void,
        (15 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    Hacl_Impl_K256_PointDouble_point_double(out, p_copy_64.as_mut_ptr());
    i0_12 = (i0_12 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
        as uint32_t;
    let mut p_copy_65: [uint64_t; 15] = [
        0 as libc::c_uint as uint64_t,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
    ];
    memcpy(
        p_copy_65.as_mut_ptr() as *mut libc::c_void,
        out as *const libc::c_void,
        (15 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    Hacl_Impl_K256_PointDouble_point_double(out, p_copy_65.as_mut_ptr());
    i0_12 = (i0_12 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
        as uint32_t;
    let mut p_copy_66: [uint64_t; 15] = [
        0 as libc::c_uint as uint64_t,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
    ];
    memcpy(
        p_copy_66.as_mut_ptr() as *mut libc::c_void,
        out as *const libc::c_void,
        (15 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    Hacl_Impl_K256_PointDouble_point_double(out, p_copy_66.as_mut_ptr());
    i0_12 = (i0_12 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
        as uint32_t;
    let mut p_copy_67: [uint64_t; 15] = [
        0 as libc::c_uint as uint64_t,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
    ];
    memcpy(
        p_copy_67.as_mut_ptr() as *mut libc::c_void,
        out as *const libc::c_void,
        (15 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    Hacl_Impl_K256_PointDouble_point_double(out, p_copy_67.as_mut_ptr());
    i0_12 = (i0_12 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
        as uint32_t;
    let mut k_12: uint32_t = (64 as libc::c_uint)
        .wrapping_sub((4 as libc::c_uint).wrapping_mul(i))
        .wrapping_sub(4 as libc::c_uint);
    let mut bits_l_12: uint64_t = Hacl_Bignum_Lib_bn_get_bits_u64(
        1 as libc::c_uint,
        r4,
        k_12,
        4 as libc::c_uint,
    );
    precomp_get_consttime(
        Hacl_K256_PrecompTable_precomp_g_pow2_192_table_w4.as_ptr(),
        bits_l_12,
        tmp.as_mut_ptr(),
    );
    let mut p_copy_68: [uint64_t; 15] = [
        0 as libc::c_uint as uint64_t,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
    ];
    memcpy(
        p_copy_68.as_mut_ptr() as *mut libc::c_void,
        out as *const libc::c_void,
        (15 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    Hacl_Impl_K256_PointAdd_point_add(out, p_copy_68.as_mut_ptr(), tmp.as_mut_ptr());
    let mut k0_12: uint32_t = (64 as libc::c_uint)
        .wrapping_sub((4 as libc::c_uint).wrapping_mul(i))
        .wrapping_sub(4 as libc::c_uint);
    let mut bits_l0_12: uint64_t = Hacl_Bignum_Lib_bn_get_bits_u64(
        1 as libc::c_uint,
        r3,
        k0_12,
        4 as libc::c_uint,
    );
    precomp_get_consttime(
        Hacl_K256_PrecompTable_precomp_g_pow2_128_table_w4.as_ptr(),
        bits_l0_12,
        tmp.as_mut_ptr(),
    );
    let mut p_copy0_12: [uint64_t; 15] = [
        0 as libc::c_uint as uint64_t,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
    ];
    memcpy(
        p_copy0_12.as_mut_ptr() as *mut libc::c_void,
        out as *const libc::c_void,
        (15 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    Hacl_Impl_K256_PointAdd_point_add(out, p_copy0_12.as_mut_ptr(), tmp.as_mut_ptr());
    let mut k1_12: uint32_t = (64 as libc::c_uint)
        .wrapping_sub((4 as libc::c_uint).wrapping_mul(i))
        .wrapping_sub(4 as libc::c_uint);
    let mut bits_l1_12: uint64_t = Hacl_Bignum_Lib_bn_get_bits_u64(
        1 as libc::c_uint,
        r2,
        k1_12,
        4 as libc::c_uint,
    );
    precomp_get_consttime(
        Hacl_K256_PrecompTable_precomp_g_pow2_64_table_w4.as_ptr(),
        bits_l1_12,
        tmp.as_mut_ptr(),
    );
    let mut p_copy1_12: [uint64_t; 15] = [
        0 as libc::c_uint as uint64_t,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
    ];
    memcpy(
        p_copy1_12.as_mut_ptr() as *mut libc::c_void,
        out as *const libc::c_void,
        (15 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    Hacl_Impl_K256_PointAdd_point_add(out, p_copy1_12.as_mut_ptr(), tmp.as_mut_ptr());
    let mut k2_12: uint32_t = (64 as libc::c_uint)
        .wrapping_sub((4 as libc::c_uint).wrapping_mul(i))
        .wrapping_sub(4 as libc::c_uint);
    let mut bits_l2_12: uint64_t = Hacl_Bignum_Lib_bn_get_bits_u64(
        1 as libc::c_uint,
        r1,
        k2_12,
        4 as libc::c_uint,
    );
    precomp_get_consttime(
        Hacl_K256_PrecompTable_precomp_basepoint_table_w4.as_ptr(),
        bits_l2_12,
        tmp.as_mut_ptr(),
    );
    let mut p_copy2_12: [uint64_t; 15] = [
        0 as libc::c_uint as uint64_t,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
    ];
    memcpy(
        p_copy2_12.as_mut_ptr() as *mut libc::c_void,
        out as *const libc::c_void,
        (15 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    Hacl_Impl_K256_PointAdd_point_add(out, p_copy2_12.as_mut_ptr(), tmp.as_mut_ptr());
    i = (i as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut i0_13: uint32_t = 0 as libc::c_uint;
    let mut p_copy_69: [uint64_t; 15] = [
        0 as libc::c_uint as uint64_t,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
    ];
    memcpy(
        p_copy_69.as_mut_ptr() as *mut libc::c_void,
        out as *const libc::c_void,
        (15 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    Hacl_Impl_K256_PointDouble_point_double(out, p_copy_69.as_mut_ptr());
    i0_13 = (i0_13 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
        as uint32_t;
    let mut p_copy_70: [uint64_t; 15] = [
        0 as libc::c_uint as uint64_t,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
    ];
    memcpy(
        p_copy_70.as_mut_ptr() as *mut libc::c_void,
        out as *const libc::c_void,
        (15 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    Hacl_Impl_K256_PointDouble_point_double(out, p_copy_70.as_mut_ptr());
    i0_13 = (i0_13 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
        as uint32_t;
    let mut p_copy_71: [uint64_t; 15] = [
        0 as libc::c_uint as uint64_t,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
    ];
    memcpy(
        p_copy_71.as_mut_ptr() as *mut libc::c_void,
        out as *const libc::c_void,
        (15 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    Hacl_Impl_K256_PointDouble_point_double(out, p_copy_71.as_mut_ptr());
    i0_13 = (i0_13 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
        as uint32_t;
    let mut p_copy_72: [uint64_t; 15] = [
        0 as libc::c_uint as uint64_t,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
    ];
    memcpy(
        p_copy_72.as_mut_ptr() as *mut libc::c_void,
        out as *const libc::c_void,
        (15 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    Hacl_Impl_K256_PointDouble_point_double(out, p_copy_72.as_mut_ptr());
    i0_13 = (i0_13 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
        as uint32_t;
    let mut k_13: uint32_t = (64 as libc::c_uint)
        .wrapping_sub((4 as libc::c_uint).wrapping_mul(i))
        .wrapping_sub(4 as libc::c_uint);
    let mut bits_l_13: uint64_t = Hacl_Bignum_Lib_bn_get_bits_u64(
        1 as libc::c_uint,
        r4,
        k_13,
        4 as libc::c_uint,
    );
    precomp_get_consttime(
        Hacl_K256_PrecompTable_precomp_g_pow2_192_table_w4.as_ptr(),
        bits_l_13,
        tmp.as_mut_ptr(),
    );
    let mut p_copy_73: [uint64_t; 15] = [
        0 as libc::c_uint as uint64_t,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
    ];
    memcpy(
        p_copy_73.as_mut_ptr() as *mut libc::c_void,
        out as *const libc::c_void,
        (15 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    Hacl_Impl_K256_PointAdd_point_add(out, p_copy_73.as_mut_ptr(), tmp.as_mut_ptr());
    let mut k0_13: uint32_t = (64 as libc::c_uint)
        .wrapping_sub((4 as libc::c_uint).wrapping_mul(i))
        .wrapping_sub(4 as libc::c_uint);
    let mut bits_l0_13: uint64_t = Hacl_Bignum_Lib_bn_get_bits_u64(
        1 as libc::c_uint,
        r3,
        k0_13,
        4 as libc::c_uint,
    );
    precomp_get_consttime(
        Hacl_K256_PrecompTable_precomp_g_pow2_128_table_w4.as_ptr(),
        bits_l0_13,
        tmp.as_mut_ptr(),
    );
    let mut p_copy0_13: [uint64_t; 15] = [
        0 as libc::c_uint as uint64_t,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
    ];
    memcpy(
        p_copy0_13.as_mut_ptr() as *mut libc::c_void,
        out as *const libc::c_void,
        (15 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    Hacl_Impl_K256_PointAdd_point_add(out, p_copy0_13.as_mut_ptr(), tmp.as_mut_ptr());
    let mut k1_13: uint32_t = (64 as libc::c_uint)
        .wrapping_sub((4 as libc::c_uint).wrapping_mul(i))
        .wrapping_sub(4 as libc::c_uint);
    let mut bits_l1_13: uint64_t = Hacl_Bignum_Lib_bn_get_bits_u64(
        1 as libc::c_uint,
        r2,
        k1_13,
        4 as libc::c_uint,
    );
    precomp_get_consttime(
        Hacl_K256_PrecompTable_precomp_g_pow2_64_table_w4.as_ptr(),
        bits_l1_13,
        tmp.as_mut_ptr(),
    );
    let mut p_copy1_13: [uint64_t; 15] = [
        0 as libc::c_uint as uint64_t,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
    ];
    memcpy(
        p_copy1_13.as_mut_ptr() as *mut libc::c_void,
        out as *const libc::c_void,
        (15 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    Hacl_Impl_K256_PointAdd_point_add(out, p_copy1_13.as_mut_ptr(), tmp.as_mut_ptr());
    let mut k2_13: uint32_t = (64 as libc::c_uint)
        .wrapping_sub((4 as libc::c_uint).wrapping_mul(i))
        .wrapping_sub(4 as libc::c_uint);
    let mut bits_l2_13: uint64_t = Hacl_Bignum_Lib_bn_get_bits_u64(
        1 as libc::c_uint,
        r1,
        k2_13,
        4 as libc::c_uint,
    );
    precomp_get_consttime(
        Hacl_K256_PrecompTable_precomp_basepoint_table_w4.as_ptr(),
        bits_l2_13,
        tmp.as_mut_ptr(),
    );
    let mut p_copy2_13: [uint64_t; 15] = [
        0 as libc::c_uint as uint64_t,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
    ];
    memcpy(
        p_copy2_13.as_mut_ptr() as *mut libc::c_void,
        out as *const libc::c_void,
        (15 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    Hacl_Impl_K256_PointAdd_point_add(out, p_copy2_13.as_mut_ptr(), tmp.as_mut_ptr());
    i = (i as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut i0_14: uint32_t = 0 as libc::c_uint;
    let mut p_copy_74: [uint64_t; 15] = [
        0 as libc::c_uint as uint64_t,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
    ];
    memcpy(
        p_copy_74.as_mut_ptr() as *mut libc::c_void,
        out as *const libc::c_void,
        (15 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    Hacl_Impl_K256_PointDouble_point_double(out, p_copy_74.as_mut_ptr());
    i0_14 = (i0_14 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
        as uint32_t;
    let mut p_copy_75: [uint64_t; 15] = [
        0 as libc::c_uint as uint64_t,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
    ];
    memcpy(
        p_copy_75.as_mut_ptr() as *mut libc::c_void,
        out as *const libc::c_void,
        (15 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    Hacl_Impl_K256_PointDouble_point_double(out, p_copy_75.as_mut_ptr());
    i0_14 = (i0_14 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
        as uint32_t;
    let mut p_copy_76: [uint64_t; 15] = [
        0 as libc::c_uint as uint64_t,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
    ];
    memcpy(
        p_copy_76.as_mut_ptr() as *mut libc::c_void,
        out as *const libc::c_void,
        (15 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    Hacl_Impl_K256_PointDouble_point_double(out, p_copy_76.as_mut_ptr());
    i0_14 = (i0_14 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
        as uint32_t;
    let mut p_copy_77: [uint64_t; 15] = [
        0 as libc::c_uint as uint64_t,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
    ];
    memcpy(
        p_copy_77.as_mut_ptr() as *mut libc::c_void,
        out as *const libc::c_void,
        (15 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    Hacl_Impl_K256_PointDouble_point_double(out, p_copy_77.as_mut_ptr());
    i0_14 = (i0_14 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
        as uint32_t;
    let mut k_14: uint32_t = (64 as libc::c_uint)
        .wrapping_sub((4 as libc::c_uint).wrapping_mul(i))
        .wrapping_sub(4 as libc::c_uint);
    let mut bits_l_14: uint64_t = Hacl_Bignum_Lib_bn_get_bits_u64(
        1 as libc::c_uint,
        r4,
        k_14,
        4 as libc::c_uint,
    );
    precomp_get_consttime(
        Hacl_K256_PrecompTable_precomp_g_pow2_192_table_w4.as_ptr(),
        bits_l_14,
        tmp.as_mut_ptr(),
    );
    let mut p_copy_78: [uint64_t; 15] = [
        0 as libc::c_uint as uint64_t,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
    ];
    memcpy(
        p_copy_78.as_mut_ptr() as *mut libc::c_void,
        out as *const libc::c_void,
        (15 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    Hacl_Impl_K256_PointAdd_point_add(out, p_copy_78.as_mut_ptr(), tmp.as_mut_ptr());
    let mut k0_14: uint32_t = (64 as libc::c_uint)
        .wrapping_sub((4 as libc::c_uint).wrapping_mul(i))
        .wrapping_sub(4 as libc::c_uint);
    let mut bits_l0_14: uint64_t = Hacl_Bignum_Lib_bn_get_bits_u64(
        1 as libc::c_uint,
        r3,
        k0_14,
        4 as libc::c_uint,
    );
    precomp_get_consttime(
        Hacl_K256_PrecompTable_precomp_g_pow2_128_table_w4.as_ptr(),
        bits_l0_14,
        tmp.as_mut_ptr(),
    );
    let mut p_copy0_14: [uint64_t; 15] = [
        0 as libc::c_uint as uint64_t,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
    ];
    memcpy(
        p_copy0_14.as_mut_ptr() as *mut libc::c_void,
        out as *const libc::c_void,
        (15 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    Hacl_Impl_K256_PointAdd_point_add(out, p_copy0_14.as_mut_ptr(), tmp.as_mut_ptr());
    let mut k1_14: uint32_t = (64 as libc::c_uint)
        .wrapping_sub((4 as libc::c_uint).wrapping_mul(i))
        .wrapping_sub(4 as libc::c_uint);
    let mut bits_l1_14: uint64_t = Hacl_Bignum_Lib_bn_get_bits_u64(
        1 as libc::c_uint,
        r2,
        k1_14,
        4 as libc::c_uint,
    );
    precomp_get_consttime(
        Hacl_K256_PrecompTable_precomp_g_pow2_64_table_w4.as_ptr(),
        bits_l1_14,
        tmp.as_mut_ptr(),
    );
    let mut p_copy1_14: [uint64_t; 15] = [
        0 as libc::c_uint as uint64_t,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
    ];
    memcpy(
        p_copy1_14.as_mut_ptr() as *mut libc::c_void,
        out as *const libc::c_void,
        (15 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    Hacl_Impl_K256_PointAdd_point_add(out, p_copy1_14.as_mut_ptr(), tmp.as_mut_ptr());
    let mut k2_14: uint32_t = (64 as libc::c_uint)
        .wrapping_sub((4 as libc::c_uint).wrapping_mul(i))
        .wrapping_sub(4 as libc::c_uint);
    let mut bits_l2_14: uint64_t = Hacl_Bignum_Lib_bn_get_bits_u64(
        1 as libc::c_uint,
        r1,
        k2_14,
        4 as libc::c_uint,
    );
    precomp_get_consttime(
        Hacl_K256_PrecompTable_precomp_basepoint_table_w4.as_ptr(),
        bits_l2_14,
        tmp.as_mut_ptr(),
    );
    let mut p_copy2_14: [uint64_t; 15] = [
        0 as libc::c_uint as uint64_t,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
    ];
    memcpy(
        p_copy2_14.as_mut_ptr() as *mut libc::c_void,
        out as *const libc::c_void,
        (15 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    Hacl_Impl_K256_PointAdd_point_add(out, p_copy2_14.as_mut_ptr(), tmp.as_mut_ptr());
    i = (i as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
}
#[inline]
unsafe extern "C" fn point_mul_g_double_vartime(
    mut out: *mut uint64_t,
    mut scalar1: *mut uint64_t,
    mut scalar2: *mut uint64_t,
    mut q2: *mut uint64_t,
) {
    let mut q1: [uint64_t; 15] = [
        0 as libc::c_uint as uint64_t,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
    ];
    let mut gx: *mut uint64_t = q1.as_mut_ptr();
    let mut gy: *mut uint64_t = q1.as_mut_ptr().offset(5 as libc::c_uint as isize);
    let mut gz: *mut uint64_t = q1.as_mut_ptr().offset(10 as libc::c_uint as isize);
    *gx.offset(0 as libc::c_uint as isize) = 0x2815b16f81798 as libc::c_ulonglong;
    *gx.offset(1 as libc::c_uint as isize) = 0xdb2dce28d959f as libc::c_ulonglong;
    *gx.offset(2 as libc::c_uint as isize) = 0xe870b07029bfc as libc::c_ulonglong;
    *gx.offset(3 as libc::c_uint as isize) = 0xbbac55a06295c as libc::c_ulonglong;
    *gx.offset(4 as libc::c_uint as isize) = 0x79be667ef9dc as libc::c_ulonglong;
    *gy.offset(0 as libc::c_uint as isize) = 0x7d08ffb10d4b8 as libc::c_ulonglong;
    *gy.offset(1 as libc::c_uint as isize) = 0x48a68554199c4 as libc::c_ulonglong;
    *gy.offset(2 as libc::c_uint as isize) = 0xe1108a8fd17b4 as libc::c_ulonglong;
    *gy.offset(3 as libc::c_uint as isize) = 0xc4655da4fbfc0 as libc::c_ulonglong;
    *gy.offset(4 as libc::c_uint as isize) = 0x483ada7726a3 as libc::c_ulonglong;
    memset(
        gz as *mut libc::c_void,
        0 as libc::c_uint as libc::c_int,
        (5 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    *gz.offset(0 as libc::c_uint as isize) = 1 as libc::c_ulonglong;
    let mut table2: [uint64_t; 480] = [
        0 as libc::c_uint as uint64_t,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
    ];
    let mut tmp: [uint64_t; 15] = [
        0 as libc::c_uint as uint64_t,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
    ];
    let mut t0: *mut uint64_t = table2.as_mut_ptr();
    let mut t1: *mut uint64_t = table2.as_mut_ptr().offset(15 as libc::c_uint as isize);
    Hacl_Impl_K256_Point_make_point_at_inf(t0);
    memcpy(
        t1 as *mut libc::c_void,
        q2 as *const libc::c_void,
        (15 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    let mut i: uint32_t = 0 as libc::c_uint;
    let mut t11: *mut uint64_t = table2
        .as_mut_ptr()
        .offset(
            i.wrapping_add(1 as libc::c_uint).wrapping_mul(15 as libc::c_uint) as isize,
        );
    let mut p_copy0: [uint64_t; 15] = [
        0 as libc::c_uint as uint64_t,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
    ];
    memcpy(
        p_copy0.as_mut_ptr() as *mut libc::c_void,
        t11 as *const libc::c_void,
        (15 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    Hacl_Impl_K256_PointDouble_point_double(tmp.as_mut_ptr(), p_copy0.as_mut_ptr());
    memcpy(
        table2
            .as_mut_ptr()
            .offset(
                (2 as libc::c_uint)
                    .wrapping_mul(i)
                    .wrapping_add(2 as libc::c_uint)
                    .wrapping_mul(15 as libc::c_uint) as isize,
            ) as *mut libc::c_void,
        tmp.as_mut_ptr() as *const libc::c_void,
        (15 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    let mut t2: *mut uint64_t = table2
        .as_mut_ptr()
        .offset(
            (2 as libc::c_uint)
                .wrapping_mul(i)
                .wrapping_add(2 as libc::c_uint)
                .wrapping_mul(15 as libc::c_uint) as isize,
        );
    let mut p_copy: [uint64_t; 15] = [
        0 as libc::c_uint as uint64_t,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
    ];
    memcpy(
        p_copy.as_mut_ptr() as *mut libc::c_void,
        q2 as *const libc::c_void,
        (15 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    Hacl_Impl_K256_PointAdd_point_add(tmp.as_mut_ptr(), p_copy.as_mut_ptr(), t2);
    memcpy(
        table2
            .as_mut_ptr()
            .offset(
                (2 as libc::c_uint)
                    .wrapping_mul(i)
                    .wrapping_add(3 as libc::c_uint)
                    .wrapping_mul(15 as libc::c_uint) as isize,
            ) as *mut libc::c_void,
        tmp.as_mut_ptr() as *const libc::c_void,
        (15 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    i = (i as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut t11_0: *mut uint64_t = table2
        .as_mut_ptr()
        .offset(
            i.wrapping_add(1 as libc::c_uint).wrapping_mul(15 as libc::c_uint) as isize,
        );
    let mut p_copy0_0: [uint64_t; 15] = [
        0 as libc::c_uint as uint64_t,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
    ];
    memcpy(
        p_copy0_0.as_mut_ptr() as *mut libc::c_void,
        t11_0 as *const libc::c_void,
        (15 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    Hacl_Impl_K256_PointDouble_point_double(tmp.as_mut_ptr(), p_copy0_0.as_mut_ptr());
    memcpy(
        table2
            .as_mut_ptr()
            .offset(
                (2 as libc::c_uint)
                    .wrapping_mul(i)
                    .wrapping_add(2 as libc::c_uint)
                    .wrapping_mul(15 as libc::c_uint) as isize,
            ) as *mut libc::c_void,
        tmp.as_mut_ptr() as *const libc::c_void,
        (15 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    let mut t2_0: *mut uint64_t = table2
        .as_mut_ptr()
        .offset(
            (2 as libc::c_uint)
                .wrapping_mul(i)
                .wrapping_add(2 as libc::c_uint)
                .wrapping_mul(15 as libc::c_uint) as isize,
        );
    let mut p_copy_0: [uint64_t; 15] = [
        0 as libc::c_uint as uint64_t,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
    ];
    memcpy(
        p_copy_0.as_mut_ptr() as *mut libc::c_void,
        q2 as *const libc::c_void,
        (15 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    Hacl_Impl_K256_PointAdd_point_add(tmp.as_mut_ptr(), p_copy_0.as_mut_ptr(), t2_0);
    memcpy(
        table2
            .as_mut_ptr()
            .offset(
                (2 as libc::c_uint)
                    .wrapping_mul(i)
                    .wrapping_add(3 as libc::c_uint)
                    .wrapping_mul(15 as libc::c_uint) as isize,
            ) as *mut libc::c_void,
        tmp.as_mut_ptr() as *const libc::c_void,
        (15 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    i = (i as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut t11_1: *mut uint64_t = table2
        .as_mut_ptr()
        .offset(
            i.wrapping_add(1 as libc::c_uint).wrapping_mul(15 as libc::c_uint) as isize,
        );
    let mut p_copy0_1: [uint64_t; 15] = [
        0 as libc::c_uint as uint64_t,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
    ];
    memcpy(
        p_copy0_1.as_mut_ptr() as *mut libc::c_void,
        t11_1 as *const libc::c_void,
        (15 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    Hacl_Impl_K256_PointDouble_point_double(tmp.as_mut_ptr(), p_copy0_1.as_mut_ptr());
    memcpy(
        table2
            .as_mut_ptr()
            .offset(
                (2 as libc::c_uint)
                    .wrapping_mul(i)
                    .wrapping_add(2 as libc::c_uint)
                    .wrapping_mul(15 as libc::c_uint) as isize,
            ) as *mut libc::c_void,
        tmp.as_mut_ptr() as *const libc::c_void,
        (15 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    let mut t2_1: *mut uint64_t = table2
        .as_mut_ptr()
        .offset(
            (2 as libc::c_uint)
                .wrapping_mul(i)
                .wrapping_add(2 as libc::c_uint)
                .wrapping_mul(15 as libc::c_uint) as isize,
        );
    let mut p_copy_1: [uint64_t; 15] = [
        0 as libc::c_uint as uint64_t,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
    ];
    memcpy(
        p_copy_1.as_mut_ptr() as *mut libc::c_void,
        q2 as *const libc::c_void,
        (15 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    Hacl_Impl_K256_PointAdd_point_add(tmp.as_mut_ptr(), p_copy_1.as_mut_ptr(), t2_1);
    memcpy(
        table2
            .as_mut_ptr()
            .offset(
                (2 as libc::c_uint)
                    .wrapping_mul(i)
                    .wrapping_add(3 as libc::c_uint)
                    .wrapping_mul(15 as libc::c_uint) as isize,
            ) as *mut libc::c_void,
        tmp.as_mut_ptr() as *const libc::c_void,
        (15 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    i = (i as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut t11_2: *mut uint64_t = table2
        .as_mut_ptr()
        .offset(
            i.wrapping_add(1 as libc::c_uint).wrapping_mul(15 as libc::c_uint) as isize,
        );
    let mut p_copy0_2: [uint64_t; 15] = [
        0 as libc::c_uint as uint64_t,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
    ];
    memcpy(
        p_copy0_2.as_mut_ptr() as *mut libc::c_void,
        t11_2 as *const libc::c_void,
        (15 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    Hacl_Impl_K256_PointDouble_point_double(tmp.as_mut_ptr(), p_copy0_2.as_mut_ptr());
    memcpy(
        table2
            .as_mut_ptr()
            .offset(
                (2 as libc::c_uint)
                    .wrapping_mul(i)
                    .wrapping_add(2 as libc::c_uint)
                    .wrapping_mul(15 as libc::c_uint) as isize,
            ) as *mut libc::c_void,
        tmp.as_mut_ptr() as *const libc::c_void,
        (15 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    let mut t2_2: *mut uint64_t = table2
        .as_mut_ptr()
        .offset(
            (2 as libc::c_uint)
                .wrapping_mul(i)
                .wrapping_add(2 as libc::c_uint)
                .wrapping_mul(15 as libc::c_uint) as isize,
        );
    let mut p_copy_2: [uint64_t; 15] = [
        0 as libc::c_uint as uint64_t,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
    ];
    memcpy(
        p_copy_2.as_mut_ptr() as *mut libc::c_void,
        q2 as *const libc::c_void,
        (15 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    Hacl_Impl_K256_PointAdd_point_add(tmp.as_mut_ptr(), p_copy_2.as_mut_ptr(), t2_2);
    memcpy(
        table2
            .as_mut_ptr()
            .offset(
                (2 as libc::c_uint)
                    .wrapping_mul(i)
                    .wrapping_add(3 as libc::c_uint)
                    .wrapping_mul(15 as libc::c_uint) as isize,
            ) as *mut libc::c_void,
        tmp.as_mut_ptr() as *const libc::c_void,
        (15 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    i = (i as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut t11_3: *mut uint64_t = table2
        .as_mut_ptr()
        .offset(
            i.wrapping_add(1 as libc::c_uint).wrapping_mul(15 as libc::c_uint) as isize,
        );
    let mut p_copy0_3: [uint64_t; 15] = [
        0 as libc::c_uint as uint64_t,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
    ];
    memcpy(
        p_copy0_3.as_mut_ptr() as *mut libc::c_void,
        t11_3 as *const libc::c_void,
        (15 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    Hacl_Impl_K256_PointDouble_point_double(tmp.as_mut_ptr(), p_copy0_3.as_mut_ptr());
    memcpy(
        table2
            .as_mut_ptr()
            .offset(
                (2 as libc::c_uint)
                    .wrapping_mul(i)
                    .wrapping_add(2 as libc::c_uint)
                    .wrapping_mul(15 as libc::c_uint) as isize,
            ) as *mut libc::c_void,
        tmp.as_mut_ptr() as *const libc::c_void,
        (15 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    let mut t2_3: *mut uint64_t = table2
        .as_mut_ptr()
        .offset(
            (2 as libc::c_uint)
                .wrapping_mul(i)
                .wrapping_add(2 as libc::c_uint)
                .wrapping_mul(15 as libc::c_uint) as isize,
        );
    let mut p_copy_3: [uint64_t; 15] = [
        0 as libc::c_uint as uint64_t,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
    ];
    memcpy(
        p_copy_3.as_mut_ptr() as *mut libc::c_void,
        q2 as *const libc::c_void,
        (15 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    Hacl_Impl_K256_PointAdd_point_add(tmp.as_mut_ptr(), p_copy_3.as_mut_ptr(), t2_3);
    memcpy(
        table2
            .as_mut_ptr()
            .offset(
                (2 as libc::c_uint)
                    .wrapping_mul(i)
                    .wrapping_add(3 as libc::c_uint)
                    .wrapping_mul(15 as libc::c_uint) as isize,
            ) as *mut libc::c_void,
        tmp.as_mut_ptr() as *const libc::c_void,
        (15 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    i = (i as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut t11_4: *mut uint64_t = table2
        .as_mut_ptr()
        .offset(
            i.wrapping_add(1 as libc::c_uint).wrapping_mul(15 as libc::c_uint) as isize,
        );
    let mut p_copy0_4: [uint64_t; 15] = [
        0 as libc::c_uint as uint64_t,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
    ];
    memcpy(
        p_copy0_4.as_mut_ptr() as *mut libc::c_void,
        t11_4 as *const libc::c_void,
        (15 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    Hacl_Impl_K256_PointDouble_point_double(tmp.as_mut_ptr(), p_copy0_4.as_mut_ptr());
    memcpy(
        table2
            .as_mut_ptr()
            .offset(
                (2 as libc::c_uint)
                    .wrapping_mul(i)
                    .wrapping_add(2 as libc::c_uint)
                    .wrapping_mul(15 as libc::c_uint) as isize,
            ) as *mut libc::c_void,
        tmp.as_mut_ptr() as *const libc::c_void,
        (15 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    let mut t2_4: *mut uint64_t = table2
        .as_mut_ptr()
        .offset(
            (2 as libc::c_uint)
                .wrapping_mul(i)
                .wrapping_add(2 as libc::c_uint)
                .wrapping_mul(15 as libc::c_uint) as isize,
        );
    let mut p_copy_4: [uint64_t; 15] = [
        0 as libc::c_uint as uint64_t,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
    ];
    memcpy(
        p_copy_4.as_mut_ptr() as *mut libc::c_void,
        q2 as *const libc::c_void,
        (15 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    Hacl_Impl_K256_PointAdd_point_add(tmp.as_mut_ptr(), p_copy_4.as_mut_ptr(), t2_4);
    memcpy(
        table2
            .as_mut_ptr()
            .offset(
                (2 as libc::c_uint)
                    .wrapping_mul(i)
                    .wrapping_add(3 as libc::c_uint)
                    .wrapping_mul(15 as libc::c_uint) as isize,
            ) as *mut libc::c_void,
        tmp.as_mut_ptr() as *const libc::c_void,
        (15 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    i = (i as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut t11_5: *mut uint64_t = table2
        .as_mut_ptr()
        .offset(
            i.wrapping_add(1 as libc::c_uint).wrapping_mul(15 as libc::c_uint) as isize,
        );
    let mut p_copy0_5: [uint64_t; 15] = [
        0 as libc::c_uint as uint64_t,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
    ];
    memcpy(
        p_copy0_5.as_mut_ptr() as *mut libc::c_void,
        t11_5 as *const libc::c_void,
        (15 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    Hacl_Impl_K256_PointDouble_point_double(tmp.as_mut_ptr(), p_copy0_5.as_mut_ptr());
    memcpy(
        table2
            .as_mut_ptr()
            .offset(
                (2 as libc::c_uint)
                    .wrapping_mul(i)
                    .wrapping_add(2 as libc::c_uint)
                    .wrapping_mul(15 as libc::c_uint) as isize,
            ) as *mut libc::c_void,
        tmp.as_mut_ptr() as *const libc::c_void,
        (15 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    let mut t2_5: *mut uint64_t = table2
        .as_mut_ptr()
        .offset(
            (2 as libc::c_uint)
                .wrapping_mul(i)
                .wrapping_add(2 as libc::c_uint)
                .wrapping_mul(15 as libc::c_uint) as isize,
        );
    let mut p_copy_5: [uint64_t; 15] = [
        0 as libc::c_uint as uint64_t,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
    ];
    memcpy(
        p_copy_5.as_mut_ptr() as *mut libc::c_void,
        q2 as *const libc::c_void,
        (15 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    Hacl_Impl_K256_PointAdd_point_add(tmp.as_mut_ptr(), p_copy_5.as_mut_ptr(), t2_5);
    memcpy(
        table2
            .as_mut_ptr()
            .offset(
                (2 as libc::c_uint)
                    .wrapping_mul(i)
                    .wrapping_add(3 as libc::c_uint)
                    .wrapping_mul(15 as libc::c_uint) as isize,
            ) as *mut libc::c_void,
        tmp.as_mut_ptr() as *const libc::c_void,
        (15 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    i = (i as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut t11_6: *mut uint64_t = table2
        .as_mut_ptr()
        .offset(
            i.wrapping_add(1 as libc::c_uint).wrapping_mul(15 as libc::c_uint) as isize,
        );
    let mut p_copy0_6: [uint64_t; 15] = [
        0 as libc::c_uint as uint64_t,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
    ];
    memcpy(
        p_copy0_6.as_mut_ptr() as *mut libc::c_void,
        t11_6 as *const libc::c_void,
        (15 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    Hacl_Impl_K256_PointDouble_point_double(tmp.as_mut_ptr(), p_copy0_6.as_mut_ptr());
    memcpy(
        table2
            .as_mut_ptr()
            .offset(
                (2 as libc::c_uint)
                    .wrapping_mul(i)
                    .wrapping_add(2 as libc::c_uint)
                    .wrapping_mul(15 as libc::c_uint) as isize,
            ) as *mut libc::c_void,
        tmp.as_mut_ptr() as *const libc::c_void,
        (15 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    let mut t2_6: *mut uint64_t = table2
        .as_mut_ptr()
        .offset(
            (2 as libc::c_uint)
                .wrapping_mul(i)
                .wrapping_add(2 as libc::c_uint)
                .wrapping_mul(15 as libc::c_uint) as isize,
        );
    let mut p_copy_6: [uint64_t; 15] = [
        0 as libc::c_uint as uint64_t,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
    ];
    memcpy(
        p_copy_6.as_mut_ptr() as *mut libc::c_void,
        q2 as *const libc::c_void,
        (15 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    Hacl_Impl_K256_PointAdd_point_add(tmp.as_mut_ptr(), p_copy_6.as_mut_ptr(), t2_6);
    memcpy(
        table2
            .as_mut_ptr()
            .offset(
                (2 as libc::c_uint)
                    .wrapping_mul(i)
                    .wrapping_add(3 as libc::c_uint)
                    .wrapping_mul(15 as libc::c_uint) as isize,
            ) as *mut libc::c_void,
        tmp.as_mut_ptr() as *const libc::c_void,
        (15 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    i = (i as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut t11_7: *mut uint64_t = table2
        .as_mut_ptr()
        .offset(
            i.wrapping_add(1 as libc::c_uint).wrapping_mul(15 as libc::c_uint) as isize,
        );
    let mut p_copy0_7: [uint64_t; 15] = [
        0 as libc::c_uint as uint64_t,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
    ];
    memcpy(
        p_copy0_7.as_mut_ptr() as *mut libc::c_void,
        t11_7 as *const libc::c_void,
        (15 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    Hacl_Impl_K256_PointDouble_point_double(tmp.as_mut_ptr(), p_copy0_7.as_mut_ptr());
    memcpy(
        table2
            .as_mut_ptr()
            .offset(
                (2 as libc::c_uint)
                    .wrapping_mul(i)
                    .wrapping_add(2 as libc::c_uint)
                    .wrapping_mul(15 as libc::c_uint) as isize,
            ) as *mut libc::c_void,
        tmp.as_mut_ptr() as *const libc::c_void,
        (15 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    let mut t2_7: *mut uint64_t = table2
        .as_mut_ptr()
        .offset(
            (2 as libc::c_uint)
                .wrapping_mul(i)
                .wrapping_add(2 as libc::c_uint)
                .wrapping_mul(15 as libc::c_uint) as isize,
        );
    let mut p_copy_7: [uint64_t; 15] = [
        0 as libc::c_uint as uint64_t,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
    ];
    memcpy(
        p_copy_7.as_mut_ptr() as *mut libc::c_void,
        q2 as *const libc::c_void,
        (15 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    Hacl_Impl_K256_PointAdd_point_add(tmp.as_mut_ptr(), p_copy_7.as_mut_ptr(), t2_7);
    memcpy(
        table2
            .as_mut_ptr()
            .offset(
                (2 as libc::c_uint)
                    .wrapping_mul(i)
                    .wrapping_add(3 as libc::c_uint)
                    .wrapping_mul(15 as libc::c_uint) as isize,
            ) as *mut libc::c_void,
        tmp.as_mut_ptr() as *const libc::c_void,
        (15 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    i = (i as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut t11_8: *mut uint64_t = table2
        .as_mut_ptr()
        .offset(
            i.wrapping_add(1 as libc::c_uint).wrapping_mul(15 as libc::c_uint) as isize,
        );
    let mut p_copy0_8: [uint64_t; 15] = [
        0 as libc::c_uint as uint64_t,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
    ];
    memcpy(
        p_copy0_8.as_mut_ptr() as *mut libc::c_void,
        t11_8 as *const libc::c_void,
        (15 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    Hacl_Impl_K256_PointDouble_point_double(tmp.as_mut_ptr(), p_copy0_8.as_mut_ptr());
    memcpy(
        table2
            .as_mut_ptr()
            .offset(
                (2 as libc::c_uint)
                    .wrapping_mul(i)
                    .wrapping_add(2 as libc::c_uint)
                    .wrapping_mul(15 as libc::c_uint) as isize,
            ) as *mut libc::c_void,
        tmp.as_mut_ptr() as *const libc::c_void,
        (15 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    let mut t2_8: *mut uint64_t = table2
        .as_mut_ptr()
        .offset(
            (2 as libc::c_uint)
                .wrapping_mul(i)
                .wrapping_add(2 as libc::c_uint)
                .wrapping_mul(15 as libc::c_uint) as isize,
        );
    let mut p_copy_8: [uint64_t; 15] = [
        0 as libc::c_uint as uint64_t,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
    ];
    memcpy(
        p_copy_8.as_mut_ptr() as *mut libc::c_void,
        q2 as *const libc::c_void,
        (15 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    Hacl_Impl_K256_PointAdd_point_add(tmp.as_mut_ptr(), p_copy_8.as_mut_ptr(), t2_8);
    memcpy(
        table2
            .as_mut_ptr()
            .offset(
                (2 as libc::c_uint)
                    .wrapping_mul(i)
                    .wrapping_add(3 as libc::c_uint)
                    .wrapping_mul(15 as libc::c_uint) as isize,
            ) as *mut libc::c_void,
        tmp.as_mut_ptr() as *const libc::c_void,
        (15 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    i = (i as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut t11_9: *mut uint64_t = table2
        .as_mut_ptr()
        .offset(
            i.wrapping_add(1 as libc::c_uint).wrapping_mul(15 as libc::c_uint) as isize,
        );
    let mut p_copy0_9: [uint64_t; 15] = [
        0 as libc::c_uint as uint64_t,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
    ];
    memcpy(
        p_copy0_9.as_mut_ptr() as *mut libc::c_void,
        t11_9 as *const libc::c_void,
        (15 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    Hacl_Impl_K256_PointDouble_point_double(tmp.as_mut_ptr(), p_copy0_9.as_mut_ptr());
    memcpy(
        table2
            .as_mut_ptr()
            .offset(
                (2 as libc::c_uint)
                    .wrapping_mul(i)
                    .wrapping_add(2 as libc::c_uint)
                    .wrapping_mul(15 as libc::c_uint) as isize,
            ) as *mut libc::c_void,
        tmp.as_mut_ptr() as *const libc::c_void,
        (15 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    let mut t2_9: *mut uint64_t = table2
        .as_mut_ptr()
        .offset(
            (2 as libc::c_uint)
                .wrapping_mul(i)
                .wrapping_add(2 as libc::c_uint)
                .wrapping_mul(15 as libc::c_uint) as isize,
        );
    let mut p_copy_9: [uint64_t; 15] = [
        0 as libc::c_uint as uint64_t,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
    ];
    memcpy(
        p_copy_9.as_mut_ptr() as *mut libc::c_void,
        q2 as *const libc::c_void,
        (15 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    Hacl_Impl_K256_PointAdd_point_add(tmp.as_mut_ptr(), p_copy_9.as_mut_ptr(), t2_9);
    memcpy(
        table2
            .as_mut_ptr()
            .offset(
                (2 as libc::c_uint)
                    .wrapping_mul(i)
                    .wrapping_add(3 as libc::c_uint)
                    .wrapping_mul(15 as libc::c_uint) as isize,
            ) as *mut libc::c_void,
        tmp.as_mut_ptr() as *const libc::c_void,
        (15 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    i = (i as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut t11_10: *mut uint64_t = table2
        .as_mut_ptr()
        .offset(
            i.wrapping_add(1 as libc::c_uint).wrapping_mul(15 as libc::c_uint) as isize,
        );
    let mut p_copy0_10: [uint64_t; 15] = [
        0 as libc::c_uint as uint64_t,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
    ];
    memcpy(
        p_copy0_10.as_mut_ptr() as *mut libc::c_void,
        t11_10 as *const libc::c_void,
        (15 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    Hacl_Impl_K256_PointDouble_point_double(tmp.as_mut_ptr(), p_copy0_10.as_mut_ptr());
    memcpy(
        table2
            .as_mut_ptr()
            .offset(
                (2 as libc::c_uint)
                    .wrapping_mul(i)
                    .wrapping_add(2 as libc::c_uint)
                    .wrapping_mul(15 as libc::c_uint) as isize,
            ) as *mut libc::c_void,
        tmp.as_mut_ptr() as *const libc::c_void,
        (15 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    let mut t2_10: *mut uint64_t = table2
        .as_mut_ptr()
        .offset(
            (2 as libc::c_uint)
                .wrapping_mul(i)
                .wrapping_add(2 as libc::c_uint)
                .wrapping_mul(15 as libc::c_uint) as isize,
        );
    let mut p_copy_10: [uint64_t; 15] = [
        0 as libc::c_uint as uint64_t,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
    ];
    memcpy(
        p_copy_10.as_mut_ptr() as *mut libc::c_void,
        q2 as *const libc::c_void,
        (15 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    Hacl_Impl_K256_PointAdd_point_add(tmp.as_mut_ptr(), p_copy_10.as_mut_ptr(), t2_10);
    memcpy(
        table2
            .as_mut_ptr()
            .offset(
                (2 as libc::c_uint)
                    .wrapping_mul(i)
                    .wrapping_add(3 as libc::c_uint)
                    .wrapping_mul(15 as libc::c_uint) as isize,
            ) as *mut libc::c_void,
        tmp.as_mut_ptr() as *const libc::c_void,
        (15 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    i = (i as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut t11_11: *mut uint64_t = table2
        .as_mut_ptr()
        .offset(
            i.wrapping_add(1 as libc::c_uint).wrapping_mul(15 as libc::c_uint) as isize,
        );
    let mut p_copy0_11: [uint64_t; 15] = [
        0 as libc::c_uint as uint64_t,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
    ];
    memcpy(
        p_copy0_11.as_mut_ptr() as *mut libc::c_void,
        t11_11 as *const libc::c_void,
        (15 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    Hacl_Impl_K256_PointDouble_point_double(tmp.as_mut_ptr(), p_copy0_11.as_mut_ptr());
    memcpy(
        table2
            .as_mut_ptr()
            .offset(
                (2 as libc::c_uint)
                    .wrapping_mul(i)
                    .wrapping_add(2 as libc::c_uint)
                    .wrapping_mul(15 as libc::c_uint) as isize,
            ) as *mut libc::c_void,
        tmp.as_mut_ptr() as *const libc::c_void,
        (15 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    let mut t2_11: *mut uint64_t = table2
        .as_mut_ptr()
        .offset(
            (2 as libc::c_uint)
                .wrapping_mul(i)
                .wrapping_add(2 as libc::c_uint)
                .wrapping_mul(15 as libc::c_uint) as isize,
        );
    let mut p_copy_11: [uint64_t; 15] = [
        0 as libc::c_uint as uint64_t,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
    ];
    memcpy(
        p_copy_11.as_mut_ptr() as *mut libc::c_void,
        q2 as *const libc::c_void,
        (15 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    Hacl_Impl_K256_PointAdd_point_add(tmp.as_mut_ptr(), p_copy_11.as_mut_ptr(), t2_11);
    memcpy(
        table2
            .as_mut_ptr()
            .offset(
                (2 as libc::c_uint)
                    .wrapping_mul(i)
                    .wrapping_add(3 as libc::c_uint)
                    .wrapping_mul(15 as libc::c_uint) as isize,
            ) as *mut libc::c_void,
        tmp.as_mut_ptr() as *const libc::c_void,
        (15 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    i = (i as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut t11_12: *mut uint64_t = table2
        .as_mut_ptr()
        .offset(
            i.wrapping_add(1 as libc::c_uint).wrapping_mul(15 as libc::c_uint) as isize,
        );
    let mut p_copy0_12: [uint64_t; 15] = [
        0 as libc::c_uint as uint64_t,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
    ];
    memcpy(
        p_copy0_12.as_mut_ptr() as *mut libc::c_void,
        t11_12 as *const libc::c_void,
        (15 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    Hacl_Impl_K256_PointDouble_point_double(tmp.as_mut_ptr(), p_copy0_12.as_mut_ptr());
    memcpy(
        table2
            .as_mut_ptr()
            .offset(
                (2 as libc::c_uint)
                    .wrapping_mul(i)
                    .wrapping_add(2 as libc::c_uint)
                    .wrapping_mul(15 as libc::c_uint) as isize,
            ) as *mut libc::c_void,
        tmp.as_mut_ptr() as *const libc::c_void,
        (15 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    let mut t2_12: *mut uint64_t = table2
        .as_mut_ptr()
        .offset(
            (2 as libc::c_uint)
                .wrapping_mul(i)
                .wrapping_add(2 as libc::c_uint)
                .wrapping_mul(15 as libc::c_uint) as isize,
        );
    let mut p_copy_12: [uint64_t; 15] = [
        0 as libc::c_uint as uint64_t,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
    ];
    memcpy(
        p_copy_12.as_mut_ptr() as *mut libc::c_void,
        q2 as *const libc::c_void,
        (15 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    Hacl_Impl_K256_PointAdd_point_add(tmp.as_mut_ptr(), p_copy_12.as_mut_ptr(), t2_12);
    memcpy(
        table2
            .as_mut_ptr()
            .offset(
                (2 as libc::c_uint)
                    .wrapping_mul(i)
                    .wrapping_add(3 as libc::c_uint)
                    .wrapping_mul(15 as libc::c_uint) as isize,
            ) as *mut libc::c_void,
        tmp.as_mut_ptr() as *const libc::c_void,
        (15 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    i = (i as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut t11_13: *mut uint64_t = table2
        .as_mut_ptr()
        .offset(
            i.wrapping_add(1 as libc::c_uint).wrapping_mul(15 as libc::c_uint) as isize,
        );
    let mut p_copy0_13: [uint64_t; 15] = [
        0 as libc::c_uint as uint64_t,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
    ];
    memcpy(
        p_copy0_13.as_mut_ptr() as *mut libc::c_void,
        t11_13 as *const libc::c_void,
        (15 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    Hacl_Impl_K256_PointDouble_point_double(tmp.as_mut_ptr(), p_copy0_13.as_mut_ptr());
    memcpy(
        table2
            .as_mut_ptr()
            .offset(
                (2 as libc::c_uint)
                    .wrapping_mul(i)
                    .wrapping_add(2 as libc::c_uint)
                    .wrapping_mul(15 as libc::c_uint) as isize,
            ) as *mut libc::c_void,
        tmp.as_mut_ptr() as *const libc::c_void,
        (15 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    let mut t2_13: *mut uint64_t = table2
        .as_mut_ptr()
        .offset(
            (2 as libc::c_uint)
                .wrapping_mul(i)
                .wrapping_add(2 as libc::c_uint)
                .wrapping_mul(15 as libc::c_uint) as isize,
        );
    let mut p_copy_13: [uint64_t; 15] = [
        0 as libc::c_uint as uint64_t,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
    ];
    memcpy(
        p_copy_13.as_mut_ptr() as *mut libc::c_void,
        q2 as *const libc::c_void,
        (15 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    Hacl_Impl_K256_PointAdd_point_add(tmp.as_mut_ptr(), p_copy_13.as_mut_ptr(), t2_13);
    memcpy(
        table2
            .as_mut_ptr()
            .offset(
                (2 as libc::c_uint)
                    .wrapping_mul(i)
                    .wrapping_add(3 as libc::c_uint)
                    .wrapping_mul(15 as libc::c_uint) as isize,
            ) as *mut libc::c_void,
        tmp.as_mut_ptr() as *const libc::c_void,
        (15 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    i = (i as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut tmp0: [uint64_t; 15] = [
        0 as libc::c_uint as uint64_t,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
    ];
    let mut i0: uint32_t = 255 as libc::c_uint;
    let mut bits_c: uint64_t = Hacl_Bignum_Lib_bn_get_bits_u64(
        4 as libc::c_uint,
        scalar1,
        i0,
        5 as libc::c_uint,
    );
    let mut bits_l32: uint32_t = bits_c as uint32_t;
    let mut a_bits_l: *const uint64_t = Hacl_K256_PrecompTable_precomp_basepoint_table_w5
        .as_ptr()
        .offset(bits_l32.wrapping_mul(15 as libc::c_uint) as isize);
    memcpy(
        out as *mut libc::c_void,
        a_bits_l as *mut uint64_t as *const libc::c_void,
        (15 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    let mut i1: uint32_t = 255 as libc::c_uint;
    let mut bits_c0: uint64_t = Hacl_Bignum_Lib_bn_get_bits_u64(
        4 as libc::c_uint,
        scalar2,
        i1,
        5 as libc::c_uint,
    );
    let mut bits_l320: uint32_t = bits_c0 as uint32_t;
    let mut a_bits_l0: *const uint64_t = table2
        .as_mut_ptr()
        .offset(bits_l320.wrapping_mul(15 as libc::c_uint) as isize);
    memcpy(
        tmp0.as_mut_ptr() as *mut libc::c_void,
        a_bits_l0 as *mut uint64_t as *const libc::c_void,
        (15 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    let mut p_copy_14: [uint64_t; 15] = [
        0 as libc::c_uint as uint64_t,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
    ];
    memcpy(
        p_copy_14.as_mut_ptr() as *mut libc::c_void,
        out as *const libc::c_void,
        (15 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    Hacl_Impl_K256_PointAdd_point_add(out, p_copy_14.as_mut_ptr(), tmp0.as_mut_ptr());
    let mut tmp1: [uint64_t; 15] = [
        0 as libc::c_uint as uint64_t,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
    ];
    let mut i_0: uint32_t = 0 as libc::c_uint;
    while i_0 < 51 as libc::c_uint {
        let mut i2: uint32_t = 0 as libc::c_uint;
        let mut p_copy0_14: [uint64_t; 15] = [
            0 as libc::c_uint as uint64_t,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
        ];
        memcpy(
            p_copy0_14.as_mut_ptr() as *mut libc::c_void,
            out as *const libc::c_void,
            (15 as libc::c_uint as libc::c_ulong)
                .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
        );
        Hacl_Impl_K256_PointDouble_point_double(out, p_copy0_14.as_mut_ptr());
        i2 = (i2 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut p_copy0_15: [uint64_t; 15] = [
            0 as libc::c_uint as uint64_t,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
        ];
        memcpy(
            p_copy0_15.as_mut_ptr() as *mut libc::c_void,
            out as *const libc::c_void,
            (15 as libc::c_uint as libc::c_ulong)
                .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
        );
        Hacl_Impl_K256_PointDouble_point_double(out, p_copy0_15.as_mut_ptr());
        i2 = (i2 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut p_copy0_16: [uint64_t; 15] = [
            0 as libc::c_uint as uint64_t,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
        ];
        memcpy(
            p_copy0_16.as_mut_ptr() as *mut libc::c_void,
            out as *const libc::c_void,
            (15 as libc::c_uint as libc::c_ulong)
                .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
        );
        Hacl_Impl_K256_PointDouble_point_double(out, p_copy0_16.as_mut_ptr());
        i2 = (i2 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut p_copy0_17: [uint64_t; 15] = [
            0 as libc::c_uint as uint64_t,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
        ];
        memcpy(
            p_copy0_17.as_mut_ptr() as *mut libc::c_void,
            out as *const libc::c_void,
            (15 as libc::c_uint as libc::c_ulong)
                .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
        );
        Hacl_Impl_K256_PointDouble_point_double(out, p_copy0_17.as_mut_ptr());
        i2 = (i2 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut p_copy0_18: [uint64_t; 15] = [
            0 as libc::c_uint as uint64_t,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
        ];
        memcpy(
            p_copy0_18.as_mut_ptr() as *mut libc::c_void,
            out as *const libc::c_void,
            (15 as libc::c_uint as libc::c_ulong)
                .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
        );
        Hacl_Impl_K256_PointDouble_point_double(out, p_copy0_18.as_mut_ptr());
        i2 = (i2 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut k: uint32_t = (255 as libc::c_uint)
            .wrapping_sub((5 as libc::c_uint).wrapping_mul(i_0))
            .wrapping_sub(5 as libc::c_uint);
        let mut bits_l: uint64_t = Hacl_Bignum_Lib_bn_get_bits_u64(
            4 as libc::c_uint,
            scalar2,
            k,
            5 as libc::c_uint,
        );
        let mut bits_l321: uint32_t = bits_l as uint32_t;
        let mut a_bits_l1: *const uint64_t = table2
            .as_mut_ptr()
            .offset(bits_l321.wrapping_mul(15 as libc::c_uint) as isize);
        memcpy(
            tmp1.as_mut_ptr() as *mut libc::c_void,
            a_bits_l1 as *mut uint64_t as *const libc::c_void,
            (15 as libc::c_uint as libc::c_ulong)
                .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
        );
        let mut p_copy0_19: [uint64_t; 15] = [
            0 as libc::c_uint as uint64_t,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
        ];
        memcpy(
            p_copy0_19.as_mut_ptr() as *mut libc::c_void,
            out as *const libc::c_void,
            (15 as libc::c_uint as libc::c_ulong)
                .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
        );
        Hacl_Impl_K256_PointAdd_point_add(
            out,
            p_copy0_19.as_mut_ptr(),
            tmp1.as_mut_ptr(),
        );
        let mut k0: uint32_t = (255 as libc::c_uint)
            .wrapping_sub((5 as libc::c_uint).wrapping_mul(i_0))
            .wrapping_sub(5 as libc::c_uint);
        let mut bits_l0: uint64_t = Hacl_Bignum_Lib_bn_get_bits_u64(
            4 as libc::c_uint,
            scalar1,
            k0,
            5 as libc::c_uint,
        );
        let mut bits_l322: uint32_t = bits_l0 as uint32_t;
        let mut a_bits_l2: *const uint64_t = Hacl_K256_PrecompTable_precomp_basepoint_table_w5
            .as_ptr()
            .offset(bits_l322.wrapping_mul(15 as libc::c_uint) as isize);
        memcpy(
            tmp1.as_mut_ptr() as *mut libc::c_void,
            a_bits_l2 as *mut uint64_t as *const libc::c_void,
            (15 as libc::c_uint as libc::c_ulong)
                .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
        );
        let mut p_copy1: [uint64_t; 15] = [
            0 as libc::c_uint as uint64_t,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
        ];
        memcpy(
            p_copy1.as_mut_ptr() as *mut libc::c_void,
            out as *const libc::c_void,
            (15 as libc::c_uint as libc::c_ulong)
                .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
        );
        Hacl_Impl_K256_PointAdd_point_add(out, p_copy1.as_mut_ptr(), tmp1.as_mut_ptr());
        i_0 = i_0.wrapping_add(1);
        i_0;
    }
}
#[inline]
unsafe extern "C" fn point_mul_g_double_split_lambda_table(
    mut out: *mut uint64_t,
    mut r1: *mut uint64_t,
    mut r2: *mut uint64_t,
    mut r3: *mut uint64_t,
    mut r4: *mut uint64_t,
    mut p2: *mut uint64_t,
    mut is_negate1: bool,
    mut is_negate2: bool,
    mut is_negate3: bool,
    mut is_negate4: bool,
) {
    let mut table2: [uint64_t; 480] = [
        0 as libc::c_uint as uint64_t,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
    ];
    let mut tmp: [uint64_t; 15] = [
        0 as libc::c_uint as uint64_t,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
    ];
    let mut t0: *mut uint64_t = table2.as_mut_ptr();
    let mut t1: *mut uint64_t = table2.as_mut_ptr().offset(15 as libc::c_uint as isize);
    Hacl_Impl_K256_Point_make_point_at_inf(t0);
    memcpy(
        t1 as *mut libc::c_void,
        p2 as *const libc::c_void,
        (15 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    let mut i: uint32_t = 0 as libc::c_uint;
    let mut t11: *mut uint64_t = table2
        .as_mut_ptr()
        .offset(
            i.wrapping_add(1 as libc::c_uint).wrapping_mul(15 as libc::c_uint) as isize,
        );
    let mut p_copy0: [uint64_t; 15] = [
        0 as libc::c_uint as uint64_t,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
    ];
    memcpy(
        p_copy0.as_mut_ptr() as *mut libc::c_void,
        t11 as *const libc::c_void,
        (15 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    Hacl_Impl_K256_PointDouble_point_double(tmp.as_mut_ptr(), p_copy0.as_mut_ptr());
    memcpy(
        table2
            .as_mut_ptr()
            .offset(
                (2 as libc::c_uint)
                    .wrapping_mul(i)
                    .wrapping_add(2 as libc::c_uint)
                    .wrapping_mul(15 as libc::c_uint) as isize,
            ) as *mut libc::c_void,
        tmp.as_mut_ptr() as *const libc::c_void,
        (15 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    let mut t2: *mut uint64_t = table2
        .as_mut_ptr()
        .offset(
            (2 as libc::c_uint)
                .wrapping_mul(i)
                .wrapping_add(2 as libc::c_uint)
                .wrapping_mul(15 as libc::c_uint) as isize,
        );
    let mut p_copy: [uint64_t; 15] = [
        0 as libc::c_uint as uint64_t,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
    ];
    memcpy(
        p_copy.as_mut_ptr() as *mut libc::c_void,
        p2 as *const libc::c_void,
        (15 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    Hacl_Impl_K256_PointAdd_point_add(tmp.as_mut_ptr(), p_copy.as_mut_ptr(), t2);
    memcpy(
        table2
            .as_mut_ptr()
            .offset(
                (2 as libc::c_uint)
                    .wrapping_mul(i)
                    .wrapping_add(3 as libc::c_uint)
                    .wrapping_mul(15 as libc::c_uint) as isize,
            ) as *mut libc::c_void,
        tmp.as_mut_ptr() as *const libc::c_void,
        (15 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    i = (i as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut t11_0: *mut uint64_t = table2
        .as_mut_ptr()
        .offset(
            i.wrapping_add(1 as libc::c_uint).wrapping_mul(15 as libc::c_uint) as isize,
        );
    let mut p_copy0_0: [uint64_t; 15] = [
        0 as libc::c_uint as uint64_t,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
    ];
    memcpy(
        p_copy0_0.as_mut_ptr() as *mut libc::c_void,
        t11_0 as *const libc::c_void,
        (15 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    Hacl_Impl_K256_PointDouble_point_double(tmp.as_mut_ptr(), p_copy0_0.as_mut_ptr());
    memcpy(
        table2
            .as_mut_ptr()
            .offset(
                (2 as libc::c_uint)
                    .wrapping_mul(i)
                    .wrapping_add(2 as libc::c_uint)
                    .wrapping_mul(15 as libc::c_uint) as isize,
            ) as *mut libc::c_void,
        tmp.as_mut_ptr() as *const libc::c_void,
        (15 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    let mut t2_0: *mut uint64_t = table2
        .as_mut_ptr()
        .offset(
            (2 as libc::c_uint)
                .wrapping_mul(i)
                .wrapping_add(2 as libc::c_uint)
                .wrapping_mul(15 as libc::c_uint) as isize,
        );
    let mut p_copy_0: [uint64_t; 15] = [
        0 as libc::c_uint as uint64_t,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
    ];
    memcpy(
        p_copy_0.as_mut_ptr() as *mut libc::c_void,
        p2 as *const libc::c_void,
        (15 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    Hacl_Impl_K256_PointAdd_point_add(tmp.as_mut_ptr(), p_copy_0.as_mut_ptr(), t2_0);
    memcpy(
        table2
            .as_mut_ptr()
            .offset(
                (2 as libc::c_uint)
                    .wrapping_mul(i)
                    .wrapping_add(3 as libc::c_uint)
                    .wrapping_mul(15 as libc::c_uint) as isize,
            ) as *mut libc::c_void,
        tmp.as_mut_ptr() as *const libc::c_void,
        (15 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    i = (i as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut t11_1: *mut uint64_t = table2
        .as_mut_ptr()
        .offset(
            i.wrapping_add(1 as libc::c_uint).wrapping_mul(15 as libc::c_uint) as isize,
        );
    let mut p_copy0_1: [uint64_t; 15] = [
        0 as libc::c_uint as uint64_t,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
    ];
    memcpy(
        p_copy0_1.as_mut_ptr() as *mut libc::c_void,
        t11_1 as *const libc::c_void,
        (15 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    Hacl_Impl_K256_PointDouble_point_double(tmp.as_mut_ptr(), p_copy0_1.as_mut_ptr());
    memcpy(
        table2
            .as_mut_ptr()
            .offset(
                (2 as libc::c_uint)
                    .wrapping_mul(i)
                    .wrapping_add(2 as libc::c_uint)
                    .wrapping_mul(15 as libc::c_uint) as isize,
            ) as *mut libc::c_void,
        tmp.as_mut_ptr() as *const libc::c_void,
        (15 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    let mut t2_1: *mut uint64_t = table2
        .as_mut_ptr()
        .offset(
            (2 as libc::c_uint)
                .wrapping_mul(i)
                .wrapping_add(2 as libc::c_uint)
                .wrapping_mul(15 as libc::c_uint) as isize,
        );
    let mut p_copy_1: [uint64_t; 15] = [
        0 as libc::c_uint as uint64_t,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
    ];
    memcpy(
        p_copy_1.as_mut_ptr() as *mut libc::c_void,
        p2 as *const libc::c_void,
        (15 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    Hacl_Impl_K256_PointAdd_point_add(tmp.as_mut_ptr(), p_copy_1.as_mut_ptr(), t2_1);
    memcpy(
        table2
            .as_mut_ptr()
            .offset(
                (2 as libc::c_uint)
                    .wrapping_mul(i)
                    .wrapping_add(3 as libc::c_uint)
                    .wrapping_mul(15 as libc::c_uint) as isize,
            ) as *mut libc::c_void,
        tmp.as_mut_ptr() as *const libc::c_void,
        (15 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    i = (i as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut t11_2: *mut uint64_t = table2
        .as_mut_ptr()
        .offset(
            i.wrapping_add(1 as libc::c_uint).wrapping_mul(15 as libc::c_uint) as isize,
        );
    let mut p_copy0_2: [uint64_t; 15] = [
        0 as libc::c_uint as uint64_t,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
    ];
    memcpy(
        p_copy0_2.as_mut_ptr() as *mut libc::c_void,
        t11_2 as *const libc::c_void,
        (15 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    Hacl_Impl_K256_PointDouble_point_double(tmp.as_mut_ptr(), p_copy0_2.as_mut_ptr());
    memcpy(
        table2
            .as_mut_ptr()
            .offset(
                (2 as libc::c_uint)
                    .wrapping_mul(i)
                    .wrapping_add(2 as libc::c_uint)
                    .wrapping_mul(15 as libc::c_uint) as isize,
            ) as *mut libc::c_void,
        tmp.as_mut_ptr() as *const libc::c_void,
        (15 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    let mut t2_2: *mut uint64_t = table2
        .as_mut_ptr()
        .offset(
            (2 as libc::c_uint)
                .wrapping_mul(i)
                .wrapping_add(2 as libc::c_uint)
                .wrapping_mul(15 as libc::c_uint) as isize,
        );
    let mut p_copy_2: [uint64_t; 15] = [
        0 as libc::c_uint as uint64_t,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
    ];
    memcpy(
        p_copy_2.as_mut_ptr() as *mut libc::c_void,
        p2 as *const libc::c_void,
        (15 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    Hacl_Impl_K256_PointAdd_point_add(tmp.as_mut_ptr(), p_copy_2.as_mut_ptr(), t2_2);
    memcpy(
        table2
            .as_mut_ptr()
            .offset(
                (2 as libc::c_uint)
                    .wrapping_mul(i)
                    .wrapping_add(3 as libc::c_uint)
                    .wrapping_mul(15 as libc::c_uint) as isize,
            ) as *mut libc::c_void,
        tmp.as_mut_ptr() as *const libc::c_void,
        (15 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    i = (i as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut t11_3: *mut uint64_t = table2
        .as_mut_ptr()
        .offset(
            i.wrapping_add(1 as libc::c_uint).wrapping_mul(15 as libc::c_uint) as isize,
        );
    let mut p_copy0_3: [uint64_t; 15] = [
        0 as libc::c_uint as uint64_t,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
    ];
    memcpy(
        p_copy0_3.as_mut_ptr() as *mut libc::c_void,
        t11_3 as *const libc::c_void,
        (15 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    Hacl_Impl_K256_PointDouble_point_double(tmp.as_mut_ptr(), p_copy0_3.as_mut_ptr());
    memcpy(
        table2
            .as_mut_ptr()
            .offset(
                (2 as libc::c_uint)
                    .wrapping_mul(i)
                    .wrapping_add(2 as libc::c_uint)
                    .wrapping_mul(15 as libc::c_uint) as isize,
            ) as *mut libc::c_void,
        tmp.as_mut_ptr() as *const libc::c_void,
        (15 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    let mut t2_3: *mut uint64_t = table2
        .as_mut_ptr()
        .offset(
            (2 as libc::c_uint)
                .wrapping_mul(i)
                .wrapping_add(2 as libc::c_uint)
                .wrapping_mul(15 as libc::c_uint) as isize,
        );
    let mut p_copy_3: [uint64_t; 15] = [
        0 as libc::c_uint as uint64_t,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
    ];
    memcpy(
        p_copy_3.as_mut_ptr() as *mut libc::c_void,
        p2 as *const libc::c_void,
        (15 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    Hacl_Impl_K256_PointAdd_point_add(tmp.as_mut_ptr(), p_copy_3.as_mut_ptr(), t2_3);
    memcpy(
        table2
            .as_mut_ptr()
            .offset(
                (2 as libc::c_uint)
                    .wrapping_mul(i)
                    .wrapping_add(3 as libc::c_uint)
                    .wrapping_mul(15 as libc::c_uint) as isize,
            ) as *mut libc::c_void,
        tmp.as_mut_ptr() as *const libc::c_void,
        (15 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    i = (i as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut t11_4: *mut uint64_t = table2
        .as_mut_ptr()
        .offset(
            i.wrapping_add(1 as libc::c_uint).wrapping_mul(15 as libc::c_uint) as isize,
        );
    let mut p_copy0_4: [uint64_t; 15] = [
        0 as libc::c_uint as uint64_t,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
    ];
    memcpy(
        p_copy0_4.as_mut_ptr() as *mut libc::c_void,
        t11_4 as *const libc::c_void,
        (15 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    Hacl_Impl_K256_PointDouble_point_double(tmp.as_mut_ptr(), p_copy0_4.as_mut_ptr());
    memcpy(
        table2
            .as_mut_ptr()
            .offset(
                (2 as libc::c_uint)
                    .wrapping_mul(i)
                    .wrapping_add(2 as libc::c_uint)
                    .wrapping_mul(15 as libc::c_uint) as isize,
            ) as *mut libc::c_void,
        tmp.as_mut_ptr() as *const libc::c_void,
        (15 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    let mut t2_4: *mut uint64_t = table2
        .as_mut_ptr()
        .offset(
            (2 as libc::c_uint)
                .wrapping_mul(i)
                .wrapping_add(2 as libc::c_uint)
                .wrapping_mul(15 as libc::c_uint) as isize,
        );
    let mut p_copy_4: [uint64_t; 15] = [
        0 as libc::c_uint as uint64_t,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
    ];
    memcpy(
        p_copy_4.as_mut_ptr() as *mut libc::c_void,
        p2 as *const libc::c_void,
        (15 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    Hacl_Impl_K256_PointAdd_point_add(tmp.as_mut_ptr(), p_copy_4.as_mut_ptr(), t2_4);
    memcpy(
        table2
            .as_mut_ptr()
            .offset(
                (2 as libc::c_uint)
                    .wrapping_mul(i)
                    .wrapping_add(3 as libc::c_uint)
                    .wrapping_mul(15 as libc::c_uint) as isize,
            ) as *mut libc::c_void,
        tmp.as_mut_ptr() as *const libc::c_void,
        (15 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    i = (i as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut t11_5: *mut uint64_t = table2
        .as_mut_ptr()
        .offset(
            i.wrapping_add(1 as libc::c_uint).wrapping_mul(15 as libc::c_uint) as isize,
        );
    let mut p_copy0_5: [uint64_t; 15] = [
        0 as libc::c_uint as uint64_t,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
    ];
    memcpy(
        p_copy0_5.as_mut_ptr() as *mut libc::c_void,
        t11_5 as *const libc::c_void,
        (15 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    Hacl_Impl_K256_PointDouble_point_double(tmp.as_mut_ptr(), p_copy0_5.as_mut_ptr());
    memcpy(
        table2
            .as_mut_ptr()
            .offset(
                (2 as libc::c_uint)
                    .wrapping_mul(i)
                    .wrapping_add(2 as libc::c_uint)
                    .wrapping_mul(15 as libc::c_uint) as isize,
            ) as *mut libc::c_void,
        tmp.as_mut_ptr() as *const libc::c_void,
        (15 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    let mut t2_5: *mut uint64_t = table2
        .as_mut_ptr()
        .offset(
            (2 as libc::c_uint)
                .wrapping_mul(i)
                .wrapping_add(2 as libc::c_uint)
                .wrapping_mul(15 as libc::c_uint) as isize,
        );
    let mut p_copy_5: [uint64_t; 15] = [
        0 as libc::c_uint as uint64_t,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
    ];
    memcpy(
        p_copy_5.as_mut_ptr() as *mut libc::c_void,
        p2 as *const libc::c_void,
        (15 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    Hacl_Impl_K256_PointAdd_point_add(tmp.as_mut_ptr(), p_copy_5.as_mut_ptr(), t2_5);
    memcpy(
        table2
            .as_mut_ptr()
            .offset(
                (2 as libc::c_uint)
                    .wrapping_mul(i)
                    .wrapping_add(3 as libc::c_uint)
                    .wrapping_mul(15 as libc::c_uint) as isize,
            ) as *mut libc::c_void,
        tmp.as_mut_ptr() as *const libc::c_void,
        (15 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    i = (i as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut t11_6: *mut uint64_t = table2
        .as_mut_ptr()
        .offset(
            i.wrapping_add(1 as libc::c_uint).wrapping_mul(15 as libc::c_uint) as isize,
        );
    let mut p_copy0_6: [uint64_t; 15] = [
        0 as libc::c_uint as uint64_t,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
    ];
    memcpy(
        p_copy0_6.as_mut_ptr() as *mut libc::c_void,
        t11_6 as *const libc::c_void,
        (15 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    Hacl_Impl_K256_PointDouble_point_double(tmp.as_mut_ptr(), p_copy0_6.as_mut_ptr());
    memcpy(
        table2
            .as_mut_ptr()
            .offset(
                (2 as libc::c_uint)
                    .wrapping_mul(i)
                    .wrapping_add(2 as libc::c_uint)
                    .wrapping_mul(15 as libc::c_uint) as isize,
            ) as *mut libc::c_void,
        tmp.as_mut_ptr() as *const libc::c_void,
        (15 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    let mut t2_6: *mut uint64_t = table2
        .as_mut_ptr()
        .offset(
            (2 as libc::c_uint)
                .wrapping_mul(i)
                .wrapping_add(2 as libc::c_uint)
                .wrapping_mul(15 as libc::c_uint) as isize,
        );
    let mut p_copy_6: [uint64_t; 15] = [
        0 as libc::c_uint as uint64_t,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
    ];
    memcpy(
        p_copy_6.as_mut_ptr() as *mut libc::c_void,
        p2 as *const libc::c_void,
        (15 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    Hacl_Impl_K256_PointAdd_point_add(tmp.as_mut_ptr(), p_copy_6.as_mut_ptr(), t2_6);
    memcpy(
        table2
            .as_mut_ptr()
            .offset(
                (2 as libc::c_uint)
                    .wrapping_mul(i)
                    .wrapping_add(3 as libc::c_uint)
                    .wrapping_mul(15 as libc::c_uint) as isize,
            ) as *mut libc::c_void,
        tmp.as_mut_ptr() as *const libc::c_void,
        (15 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    i = (i as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut t11_7: *mut uint64_t = table2
        .as_mut_ptr()
        .offset(
            i.wrapping_add(1 as libc::c_uint).wrapping_mul(15 as libc::c_uint) as isize,
        );
    let mut p_copy0_7: [uint64_t; 15] = [
        0 as libc::c_uint as uint64_t,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
    ];
    memcpy(
        p_copy0_7.as_mut_ptr() as *mut libc::c_void,
        t11_7 as *const libc::c_void,
        (15 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    Hacl_Impl_K256_PointDouble_point_double(tmp.as_mut_ptr(), p_copy0_7.as_mut_ptr());
    memcpy(
        table2
            .as_mut_ptr()
            .offset(
                (2 as libc::c_uint)
                    .wrapping_mul(i)
                    .wrapping_add(2 as libc::c_uint)
                    .wrapping_mul(15 as libc::c_uint) as isize,
            ) as *mut libc::c_void,
        tmp.as_mut_ptr() as *const libc::c_void,
        (15 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    let mut t2_7: *mut uint64_t = table2
        .as_mut_ptr()
        .offset(
            (2 as libc::c_uint)
                .wrapping_mul(i)
                .wrapping_add(2 as libc::c_uint)
                .wrapping_mul(15 as libc::c_uint) as isize,
        );
    let mut p_copy_7: [uint64_t; 15] = [
        0 as libc::c_uint as uint64_t,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
    ];
    memcpy(
        p_copy_7.as_mut_ptr() as *mut libc::c_void,
        p2 as *const libc::c_void,
        (15 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    Hacl_Impl_K256_PointAdd_point_add(tmp.as_mut_ptr(), p_copy_7.as_mut_ptr(), t2_7);
    memcpy(
        table2
            .as_mut_ptr()
            .offset(
                (2 as libc::c_uint)
                    .wrapping_mul(i)
                    .wrapping_add(3 as libc::c_uint)
                    .wrapping_mul(15 as libc::c_uint) as isize,
            ) as *mut libc::c_void,
        tmp.as_mut_ptr() as *const libc::c_void,
        (15 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    i = (i as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut t11_8: *mut uint64_t = table2
        .as_mut_ptr()
        .offset(
            i.wrapping_add(1 as libc::c_uint).wrapping_mul(15 as libc::c_uint) as isize,
        );
    let mut p_copy0_8: [uint64_t; 15] = [
        0 as libc::c_uint as uint64_t,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
    ];
    memcpy(
        p_copy0_8.as_mut_ptr() as *mut libc::c_void,
        t11_8 as *const libc::c_void,
        (15 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    Hacl_Impl_K256_PointDouble_point_double(tmp.as_mut_ptr(), p_copy0_8.as_mut_ptr());
    memcpy(
        table2
            .as_mut_ptr()
            .offset(
                (2 as libc::c_uint)
                    .wrapping_mul(i)
                    .wrapping_add(2 as libc::c_uint)
                    .wrapping_mul(15 as libc::c_uint) as isize,
            ) as *mut libc::c_void,
        tmp.as_mut_ptr() as *const libc::c_void,
        (15 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    let mut t2_8: *mut uint64_t = table2
        .as_mut_ptr()
        .offset(
            (2 as libc::c_uint)
                .wrapping_mul(i)
                .wrapping_add(2 as libc::c_uint)
                .wrapping_mul(15 as libc::c_uint) as isize,
        );
    let mut p_copy_8: [uint64_t; 15] = [
        0 as libc::c_uint as uint64_t,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
    ];
    memcpy(
        p_copy_8.as_mut_ptr() as *mut libc::c_void,
        p2 as *const libc::c_void,
        (15 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    Hacl_Impl_K256_PointAdd_point_add(tmp.as_mut_ptr(), p_copy_8.as_mut_ptr(), t2_8);
    memcpy(
        table2
            .as_mut_ptr()
            .offset(
                (2 as libc::c_uint)
                    .wrapping_mul(i)
                    .wrapping_add(3 as libc::c_uint)
                    .wrapping_mul(15 as libc::c_uint) as isize,
            ) as *mut libc::c_void,
        tmp.as_mut_ptr() as *const libc::c_void,
        (15 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    i = (i as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut t11_9: *mut uint64_t = table2
        .as_mut_ptr()
        .offset(
            i.wrapping_add(1 as libc::c_uint).wrapping_mul(15 as libc::c_uint) as isize,
        );
    let mut p_copy0_9: [uint64_t; 15] = [
        0 as libc::c_uint as uint64_t,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
    ];
    memcpy(
        p_copy0_9.as_mut_ptr() as *mut libc::c_void,
        t11_9 as *const libc::c_void,
        (15 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    Hacl_Impl_K256_PointDouble_point_double(tmp.as_mut_ptr(), p_copy0_9.as_mut_ptr());
    memcpy(
        table2
            .as_mut_ptr()
            .offset(
                (2 as libc::c_uint)
                    .wrapping_mul(i)
                    .wrapping_add(2 as libc::c_uint)
                    .wrapping_mul(15 as libc::c_uint) as isize,
            ) as *mut libc::c_void,
        tmp.as_mut_ptr() as *const libc::c_void,
        (15 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    let mut t2_9: *mut uint64_t = table2
        .as_mut_ptr()
        .offset(
            (2 as libc::c_uint)
                .wrapping_mul(i)
                .wrapping_add(2 as libc::c_uint)
                .wrapping_mul(15 as libc::c_uint) as isize,
        );
    let mut p_copy_9: [uint64_t; 15] = [
        0 as libc::c_uint as uint64_t,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
    ];
    memcpy(
        p_copy_9.as_mut_ptr() as *mut libc::c_void,
        p2 as *const libc::c_void,
        (15 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    Hacl_Impl_K256_PointAdd_point_add(tmp.as_mut_ptr(), p_copy_9.as_mut_ptr(), t2_9);
    memcpy(
        table2
            .as_mut_ptr()
            .offset(
                (2 as libc::c_uint)
                    .wrapping_mul(i)
                    .wrapping_add(3 as libc::c_uint)
                    .wrapping_mul(15 as libc::c_uint) as isize,
            ) as *mut libc::c_void,
        tmp.as_mut_ptr() as *const libc::c_void,
        (15 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    i = (i as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut t11_10: *mut uint64_t = table2
        .as_mut_ptr()
        .offset(
            i.wrapping_add(1 as libc::c_uint).wrapping_mul(15 as libc::c_uint) as isize,
        );
    let mut p_copy0_10: [uint64_t; 15] = [
        0 as libc::c_uint as uint64_t,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
    ];
    memcpy(
        p_copy0_10.as_mut_ptr() as *mut libc::c_void,
        t11_10 as *const libc::c_void,
        (15 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    Hacl_Impl_K256_PointDouble_point_double(tmp.as_mut_ptr(), p_copy0_10.as_mut_ptr());
    memcpy(
        table2
            .as_mut_ptr()
            .offset(
                (2 as libc::c_uint)
                    .wrapping_mul(i)
                    .wrapping_add(2 as libc::c_uint)
                    .wrapping_mul(15 as libc::c_uint) as isize,
            ) as *mut libc::c_void,
        tmp.as_mut_ptr() as *const libc::c_void,
        (15 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    let mut t2_10: *mut uint64_t = table2
        .as_mut_ptr()
        .offset(
            (2 as libc::c_uint)
                .wrapping_mul(i)
                .wrapping_add(2 as libc::c_uint)
                .wrapping_mul(15 as libc::c_uint) as isize,
        );
    let mut p_copy_10: [uint64_t; 15] = [
        0 as libc::c_uint as uint64_t,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
    ];
    memcpy(
        p_copy_10.as_mut_ptr() as *mut libc::c_void,
        p2 as *const libc::c_void,
        (15 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    Hacl_Impl_K256_PointAdd_point_add(tmp.as_mut_ptr(), p_copy_10.as_mut_ptr(), t2_10);
    memcpy(
        table2
            .as_mut_ptr()
            .offset(
                (2 as libc::c_uint)
                    .wrapping_mul(i)
                    .wrapping_add(3 as libc::c_uint)
                    .wrapping_mul(15 as libc::c_uint) as isize,
            ) as *mut libc::c_void,
        tmp.as_mut_ptr() as *const libc::c_void,
        (15 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    i = (i as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut t11_11: *mut uint64_t = table2
        .as_mut_ptr()
        .offset(
            i.wrapping_add(1 as libc::c_uint).wrapping_mul(15 as libc::c_uint) as isize,
        );
    let mut p_copy0_11: [uint64_t; 15] = [
        0 as libc::c_uint as uint64_t,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
    ];
    memcpy(
        p_copy0_11.as_mut_ptr() as *mut libc::c_void,
        t11_11 as *const libc::c_void,
        (15 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    Hacl_Impl_K256_PointDouble_point_double(tmp.as_mut_ptr(), p_copy0_11.as_mut_ptr());
    memcpy(
        table2
            .as_mut_ptr()
            .offset(
                (2 as libc::c_uint)
                    .wrapping_mul(i)
                    .wrapping_add(2 as libc::c_uint)
                    .wrapping_mul(15 as libc::c_uint) as isize,
            ) as *mut libc::c_void,
        tmp.as_mut_ptr() as *const libc::c_void,
        (15 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    let mut t2_11: *mut uint64_t = table2
        .as_mut_ptr()
        .offset(
            (2 as libc::c_uint)
                .wrapping_mul(i)
                .wrapping_add(2 as libc::c_uint)
                .wrapping_mul(15 as libc::c_uint) as isize,
        );
    let mut p_copy_11: [uint64_t; 15] = [
        0 as libc::c_uint as uint64_t,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
    ];
    memcpy(
        p_copy_11.as_mut_ptr() as *mut libc::c_void,
        p2 as *const libc::c_void,
        (15 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    Hacl_Impl_K256_PointAdd_point_add(tmp.as_mut_ptr(), p_copy_11.as_mut_ptr(), t2_11);
    memcpy(
        table2
            .as_mut_ptr()
            .offset(
                (2 as libc::c_uint)
                    .wrapping_mul(i)
                    .wrapping_add(3 as libc::c_uint)
                    .wrapping_mul(15 as libc::c_uint) as isize,
            ) as *mut libc::c_void,
        tmp.as_mut_ptr() as *const libc::c_void,
        (15 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    i = (i as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut t11_12: *mut uint64_t = table2
        .as_mut_ptr()
        .offset(
            i.wrapping_add(1 as libc::c_uint).wrapping_mul(15 as libc::c_uint) as isize,
        );
    let mut p_copy0_12: [uint64_t; 15] = [
        0 as libc::c_uint as uint64_t,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
    ];
    memcpy(
        p_copy0_12.as_mut_ptr() as *mut libc::c_void,
        t11_12 as *const libc::c_void,
        (15 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    Hacl_Impl_K256_PointDouble_point_double(tmp.as_mut_ptr(), p_copy0_12.as_mut_ptr());
    memcpy(
        table2
            .as_mut_ptr()
            .offset(
                (2 as libc::c_uint)
                    .wrapping_mul(i)
                    .wrapping_add(2 as libc::c_uint)
                    .wrapping_mul(15 as libc::c_uint) as isize,
            ) as *mut libc::c_void,
        tmp.as_mut_ptr() as *const libc::c_void,
        (15 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    let mut t2_12: *mut uint64_t = table2
        .as_mut_ptr()
        .offset(
            (2 as libc::c_uint)
                .wrapping_mul(i)
                .wrapping_add(2 as libc::c_uint)
                .wrapping_mul(15 as libc::c_uint) as isize,
        );
    let mut p_copy_12: [uint64_t; 15] = [
        0 as libc::c_uint as uint64_t,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
    ];
    memcpy(
        p_copy_12.as_mut_ptr() as *mut libc::c_void,
        p2 as *const libc::c_void,
        (15 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    Hacl_Impl_K256_PointAdd_point_add(tmp.as_mut_ptr(), p_copy_12.as_mut_ptr(), t2_12);
    memcpy(
        table2
            .as_mut_ptr()
            .offset(
                (2 as libc::c_uint)
                    .wrapping_mul(i)
                    .wrapping_add(3 as libc::c_uint)
                    .wrapping_mul(15 as libc::c_uint) as isize,
            ) as *mut libc::c_void,
        tmp.as_mut_ptr() as *const libc::c_void,
        (15 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    i = (i as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut t11_13: *mut uint64_t = table2
        .as_mut_ptr()
        .offset(
            i.wrapping_add(1 as libc::c_uint).wrapping_mul(15 as libc::c_uint) as isize,
        );
    let mut p_copy0_13: [uint64_t; 15] = [
        0 as libc::c_uint as uint64_t,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
    ];
    memcpy(
        p_copy0_13.as_mut_ptr() as *mut libc::c_void,
        t11_13 as *const libc::c_void,
        (15 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    Hacl_Impl_K256_PointDouble_point_double(tmp.as_mut_ptr(), p_copy0_13.as_mut_ptr());
    memcpy(
        table2
            .as_mut_ptr()
            .offset(
                (2 as libc::c_uint)
                    .wrapping_mul(i)
                    .wrapping_add(2 as libc::c_uint)
                    .wrapping_mul(15 as libc::c_uint) as isize,
            ) as *mut libc::c_void,
        tmp.as_mut_ptr() as *const libc::c_void,
        (15 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    let mut t2_13: *mut uint64_t = table2
        .as_mut_ptr()
        .offset(
            (2 as libc::c_uint)
                .wrapping_mul(i)
                .wrapping_add(2 as libc::c_uint)
                .wrapping_mul(15 as libc::c_uint) as isize,
        );
    let mut p_copy_13: [uint64_t; 15] = [
        0 as libc::c_uint as uint64_t,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
    ];
    memcpy(
        p_copy_13.as_mut_ptr() as *mut libc::c_void,
        p2 as *const libc::c_void,
        (15 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    Hacl_Impl_K256_PointAdd_point_add(tmp.as_mut_ptr(), p_copy_13.as_mut_ptr(), t2_13);
    memcpy(
        table2
            .as_mut_ptr()
            .offset(
                (2 as libc::c_uint)
                    .wrapping_mul(i)
                    .wrapping_add(3 as libc::c_uint)
                    .wrapping_mul(15 as libc::c_uint) as isize,
            ) as *mut libc::c_void,
        tmp.as_mut_ptr() as *const libc::c_void,
        (15 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    i = (i as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut tmp0: [uint64_t; 15] = [
        0 as libc::c_uint as uint64_t,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
    ];
    let mut tmp1: [uint64_t; 15] = [
        0 as libc::c_uint as uint64_t,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
    ];
    let mut i0: uint32_t = 125 as libc::c_uint;
    let mut bits_c: uint64_t = Hacl_Bignum_Lib_bn_get_bits_u64(
        4 as libc::c_uint,
        r1,
        i0,
        5 as libc::c_uint,
    );
    let mut bits_l32: uint32_t = bits_c as uint32_t;
    let mut a_bits_l: *const uint64_t = Hacl_K256_PrecompTable_precomp_basepoint_table_w5
        .as_ptr()
        .offset(bits_l32.wrapping_mul(15 as libc::c_uint) as isize);
    memcpy(
        out as *mut libc::c_void,
        a_bits_l as *mut uint64_t as *const libc::c_void,
        (15 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    point_negate_conditional_vartime(out, is_negate1);
    let mut i1: uint32_t = 125 as libc::c_uint;
    let mut bits_c0: uint64_t = Hacl_Bignum_Lib_bn_get_bits_u64(
        4 as libc::c_uint,
        r2,
        i1,
        5 as libc::c_uint,
    );
    let mut bits_l320: uint32_t = bits_c0 as uint32_t;
    let mut a_bits_l0: *const uint64_t = Hacl_K256_PrecompTable_precomp_basepoint_table_w5
        .as_ptr()
        .offset(bits_l320.wrapping_mul(15 as libc::c_uint) as isize);
    memcpy(
        tmp1.as_mut_ptr() as *mut libc::c_void,
        a_bits_l0 as *mut uint64_t as *const libc::c_void,
        (15 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    point_negate_conditional_vartime(tmp1.as_mut_ptr(), is_negate2);
    point_mul_lambda_inplace(tmp1.as_mut_ptr());
    let mut p_copy_14: [uint64_t; 15] = [
        0 as libc::c_uint as uint64_t,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
    ];
    memcpy(
        p_copy_14.as_mut_ptr() as *mut libc::c_void,
        out as *const libc::c_void,
        (15 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    Hacl_Impl_K256_PointAdd_point_add(out, p_copy_14.as_mut_ptr(), tmp1.as_mut_ptr());
    let mut tmp10: [uint64_t; 15] = [
        0 as libc::c_uint as uint64_t,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
    ];
    let mut i2: uint32_t = 125 as libc::c_uint;
    let mut bits_c1: uint64_t = Hacl_Bignum_Lib_bn_get_bits_u64(
        4 as libc::c_uint,
        r3,
        i2,
        5 as libc::c_uint,
    );
    let mut bits_l321: uint32_t = bits_c1 as uint32_t;
    let mut a_bits_l1: *const uint64_t = table2
        .as_mut_ptr()
        .offset(bits_l321.wrapping_mul(15 as libc::c_uint) as isize);
    memcpy(
        tmp0.as_mut_ptr() as *mut libc::c_void,
        a_bits_l1 as *mut uint64_t as *const libc::c_void,
        (15 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    point_negate_conditional_vartime(tmp0.as_mut_ptr(), is_negate3);
    let mut i3: uint32_t = 125 as libc::c_uint;
    let mut bits_c2: uint64_t = Hacl_Bignum_Lib_bn_get_bits_u64(
        4 as libc::c_uint,
        r4,
        i3,
        5 as libc::c_uint,
    );
    let mut bits_l322: uint32_t = bits_c2 as uint32_t;
    let mut a_bits_l2: *const uint64_t = table2
        .as_mut_ptr()
        .offset(bits_l322.wrapping_mul(15 as libc::c_uint) as isize);
    memcpy(
        tmp10.as_mut_ptr() as *mut libc::c_void,
        a_bits_l2 as *mut uint64_t as *const libc::c_void,
        (15 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    point_negate_conditional_vartime(tmp10.as_mut_ptr(), is_negate4);
    point_mul_lambda_inplace(tmp10.as_mut_ptr());
    let mut p_copy0_14: [uint64_t; 15] = [
        0 as libc::c_uint as uint64_t,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
    ];
    memcpy(
        p_copy0_14.as_mut_ptr() as *mut libc::c_void,
        tmp0.as_mut_ptr() as *const libc::c_void,
        (15 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    Hacl_Impl_K256_PointAdd_point_add(
        tmp0.as_mut_ptr(),
        p_copy0_14.as_mut_ptr(),
        tmp10.as_mut_ptr(),
    );
    let mut p_copy1: [uint64_t; 15] = [
        0 as libc::c_uint as uint64_t,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
    ];
    memcpy(
        p_copy1.as_mut_ptr() as *mut libc::c_void,
        out as *const libc::c_void,
        (15 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    Hacl_Impl_K256_PointAdd_point_add(out, p_copy1.as_mut_ptr(), tmp0.as_mut_ptr());
    let mut tmp2: [uint64_t; 15] = [
        0 as libc::c_uint as uint64_t,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
    ];
    let mut i_0: uint32_t = 0 as libc::c_uint;
    while i_0 < 25 as libc::c_uint {
        let mut i4: uint32_t = 0 as libc::c_uint;
        let mut p_copy2: [uint64_t; 15] = [
            0 as libc::c_uint as uint64_t,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
        ];
        memcpy(
            p_copy2.as_mut_ptr() as *mut libc::c_void,
            out as *const libc::c_void,
            (15 as libc::c_uint as libc::c_ulong)
                .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
        );
        Hacl_Impl_K256_PointDouble_point_double(out, p_copy2.as_mut_ptr());
        i4 = (i4 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut p_copy2_0: [uint64_t; 15] = [
            0 as libc::c_uint as uint64_t,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
        ];
        memcpy(
            p_copy2_0.as_mut_ptr() as *mut libc::c_void,
            out as *const libc::c_void,
            (15 as libc::c_uint as libc::c_ulong)
                .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
        );
        Hacl_Impl_K256_PointDouble_point_double(out, p_copy2_0.as_mut_ptr());
        i4 = (i4 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut p_copy2_1: [uint64_t; 15] = [
            0 as libc::c_uint as uint64_t,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
        ];
        memcpy(
            p_copy2_1.as_mut_ptr() as *mut libc::c_void,
            out as *const libc::c_void,
            (15 as libc::c_uint as libc::c_ulong)
                .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
        );
        Hacl_Impl_K256_PointDouble_point_double(out, p_copy2_1.as_mut_ptr());
        i4 = (i4 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut p_copy2_2: [uint64_t; 15] = [
            0 as libc::c_uint as uint64_t,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
        ];
        memcpy(
            p_copy2_2.as_mut_ptr() as *mut libc::c_void,
            out as *const libc::c_void,
            (15 as libc::c_uint as libc::c_ulong)
                .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
        );
        Hacl_Impl_K256_PointDouble_point_double(out, p_copy2_2.as_mut_ptr());
        i4 = (i4 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut p_copy2_3: [uint64_t; 15] = [
            0 as libc::c_uint as uint64_t,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
        ];
        memcpy(
            p_copy2_3.as_mut_ptr() as *mut libc::c_void,
            out as *const libc::c_void,
            (15 as libc::c_uint as libc::c_ulong)
                .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
        );
        Hacl_Impl_K256_PointDouble_point_double(out, p_copy2_3.as_mut_ptr());
        i4 = (i4 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut k: uint32_t = (125 as libc::c_uint)
            .wrapping_sub((5 as libc::c_uint).wrapping_mul(i_0))
            .wrapping_sub(5 as libc::c_uint);
        let mut bits_l: uint64_t = Hacl_Bignum_Lib_bn_get_bits_u64(
            4 as libc::c_uint,
            r4,
            k,
            5 as libc::c_uint,
        );
        let mut bits_l323: uint32_t = bits_l as uint32_t;
        let mut a_bits_l3: *const uint64_t = table2
            .as_mut_ptr()
            .offset(bits_l323.wrapping_mul(15 as libc::c_uint) as isize);
        memcpy(
            tmp2.as_mut_ptr() as *mut libc::c_void,
            a_bits_l3 as *mut uint64_t as *const libc::c_void,
            (15 as libc::c_uint as libc::c_ulong)
                .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
        );
        point_negate_conditional_vartime(tmp2.as_mut_ptr(), is_negate4);
        point_mul_lambda_inplace(tmp2.as_mut_ptr());
        let mut p_copy2_4: [uint64_t; 15] = [
            0 as libc::c_uint as uint64_t,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
        ];
        memcpy(
            p_copy2_4.as_mut_ptr() as *mut libc::c_void,
            out as *const libc::c_void,
            (15 as libc::c_uint as libc::c_ulong)
                .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
        );
        Hacl_Impl_K256_PointAdd_point_add(
            out,
            p_copy2_4.as_mut_ptr(),
            tmp2.as_mut_ptr(),
        );
        let mut k0: uint32_t = (125 as libc::c_uint)
            .wrapping_sub((5 as libc::c_uint).wrapping_mul(i_0))
            .wrapping_sub(5 as libc::c_uint);
        let mut bits_l0: uint64_t = Hacl_Bignum_Lib_bn_get_bits_u64(
            4 as libc::c_uint,
            r3,
            k0,
            5 as libc::c_uint,
        );
        let mut bits_l324: uint32_t = bits_l0 as uint32_t;
        let mut a_bits_l4: *const uint64_t = table2
            .as_mut_ptr()
            .offset(bits_l324.wrapping_mul(15 as libc::c_uint) as isize);
        memcpy(
            tmp2.as_mut_ptr() as *mut libc::c_void,
            a_bits_l4 as *mut uint64_t as *const libc::c_void,
            (15 as libc::c_uint as libc::c_ulong)
                .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
        );
        point_negate_conditional_vartime(tmp2.as_mut_ptr(), is_negate3);
        let mut p_copy3: [uint64_t; 15] = [
            0 as libc::c_uint as uint64_t,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
        ];
        memcpy(
            p_copy3.as_mut_ptr() as *mut libc::c_void,
            out as *const libc::c_void,
            (15 as libc::c_uint as libc::c_ulong)
                .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
        );
        Hacl_Impl_K256_PointAdd_point_add(out, p_copy3.as_mut_ptr(), tmp2.as_mut_ptr());
        let mut k1: uint32_t = (125 as libc::c_uint)
            .wrapping_sub((5 as libc::c_uint).wrapping_mul(i_0))
            .wrapping_sub(5 as libc::c_uint);
        let mut bits_l1: uint64_t = Hacl_Bignum_Lib_bn_get_bits_u64(
            4 as libc::c_uint,
            r2,
            k1,
            5 as libc::c_uint,
        );
        let mut bits_l325: uint32_t = bits_l1 as uint32_t;
        let mut a_bits_l5: *const uint64_t = Hacl_K256_PrecompTable_precomp_basepoint_table_w5
            .as_ptr()
            .offset(bits_l325.wrapping_mul(15 as libc::c_uint) as isize);
        memcpy(
            tmp2.as_mut_ptr() as *mut libc::c_void,
            a_bits_l5 as *mut uint64_t as *const libc::c_void,
            (15 as libc::c_uint as libc::c_ulong)
                .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
        );
        point_negate_conditional_vartime(tmp2.as_mut_ptr(), is_negate2);
        point_mul_lambda_inplace(tmp2.as_mut_ptr());
        let mut p_copy4: [uint64_t; 15] = [
            0 as libc::c_uint as uint64_t,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
        ];
        memcpy(
            p_copy4.as_mut_ptr() as *mut libc::c_void,
            out as *const libc::c_void,
            (15 as libc::c_uint as libc::c_ulong)
                .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
        );
        Hacl_Impl_K256_PointAdd_point_add(out, p_copy4.as_mut_ptr(), tmp2.as_mut_ptr());
        let mut k2: uint32_t = (125 as libc::c_uint)
            .wrapping_sub((5 as libc::c_uint).wrapping_mul(i_0))
            .wrapping_sub(5 as libc::c_uint);
        let mut bits_l2: uint64_t = Hacl_Bignum_Lib_bn_get_bits_u64(
            4 as libc::c_uint,
            r1,
            k2,
            5 as libc::c_uint,
        );
        let mut bits_l326: uint32_t = bits_l2 as uint32_t;
        let mut a_bits_l6: *const uint64_t = Hacl_K256_PrecompTable_precomp_basepoint_table_w5
            .as_ptr()
            .offset(bits_l326.wrapping_mul(15 as libc::c_uint) as isize);
        memcpy(
            tmp2.as_mut_ptr() as *mut libc::c_void,
            a_bits_l6 as *mut uint64_t as *const libc::c_void,
            (15 as libc::c_uint as libc::c_ulong)
                .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
        );
        point_negate_conditional_vartime(tmp2.as_mut_ptr(), is_negate1);
        let mut p_copy5: [uint64_t; 15] = [
            0 as libc::c_uint as uint64_t,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
        ];
        memcpy(
            p_copy5.as_mut_ptr() as *mut libc::c_void,
            out as *const libc::c_void,
            (15 as libc::c_uint as libc::c_ulong)
                .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
        );
        Hacl_Impl_K256_PointAdd_point_add(out, p_copy5.as_mut_ptr(), tmp2.as_mut_ptr());
        i_0 = i_0.wrapping_add(1);
        i_0;
    }
}
#[inline]
unsafe extern "C" fn check_ecmult_endo_split(
    mut r1: *mut uint64_t,
    mut r2: *mut uint64_t,
    mut r3: *mut uint64_t,
    mut r4: *mut uint64_t,
) -> bool {
    let mut f20: uint64_t = *r1.offset(2 as libc::c_uint as isize);
    let mut f30: uint64_t = *r1.offset(3 as libc::c_uint as isize);
    let mut b1: bool = f20 == 0 as libc::c_ulonglong && f30 == 0 as libc::c_ulonglong;
    let mut f21: uint64_t = *r2.offset(2 as libc::c_uint as isize);
    let mut f31: uint64_t = *r2.offset(3 as libc::c_uint as isize);
    let mut b2: bool = f21 == 0 as libc::c_ulonglong && f31 == 0 as libc::c_ulonglong;
    let mut f22: uint64_t = *r3.offset(2 as libc::c_uint as isize);
    let mut f32: uint64_t = *r3.offset(3 as libc::c_uint as isize);
    let mut b3: bool = f22 == 0 as libc::c_ulonglong && f32 == 0 as libc::c_ulonglong;
    let mut f2: uint64_t = *r4.offset(2 as libc::c_uint as isize);
    let mut f3: uint64_t = *r4.offset(3 as libc::c_uint as isize);
    let mut b4: bool = f2 == 0 as libc::c_ulonglong && f3 == 0 as libc::c_ulonglong;
    return b1 as libc::c_int != 0 && b2 as libc::c_int != 0 && b3 as libc::c_int != 0
        && b4 as libc::c_int != 0;
}
#[inline]
unsafe extern "C" fn point_mul_g_double_split_lambda_vartime(
    mut out: *mut uint64_t,
    mut scalar1: *mut uint64_t,
    mut scalar2: *mut uint64_t,
    mut p2: *mut uint64_t,
) {
    let mut g: [uint64_t; 15] = [
        0 as libc::c_uint as uint64_t,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
    ];
    let mut gx: *mut uint64_t = g.as_mut_ptr();
    let mut gy: *mut uint64_t = g.as_mut_ptr().offset(5 as libc::c_uint as isize);
    let mut gz: *mut uint64_t = g.as_mut_ptr().offset(10 as libc::c_uint as isize);
    *gx.offset(0 as libc::c_uint as isize) = 0x2815b16f81798 as libc::c_ulonglong;
    *gx.offset(1 as libc::c_uint as isize) = 0xdb2dce28d959f as libc::c_ulonglong;
    *gx.offset(2 as libc::c_uint as isize) = 0xe870b07029bfc as libc::c_ulonglong;
    *gx.offset(3 as libc::c_uint as isize) = 0xbbac55a06295c as libc::c_ulonglong;
    *gx.offset(4 as libc::c_uint as isize) = 0x79be667ef9dc as libc::c_ulonglong;
    *gy.offset(0 as libc::c_uint as isize) = 0x7d08ffb10d4b8 as libc::c_ulonglong;
    *gy.offset(1 as libc::c_uint as isize) = 0x48a68554199c4 as libc::c_ulonglong;
    *gy.offset(2 as libc::c_uint as isize) = 0xe1108a8fd17b4 as libc::c_ulonglong;
    *gy.offset(3 as libc::c_uint as isize) = 0xc4655da4fbfc0 as libc::c_ulonglong;
    *gy.offset(4 as libc::c_uint as isize) = 0x483ada7726a3 as libc::c_ulonglong;
    memset(
        gz as *mut libc::c_void,
        0 as libc::c_uint as libc::c_int,
        (5 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    *gz.offset(0 as libc::c_uint as isize) = 1 as libc::c_ulonglong;
    let mut r1234: [uint64_t; 16] = [
        0 as libc::c_uint as uint64_t,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
    ];
    let mut q1234: [uint64_t; 60] = [
        0 as libc::c_uint as uint64_t,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
    ];
    let mut r1: *mut uint64_t = r1234.as_mut_ptr();
    let mut r2: *mut uint64_t = r1234.as_mut_ptr().offset(4 as libc::c_uint as isize);
    let mut r3: *mut uint64_t = r1234.as_mut_ptr().offset(8 as libc::c_uint as isize);
    let mut r4: *mut uint64_t = r1234.as_mut_ptr().offset(12 as libc::c_uint as isize);
    let mut q1: *mut uint64_t = q1234.as_mut_ptr();
    let mut q2: *mut uint64_t = q1234.as_mut_ptr().offset(15 as libc::c_uint as isize);
    let mut q3: *mut uint64_t = q1234.as_mut_ptr().offset(30 as libc::c_uint as isize);
    let mut q4: *mut uint64_t = q1234.as_mut_ptr().offset(45 as libc::c_uint as isize);
    let mut scrut0: __bool_bool = ecmult_endo_split(
        r1,
        r2,
        q1,
        q2,
        scalar1,
        g.as_mut_ptr(),
    );
    let mut is_high10: bool = scrut0.fst;
    let mut is_high20: bool = scrut0.snd;
    let mut scrut: __bool_bool = ecmult_endo_split(r3, r4, q3, q4, scalar2, p2);
    let mut is_high30: bool = scrut.fst;
    let mut is_high40: bool = scrut.snd;
    let mut scrut1: __bool_bool_bool_bool = {
        let mut init = __bool_bool_bool_bool_s {
            fst: is_high10,
            snd: is_high20,
            thd: is_high30,
            f3: is_high40,
        };
        init
    };
    let mut is_high1: bool = scrut1.fst;
    let mut is_high2: bool = scrut1.snd;
    let mut is_high3: bool = scrut1.thd;
    let mut is_high4: bool = scrut1.f3;
    let mut is_r1234_valid: bool = check_ecmult_endo_split(r1, r2, r3, r4);
    if is_r1234_valid {
        point_mul_g_double_split_lambda_table(
            out,
            r1,
            r2,
            r3,
            r4,
            p2,
            is_high1,
            is_high2,
            is_high3,
            is_high4,
        );
    } else {
        point_mul_g_double_vartime(out, scalar1, scalar2, p2);
    };
}
#[inline]
unsafe extern "C" fn fmul_eq_vartime(
    mut r: *mut uint64_t,
    mut z: *mut uint64_t,
    mut x: *mut uint64_t,
) -> bool {
    let mut tmp: [uint64_t; 5] = [0 as libc::c_uint as uint64_t, 0, 0, 0, 0];
    Hacl_K256_Field_fmul(tmp.as_mut_ptr(), r, z);
    let mut f_copy: [uint64_t; 5] = [0 as libc::c_uint as uint64_t, 0, 0, 0, 0];
    memcpy(
        f_copy.as_mut_ptr() as *mut libc::c_void,
        tmp.as_mut_ptr() as *const libc::c_void,
        (5 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    Hacl_K256_Field_fnormalize(tmp.as_mut_ptr(), f_copy.as_mut_ptr());
    let mut b: bool = Hacl_K256_Field_is_felem_eq_vartime(tmp.as_mut_ptr(), x);
    return b;
}
#[no_mangle]
pub unsafe extern "C" fn Hacl_K256_ECDSA_ecdsa_sign_hashed_msg(
    mut signature: *mut uint8_t,
    mut msgHash: *mut uint8_t,
    mut private_key: *mut uint8_t,
    mut nonce: *mut uint8_t,
) -> bool {
    let mut oneq: [uint64_t; 4] = [
        0x1 as libc::c_ulonglong,
        0 as libc::c_ulonglong,
        0 as libc::c_ulonglong,
        0 as libc::c_ulonglong,
    ];
    let mut rsdk_q: [uint64_t; 16] = [
        0 as libc::c_uint as uint64_t,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
    ];
    let mut r_q: *mut uint64_t = rsdk_q.as_mut_ptr();
    let mut s_q: *mut uint64_t = rsdk_q.as_mut_ptr().offset(4 as libc::c_uint as isize);
    let mut d_a: *mut uint64_t = rsdk_q.as_mut_ptr().offset(8 as libc::c_uint as isize);
    let mut k_q: *mut uint64_t = rsdk_q.as_mut_ptr().offset(12 as libc::c_uint as isize);
    let mut is_b_valid0: uint64_t = load_qelem_check(d_a, private_key);
    let mut oneq10: [uint64_t; 4] = [
        0x1 as libc::c_ulonglong,
        0 as libc::c_ulonglong,
        0 as libc::c_ulonglong,
        0 as libc::c_ulonglong,
    ];
    let mut i: uint32_t = 0 as libc::c_uint;
    let mut uu____0: uint64_t = oneq10[i as usize];
    let mut x: uint64_t = uu____0 ^ is_b_valid0 & (*d_a.offset(i as isize) ^ uu____0);
    let mut os: *mut uint64_t = d_a;
    *os.offset(i as isize) = x;
    i = (i as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut uu____0_0: uint64_t = oneq10[i as usize];
    let mut x_0: uint64_t = uu____0_0
        ^ is_b_valid0 & (*d_a.offset(i as isize) ^ uu____0_0);
    let mut os_0: *mut uint64_t = d_a;
    *os_0.offset(i as isize) = x_0;
    i = (i as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut uu____0_1: uint64_t = oneq10[i as usize];
    let mut x_1: uint64_t = uu____0_1
        ^ is_b_valid0 & (*d_a.offset(i as isize) ^ uu____0_1);
    let mut os_1: *mut uint64_t = d_a;
    *os_1.offset(i as isize) = x_1;
    i = (i as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut uu____0_2: uint64_t = oneq10[i as usize];
    let mut x_2: uint64_t = uu____0_2
        ^ is_b_valid0 & (*d_a.offset(i as isize) ^ uu____0_2);
    let mut os_2: *mut uint64_t = d_a;
    *os_2.offset(i as isize) = x_2;
    i = (i as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut is_sk_valid: uint64_t = is_b_valid0;
    let mut is_b_valid: uint64_t = load_qelem_check(k_q, nonce);
    let mut oneq1: [uint64_t; 4] = [
        0x1 as libc::c_ulonglong,
        0 as libc::c_ulonglong,
        0 as libc::c_ulonglong,
        0 as libc::c_ulonglong,
    ];
    let mut i_0: uint32_t = 0 as libc::c_uint;
    let mut uu____1: uint64_t = oneq1[i_0 as usize];
    let mut x_3: uint64_t = uu____1 ^ is_b_valid & (*k_q.offset(i_0 as isize) ^ uu____1);
    let mut os_3: *mut uint64_t = k_q;
    *os_3.offset(i_0 as isize) = x_3;
    i_0 = (i_0 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut uu____1_0: uint64_t = oneq1[i_0 as usize];
    let mut x_4: uint64_t = uu____1_0
        ^ is_b_valid & (*k_q.offset(i_0 as isize) ^ uu____1_0);
    let mut os_4: *mut uint64_t = k_q;
    *os_4.offset(i_0 as isize) = x_4;
    i_0 = (i_0 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut uu____1_1: uint64_t = oneq1[i_0 as usize];
    let mut x_5: uint64_t = uu____1_1
        ^ is_b_valid & (*k_q.offset(i_0 as isize) ^ uu____1_1);
    let mut os_5: *mut uint64_t = k_q;
    *os_5.offset(i_0 as isize) = x_5;
    i_0 = (i_0 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut uu____1_2: uint64_t = oneq1[i_0 as usize];
    let mut x_6: uint64_t = uu____1_2
        ^ is_b_valid & (*k_q.offset(i_0 as isize) ^ uu____1_2);
    let mut os_6: *mut uint64_t = k_q;
    *os_6.offset(i_0 as isize) = x_6;
    i_0 = (i_0 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut is_nonce_valid: uint64_t = is_b_valid;
    let mut are_sk_nonce_valid: uint64_t = is_sk_valid & is_nonce_valid;
    let mut tmp: [uint64_t; 5] = [0 as libc::c_uint as uint64_t, 0, 0, 0, 0];
    let mut x_bytes: [uint8_t; 32] = [
        0 as libc::c_uint as uint8_t,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
    ];
    let mut p: [uint64_t; 15] = [
        0 as libc::c_uint as uint64_t,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
    ];
    point_mul_g(p.as_mut_ptr(), k_q);
    to_aff_point_x(tmp.as_mut_ptr(), p.as_mut_ptr());
    Hacl_K256_Field_store_felem(x_bytes.as_mut_ptr(), tmp.as_mut_ptr());
    load_qelem_modq(r_q, x_bytes.as_mut_ptr());
    let mut z: [uint64_t; 4] = [0 as libc::c_uint as uint64_t, 0, 0, 0];
    let mut kinv: [uint64_t; 4] = [0 as libc::c_uint as uint64_t, 0, 0, 0];
    load_qelem_modq(z.as_mut_ptr(), msgHash);
    qinv(kinv.as_mut_ptr(), k_q);
    qmul(s_q, r_q, d_a);
    let mut f2_copy: [uint64_t; 4] = [0 as libc::c_uint as uint64_t, 0, 0, 0];
    memcpy(
        f2_copy.as_mut_ptr() as *mut libc::c_void,
        s_q as *const libc::c_void,
        (4 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    qadd(s_q, z.as_mut_ptr(), f2_copy.as_mut_ptr());
    let mut f2_copy0: [uint64_t; 4] = [0 as libc::c_uint as uint64_t, 0, 0, 0];
    memcpy(
        f2_copy0.as_mut_ptr() as *mut libc::c_void,
        s_q as *const libc::c_void,
        (4 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    qmul(s_q, kinv.as_mut_ptr(), f2_copy0.as_mut_ptr());
    store_qelem(signature, r_q);
    store_qelem(signature.offset(32 as libc::c_uint as isize), s_q);
    let mut is_r_zero: uint64_t = is_qelem_zero(r_q);
    let mut is_s_zero: uint64_t = is_qelem_zero(s_q);
    let mut m: uint64_t = are_sk_nonce_valid & (!is_r_zero & !is_s_zero);
    let mut res: bool = m == 0xffffffffffffffff as libc::c_ulonglong;
    return res;
}
#[no_mangle]
pub unsafe extern "C" fn Hacl_K256_ECDSA_ecdsa_sign_sha256(
    mut signature: *mut uint8_t,
    mut msg_len: uint32_t,
    mut msg: *mut uint8_t,
    mut private_key: *mut uint8_t,
    mut nonce: *mut uint8_t,
) -> bool {
    let mut msgHash: [uint8_t; 32] = [
        0 as libc::c_uint as uint8_t,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
    ];
    Hacl_Hash_SHA2_hash_256(msgHash.as_mut_ptr(), msg, msg_len);
    let mut b: bool = Hacl_K256_ECDSA_ecdsa_sign_hashed_msg(
        signature,
        msgHash.as_mut_ptr(),
        private_key,
        nonce,
    );
    return b;
}
#[no_mangle]
pub unsafe extern "C" fn Hacl_K256_ECDSA_ecdsa_verify_hashed_msg(
    mut m: *mut uint8_t,
    mut public_key: *mut uint8_t,
    mut signature: *mut uint8_t,
) -> bool {
    let mut tmp: [uint64_t; 35] = [
        0 as libc::c_uint as uint64_t,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
    ];
    let mut pk: *mut uint64_t = tmp.as_mut_ptr();
    let mut r_q: *mut uint64_t = tmp.as_mut_ptr().offset(15 as libc::c_uint as isize);
    let mut s_q: *mut uint64_t = tmp.as_mut_ptr().offset(19 as libc::c_uint as isize);
    let mut u1: *mut uint64_t = tmp.as_mut_ptr().offset(23 as libc::c_uint as isize);
    let mut u2: *mut uint64_t = tmp.as_mut_ptr().offset(27 as libc::c_uint as isize);
    let mut m_q: *mut uint64_t = tmp.as_mut_ptr().offset(31 as libc::c_uint as isize);
    let mut is_pk_valid: bool = load_point_vartime(pk, public_key);
    let mut is_r_valid: bool = load_qelem_vartime(r_q, signature);
    let mut is_s_valid: bool = load_qelem_vartime(
        s_q,
        signature.offset(32 as libc::c_uint as isize),
    );
    let mut is_rs_valid: bool = is_r_valid as libc::c_int != 0
        && is_s_valid as libc::c_int != 0;
    load_qelem_modq(m_q, m);
    if !(is_pk_valid as libc::c_int != 0 && is_rs_valid as libc::c_int != 0) {
        return 0 as libc::c_int != 0;
    }
    let mut sinv: [uint64_t; 4] = [0 as libc::c_uint as uint64_t, 0, 0, 0];
    qinv(sinv.as_mut_ptr(), s_q);
    qmul(u1, m_q, sinv.as_mut_ptr());
    qmul(u2, r_q, sinv.as_mut_ptr());
    let mut res: [uint64_t; 15] = [
        0 as libc::c_uint as uint64_t,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
    ];
    point_mul_g_double_split_lambda_vartime(res.as_mut_ptr(), u1, u2, pk);
    let mut tmp1: [uint64_t; 5] = [0 as libc::c_uint as uint64_t, 0, 0, 0, 0];
    let mut pz: *mut uint64_t = res.as_mut_ptr().offset(10 as libc::c_uint as isize);
    Hacl_K256_Field_fnormalize(tmp1.as_mut_ptr(), pz);
    let mut b: bool = Hacl_K256_Field_is_felem_zero_vartime(tmp1.as_mut_ptr());
    if b {
        return 0 as libc::c_int != 0;
    }
    let mut x: *mut uint64_t = res.as_mut_ptr();
    let mut z: *mut uint64_t = res.as_mut_ptr().offset(10 as libc::c_uint as isize);
    let mut r_bytes: [uint8_t; 32] = [
        0 as libc::c_uint as uint8_t,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
    ];
    let mut r_fe: [uint64_t; 5] = [0 as libc::c_uint as uint64_t, 0, 0, 0, 0];
    let mut tmp_q: [uint64_t; 5] = [0 as libc::c_uint as uint64_t, 0, 0, 0, 0];
    let mut tmp_x: [uint64_t; 5] = [0 as libc::c_uint as uint64_t, 0, 0, 0, 0];
    store_qelem(r_bytes.as_mut_ptr(), r_q);
    Hacl_K256_Field_load_felem(r_fe.as_mut_ptr(), r_bytes.as_mut_ptr());
    Hacl_K256_Field_fnormalize(tmp_x.as_mut_ptr(), x);
    let mut is_rz_x: bool = fmul_eq_vartime(r_fe.as_mut_ptr(), z, tmp_x.as_mut_ptr());
    if !is_rz_x {
        let mut is_r_lt_p_m_q: bool = Hacl_K256_Field_is_felem_lt_prime_minus_order_vartime(
            r_fe.as_mut_ptr(),
        );
        if is_r_lt_p_m_q {
            tmp_q[0 as libc::c_uint as usize] = 0x25e8cd0364141 as libc::c_ulonglong;
            tmp_q[1 as libc::c_uint as usize] = 0xe6af48a03bbfd as libc::c_ulonglong;
            tmp_q[2 as libc::c_uint as usize] = 0xffffffebaaedc as libc::c_ulonglong;
            tmp_q[3 as libc::c_uint as usize] = 0xfffffffffffff as libc::c_ulonglong;
            tmp_q[4 as libc::c_uint as usize] = 0xffffffffffff as libc::c_ulonglong;
            let mut f2_copy: [uint64_t; 5] = [0 as libc::c_uint as uint64_t, 0, 0, 0, 0];
            memcpy(
                f2_copy.as_mut_ptr() as *mut libc::c_void,
                tmp_q.as_mut_ptr() as *const libc::c_void,
                (5 as libc::c_uint as libc::c_ulong)
                    .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
            );
            Hacl_K256_Field_fadd(
                tmp_q.as_mut_ptr(),
                r_fe.as_mut_ptr(),
                f2_copy.as_mut_ptr(),
            );
            return fmul_eq_vartime(tmp_q.as_mut_ptr(), z, tmp_x.as_mut_ptr());
        }
        return 0 as libc::c_int != 0;
    }
    return 1 as libc::c_int != 0;
}
#[no_mangle]
pub unsafe extern "C" fn Hacl_K256_ECDSA_ecdsa_verify_sha256(
    mut msg_len: uint32_t,
    mut msg: *mut uint8_t,
    mut public_key: *mut uint8_t,
    mut signature: *mut uint8_t,
) -> bool {
    let mut mHash: [uint8_t; 32] = [
        0 as libc::c_uint as uint8_t,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
    ];
    Hacl_Hash_SHA2_hash_256(mHash.as_mut_ptr(), msg, msg_len);
    let mut b: bool = Hacl_K256_ECDSA_ecdsa_verify_hashed_msg(
        mHash.as_mut_ptr(),
        public_key,
        signature,
    );
    return b;
}
#[no_mangle]
pub unsafe extern "C" fn Hacl_K256_ECDSA_secp256k1_ecdsa_signature_normalize(
    mut signature: *mut uint8_t,
) -> bool {
    let mut s_q: [uint64_t; 4] = [0 as libc::c_uint as uint64_t, 0, 0, 0];
    let mut s: *mut uint8_t = signature.offset(32 as libc::c_uint as isize);
    let mut is_sk_valid: bool = load_qelem_vartime(s_q.as_mut_ptr(), s);
    if !is_sk_valid {
        return 0 as libc::c_int != 0;
    }
    let mut is_sk_lt_q_halved: bool = is_qelem_le_q_halved_vartime(s_q.as_mut_ptr());
    qnegate_conditional_vartime(s_q.as_mut_ptr(), !is_sk_lt_q_halved);
    store_qelem(signature.offset(32 as libc::c_uint as isize), s_q.as_mut_ptr());
    return 1 as libc::c_int != 0;
}
#[no_mangle]
pub unsafe extern "C" fn Hacl_K256_ECDSA_secp256k1_ecdsa_is_signature_normalized(
    mut signature: *mut uint8_t,
) -> bool {
    let mut s_q: [uint64_t; 4] = [0 as libc::c_uint as uint64_t, 0, 0, 0];
    let mut s: *mut uint8_t = signature.offset(32 as libc::c_uint as isize);
    let mut is_s_valid: bool = load_qelem_vartime(s_q.as_mut_ptr(), s);
    let mut is_s_lt_q_halved: bool = is_qelem_le_q_halved_vartime(s_q.as_mut_ptr());
    return is_s_valid as libc::c_int != 0 && is_s_lt_q_halved as libc::c_int != 0;
}
#[no_mangle]
pub unsafe extern "C" fn Hacl_K256_ECDSA_secp256k1_ecdsa_sign_hashed_msg(
    mut signature: *mut uint8_t,
    mut msgHash: *mut uint8_t,
    mut private_key: *mut uint8_t,
    mut nonce: *mut uint8_t,
) -> bool {
    let mut b: bool = Hacl_K256_ECDSA_ecdsa_sign_hashed_msg(
        signature,
        msgHash,
        private_key,
        nonce,
    );
    if b {
        return Hacl_K256_ECDSA_secp256k1_ecdsa_signature_normalize(signature);
    }
    return 0 as libc::c_int != 0;
}
#[no_mangle]
pub unsafe extern "C" fn Hacl_K256_ECDSA_secp256k1_ecdsa_sign_sha256(
    mut signature: *mut uint8_t,
    mut msg_len: uint32_t,
    mut msg: *mut uint8_t,
    mut private_key: *mut uint8_t,
    mut nonce: *mut uint8_t,
) -> bool {
    let mut msgHash: [uint8_t; 32] = [
        0 as libc::c_uint as uint8_t,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
    ];
    Hacl_Hash_SHA2_hash_256(msgHash.as_mut_ptr(), msg, msg_len);
    let mut b: bool = Hacl_K256_ECDSA_secp256k1_ecdsa_sign_hashed_msg(
        signature,
        msgHash.as_mut_ptr(),
        private_key,
        nonce,
    );
    return b;
}
#[no_mangle]
pub unsafe extern "C" fn Hacl_K256_ECDSA_secp256k1_ecdsa_verify_hashed_msg(
    mut msgHash: *mut uint8_t,
    mut public_key: *mut uint8_t,
    mut signature: *mut uint8_t,
) -> bool {
    let mut is_s_normalized: bool = Hacl_K256_ECDSA_secp256k1_ecdsa_is_signature_normalized(
        signature,
    );
    if !is_s_normalized {
        return 0 as libc::c_int != 0;
    }
    return Hacl_K256_ECDSA_ecdsa_verify_hashed_msg(msgHash, public_key, signature);
}
#[no_mangle]
pub unsafe extern "C" fn Hacl_K256_ECDSA_secp256k1_ecdsa_verify_sha256(
    mut msg_len: uint32_t,
    mut msg: *mut uint8_t,
    mut public_key: *mut uint8_t,
    mut signature: *mut uint8_t,
) -> bool {
    let mut mHash: [uint8_t; 32] = [
        0 as libc::c_uint as uint8_t,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
    ];
    Hacl_Hash_SHA2_hash_256(mHash.as_mut_ptr(), msg, msg_len);
    let mut b: bool = Hacl_K256_ECDSA_secp256k1_ecdsa_verify_hashed_msg(
        mHash.as_mut_ptr(),
        public_key,
        signature,
    );
    return b;
}
#[no_mangle]
pub unsafe extern "C" fn Hacl_K256_ECDSA_public_key_uncompressed_to_raw(
    mut pk_raw: *mut uint8_t,
    mut pk: *mut uint8_t,
) -> bool {
    let mut pk0: uint8_t = *pk.offset(0 as libc::c_uint as isize);
    if pk0 as libc::c_uint != 0x4 as libc::c_uint {
        return 0 as libc::c_int != 0;
    }
    memcpy(
        pk_raw as *mut libc::c_void,
        pk.offset(1 as libc::c_uint as isize) as *const libc::c_void,
        (64 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
    );
    return 1 as libc::c_int != 0;
}
#[no_mangle]
pub unsafe extern "C" fn Hacl_K256_ECDSA_public_key_uncompressed_from_raw(
    mut pk: *mut uint8_t,
    mut pk_raw: *mut uint8_t,
) {
    *pk.offset(0 as libc::c_uint as isize) = 0x4 as libc::c_uint as uint8_t;
    memcpy(
        pk.offset(1 as libc::c_uint as isize) as *mut libc::c_void,
        pk_raw as *const libc::c_void,
        (64 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
    );
}
#[no_mangle]
pub unsafe extern "C" fn Hacl_K256_ECDSA_public_key_compressed_to_raw(
    mut pk_raw: *mut uint8_t,
    mut pk: *mut uint8_t,
) -> bool {
    let mut xa: [uint64_t; 5] = [0 as libc::c_uint as uint64_t, 0, 0, 0, 0];
    let mut ya: [uint64_t; 5] = [0 as libc::c_uint as uint64_t, 0, 0, 0, 0];
    let mut b: bool = aff_point_decompress_vartime(xa.as_mut_ptr(), ya.as_mut_ptr(), pk);
    let mut pk_xb: *mut uint8_t = pk.offset(1 as libc::c_uint as isize);
    if b {
        memcpy(
            pk_raw as *mut libc::c_void,
            pk_xb as *const libc::c_void,
            (32 as libc::c_uint as libc::c_ulong)
                .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
        );
        Hacl_K256_Field_store_felem(
            pk_raw.offset(32 as libc::c_uint as isize),
            ya.as_mut_ptr(),
        );
    }
    return b;
}
#[no_mangle]
pub unsafe extern "C" fn Hacl_K256_ECDSA_public_key_compressed_from_raw(
    mut pk: *mut uint8_t,
    mut pk_raw: *mut uint8_t,
) {
    let mut pk_x: *mut uint8_t = pk_raw;
    let mut pk_y: *mut uint8_t = pk_raw.offset(32 as libc::c_uint as isize);
    let mut x0: uint8_t = *pk_y.offset(31 as libc::c_uint as isize);
    let mut is_pk_y_odd: bool = x0 as uint32_t & 1 as libc::c_uint == 1 as libc::c_uint;
    let mut ite: uint8_t = 0;
    if is_pk_y_odd {
        ite = 0x3 as libc::c_uint as uint8_t;
    } else {
        ite = 0x2 as libc::c_uint as uint8_t;
    }
    *pk.offset(0 as libc::c_uint as isize) = ite;
    memcpy(
        pk.offset(1 as libc::c_uint as isize) as *mut libc::c_void,
        pk_x as *const libc::c_void,
        (32 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
    );
}
#[no_mangle]
pub unsafe extern "C" fn Hacl_K256_ECDSA_is_public_key_valid(
    mut public_key: *mut uint8_t,
) -> bool {
    let mut p: [uint64_t; 15] = [
        0 as libc::c_uint as uint64_t,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
    ];
    let mut is_pk_valid: bool = load_point_vartime(p.as_mut_ptr(), public_key);
    return is_pk_valid;
}
#[no_mangle]
pub unsafe extern "C" fn Hacl_K256_ECDSA_is_private_key_valid(
    mut private_key: *mut uint8_t,
) -> bool {
    let mut s_q: [uint64_t; 4] = [0 as libc::c_uint as uint64_t, 0, 0, 0];
    let mut res: uint64_t = load_qelem_check(s_q.as_mut_ptr(), private_key);
    return res == 0xffffffffffffffff as libc::c_ulonglong;
}
#[no_mangle]
pub unsafe extern "C" fn Hacl_K256_ECDSA_secret_to_public(
    mut public_key: *mut uint8_t,
    mut private_key: *mut uint8_t,
) -> bool {
    let mut tmp: [uint64_t; 19] = [
        0 as libc::c_uint as uint64_t,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
    ];
    let mut pk: *mut uint64_t = tmp.as_mut_ptr();
    let mut sk: *mut uint64_t = tmp.as_mut_ptr().offset(15 as libc::c_uint as isize);
    let mut is_b_valid: uint64_t = load_qelem_check(sk, private_key);
    let mut oneq: [uint64_t; 4] = [
        0x1 as libc::c_ulonglong,
        0 as libc::c_ulonglong,
        0 as libc::c_ulonglong,
        0 as libc::c_ulonglong,
    ];
    let mut i: uint32_t = 0 as libc::c_uint;
    let mut uu____0: uint64_t = oneq[i as usize];
    let mut x: uint64_t = uu____0 ^ is_b_valid & (*sk.offset(i as isize) ^ uu____0);
    let mut os: *mut uint64_t = sk;
    *os.offset(i as isize) = x;
    i = (i as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut uu____0_0: uint64_t = oneq[i as usize];
    let mut x_0: uint64_t = uu____0_0
        ^ is_b_valid & (*sk.offset(i as isize) ^ uu____0_0);
    let mut os_0: *mut uint64_t = sk;
    *os_0.offset(i as isize) = x_0;
    i = (i as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut uu____0_1: uint64_t = oneq[i as usize];
    let mut x_1: uint64_t = uu____0_1
        ^ is_b_valid & (*sk.offset(i as isize) ^ uu____0_1);
    let mut os_1: *mut uint64_t = sk;
    *os_1.offset(i as isize) = x_1;
    i = (i as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut uu____0_2: uint64_t = oneq[i as usize];
    let mut x_2: uint64_t = uu____0_2
        ^ is_b_valid & (*sk.offset(i as isize) ^ uu____0_2);
    let mut os_2: *mut uint64_t = sk;
    *os_2.offset(i as isize) = x_2;
    i = (i as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut is_sk_valid: uint64_t = is_b_valid;
    point_mul_g(pk, sk);
    Hacl_Impl_K256_Point_point_store(public_key, pk);
    return is_sk_valid == 0xffffffffffffffff as libc::c_ulonglong;
}
#[no_mangle]
pub unsafe extern "C" fn Hacl_K256_ECDSA_ecdh(
    mut shared_secret: *mut uint8_t,
    mut their_pubkey: *mut uint8_t,
    mut private_key: *mut uint8_t,
) -> bool {
    let mut tmp: [uint64_t; 34] = [
        0 as libc::c_uint as uint64_t,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
    ];
    let mut pk: *mut uint64_t = tmp.as_mut_ptr();
    let mut ss: *mut uint64_t = tmp.as_mut_ptr().offset(15 as libc::c_uint as isize);
    let mut sk: *mut uint64_t = tmp.as_mut_ptr().offset(30 as libc::c_uint as isize);
    let mut is_pk_valid: bool = load_point_vartime(pk, their_pubkey);
    let mut is_b_valid: uint64_t = load_qelem_check(sk, private_key);
    let mut oneq: [uint64_t; 4] = [
        0x1 as libc::c_ulonglong,
        0 as libc::c_ulonglong,
        0 as libc::c_ulonglong,
        0 as libc::c_ulonglong,
    ];
    let mut i: uint32_t = 0 as libc::c_uint;
    let mut uu____0: uint64_t = oneq[i as usize];
    let mut x: uint64_t = uu____0 ^ is_b_valid & (*sk.offset(i as isize) ^ uu____0);
    let mut os: *mut uint64_t = sk;
    *os.offset(i as isize) = x;
    i = (i as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut uu____0_0: uint64_t = oneq[i as usize];
    let mut x_0: uint64_t = uu____0_0
        ^ is_b_valid & (*sk.offset(i as isize) ^ uu____0_0);
    let mut os_0: *mut uint64_t = sk;
    *os_0.offset(i as isize) = x_0;
    i = (i as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut uu____0_1: uint64_t = oneq[i as usize];
    let mut x_1: uint64_t = uu____0_1
        ^ is_b_valid & (*sk.offset(i as isize) ^ uu____0_1);
    let mut os_1: *mut uint64_t = sk;
    *os_1.offset(i as isize) = x_1;
    i = (i as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut uu____0_2: uint64_t = oneq[i as usize];
    let mut x_2: uint64_t = uu____0_2
        ^ is_b_valid & (*sk.offset(i as isize) ^ uu____0_2);
    let mut os_2: *mut uint64_t = sk;
    *os_2.offset(i as isize) = x_2;
    i = (i as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut is_sk_valid: uint64_t = is_b_valid;
    if is_pk_valid {
        Hacl_Impl_K256_PointMul_point_mul(ss, sk, pk);
        Hacl_Impl_K256_Point_point_store(shared_secret, ss);
    }
    return is_sk_valid == 0xffffffffffffffff as libc::c_ulonglong
        && is_pk_valid as libc::c_int != 0;
}
