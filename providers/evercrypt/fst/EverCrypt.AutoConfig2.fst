module EverCrypt.AutoConfig2

module SC = EverCrypt.StaticConfig

module ST = FStar.HyperStack.ST
module HS = FStar.HyperStack
module B = LowStar.Buffer
module S = FStar.Seq
module SC = EverCrypt.StaticConfig

open FStar.HyperStack.ST

#set-options "--max_fuel 0 --max_ifuel 0"

(** Only partially specified; the flag may be false because it has been
  intentionally disabled by the client, for instance. *)

type flag (b: bool) =
  b':bool { b' ==> b }

(** Flags, cached in a mutable global reference *)

let eternal_pointer a = buf:B.buffer a { B.recallable buf /\ B.length buf = 1 }

unfold
let cached_flag (b: bool) = eternal_pointer (flag b)

let cpu_has_shaext: cached_flag X64.CPU_Features_s.sha_enabled =
  B.gcmalloc_of_list HS.root [ false ]
let cpu_has_aesni: cached_flag X64.CPU_Features_s.aesni_enabled =
  B.gcmalloc_of_list HS.root [ false ]
let cpu_has_pclmulqdq: cached_flag X64.CPU_Features_s.pclmulqdq_enabled =
  B.gcmalloc_of_list HS.root [ false ]
let cpu_has_avx2: cached_flag X64.CPU_Features_s.avx2_enabled =
  B.gcmalloc_of_list HS.root [ false ]
let cpu_has_avx: cached_flag X64.CPU_Features_s.avx_enabled =
  B.gcmalloc_of_list HS.root [ false ]
let cpu_has_bmi2: cached_flag X64.CPU_Features_s.bmi2_enabled =
  B.gcmalloc_of_list HS.root [ false ]
let cpu_has_adx: cached_flag X64.CPU_Features_s.adx_enabled =
  B.gcmalloc_of_list HS.root [ false ]

let user_wants_hacl: eternal_pointer bool = B.gcmalloc_of_list HS.root [ SC.hacl ]
let user_wants_vale: eternal_pointer bool = B.gcmalloc_of_list HS.root [ SC.vale ]
let user_wants_openssl: eternal_pointer bool = B.gcmalloc_of_list HS.root [ SC.openssl ]
let user_wants_bcrypt: eternal_pointer bool = B.gcmalloc_of_list HS.root [ SC.bcrypt ]

inline_for_extraction
let mk_getter #b (f: cached_flag b): getter b = fun () ->
  B.recall f;
  B.index f 0ul

let has_shaext = mk_getter cpu_has_shaext
let has_aesni = mk_getter cpu_has_aesni
let has_pclmulqdq = mk_getter cpu_has_pclmulqdq
let has_avx2 = mk_getter cpu_has_avx2
let has_avx = mk_getter cpu_has_avx
let has_bmi2 = mk_getter cpu_has_bmi2
let has_adx = mk_getter cpu_has_adx

let wants_vale () = B.recall user_wants_vale; B.index user_wants_vale 0ul
let wants_hacl () = B.recall user_wants_hacl; B.index user_wants_hacl 0ul
let wants_openssl () = B.recall user_wants_openssl; B.index user_wants_openssl 0ul
let wants_bcrypt () = B.recall user_wants_bcrypt; B.index user_wants_bcrypt 0ul

let fp () =
  B.loc_buffer cpu_has_shaext `B.loc_union`
  B.loc_buffer cpu_has_aesni `B.loc_union`
  B.loc_buffer cpu_has_pclmulqdq `B.loc_union`
  B.loc_buffer cpu_has_avx2 `B.loc_union`
  B.loc_buffer cpu_has_avx `B.loc_union`
  B.loc_buffer cpu_has_bmi2 `B.loc_union`
  B.loc_buffer cpu_has_adx `B.loc_union`
  B.loc_buffer user_wants_hacl `B.loc_union`
  B.loc_buffer user_wants_vale `B.loc_union`
  B.loc_buffer user_wants_openssl `B.loc_union`
  B.loc_buffer user_wants_bcrypt

let recall () =
  B.recall cpu_has_shaext;
  B.recall cpu_has_aesni;
  B.recall cpu_has_pclmulqdq;
  B.recall cpu_has_avx2;
  B.recall cpu_has_avx;
  B.recall cpu_has_bmi2;
  B.recall cpu_has_adx;
  B.recall user_wants_hacl;
  B.recall user_wants_vale;
  B.recall user_wants_openssl;
  B.recall user_wants_bcrypt

#set-options "--z3rlimit 50"
let init () =
  // TODO: use an && here once macros are improved
  if EverCrypt.TargetConfig.x64 then
    if SC.vale then begin
      if Cpuid_stdcalls.check_aesni () <> 0UL then begin
        B.recall cpu_has_aesni;
        B.upd cpu_has_aesni 0ul true;
        B.recall cpu_has_pclmulqdq;
        B.upd cpu_has_pclmulqdq 0ul true
      end;
      if Cpuid_stdcalls.check_sha () <> 0UL then begin
        B.recall cpu_has_shaext;
        B.upd cpu_has_shaext 0ul true
      end;
      if Cpuid_stdcalls.check_avx () <> 0UL then begin
        B.recall cpu_has_avx;
        B.upd cpu_has_avx 0ul true
      end;
      if Cpuid_stdcalls.check_avx2 () <> 0UL then begin
        B.recall cpu_has_avx2;
        B.upd cpu_has_avx2 0ul true
      end;
      if Cpuid_stdcalls.check_adx_bmi2 () <> 0UL then begin
        B.recall cpu_has_bmi2;
        B.upd cpu_has_bmi2 0ul true;
        B.recall cpu_has_adx;
        B.upd cpu_has_adx 0ul true
      end
    end


inline_for_extraction noextract
let mk_disabler (f: eternal_pointer bool { B.loc_includes (fp ()) (B.loc_buffer f) }): disabler = fun () ->
  B.recall f;
  B.upd f 0ul false

/// FIXME use mk_disabler
let disable_avx2 () = B.recall cpu_has_avx2; B.upd cpu_has_avx2 0ul false
let disable_avx () = B.recall cpu_has_avx; B.upd cpu_has_avx 0ul false
let disable_bmi2 () = B.recall cpu_has_bmi2; B.upd cpu_has_bmi2 0ul false
let disable_adx () = B.recall cpu_has_adx; B.upd cpu_has_adx 0ul false
let disable_shaext () = B.recall cpu_has_shaext; B.upd cpu_has_shaext 0ul false
let disable_aesni () = B.recall cpu_has_aesni; B.upd cpu_has_aesni 0ul false
let disable_pclmulqdq () = B.recall cpu_has_pclmulqdq; B.upd cpu_has_pclmulqdq 0ul false
let disable_vale = mk_disabler user_wants_vale
let disable_hacl = mk_disabler user_wants_hacl
let disable_openssl = mk_disabler user_wants_openssl
let disable_bcrypt = mk_disabler user_wants_bcrypt
