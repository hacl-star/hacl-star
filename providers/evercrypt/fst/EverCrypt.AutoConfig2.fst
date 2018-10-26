module EverCrypt.AutoConfig2

module HS = FStar.HyperStack
module B = LowStar.Buffer
module S = FStar.Seq

open FStar.HyperStack.ST

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

let user_wants_hacl: eternal_pointer bool = B.gcmalloc_of_list HS.root [ false ]
let user_wants_vale: eternal_pointer bool = B.gcmalloc_of_list HS.root [ false ]
let user_wants_openssl: eternal_pointer bool = B.gcmalloc_of_list HS.root [ false ]
let user_wants_bcrypt: eternal_pointer bool = B.gcmalloc_of_list HS.root [ false ]

inline_for_extraction
let mk_getter #b (f: cached_flag b): getter b = fun () ->
  B.recall f;
  B.index f 0ul

let has_shaext = mk_getter cpu_has_shaext
let has_aesni = mk_getter cpu_has_aesni

let wants_vale () = B.recall user_wants_vale; B.index user_wants_vale 0ul
let wants_hacl () = B.recall user_wants_hacl; B.index user_wants_hacl 0ul
let wants_openssl () = B.recall user_wants_openssl; B.index user_wants_openssl 0ul
let wants_bcrypt () = B.recall user_wants_bcrypt; B.index user_wants_bcrypt 0ul

let fp () =
  B.loc_union (B.loc_union (B.loc_union (B.loc_union (B.loc_union
    (B.loc_buffer cpu_has_shaext) (B.loc_buffer cpu_has_aesni))
    (B.loc_buffer user_wants_hacl)) (B.loc_buffer user_wants_vale))
    (B.loc_buffer user_wants_openssl)) (B.loc_buffer user_wants_bcrypt)

let recall () =
  B.recall cpu_has_shaext;
  B.recall cpu_has_aesni;
  B.recall user_wants_hacl;
  B.recall user_wants_vale;
  B.recall user_wants_openssl;
  B.recall user_wants_bcrypt

let init () =
  if Check_aesni_stdcall.check_aesni_stdcall () <> 0UL then begin
    B.recall cpu_has_aesni;
    B.upd cpu_has_aesni 0ul true
  end;
  if Check_sha_stdcall.check_sha_stdcall () <> 0UL then begin
    B.recall cpu_has_shaext;
    B.upd cpu_has_shaext 0ul true
  end

inline_for_extraction
let mk_disabler (f: eternal_pointer bool { B.loc_includes (fp ()) (B.loc_buffer f) }): disabler = fun () ->
  B.recall f;
  B.upd f 0ul false

let disable_shaext () = B.recall cpu_has_shaext; B.upd cpu_has_shaext 0ul false
let disable_aesni () = B.recall cpu_has_aesni; B.upd cpu_has_aesni 0ul false
let disable_vale = mk_disabler user_wants_vale
let disable_hacl = mk_disabler user_wants_hacl
let disable_openssl = mk_disabler user_wants_openssl
let disable_bcrypt = mk_disabler user_wants_bcrypt
