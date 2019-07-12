module Interop_Printer

#set-options "--initial_fuel 4 --initial_ifuel 2 --max_fuel 4 --max_ifuel 2"

type base_type =
  | TUInt8
  | TUInt64
  | TUInt128

type ty =
  | TGhost of string // Ghost parameter of type given as a string
  | TBuffer of base_type
  | TBase of base_type

type label = | Sec | Pub

type stack_slots = | Stk of nat

type arg = string * ty * label
type func_ty = string * list arg * stack_slots

type os = | Windows | Linux
type target = | X86

let calling_registers os target = match target with
  | X86 -> begin match os with
    | Windows -> ["rcx"; "rdx"; "r8"; "r9"]
    | Linux -> ["rdi"; "rsi"; "rdx"; "rcx"; "r8"; "r9"]
  end

let callee_saved os target = match target with
  | X86 -> begin match os with
    | Windows -> ["rbx"; "rbp"; "rdi"; "rsi"; "rsp"; "r12"; "r13"; "r14"; "r15"]
    | Linux -> ["rbx"; "rbp"; "r12"; "r13"; "r14"; "r15"]
  end

let xmm_callee_saved os target = match target with
  | X86 -> begin match os with
    | Windows -> ["xmm6"; "xmm7"; "xmm8"; "xmm9"; "xmm10"; "xmm11"; "xmm12"; "xmm13"; "xmm14"; "xmm15"]
    | Linux -> []
  end

let print_low_nat_ty = function
  | TUInt8 -> "nat8"
  | TUInt64 -> "nat64"
  | TUInt128 -> "nat128"

let print_low_ty ty t = match ty with
  | TGhost ty -> "Ghost.erased (" ^ ty ^ ")"
  | TBuffer ty -> if t = Pub then "b8" else "s8"
  | TBase ty -> print_low_nat_ty ty

let rec print_low_args = function
  | [] -> "Stack unit"
  | (a, ty, t)::q -> a ^ ":" ^ print_low_ty ty t ^ " -> " ^ print_low_args q

let rec print_low_args_and = function
  | [] -> ""
  | (a, ty, t)::q -> a ^ ":" ^ print_low_ty ty t ^ " -> " ^ print_low_args_and q

let rec print_args_list = function
  | [] -> ""
  | (a,ty, t)::q -> "(" ^ a ^ ":" ^ print_low_ty ty t ^ ") " ^ print_args_list q

let rec print_args_names = function
  | [] -> ""
  | (a, _, _)::q -> a ^ " " ^ print_args_names q

let rec print_args_names_reveal = function
  | [] -> ""
  | (a, TGhost _, _)::q -> "(Ghost.reveal " ^ a ^ ") " ^ print_args_names_reveal q
  | (a, _, _)::q -> a ^ " " ^ print_args_names_reveal q


let rec print_buffers_list = function
  | [] -> "[]"
  | (a,ty, _)::q ->
    (if TBuffer? ty then a ^ "::" else "") ^
    print_buffers_list q

let is_buffer arg =
  let _, ty, _ = arg in TBuffer? ty

let not_ghost (a, ty, _) = not (TGhost? ty)

let rec liveness heap args =
  let args = List.Tot.Base.filter is_buffer args in
  let rec aux heap = function
  | [] -> "True"
  | [(a,TBuffer ty, _)] -> "live " ^ heap ^ " " ^ a
  | [(a, TBase ty, _)] | [(a, TGhost ty, _)] -> "" // Should not happen
  | (a, TBuffer ty, _)::q -> "live " ^ heap ^ " " ^ a ^ " /\\ " ^ aux heap q
  | (a, TBase ty, _)::q | (a, TGhost ty, _)::q -> aux heap q // Should not happen
  in aux heap args

let print_base_type = function
  | TUInt8 -> "(TBase TUInt8)"
  | TUInt64 -> "(TBase TUInt64)"
  | TUInt128 -> "(TBase TUInt128)"

let single_length_t (arg: arg) = match arg with
  | (_, TBase _, _) | (_, TGhost _, _) -> ""
  | (a, TBuffer ty, _) -> "  length_t_eq " ^ print_base_type ty ^ " " ^ a ^ ";\n"

let rec print_length_t = function
  | [] -> ""
  | a::q -> single_length_t a ^ print_length_t q

let namelist_of_args args =
  let rec aux = function
  | [] -> ""
  | [a, _, _] -> a
  | (a, _, _)::q -> a ^ ";" ^ aux q in
  "[" ^ aux args ^ "]"

let disjoint (args:list arg) =  //AR: added an annotation, see #1502
  let args = List.Tot.Base.filter is_buffer args in
  "bufs_disjoint " ^ namelist_of_args args

let reg_to_low = function
  | "rax" -> "Rax"
  | "rbx" -> "Rbx"
  | "rcx" -> "Rcx"
  | "rdx" -> "Rdx"
  | "rsi" -> "Rsi"
  | "rdi" -> "Rdi"
  | "rbp" -> "Rbp"
  | "rsp" -> "Rsp"
  | "r8" -> "R8"
  | "r9" -> "R9"
  | "r10" -> "R10"
  | "r11" -> "R11"
  | "r12" -> "R12"
  | "r13" -> "R13"
  | "r14" -> "R14"
  | "r15" -> "R15"
  |  _ -> "error"

let print_low_calling_stack (args:list arg) (stkstart) =
  let rec aux (i:nat) (args:list arg) : Tot string (decreases %[args]) = match args with
    | [] -> ""
    | (_, TGhost _, _)::q -> aux i q // We ignore ghost parameters
    | (a, TBase _, _)::q -> "  let mem = buffer_write #(TBase TUInt64) stack_b " ^ (string_of_int (i+stkstart)) ^ " " ^ a ^ " mem in\n" ^ aux (i+1) q
    | (a, TBuffer _, _)::q -> "  let mem = buffer_write #(TBase TUInt64) stack_b " ^ (string_of_int (i+stkstart)) ^ " (addrs " ^ a ^ ") mem in\n" ^ aux (i+1) q
  in aux 0 args

let print_low_calling_args os target (args:list arg) stkstart =
  let rec aux regs (args:list arg) =
  match regs, args with
    | [], q -> "    | _ -> init_regs r end in\n" ^ print_low_calling_stack q stkstart
    | _, [] -> "    | _ -> init_regs r end in\n"
    | re, (_, TGhost _, _)::q -> aux re q // We ignore ghost parameters
    | r1::rn, (a, ty, _)::q -> "    | " ^ (reg_to_low r1) ^ " -> " ^
      (if TBuffer? ty then "addr_" ^ a else a) ^
      "\n" ^ aux rn q
  in aux (calling_registers os target) args

let print_low_callee_saved os target =
  let rec aux = function
    | [] -> ""
    | a::q -> "  assert(s0.regs " ^ (reg_to_low a) ^ " == s1.regs " ^ (reg_to_low a) ^ ");\n" ^ aux q
  in aux (callee_saved os target)

let xmm_to_low = function
  | "xmm0" -> "0"
  | "xmm1" -> "1"
  | "xmm2" -> "2"
  | "xmm3" -> "3"
  | "xmm4" -> "4"
  | "xmm5" -> "5"
  | "xmm6" -> "6"
  | "xmm7" -> "7"
  | "xmm8" -> "8"
  | "xmm9" -> "9"
  | "xmm10" -> "10"
  | "xmm11" -> "11"
  | "xmm12" -> "12"
  | "xmm13" -> "13"
  | "xmm14" -> "14"
  | "xmm15" -> "15"
  | _ -> "error"

let print_low_xmm_callee_saved os target =
  let rec aux = function
    | [] -> ""
    | a::q -> "  assert(s0.xmms " ^ (xmm_to_low a) ^ " == s1.xmms " ^ (xmm_to_low a) ^ ");\n" ^ aux q
  in aux (xmm_callee_saved os target)

let rec generate_low_addrs = function
  | [] -> ""
  | (a, TBuffer _, _)::q -> "  let addr_" ^ a ^ " = addrs " ^ a ^ " in\n" ^ generate_low_addrs q
  | _::q -> generate_low_addrs q

let size = function
  | TUInt8 -> "1"
  | TUInt64 -> "8"
  | TUInt128 -> "16"

let print_length = function
  | (_, TBase _, _) | (_, TGhost _, _) -> ""
  | (a, TBuffer ty, _) -> "length " ^ a ^ " % " ^ (size ty) ^ " == 0"

let print_lengths args =
 let rec aux = function
 | [] -> ""
 | [a] -> print_length a
 | a::q  -> print_length a ^ " /\\ " ^ aux q
 in aux (List.Tot.Base.filter is_buffer args)

let taint_of_label = function
  | Sec -> "Secret"
  | Pub -> "Public"

let create_taint_fun (args:list arg) =
  let rec aux args = match args with
  | [] -> "    Public "
  | (a, TBuffer _, t)::q -> "    if StrongExcludedMiddle.strong_excluded_middle (x == "^a^") then " ^ taint_of_label t ^ " else\n" ^ aux q
  | _::q -> aux q
  in "  let taint_func (x:b8) : GTot taint =\n" ^ aux args ^ "in\n"

let create_state os target args stack slots stkstart =
  create_taint_fun args ^
  "  let buffers = " ^ (if stack then "stack_b::" else "") ^ print_buffers_list args ^ " in\n" ^
  "  let (mem:mem) = {addrs = addrs; ptrs = buffers; hs = h0} in\n" ^
  generate_low_addrs args ^
  (if stack then "  let addr_stack:nat64 = addrs stack_b + " ^ (string_of_int (slots `op_Multiply` 8)) ^ " in\n" else "") ^
  "  let regs = fun r -> begin match r with\n" ^
  (if stack then "    | Rsp -> addr_stack\n" else "") ^
  (print_low_calling_args os target args stkstart) ^
  "  let xmms = init_xmms in\n" ^
  "  let s0 = {ok = true; regs = regs; xmms = xmms; flags = 0; mem = mem; memTaint = create_valid_memtaint mem buffers taint_func} in\n" ^
  print_length_t (if stack then ("stack_b", TBuffer TUInt64, Pub)::args else args)

let print_vale_bufferty = function
  | TUInt8 -> "buffer8"
  | TUInt64 -> "buffer64"
  | TUInt128 -> "buffer128"

let print_vale_ty = function
  | TUInt8 -> "nat8"
  | TUInt64 -> "nat64"
  | TUInt128 -> "quad32"

let print_vale_full_ty = function
  | TGhost ty -> "(" ^ ty ^ ")"
  | TBase ty -> print_vale_ty ty
  | TBuffer ty -> print_vale_bufferty ty

let rec print_args_vale_list = function
  | [] -> ""
  | (a,ty, _)::q -> "(" ^ a ^ ":" ^ print_vale_full_ty ty ^ ") " ^ print_args_vale_list q

let translate_lowstar os target (func:func_ty) =
  let name, args, Stk slots = func in
  let additional = (if os = Windows then 5 else 0) in
  let buffer_args = List.Tot.Base.filter is_buffer args in
  let real_args = List.Tot.Base.filter not_ghost args in
  let nbr_stack_args = List.Tot.Base.length real_args -
    List.Tot.Base.length (calling_registers os target) in
  let length_stack = (slots + additional + nbr_stack_args) `op_Multiply` 8 in
  let stack_needed = length_stack > 0 in
  let fuel_value = string_of_int (List.Tot.Base.length buffer_args + 3) in
  let implies_precond = if stack_needed then "B.length stack_b == " ^ string_of_int length_stack ^
    " /\ live h0 stack_b /\ buf_disjoint_from stack_b " ^ (namelist_of_args (buffer_args)) ^ " /\ "
  else "" in
  let stack_precond memname = if stack_needed then
    "/\ B.length stack_b == " ^ string_of_int length_stack ^
    " /\ live " ^ memname ^ " stack_b /\ buf_disjoint_from stack_b " ^ (namelist_of_args (buffer_args))
  else "" in
  let separator0 = if (List.Tot.Base.length buffer_args = 0) then "" else " /\\ " in
  let separator1 = if (List.Tot.Base.length buffer_args <= 1) then "" else " /\\ " in
  "module Vale_" ^ name ^
  "\n\nopen X64.Machine_s\nopen X64.Memory\nopen X64.Vale.State\nopen X64.Vale.Decls\n\n" ^
  "val va_code_" ^ name ^ ": unit -> va_code\n\n" ^
  "//TODO: Fill this
  //va_pre and va_post should correspond to the pre- and postconditions generated by Vale\n" ^
  "let va_pre (va_b0:va_code) (va_s0:va_state)" ^ (if stack_needed then " (stack_b:buffer64)\n" else "\n") ^
  (print_args_vale_list args) ^ " = True\n\n" ^
  "let va_post (va_b0:va_code) (va_s0:va_state) (va_sM:va_state) (va_fM:va_fuel)" ^
  (if stack_needed then " (stack_b:buffer64)\n" else "\n") ^
  (print_args_vale_list args) ^ " = True\n\n" ^
  "val va_lemma_" ^ name ^ "(va_b0:va_code) (va_s0:va_state)" ^
  (if stack_needed then " (stack_b:buffer64)\n" else "\n") ^
  (print_args_vale_list args) ^ ": Ghost ((va_sM:va_state) * (va_fM:va_fuel))\n  " ^
  "(requires va_pre va_b0 va_s0 " ^ (if stack_needed then "stack_b " else "") ^
  (print_args_names args) ^ ")\n  " ^
  "(ensures (fun (va_sM, va_fM) -> va_post va_b0 va_s0 va_sM va_fM " ^
  (if stack_needed then "stack_b " else "") ^
  (print_args_names args) ^ "))" ^
  "\n\n\n\n" ^
  "module " ^ name ^
  "\n\nopen LowStar.Buffer\nmodule B = LowStar.Buffer\nmodule BV = LowStar.BufferView\nopen LowStar.Modifies\nmodule M = LowStar.Modifies\nopen LowStar.ModifiesPat\nopen FStar.HyperStack.ST\nmodule HS = FStar.HyperStack\nmodule S8 = SecretByte\nopen Interop\nopen Words_s\nopen Types_s\nopen X64.Machine_s\nopen X64.Memory_s\nopen X64.Vale.State\nopen X64.Vale.Decls\nopen BufferViewHelpers\nopen Interop_assumptions\n#set-options \"--z3rlimit 40\"\n\n" ^
  "open Vale_" ^ name ^ "\n\n" ^
  "let b8 = B.buffer UInt8.t\n" ^
  "let s8 = B.buffer S8.t\n\n" ^
   "let rec loc_locs_disjoint_rec (l:b8) (ls:list b8) : Type0 =\n" ^
   "  match ls with\n" ^
   "  | [] -> True\n" ^
   "  | h::t -> M.loc_disjoint (M.loc_buffer l) (M.loc_buffer h) /\ loc_locs_disjoint_rec l t\n\n" ^
  "let rec locs_disjoint_rec (ls:list b8) : Type0 =\n"^
  "  match ls with\n"^
  "  | [] -> True\n" ^
  "  | h::t -> loc_locs_disjoint_rec h t /\ locs_disjoint_rec t\n\n" ^
  "unfold\nlet bufs_disjoint (ls:list b8) : Type0 = normalize (locs_disjoint_rec ls)\n\n" ^
  "unfold\nlet buf_disjoint_from (b:b8) (ls:list b8) : Type0 = normalize (loc_locs_disjoint_rec b ls)\n\n" ^
  "// TODO: Complete with your pre- and post-conditions\n" ^
  "let pre_cond (h:HS.mem) " ^ (print_args_list args) ^ "= " ^ (liveness "h" args) ^ separator1 ^ (disjoint args) ^ separator0 ^ (print_lengths args) ^ "\n" ^
  "let post_cond (h0:HS.mem) (h1:HS.mem) " ^ (print_args_list args) ^ "= "
    ^ (liveness "h0" args) ^ " /\\ " ^ (liveness "h1" args) ^ separator0 ^ (print_lengths args) ^ "\n\n" ^
  "#set-options \"--initial_fuel " ^ fuel_value ^ " --max_fuel " ^ fuel_value ^ " --initial_ifuel 2 --max_ifuel 2\"\n" ^
  "// TODO: Prove these two lemmas if they are not proven automatically\n" ^
  "let implies_pre (h0:HS.mem) " ^ (print_args_list args) ^
  (if stack_needed then " (stack_b:b8) " else "") ^
  ": Lemma\n" ^
  "  (requires pre_cond h0 " ^ (print_args_names args) ^ stack_precond "h0" ^ ")\n" ^
  "  (ensures (\n" ^ implies_precond ^ "(" ^
  (create_state os target args stack_needed slots (slots + additional)) ^
  "  va_pre (va_code_" ^ name ^ " ()) s0 " ^
  (if stack_needed then "stack_b " else "") ^
  (print_args_names_reveal args) ^ "))) =\n" ^
  print_length_t (if stack_needed then ("stack_b", TBuffer TUInt64, Pub)::args else args) ^
  "  ()\n\n" ^
  "let implies_post (va_s0:va_state) (va_sM:va_state) (va_fM:va_fuel) " ^ (print_args_list args) ^
  (if stack_needed then " (stack_b:b8)" else "") ^
  " : Lemma\n" ^
  "  (requires pre_cond va_s0.mem.hs " ^ (print_args_names args) ^ stack_precond "va_s0.mem.hs" ^ "/\\\n" ^
  "    va_post (va_code_" ^ name ^ " ()) va_s0 va_sM va_fM " ^
  (if stack_needed then "stack_b " else "") ^
  (print_args_names_reveal args) ^ ")\n" ^
  "  (ensures post_cond va_s0.mem.hs va_sM.mem.hs " ^ (print_args_names args) ^ ") =\n" ^
  print_length_t (if stack_needed then ("stack_b", TBuffer TUInt64, Pub)::args else args) ^
  "  ()\n\n" ^
  "val " ^ name ^ ": " ^ (print_low_args args) ^
  "\n\t(requires (fun h -> pre_cond h " ^ (print_args_names args) ^ "))\n\t" ^
  "(ensures (fun h0 _ h1 -> post_cond h0 h1 " ^ (print_args_names args) ^ "))\n\n" ^
  "val ghost_" ^ name ^ ": " ^ (print_low_args_and args) ^
  (if stack_needed then " stack_b:b8 -> " else "") ^
    "(h0:HS.mem{pre_cond h0 " ^ (print_args_names args) ^
    stack_precond "h0" ^
    "}) -> GTot (h1:HS.mem{post_cond h0 h1 " ^ (print_args_names args) ^ "})\n\n" ^
  "let ghost_" ^ name ^ " " ^ (print_args_names args) ^
  (if stack_needed then "stack_b " else "") ^ "h0 =\n" ^
  (create_state os target args stack_needed slots (slots+additional)) ^
  "  implies_pre h0 " ^ (print_args_names args) ^
  (if stack_needed then "stack_b " else "") ^ ";\n" ^
  "  let s1, f1 = va_lemma_" ^ name ^ " (va_code_" ^ name ^ " ()) s0 " ^
  (if stack_needed then "stack_b " else "") ^
  print_args_names_reveal args ^ " in\n" ^
  "  // Ensures that the Vale execution was correct\n" ^
  "  assert(s1.ok);\n" ^
  "  // Ensures that the callee_saved registers are correct\n" ^
  (print_low_callee_saved os target) ^ (print_low_xmm_callee_saved os target) ^
  "  // Ensures that va_code_" ^ name ^ " is actually Vale code, and that s1 is the result of executing this code\n" ^
  "  assert (va_ensure_total (va_code_" ^ name ^ " ()) s0 s1 f1);\n" ^
  "  implies_post s0 s1 f1 " ^ (print_args_names args) ^
  (if stack_needed then "stack_b " else "") ^ ";\n" ^
  "  s1.mem.hs\n\n" ^
  "let " ^ name ^ " " ^ (print_args_names args) ^ " =\n" ^
  (if stack_needed then "  push_frame();\n" ^
    "  let (stack_b:b8) = B.alloca (UInt8.uint_to_t 0) (UInt32.uint_to_t " ^ string_of_int length_stack ^ ") in\n"  else "") ^
  "  st_put (fun h -> pre_cond h " ^ (print_args_names args) ^ stack_precond "h" ^ ") (ghost_" ^ name ^ " " ^ (print_args_names args) ^
  (if stack_needed then "stack_b);\n  pop_frame()\n" else ")\n")

let print_vale_arg = function
  | (a, ty, _) -> "ghost " ^ a ^ ":" ^ print_vale_full_ty ty

let rec print_vale_args = function
  | [] -> ""
  | [arg] -> print_vale_arg arg
  | arg::q -> print_vale_arg arg ^ ", " ^ print_vale_args q

let rec print_vale_loc_buff = function
  | [] -> ""
  | [(_, TBase _, _)] | [(_, TGhost _, _)] -> ""
  | [(a, TBuffer _, _)] -> "loc_buffer("^a^")"
  | (a, TBuffer _, _)::q -> "loc_buffer("^a^"), " ^ print_vale_loc_buff q
  | a::q -> print_vale_loc_buff q

let rec print_buff_readable = function
  | [] -> ""
  | (a, TBuffer _, _)::q -> "        buffer_readable(mem, "^a^");\n" ^ print_buff_readable q
  | a::q -> print_buff_readable q

let print_ty_number = function
  | TUInt8 -> "8"
  | TUInt64 -> "64"
  | TUInt128 -> "128"

let rec print_valid_taints = function
  | [] -> ""
  | (a, TBuffer ty, t)::q -> "        valid_taint_buf" ^ (print_ty_number ty) ^ "(" ^ a ^ ", mem, memTaint, "^ taint_of_label t ^");\n" ^ print_valid_taints q
  | a::q -> print_buff_readable q

let print_vale_arg_value = function
  | (_, TGhost _, _) -> "error" // Should not happen
  | (a, TBuffer ty, _) -> "buffer_addr(" ^ a ^ ", mem)"
  | (a, TBase ty, _) -> a

let print_vale_calling_stack sstart (args:list arg) =
  let rec aux (i:nat) (args:list arg) : Tot string (decreases %[args])  =
  match args with
  | [] -> ""
  | a::q -> "        buffer_read(stack_b, " ^ (string_of_int (sstart + i)) ^ ", mem) == " ^  print_vale_arg_value a ^ ";\n" ^ aux (i+1) q
  in aux 0 args

let print_calling_args os target sstart (args:list arg) =
  let rec aux regs (args:list arg) =
  match regs, args with
    | [], q -> print_vale_calling_stack sstart q
    | _, [] -> ""
    | r1::rn, a::q -> "        " ^ r1 ^ " == " ^ print_vale_arg_value a ^ ";\n" ^ aux rn q
  in aux (calling_registers os target) args

let print_callee_saved os target =
  let rec aux = function
    | [] -> ""
    | a::q -> "        " ^ a ^ " == old(" ^ a ^ ");\n" ^ aux q
  in aux (callee_saved os target)

let print_xmm_callee_saved os target =
  let rec aux = function
    | [] -> ""
    | a::q -> "        " ^ a ^ " == old(" ^ a ^ ");\n" ^ aux q
  in aux (xmm_callee_saved os target)

let translate_vale os target (func:func_ty) =
  let name, args, Stk slots = func in
  let real_args = List.Tot.Base.filter not_ghost args in
  let stack_before_args = slots + (if os = Windows then 5 else 0) in // Account for shadow space on windows
  let nbr_stack_args = stack_before_args + List.Tot.Base.length real_args -
    List.Tot.Base.length (calling_registers os target) in
  let stack_needed = nbr_stack_args > 0 in
  let args = if stack_needed then ("stack_b", TBuffer TUInt64, Pub)::args else args in
  "module Vale_" ^ name ^
  "\n#verbatim{:interface}{:implementation}\n" ^
  "\nopen X64.Machine_s\nopen X64.Memory_s\nopen X64.Vale.State\nopen X64.Vale.Decls\n#set-options \"--z3rlimit 20\"\n#endverbatim\n\n" ^
  "procedure {:quick} " ^ name ^ "(" ^ print_vale_args args ^")\n" ^
  "    requires/ensures\n" ^
  "        locs_disjoint(list(" ^ print_vale_loc_buff args ^ "));\n" ^
  print_buff_readable args ^
  print_valid_taints args ^
  (if stack_needed then
  (if stack_needed then  "        buffer_length(stack_b) >= " ^ (string_of_int nbr_stack_args) ^ ";\n" else "") ^
  "        valid_stack_slots(mem, rsp, stack_b, " ^ (string_of_int slots) ^ ", memTaint);\n"
  else "") ^
  // stack_b and ghost args are not real arguments
  print_calling_args os target stack_before_args real_args ^
  "    ensures\n" ^ print_callee_saved os target ^ print_xmm_callee_saved os target ^
  "    modifies\n" ^
  "        rax; rbx; rcx; rdx; rsi; rdi; rbp; rsp; r8; r9; r10; r11; r12; r13; r14; r15;\n" ^
  "        xmm0; xmm1; xmm2; xmm3; xmm4; xmm5; xmm6; xmm7; xmm8; xmm9; xmm10; xmm11; xmm12; xmm13; xmm14; xmm15;\n" ^
  "        efl; mem;\n"^
  "{\n\n}\n"
