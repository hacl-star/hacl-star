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

type stack_slots = | AddStk of nat

type save_regs = | SaveRegsStk of bool

type modified = | Modifies of list string

type arg = string * ty * label
type func_ty = string * list arg * save_regs * stack_slots * modified

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

(* Only called with a list of buffer args *)
let rec disj_disjoint a = function
  | [] -> ""
  | (b, _, _)::q -> "  disjoint_or_eq " ^ a ^ " " ^ b ^ " /\ \n" ^ disj_disjoint a q

let disjoint args =
  let args = List.Tot.Base.filter is_buffer args in
  let rec aux (args: list arg) = match args with
  | [] -> ""
  | (a, _, _)::q -> disj_disjoint a q ^ aux q in
  aux args

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
    | [], q -> "    | _ -> init_regs r end)\n" ^ print_low_calling_stack q stkstart
    | _, [] -> "    | _ -> init_regs r end)\n"
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

let create_state target args stack slots stkstart saveRegs =
  let stack_length = if saveRegs then "(if is_win then " ^ (string_of_int (224 + slots `op_Multiply` 8)) ^ " else " ^ (string_of_int (64 + slots `op_Multiply` 8)) ^ ")" else string_of_int (slots `op_Multiply` 8) in
  create_taint_fun args ^
  "  let buffers = " ^ (if stack then "stack_b::" else "") ^ print_buffers_list args ^ " in\n" ^
  "  let (mem:mem) = {addrs = addrs; ptrs = buffers; hs = h0} in\n" ^
  generate_low_addrs args ^
  (if stack then "  let addr_stack:nat64 = addrs stack_b + " ^ stack_length ^ " in\n" else "") ^
  "  let regs = if is_win then (
    fun r -> begin match r with\n" ^
    (if stack then "    | Rsp -> addr_stack\n" else "") ^
    (print_low_calling_args Windows target args stkstart) ^
  "  else (\n" ^
  "    fun r -> begin match r with\n" ^
    (if stack then "    | Rsp -> addr_stack\n" else "") ^
    (print_low_calling_args Linux target args stkstart) ^  
  "  in let regs = FunctionalExtensionality.on reg regs\n" ^
  "  in let xmms = FunctionalExtensionality.on xmm init_xmms in\n"

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

let rec print_disjoint_stack (args:list arg) = match args with
  | [] -> ""
  | (a, TBuffer _, _)::q -> "  assert(Interop.disjoint stack_b " ^ a ^ ");\n" ^ print_disjoint_stack q
  | _ :: q -> print_disjoint_stack q

let rec print_modifies (args:list string) = match args with
  | [] -> "M.loc_none"
  | [a] -> "M.loc_buffer " ^ a
  | a::q -> "M.loc_union (M.loc_buffer " ^ a ^ ") ( "  ^ print_modifies q ^ ")"

let translate_core_lowstar target (func:func_ty) (stack_needed:bool) (length_stack:int) (slots:int) (additional:int) =
  let name, args, SaveRegsStk save, AddStk slots, Modifies modified = func in
  // let additional = (if os = Windows then 5 else 0) in
  let buffer_args = List.Tot.Base.filter is_buffer args in
    // let nbr_stack_args = List.Tot.Base.length real_args - 
  //   List.Tot.Base.length (calling_registers os target) in
  // let length_stack = (slots + additional + nbr_stack_args) `op_Multiply` 8 in
  // let stack_needed = length_stack > 0 in
  // let fuel_value = string_of_int (List.Tot.Base.length buffer_args + 3) in
  let stack_length = if save then
    "(if is_win then " ^ string_of_int (224 + length_stack) ^ " else " ^ string_of_int (64 + length_stack) ^ ")" else string_of_int (length_stack) in
  let implies_precond = if stack_needed then "B.length stack_b == " ^ stack_length ^
    " /\ live h0 stack_b /\ buf_disjoint_from stack_b " ^ (namelist_of_args (buffer_args)) ^ " /\ "
  else "" in
  let stack_precond memname = if stack_needed then
    "/\ B.length stack_b == " ^ stack_length ^
    " /\ live " ^ memname ^ " stack_b /\ buf_disjoint_from stack_b " ^ (namelist_of_args (buffer_args))
  else "" in
  "let create_initial_trusted_state is_win " ^ (print_args_names args) ^ "stack_b " ^
  "(h0:HS.mem{pre_cond h0 " ^ (print_args_names args) ^ stack_precond "h0" ^ "}) : GTot TS.traceState =\n" ^
  create_state target args stack_needed slots (slots+additional) save ^
  "  let (s0:BS.state) = {BS.ok = true; BS.regs = regs; BS.xmms = xmms; BS.flags = 0;
       BS.mem = Interop.down_mem h0 addrs buffers} in\n" ^
  "  {TS.state = s0; TS.trace = []; TS.memTaint = create_valid_memtaint mem buffers taint_func}\n\n" ^
  "val lemma_ghost_" ^ name ^ ": is_win:bool -> " ^ (print_low_args_and args) ^ 
  (if stack_needed then " stack_b:b8 -> " else "") ^
    "(h0:HS.mem{pre_cond h0 " ^ (print_args_names args) ^ 
    stack_precond "h0" ^
    "}) ->\n" ^
  "  Ghost (TS.traceState * nat * HS.mem)\n" ^
  "    (requires True)\n" ^ 
  "    (ensures (fun (s1, f1, h1) ->\n" ^
  "      (let s0 = create_initial_trusted_state is_win " ^ print_args_names args ^ "stack_b h0 in\n" ^
  "      Some s1 == TS.taint_eval_code (va_code_" ^ name ^ " is_win) f1 s0 /\\\n" ^
  "      Interop.correct_down h1 addrs " ^ (namelist_of_args (("stack_b", TBuffer TUInt64, Pub)::buffer_args))  ^ " s1.TS.state.BS.mem /\\\n" ^
  "      post_cond h0 h1 " ^ (print_args_names args) ^ " /\\\n" ^
  "      calling_conventions is_win s0 s1 /\\\n" ^
  "      M.modifies (" ^ print_modifies ("stack_b" :: modified) ^ ") h0 h1)\n" ^
  "    ))\n\n" ^
  "// ===============================================================================================\n" ^
  "//  Everything below this line is untrusted\n\n" ^
  "let create_initial_vale_state is_win " ^ (print_args_names args) ^ "stack_b " ^
  "(h0:HS.mem{pre_cond h0 " ^ (print_args_names args) ^ stack_precond "h0" ^ "}) : GTot va_state =\n" ^
  create_state target args stack_needed slots (slots+additional) save ^
  "  {ok = true; regs = regs; xmms = xmms; flags = 0; mem = mem;
      memTaint = create_valid_memtaint mem buffers taint_func}\n\n" ^
  "let create_lemma is_win " ^ (print_args_names args) ^ "stack_b (h0:HS.mem{pre_cond h0 " ^
    (print_args_names args) ^ stack_precond "h0" ^ "}) : Lemma\n" ^
    "  (create_initial_trusted_state is_win " ^ print_args_names args ^ 
    "stack_b h0 == state_to_S (create_initial_vale_state is_win " ^ print_args_names args ^ "stack_b h0)) =\n" ^
  "    let s_init = create_initial_trusted_state is_win " ^ print_args_names args ^ "stack_b h0 in\n" ^
  "    let s0 = create_initial_vale_state is_win " ^ print_args_names args ^ "stack_b h0 in\n" ^
  "    let s1 = state_to_S s0 in\n" ^
  "    assert (FunctionalExtensionality.feq (regs' s1.TS.state) (regs' s_init.TS.state));\n" ^
  "    assert (FunctionalExtensionality.feq (xmms' s1.TS.state) (xmms' s_init.TS.state))\n\n" ^
  "// TODO: Prove these two lemmas if they are not proven automatically\n" ^
  "let implies_pre (is_win:bool) (h0:HS.mem) " ^ (print_args_list args) ^ 
  (if stack_needed then " (stack_b:b8) " else "") ^
  ": Lemma\n" ^
  "  (requires pre_cond h0 " ^ (print_args_names args) ^ stack_precond "h0" ^ ")\n" ^
  "  (ensures (\n" ^ implies_precond ^ "(\n" ^
  "  let s0 = create_initial_vale_state is_win " ^ print_args_names args ^ "stack_b h0 in\n" ^
  print_length_t (if stack_needed then ("stack_b", TBuffer TUInt64, Pub)::args else args) ^
  "  va_pre (va_code_" ^ name ^ " is_win) s0 is_win" ^ 
  (if stack_needed then " stack_b " else " ") ^
  (print_args_names_reveal args) ^ "))) =\n" ^
  print_length_t (if stack_needed then ("stack_b", TBuffer TUInt64, Pub)::args else args) ^ 
  (if stack_needed then print_disjoint_stack args else "") ^
  "  ()\n\n" ^
  "let implies_post (is_win:bool) (va_s0:va_state) (va_sM:va_state) (va_fM:va_fuel) " ^ (print_args_list args) ^
  (if stack_needed then " (stack_b:b8)" else "") ^
  " : Lemma\n" ^
  "  (requires pre_cond va_s0.mem.hs " ^ (print_args_names args) ^ stack_precond "va_s0.mem.hs" ^ "/\\\n" ^
  "    va_post (va_code_" ^ name ^ " is_win) va_s0 va_sM va_fM is_win" ^
  (if stack_needed then " stack_b " else " ") ^
  (print_args_names_reveal args) ^ ")\n" ^
  "  (ensures post_cond va_s0.mem.hs va_sM.mem.hs " ^ (print_args_names args) ^ ") =\n" ^
  print_length_t (if stack_needed then ("stack_b", TBuffer TUInt64, Pub)::args else args) ^ 
  "  ()\n\n" ^
  "let lemma_ghost_" ^ name ^ " is_win " ^ (print_args_names args) ^
  (if stack_needed then "stack_b " else "") ^ "h0 =\n" ^
  print_length_t (if stack_needed then ("stack_b", TBuffer TUInt64, Pub)::args else args) ^
  "  implies_pre is_win h0 " ^ (print_args_names args) ^ "stack_b;\n" ^
  "  let s0 = create_initial_trusted_state is_win " ^ print_args_names args ^ "stack_b h0 in\n" ^
  "  let s0' = create_initial_vale_state is_win " ^ print_args_names args ^ "stack_b h0 in\n" ^
  "  create_lemma is_win " ^ print_args_names args ^ "stack_b h0;\n" ^
  "  let s_v, f_v = va_lemma_" ^ name ^ " (va_code_" ^ name ^ " is_win) s0' is_win" ^
  (if stack_needed then " stack_b " else " ") ^
  print_args_names_reveal args ^ "in\n" ^
  "  implies_post is_win s0' s_v f_v " ^ print_args_names args ^ "stack_b;\n" ^
  "  let s1 = Some?.v (TS.taint_eval_code (va_code_" ^ name ^ " is_win) f_v s0) in\n" ^
  "  assert (state_eq_S s1 (state_to_S s_v));\n" ^  
  "  assert (FunctionalExtensionality.feq s1.TS.state.BS.regs s_v.regs);\n" ^
  "  assert (FunctionalExtensionality.feq s1.TS.state.BS.xmms s_v.xmms);\n" ^
  "  s1, f_v, s_v.mem.hs\n\n"

let translate_lowstar target (func:func_ty) =
  let name, args, SaveRegsStk saveRegs, AddStk slots, Modifies modified = func in
  let additional = 5 in
  let buffer_args = List.Tot.Base.filter is_buffer args in
  let real_args = List.Tot.Base.filter not_ghost args in
  let nbr_stack_args = List.Tot.Base.length real_args - 4 in
  let length_stack = (slots + additional + nbr_stack_args) `op_Multiply` 8 in
  let string_length_stack = if saveRegs then 
    "(if win then " ^ string_of_int (224 + length_stack) ^ " else " ^ string_of_int (64 + length_stack) ^ ")"
    else string_of_int length_stack in
  let stack_needed = length_stack > 0 || saveRegs in
  let fuel_value = string_of_int (List.Tot.Base.length buffer_args + 3) in
  let lin_stack_precond memname = if stack_needed then
    "/\ B.length stack_b == " ^ (if saveRegs then string_of_int (64 + length_stack) else string_of_int length_stack) ^
    " /\ live " ^ memname ^ " stack_b /\ buf_disjoint_from stack_b " ^ (namelist_of_args (buffer_args)) else "" in
  let win_stack_precond memname = if stack_needed then
    "/\ B.length stack_b == " ^ (if saveRegs then string_of_int (224 + length_stack) else string_of_int length_stack) ^
    " /\ live " ^ memname ^ " stack_b /\ buf_disjoint_from stack_b " ^ (namelist_of_args (buffer_args)) else "" in    
  let separator0 = if (List.Tot.Base.length buffer_args = 0) then "" else " /\\ " in
  let separator1 = if (List.Tot.Base.length buffer_args <= 1) then "" else " /\\ " in  
  "module Vale_" ^ name ^
  "\n\nopen X64.Machine_s\nopen X64.Memory\nopen X64.Vale.State\nopen X64.Vale.Decls\n\n" ^
  "val va_code_" ^ name ^ ": bool -> va_code\n\n" ^
  "let va_code_" ^ name ^ " = va_code_" ^ name ^ "\n\n" ^
  "//va_pre and va_post should correspond to the pre- and postconditions generated by Vale\n" ^
  "let va_pre (va_b0:va_code) (va_s0:va_state) (win:bool)" ^ (if stack_needed then " (stack_b:buffer64)\n" else "\n") ^
  (print_args_vale_list args) ^ " = va_req_" ^ name ^ " va_b0 va_s0 win " ^ 
  (if stack_needed then "stack_b " else "") ^
  (print_args_names args) ^ "\n\n" ^
  "let va_post (va_b0:va_code) (va_s0:va_state) (va_sM:va_state) (va_fM:va_fuel) (win:bool) " ^
  (if stack_needed then " (stack_b:buffer64)\n" else "\n") ^
  (print_args_vale_list args) ^ " = va_ens_" ^ name ^ " va_b0 va_s0 win " ^
  (if stack_needed then "stack_b " else "") ^
  (print_args_names args) ^
  "va_sM va_fM\n\n" ^
  "val va_lemma_" ^ name ^ "(va_b0:va_code) (va_s0:va_state) (win:bool)" ^
  (if stack_needed then " (stack_b:buffer64)\n" else "\n") ^
  (print_args_vale_list args) ^ ": Ghost ((va_sM:va_state) * (va_fM:va_fuel))\n  " ^
  "(requires va_pre va_b0 va_s0 win " ^ (if stack_needed then "stack_b " else "") ^
  (print_args_names args) ^ ")\n  " ^
  "(ensures (fun (va_sM, va_fM) -> va_post va_b0 va_s0 va_sM va_fM win " ^ 
  (if stack_needed then "stack_b " else "") ^
  (print_args_names args) ^ "))" ^
  "\n\n" ^
  "let va_lemma_" ^ name ^ " = va_lemma_" ^ name ^
  "\n\n" ^
  "module " ^ name ^
  "\n\nopen LowStar.Buffer\nmodule B = LowStar.Buffer\nmodule BV = LowStar.BufferView\nopen LowStar.Modifies\nmodule M = LowStar.Modifies\nopen LowStar.ModifiesPat\nopen FStar.HyperStack.ST\nmodule HS = FStar.HyperStack\nopen Interop\nopen Types_s\n\n" ^
  "// TODO: Complete with your pre- and post-conditions\n" ^
  "let pre_cond (h:HS.mem) " ^ (print_args_list args) ^ "= " ^ (liveness "h" args) ^ separator1 ^ (disjoint args) ^ (print_lengths args) ^ "\n\n" ^
  "let post_cond (h:HS.mem) (h':HS.mem) " ^ (print_args_list args) ^ "= " 
    ^ (liveness "h" args) ^ " /\\ " ^ (liveness "h'" args) ^ separator0 ^ (print_lengths args) ^ "\n\n" ^
  "let full_post_cond (h:HS.mem) (h':HS.mem) " ^ (print_args_list args) ^ " =\n" ^
  "  post_cond h h' " ^ (print_args_names args) ^ " /\\\n" ^
  "  M.modifies (" ^ (print_modifies modified) ^ ") h h'\n\n" ^
  "val " ^ name ^ ": " ^ (print_low_args args) ^
  "\n\t(requires (fun h -> pre_cond h " ^ (print_args_names args) ^ "))\n\t" ^
  "(ensures (fun h0 _ h1 -> full_post_cond h0 h1 " ^ (print_args_names args) ^ "))\n\n" ^    
  "module " ^ name ^
  "\n\nopen LowStar.Buffer\nmodule B = LowStar.Buffer\nmodule BV = LowStar.BufferView\nopen LowStar.Modifies\nmodule M = LowStar.Modifies\nopen LowStar.ModifiesPat\nopen FStar.HyperStack.ST\nmodule HS = FStar.HyperStack\nopen Interop\nopen Words_s\nopen Types_s\nopen X64.Machine_s\nopen X64.Memory_s\nopen X64.Vale.State\nopen X64.Vale.Decls\nopen BufferViewHelpers\nopen Interop_assumptions\nopen X64.Vale.StateLemmas\nopen X64.Vale.Lemmas\nmodule TS = X64.Taint_Semantics_s\nmodule ME = X64.Memory_s\nmodule BS = X64.Bytes_Semantics_s\n\nfriend SecretByte\nfriend X64.Memory_s\nfriend X64.Memory\nfriend X64.Vale.Decls\nfriend X64.Vale.StateLemmas\n#set-options \"--z3rlimit 60\"\n\n" ^
  "open Vale_" ^ name ^ "\n\n" ^

  "#set-options \"--initial_fuel " ^ fuel_value ^ " --max_fuel " ^ fuel_value ^ " --initial_ifuel 2 --max_ifuel 2\"\n" ^
  
  translate_core_lowstar target func stack_needed length_stack slots additional ^
  "#set-options \"--max_fuel 0 --max_ifuel 0\"\n\n" ^
  "let " ^ name ^ " " ^ (print_args_names args) ^ " =\n" ^
  (if stack_needed then "  push_frame();\n" ^
    "  let (stack_b:b8) = B.alloca (UInt8.uint_to_t 0) (UInt32.uint_to_t " ^ string_length_stack ^ ") in\n"  else "") ^
  " if win then\n" ^
  "  st_put\n" ^
  "    (fun h -> pre_cond h " ^ (print_args_names args) ^ win_stack_precond "h" ^ ")\n" ^
  "    (fun h -> let _, _, h1 =
      lemma_ghost_" ^ name ^ " true " ^ (print_args_names args) ^ "stack_b h\n" ^
  "    in h1)\n" ^
  "  else st_put\n" ^
  "    (fun h -> pre_cond h " ^ (print_args_names args) ^ lin_stack_precond "h" ^ ")\n" ^  
  "    (fun h -> let _, _, h1 =
      lemma_ghost_" ^ name ^ " false " ^ (print_args_names args) ^ "stack_b h\n" ^
  "    in h1);\n" ^
  "  pop_frame()\n"
  
let print_vale_arg = function
  | (a, ty, _) -> "ghost " ^ a ^ ":" ^ print_vale_full_ty ty

let rec print_vale_args = function
  | [] -> ""
  | [arg] -> print_vale_arg arg
  | arg::q -> print_vale_arg arg ^ ", " ^ print_vale_args q

let rec print_vale_disjoint_or_eq_aux a = function
  | [] -> ""
  | (b, TBuffer _, _)::q -> "        locs_disjoint(list(loc_buffer("^a^"), loc_buffer("^b^"))) \/ "^a^ " == "^b ^ ";\n"^ print_vale_disjoint_or_eq_aux a q
  | _::q -> print_vale_disjoint_or_eq_aux a q

let rec print_vale_disjoint_or_eq = function
  | [] -> ""
  | (a, TBuffer _, _)::q -> print_vale_disjoint_or_eq_aux a q ^ print_vale_disjoint_or_eq q
  | a::q -> print_vale_disjoint_or_eq q

let rec print_vale_disjoint_aux a = function
  | [] -> ""
  | (b, TBuffer _, _)::q -> "        locs_disjoint(list(loc_buffer("^a^"), loc_buffer("^b^")));\n" ^ print_vale_disjoint_aux a q
  | _::q -> print_vale_disjoint_aux a q

let rec print_vale_disjoint = function
  | [] -> ""
  | (a, TBuffer _, _)::q -> print_vale_disjoint_aux a q ^ print_vale_disjoint q
  | a::q -> print_vale_disjoint q

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
  | a::q -> print_valid_taints q

let print_vale_arg_value = function
  | (_, TGhost _, _) -> "error" // Should not happen
  | (a, TBuffer ty, _) -> "buffer_addr(" ^ a ^ ", mem)"
  | (a, TBase ty, _) -> a

let print_vale_calling_stack is_win sstart (args:list arg) =
  let rec aux (i:nat) (args:list arg) : Tot string (decreases %[args])  =
  match args with
  | [] -> ""
  | a::q -> "        " ^ is_win ^ " " ^ "buffer_read(stack_b, " ^ (string_of_int (sstart + i)) ^ ", mem) == " ^  print_vale_arg_value a ^ ";\n" ^ aux (i+1) q
  in aux 0 args

let print_calling_args_aux is_win os target sstart (args:list arg) =
  let rec aux regs (args:list arg) =
  match regs, args with
    | [], q -> print_vale_calling_stack is_win sstart q
    | _, [] -> ""
    | r1::rn, a::q -> "        " ^ is_win ^ " " ^ r1 ^ " == " ^ print_vale_arg_value a ^ ";\n" ^ aux rn q
  in aux (calling_registers os target) args


let print_calling_args target sstart (args:list arg) =
  // Windows calling conventions
  print_calling_args_aux "win ==>" Windows target sstart args ^
  // Linux calling conventions
  print_calling_args_aux "!win ==>" Linux target sstart args

let print_callee_saved_aux is_win os target =
  let rec aux = function
    | [] -> ""
    | a::q -> "        " ^ is_win ^ " " ^ a ^ " == old(" ^ a ^ ");\n" ^ aux q
  in aux (callee_saved os target)

let print_callee_saved target =
  // Windows calling conventions
  print_callee_saved_aux "win ==> " Windows target ^
  // Linux calling conventions
  print_callee_saved_aux "!win ==> " Linux target

let print_xmm_callee_saved_aux is_win os target =
  let rec aux = function
    | [] -> ""
    | a::q -> "        " ^ is_win ^ " " ^ a ^ " == old(" ^ a ^ ");\n" ^ aux q
  in aux (xmm_callee_saved os target)

let print_xmm_callee_saved target =
  print_xmm_callee_saved_aux "win ==> " Windows target ^
  print_xmm_callee_saved_aux "!win ==> " Linux target

let rec print_vale_modifies (args:list string) = match args with
  | [] -> "loc_none"
  | [a] -> "loc_buffer(" ^ a ^ ")"
  | a::q -> "loc_union(loc_buffer(" ^ a ^ "), " ^ print_vale_modifies q ^ ")"

let translate_vale target (func:func_ty) =
  let name, args, SaveRegsStk save, AddStk slots, Modifies modified = func in
  let real_args = List.Tot.Base.filter not_ghost args in
  let stack_before_args = slots + 5 in // Account for shadow space on windows
  let nbr_stack_args = stack_before_args + List.Tot.Base.length real_args - 
    4 in
  let stack_needed = nbr_stack_args > 0 in  
  let args = if stack_needed then ("stack_b", TBuffer TUInt64, Pub)::args else args in
  "module Vale_" ^ name ^
  "\n#verbatim{:interface}{:implementation}\n" ^ 
  "\nopen X64.Machine_s\nopen X64.Memory\nopen X64.Vale.State\nopen X64.Vale.Decls\n#set-options \"--z3rlimit 20\"\n#endverbatim\n\n" ^
  "procedure {:quick}{:exportSpecs} " ^ name ^ "(inline win:bool," ^ print_vale_args args ^")\n" ^
  "    requires\n" ^
  // By default, buffer arguments are disjoint or equal
  print_vale_disjoint_or_eq (List.Tot.Base.tl args) ^
  // stack_b is disjoint from all other buffers
  print_vale_disjoint_aux "stack_b" (List.Tot.Base.tl args) ^
  print_buff_readable args ^
  print_valid_taints args ^
  (if stack_needed then
  "        valid_stack_slots(mem, rsp, stack_b, " ^ (if save then "if win then " ^ string_of_int (28 + slots) ^ " else " ^ string_of_int (8 + slots) else string_of_int slots) ^ ", memTaint);\n"
  else "") ^
  // stack_b and ghost args are not real arguments
  print_calling_args target stack_before_args real_args ^
  "    ensures\n" ^ 
  "        modifies_mem(" ^ print_vale_modifies ("stack_b" :: modified) ^ ", old(mem), mem);\n" ^
  print_callee_saved target ^ 
  print_xmm_callee_saved target ^
  "    reads memTaint;\n" ^
  "    modifies\n" ^
  "        rax; rbx; rcx; rdx; rsi; rdi; rbp; rsp; r8; r9; r10; r11; r12; r13; r14; r15;\n" ^
  "        xmm0; xmm1; xmm2; xmm3; xmm4; xmm5; xmm6; xmm7; xmm8; xmm9; xmm10; xmm11; xmm12; xmm13; xmm14; xmm15;\n" ^
  "        efl; mem;\n"^
  "{\n\n}\n"
