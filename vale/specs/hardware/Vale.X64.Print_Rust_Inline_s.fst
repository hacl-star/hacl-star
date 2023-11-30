module Vale.X64.Print_Rust_Inline_s

open FStar.Mul
open FStar.List.Tot
open Vale.X64.Machine_s
open Vale.X64.Bytes_Code_s
open Vale.X64.Machine_Semantics_s
open Vale.X64.Instruction_s
open FStar.IO
open Vale.Interop.Base
open Vale.Interop.X64
module P = Vale.X64.Print_s

let print_rettype (ret_val:option string) = match ret_val with
  | None -> "()"
  | Some _ -> "u64"

let print_basetype (t:base_typ) = match t with
  | TUInt8 -> "u8"
  | TUInt16 -> "u16"
  | TUInt32 -> "u32"
  | TUInt64 -> "u64"
  | TUInt128 -> "ERROR"

// Returns "arg1: u8" or "arg0: &mut [u64]" for instance
let print_arg (a:td) (i:nat) (names:nat -> string) = match a with
  | TD_Base src -> names i ^ ": " ^ print_basetype src
  | TD_Buffer src _ _ -> names i ^ ": &mut [" ^ print_basetype src ^ "]"
  | TD_ImmBuffer src _ _ -> names i ^ ": &[" ^ print_basetype src ^ "]"

// Prints a list of args with their types, separated by a comma
let rec print_args (args:list td) (i:nat) (names:nat -> string) = match args with
  | [] -> ""
  | [a] -> print_arg a i names
  | a::q -> print_arg a i names ^ ", " ^ print_args q (i+1) names

let rec build_reserved_args_outs (l:list instr_out) (reserved:reg_64 -> bool)
  : Tot (reg_64 -> bool)
  (decreases l) =
  fun r ->
  match l with
  | [] -> reserved r
  | hd::tl ->
    let (_, op) = hd in
    let reserved : (reg_64 -> bool) = (fun r ->
      match op with
      | IOpIm (IOp64One (OReg reg)) ->
          // Implicit register, adding it to "reserved" registers
          if r = reg then true else reserved r
      | _ -> reserved r)
    in build_reserved_args_outs tl reserved r

let rec build_reserved_args_ins (l:list instr_operand) (reserved:reg_64 -> bool)
  : Tot (reg_64 -> bool)
  (decreases l) =
  fun r ->
  match l with
  | [] -> reserved r
  | hd::tl ->
    let reserved : (reg_64 -> bool) = (fun r ->
      match hd with
      | IOpIm (IOp64One (OReg reg)) ->
          // Implicit register, adding it to "reserved" registers
          if r = reg then true else reserved r
      | _ -> reserved r)
    in build_reserved_args_ins tl reserved r

// Traverses code, looking for instructions implicitly using registers.
// When found, mark such registers as reserved so that they are not used during implicit allocation
let rec build_reserved_args (c:code) (reserved:reg_64 -> bool)
  : Tot (reg_64 -> bool)
  (decreases c) =
  fun r ->
   (match c with
  | Ins ins ->  begin
      match ins with
      | Instr i _ _ ->
          let reserved = build_reserved_args_outs i.outs reserved in
          let reserved = build_reserved_args_ins (InstrTypeRecord?.args i) reserved in
          reserved r
      | _ -> reserved r
    end
  | Block l ->  (build_reserved_args_block l reserved) r
  | IfElse cond ifTrue ifFalse ->
      let reservedT = build_reserved_args ifTrue reserved in
      build_reserved_args ifFalse reservedT r
  | While cond body -> build_reserved_args body reserved r
)

and build_reserved_args_block (l:list code) (reserved:reg_64 -> bool)
  : Tot (reg_64 -> bool)
  (decreases l) =
  fun r -> (
  match l with
  | [] -> reserved r
  | hd::tl ->
    let reserved = build_reserved_args hd reserved in
    build_reserved_args_block tl reserved r
  )

// If the register in which a is passed is modified, we should specify "name = inout(reg) name,"
// If the register is reserved, we should explicitly allocate it
let print_modified_input
  (n:nat) (a:td) (i:nat{i < n}) (of_arg:reg_nat n -> reg_64) (regs_mod:reg_64 -> bool) (reserved_regs:reg_64 -> bool)
  (reg_names:reg_64 -> string) (arg_names:nat -> string) : list string & (reg_64 -> string) =
   if regs_mod (of_arg i) then
     let arg_name = arg_names i in
     // If the register is reserved, explicitly allocate the variable in it
     let reg_alloc = if reserved_regs (of_arg i) then reg_names (of_arg i) else "reg" in
     let arg_reg = arg_name ^ " = inout(" ^ reg_alloc ^ ") " ^ arg_name in
     // If the register corresponds to an argument `name`, print it as {name} in the code
     let modified_reg_names = fun r -> if r = of_arg i then "{" ^ arg_name ^ "}" else reg_names r in
     [arg_reg], modified_reg_names
   else
     [], reg_names

// Get a list of strings corresponding to modified inputs
let rec get_modified_input_strings
  (n:nat) (of_arg:reg_nat n -> reg_64) (regs_mod:reg_64 -> bool) (reserved_regs:reg_64 -> bool)
  (args:list td) (i:nat{i + List.Tot.length args <= n}) (ret_val:option string)
  (reg_names:reg_64 -> string) (arg_names:nat -> string) : list string & (reg_64 -> string)
  = match args with
  | [] -> [], reg_names // If we supported return values, they would need to be specified here with an out(reg)
  | a::q ->
      let output, reg_names = print_modified_input n a i of_arg regs_mod reserved_regs reg_names arg_names in
      let outputs, reg_names = get_modified_input_strings n of_arg regs_mod reserved_regs q (i+1) ret_val reg_names arg_names in
      output @ outputs, reg_names

// Print the list of modified inputs, separated by commas
let print_modified_inputs
  (n:nat)
  (of_arg:reg_nat n -> reg_64)
  (regs_mod:reg_64 -> bool)
  (reserved_regs:reg_64 -> bool)
  (args:list td{List.Tot.length args <= n})
  (ret_val:option string)
  (reg_names:reg_64 -> string)
  (arg_names:nat -> string) =
  let rec aux = function
  | [] -> ""
  | a :: q -> "    " ^ a ^ ",\n" ^ aux q
  in
  let outputs, output_reg_names = get_modified_input_strings n of_arg regs_mod reserved_regs args 0 ret_val reg_names arg_names in
  aux outputs, output_reg_names

// If the register in which an arg is passed is not modified, we should specify it as `name = in(reg) name`.
// If the argument needs to be in a specific register, e.g., rdx, we instead specify `name = in("rdx") name`
let print_nonmodified_input
  (n:nat) (of_arg:reg_nat n -> reg_64) (regs_mod:reg_64 -> bool) (reserved_regs:reg_64 -> bool)
  (a:td) (i:nat{i < n}) (reg_names:reg_64 -> string) (arg_names:nat -> string) : list string & (reg_64 -> string) =
   if regs_mod (of_arg i) then [], reg_names else
     let arg_name = arg_names i in
     // If the register is reserved, explicitly allocate the variable in it
     let reg_alloc = if reserved_regs (of_arg i) then reg_names (of_arg i) else "reg" in
     let arg_reg = arg_name ^ " = in(" ^ reg_alloc ^ ") " ^ arg_name in
     // If the register corresponds to an argument `name`, print it as {name} in the code
     let modified_reg_names = fun r -> if r = of_arg i then "{" ^ arg_name ^ "}" else reg_names r in
     [arg_reg], modified_reg_names

// Get a list of strings corresponding to modified inputs
let rec get_nonmodified_input_strings
  (n:nat) (of_arg:reg_nat n -> reg_64) (regs_mod:reg_64 -> bool) (reserved_regs:reg_64 -> bool)
  (args:list td) (i:nat{List.Tot.length args + i <= n}) (reg_names:reg_64 -> string) (arg_names:nat -> string)
  = match args with
  | [] -> [], reg_names
  | a::q ->
    let input, reg_names = print_nonmodified_input n of_arg regs_mod reserved_regs a i reg_names arg_names in
    let inputs, reg_names = get_nonmodified_input_strings n of_arg regs_mod reserved_regs q (i+1) reg_names arg_names in
    input @ inputs, reg_names

let print_nonmodified_inputs
  (n:nat) (of_arg:reg_nat n -> reg_64) (regs_mod:reg_64 -> bool) (reserved_regs:reg_64 -> bool)
  (args:list td{List.Tot.length args <= n}) (reg_names:reg_64 -> string) (arg_names:nat -> string) =
  let rec aux = function
  | [] -> ""
  | a :: q -> "    " ^ a ^ ",\n" ^ aux q
  in
  let inputs, input_reg_names = get_nonmodified_input_strings n of_arg regs_mod reserved_regs args 0 reg_names arg_names in
  aux inputs, input_reg_names


// Print the list of modified registers, + memory and cc
let print_modified_registers
  (n:nat)
  (ret_val:option string)
  (of_arg:reg_nat n -> reg_64)
  (regs_mod:reg_64 -> bool)
  (reserved_args:reg_64 -> bool)
  (args:list td) =
  let rec input_register (i:nat) (a:reg_64) : Tot bool (decreases (n-i)) =
    if i >= n then false
    else
      a = of_arg i // This register was already specified for the i-th argument
      || input_register (i+1) a
  in
  let rec aux = function
  | [] -> ""
  | a::q ->
    // This register is not modified, or was already specified as input or output: we skip it
    if not (regs_mod a) || input_register 0 a then aux q
    // Register not modified or already specified in inputs, we add it
    else "    out(" ^ P.print_reg_name a ^ ") _,\n" ^ aux q
  in aux [rRax; rRbx; rRcx; rRdx; rRsi; rRdi; rRbp; rRsp; rR8; rR9; rR10; rR11; rR12; rR13; rR14; rR15]

(* This is a copy from X64.Print_s, and should remain in sync. The difference is that
   each line should be in quotes, and end by a colon in Rust inline assembly *)
let print_cmp (c:ocmp) (counter:int) (p:P.printer) : string =
  let print_ops (o1:operand64) (o2:operand64) : string =
    let first, second = p.P.op_order (P.print_operand o1 p) (P.print_operand o2 p) in
    "  cmp " ^ first ^ ", " ^ second ^ "\n"
  in
  match c with
  | OEq o1 o2 -> "    \"" ^ print_ops o1 o2 ^ "  je " ^ "L" ^ string_of_int counter ^ "\",\n"
  | ONe o1 o2 -> "    \"" ^ print_ops o1 o2 ^ "  jne "^ "L" ^ string_of_int counter ^ "\",\n"
  | OLe o1 o2 -> "    \"" ^ print_ops o1 o2 ^ "  jbe "^ "L" ^ string_of_int counter ^ "\",\n"
  | OGe o1 o2 -> "    \"" ^ print_ops o1 o2 ^ "  jae "^ "L" ^ string_of_int counter ^ "\",\n"
  | OLt o1 o2 -> "    \"" ^ print_ops o1 o2 ^ "  jb " ^ "L" ^ string_of_int counter ^ "\",\n"
  | OGt o1 o2 -> "    \"" ^ print_ops o1 o2 ^ "  ja " ^ "L" ^ string_of_int counter ^ "\",\n"

let rec print_spaces (n:nat) : string =
  match n with
  | 0 -> ""
  | n -> " " ^ print_spaces (n-1)

(* Overriding printer for formatting instructions *)
let print_ins (ins:ins) (p:P.printer) : string =
  match ins with
  | Instr _ _ (AnnotateComment s) -> "    // " ^ s
  | Instr _ _ (AnnotateLargeComment s) -> "\n    /////// " ^ s ^ " ////// \n"
  | Instr _ _ (AnnotateSpace n) -> print_spaces n
  | _ -> "    \"" ^ P.print_ins ins p ^ "\","

let rec print_block (b:codes) (n:int) (p:P.printer) : string & int =
  match b with
  | Nil -> "", n
  | Ins (Instr _ _ (AnnotateSpace spaces)) :: Ins (Instr _ _ (AnnotateComment s)) :: tail ->
    let head_str =  "    // " ^ s ^ "\n" in
    let rest, n' = print_block tail n p in
    print_spaces spaces ^ head_str ^ rest, n'
  | Ins (Instr _ _ (AnnotateSpace spaces)) :: Ins i :: tail ->
    let head_str = print_ins i p in
    let rest, n' = print_block tail n p in
    print_spaces spaces ^ head_str ^ rest, n'
  | Ins (Instr _ _ (AnnotateNewline _)) :: tail ->
    let rest, n' = print_block tail n p in
    "\n" ^ rest, n'
  | head :: tail ->
    let head_str, n' = print_code head n p in
    let rest, n'' = print_block tail n' p in
    head_str ^ rest, n''
and print_code (c:code) (n:int) (p:P.printer) : string & int =
  match c with
  | Ins ins -> (print_ins ins p ^ "\n", n)
  | Block b -> print_block b n p
  | IfElse cond true_code false_code ->
    let n1 = n in
    let n2 = n + 1 in
    let cmp = print_cmp (P.cmp_not cond) n1 p in
    let true_str, n' = print_code true_code (n + 2) p in
    let jmp = "    \"  jmp L" ^ string_of_int n2 ^ "\",\n" in
    let label1 = "    \"L" ^ string_of_int n1 ^ ":\"\n" in
    let false_str, n' = print_code false_code n' p in
    let label2 = "    \"L" ^ string_of_int n2 ^ ":\"\n" in
    cmp ^ true_str ^ jmp ^ label1 ^ false_str ^ label2, n'
  | While cond body ->
    let n1 = n in
    let n2 = n + 1 in
    let jmp = "    \"  jmp L" ^ string_of_int n2 ^ "\",\n" in
    let label1 = "    \"" ^ p.P.align() ^ " 16\nL" ^ string_of_int n1 ^ ":\"\n" in
    let body_str, n' = print_code body (n + 2) p in
    let label2 = "    \"" ^ p.P.align() ^ " 16\nL" ^ string_of_int n2 ^ ":\"\n" in
    let cmp = print_cmp cond n1 p in
    jmp ^ label1 ^ body_str ^ label2 ^ cmp, n'

(* Top-level comments, for a function declaration *)
let rec print_fn_comments = function
  | [] -> ""
  | hd::tl -> "/// " ^ hd ^ "\n" ^ print_fn_comments tl

let rec remove_blank (c:code) : code =
  match c with
  | Ins _ -> c
  | Block b -> Block (remove_blanks b)
  | IfElse cond ct cf -> IfElse cond (remove_blank ct) (remove_blank cf)
  | While cond cb -> While cond (remove_blank cb)
and remove_blanks (b:codes) : codes =
  match b with
  | [] -> []
  | Ins (Instr _ _ (AnnotateGhost _)) :: cs -> remove_blanks cs
  | Block b :: cs ->
    (
      match remove_blanks b with
      | [] -> remove_blanks cs
      | b -> Block b :: remove_blanks cs
    )
  | c :: cs -> c :: remove_blanks cs

// Check if any argument is passed in the rax register
let rec uses_rax (#n:nat) (args:list td) (i:nat{i + List.length args = n}) (of_arg:reg_nat n -> reg_64) =
  match args with
  | [] -> false
  | a::q -> if of_arg i = rRax then true else uses_rax q (i+1) of_arg

let print_inline
  (name:string)
  (label:int)
  (ret_val:option string)
  (n:nat)
  (args:list td{List.length args = n})
  (arg_names:nat -> string)
  (code:code)
  (of_arg:reg_nat (List.length args) -> reg_64)
  (regs_mod:reg_64 -> bool)
  (fn_comments:list string)
  : FStar.All.ML int =
  let comments = print_fn_comments fn_comments in

  let reserved_regs = build_reserved_args code (fun _ -> false) in

  let inputs_use_rax = uses_rax args 0 of_arg in
  if Some? ret_val then
    FStar.All.failwith "return arguments are not support in Rust inline assembly printer";

  if inputs_use_rax && Some? ret_val then
    FStar.All.failwith "inputs are not allowed to be passed in rax when there is a return argument";

  // Signature:
  // #[inline(always)]
  // fn [name] (args) -> (ret_type) {
  let header = "#[inline(always)]\nfn " ^ name ^ " (" ^ print_args args 0 arg_names ^ ") -> " ^ print_rettype ret_val ^ " {\n" in

  // Start printing the code, need an unsafe block and the asm! macro
  let start_code =  "  unsafe {\n    asm!(\n" in

  // Initially, the register names are the same as in assembly
  // This function will be modified to address arguments by their name instead of explicitly allocating them
  // TODO: Need to redefine print_reg_name to avoid the % prefix
  let init_reg_names r = P.print_reg_name r in

  // Each *modified* input should be specified as `name = inout(reg) name`
  // If we have a return value, it should be written only and specified as "name = out(reg) name"
  let output_str, output_reg_names =  print_modified_inputs n of_arg regs_mod reserved_regs args ret_val init_reg_names arg_names in


  // Each *non-modified* input should be specified as `name = in(reg) name`
  let input_str, inlined_reg_names = print_nonmodified_inputs n of_arg regs_mod reserved_regs args output_reg_names arg_names in

  // Every modified register that wasn't used for the inputs/outputs should be specified as, e.g., "out("rdx") _"
  // This also ensures that this register is not used for allocation of input/output in Rust
  let modified_str = print_modified_registers n ret_val of_arg regs_mod reserved_regs args in

  // We do not support for reg32 and small registers
  let inlined_reg32_names _ = "ERROR" in
  let inlined_small_reg_names _ = "ERROR" in

  let printer = {P.gcc with
    P.print_reg_name = inlined_reg_names;
    P.print_reg32_name = inlined_reg32_names;
    P.print_small_reg_name = inlined_small_reg_names } in

  let (code_str, final_label) = print_code (remove_blank code) label printer in

  // Close the asm! block, then the unsafe block, then the function
  let close_code = "    );\n  }\n}" in

  print_string (comments ^ header ^ start_code ^ code_str ^ output_str ^ input_str ^ modified_str ^ close_code);
  final_label
