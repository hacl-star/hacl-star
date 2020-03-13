module Vale.X64.Print_Inline_s

open FStar.Mul
open Vale.X64.Machine_s
open Vale.X64.Bytes_Code_s
open Vale.X64.Machine_Semantics_s
open Vale.X64.Instruction_s
open FStar.IO
open Vale.Interop.Base
open Vale.Interop.X64
module P = Vale.X64.Print_s

let print_rettype (ret_val:option string) = match ret_val with
  | None -> "void"
  | Some _ -> "uint64_t"

let print_basetype (t:base_typ) = match t with
  | TUInt8 -> "uint8_t"
  | TUInt16 -> "uint16_t"
  | TUInt32 -> "uint32_t"
  | TUInt64 -> "uint64_t"
  | TUInt128 -> "ERROR"

// Returns "uint8_t arg2" or "uint64_t* arg0" for instance
let print_arg (a:td) (i:nat) (names:nat -> string) = match a with
  | TD_Base src -> print_basetype src ^ " " ^ names i
  | TD_Buffer src _ _ | TD_ImmBuffer src _ _ -> print_basetype src ^ " *" ^ names i

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

// Prints `"=&r" (name)` if an output is specified
let print_output_ret ret_val (reg_names:reg_64 -> string) (counter:nat) : list string & (reg_64 -> string) & nat
  = match ret_val with
  | None -> [], reg_names, counter
  | Some name -> (["\"=&r\" (" ^ name ^ ")"],
      // If r = rax then address it as current arg number
      (fun r -> if r = 0 then string_of_int counter else reg_names r),
      counter + 1)

// If the register in which a is passed is modified, we should specify `"+&r" (name)`
let print_modified_input
  (n:nat) (a:td) (i:nat{i < n}) (of_arg:reg_nat n -> reg_64) (regs_mod:reg_64 -> bool) (reserved_regs:reg_64 -> bool)
  (reg_names:reg_64 -> string) (counter:nat) (arg_names:nat -> string) : list string & (reg_64 -> string) & nat =
   if regs_mod (of_arg i) then
    (["\"+&r\" (" ^ arg_names i ^ (if reserved_regs (of_arg i) then "_r)" else ")")],
     (fun r -> if r = of_arg i && not (reserved_regs r) then string_of_int counter else reg_names r),
     counter + 1
     ) else ([], reg_names, counter)

// Get a list of strings corresponding to modified inputs
let rec get_modified_input_strings
  (n:nat) (of_arg:reg_nat n -> reg_64) (regs_mod:reg_64 -> bool) (reserved_regs:reg_64 -> bool)
  (args:list td) (i:nat{i + List.Tot.length args <= n}) (ret_val:option string)
  (reg_names:reg_64 -> string) (counter:nat) (arg_names:nat -> string) : list string & (reg_64 -> string) & nat
  = match args with
  | [] -> print_output_ret ret_val reg_names counter
  | a::q ->
      let output, reg_names, counter = print_modified_input n a i of_arg regs_mod reserved_regs reg_names counter arg_names in
      let outputs, reg_names, counter = get_modified_input_strings n of_arg regs_mod reserved_regs q (i+1) ret_val reg_names counter arg_names in
      output @ outputs, reg_names, counter

// Print the list of modified inputs, separated by commas
let print_modified_inputs
  (n:nat)
  (of_arg:reg_nat n -> reg_64)
  (regs_mod:reg_64 -> bool)
  (reserved_regs:reg_64 -> bool)
  (args:list td{List.Tot.length args <= n})
  (ret_val:option string)
  (reg_names:reg_64 -> string)
  (counter:nat)
  (arg_names:nat -> string) =
  let rec aux = function
  | [] -> "\n"
  | [a] -> a ^ "\n"
  | a :: q -> a ^ ", " ^ aux q
  in
  let outputs, output_reg_names, output_nbr = get_modified_input_strings n of_arg regs_mod reserved_regs args 0 ret_val reg_names counter arg_names in
  aux outputs, output_reg_names, output_nbr

// If the register in which an arg is passed is not modified, we should specify it as `"r" (name)`
let print_nonmodified_input
  (n:nat) (of_arg:reg_nat n -> reg_64) (regs_mod:reg_64 -> bool) (reserved_regs:reg_64 -> bool)
  (a:td) (i:nat{i < n}) (reg_names:reg_64 -> string) (counter:nat) (arg_names:nat -> string) : list string & (reg_64 -> string) & nat =
   if regs_mod (of_arg i) then ([], reg_names, counter) else
     (["\"r\" (" ^ arg_names i ^ (if reserved_regs (of_arg i) then "_r)" else  ")")],
     (fun r -> if r = of_arg i && not (reserved_regs r) then string_of_int counter else reg_names r),
     counter + 1)

// Get a list of strings corresponding to modified inputs
let rec get_nonmodified_input_strings
  (n:nat) (of_arg:reg_nat n -> reg_64) (regs_mod:reg_64 -> bool) (reserved_regs:reg_64 -> bool)
  (args:list td) (i:nat{List.Tot.length args + i <= n}) (reg_names:reg_64 -> string) (counter:nat) (arg_names:nat -> string)
  = match args with
  | [] -> [], reg_names, counter
  | a::q ->
    let input, reg_names, counter = print_nonmodified_input n of_arg regs_mod reserved_regs a i reg_names counter arg_names in
    let inputs, reg_names, counter = get_nonmodified_input_strings n of_arg regs_mod reserved_regs q (i+1) reg_names counter arg_names in
    input @ inputs, reg_names, counter

let print_nonmodified_inputs
  (n:nat) (of_arg:reg_nat n -> reg_64) (regs_mod:reg_64 -> bool) (reserved_regs:reg_64 -> bool)
  (args:list td{List.Tot.length args <= n}) (reg_names:reg_64 -> string) (counter:nat) (arg_names:nat -> string) =
  let rec aux = function
  | [] -> "\n"
  | [a] -> a ^ "\n"
  | a :: q -> a ^ ", " ^ aux q
  in
  let inputs, input_reg_names, counter = get_nonmodified_input_strings n of_arg regs_mod reserved_regs args 0 reg_names counter arg_names in
  aux inputs, input_reg_names, counter

// Print the list of modified registers, + memory and cc
let print_modified_registers
  (n:nat)
  (ret_val:option string)
  (of_arg:reg_nat n -> reg_64)
  (regs_mod:reg_64 -> bool)
  (reserved_args:reg_64 -> bool)
  (args:list td) =
  // This register was already specified as output
  let output_register a = Some? ret_val && a = rRax in
  let rec input_register (i:nat) (a:reg_64) : Tot bool (decreases (n-i)) =
    if i >= n then false
    else
      a = of_arg i // This register was already specified for the i-th argument
      || input_register (i+1) a
  in
  let rec aux = function
  | [] -> "\"memory\", \"cc\"\n"
  | a::q ->
    // This register is not modified, or was already specified as input or output: we skip it
    if not (regs_mod a) || input_register 0 a || output_register a then aux q
    // Register not modified or already specified in inputs, we add it
    else "\"%" ^ P.print_reg_name a ^ "\", " ^ aux q
  in aux [rRax; rRbx; rRcx; rRdx; rRsi; rRdi; rRbp; rRsp; rR8; rR9; rR10; rR11; rR12; rR13; rR14; rR15]

// Prints "register uint64_t *argi_r asm("[reg]") = argi;\n"
let print_explicit_register_arg (n:nat) (a:td) (i:nat{i < n}) (of_arg:reg_nat n -> reg_64) (reserved:reg_64 -> bool) (names:nat -> string) =
  let ty = match a with
    | TD_Base _ -> "uint64_t "
    | _ -> "uint64_t *"
  in
  if reserved (of_arg i) then
    // If the associated register is reserved, we really this argument in it. For instance if it is Rdx and we have Mul(x) instructions
    true, "  register " ^ ty ^ names i ^ "_r asm(\"" ^ P.print_reg_name (of_arg i) ^ "\") = " ^ names i ^ ";\n"
  else false, ""

let rec print_explicit_register_args (n:nat) (args:list td) (i:nat{i + List.length args = n}) (of_arg:reg_nat n -> reg_64) (reserved:reg_64 -> bool) (names:nat -> string) =
  match args with
  | [] -> false, ""
  | a::q ->
    let was_explicit, explicit_str = print_explicit_register_arg n a i of_arg reserved names in
    let are_explicit, rest_str = print_explicit_register_args n q (i+1) of_arg reserved names in
    was_explicit || are_explicit, explicit_str ^ rest_str

// If we have a return parameter with a reserved register, print "register uint64_t [name] asm("rax");\n"
let print_register_ret (reserved:reg_64 -> bool) = function
  | None -> ""
  | Some name -> if reserved rRax then "  register uint64_t " ^ name ^ " asm(\"rax\");\n" else "  uint64_t " ^ name ^ ";\n"

(* This is a copy from X64.Print_s, and should remain in sync. The difference is that
   each line should be in quotes, and end by a semicolon in inline assembly *)
let print_cmp (c:ocmp) (counter:int) (p:P.printer) : string =
  let print_ops (o1:operand64) (o2:operand64) : string =
    let first, second = p.P.op_order (P.print_operand o1 p) (P.print_operand o2 p) in
    "  cmp " ^ first ^ ", " ^ second ^ "\n"
  in
  match c with
  | OEq o1 o2 -> "    \"" ^ print_ops o1 o2 ^ "  je " ^ "L" ^ string_of_int counter ^ ";\"\n"
  | ONe o1 o2 -> "    \"" ^ print_ops o1 o2 ^ "  jne "^ "L" ^ string_of_int counter ^ ";\"\n"
  | OLe o1 o2 -> "    \"" ^ print_ops o1 o2 ^ "  jbe "^ "L" ^ string_of_int counter ^ ";\"\n"
  | OGe o1 o2 -> "    \"" ^ print_ops o1 o2 ^ "  jae "^ "L" ^ string_of_int counter ^ ";\"\n"
  | OLt o1 o2 -> "    \"" ^ print_ops o1 o2 ^ "  jb " ^ "L" ^ string_of_int counter ^ ";\"\n"
  | OGt o1 o2 -> "    \"" ^ print_ops o1 o2 ^ "  ja " ^ "L" ^ string_of_int counter ^ ";\"\n"

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
  | _ -> "    \"" ^ P.print_ins ins p ^ ";\""

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
    let jmp = "    \"  jmp L" ^ string_of_int n2 ^ ";\"\n" in
    let label1 = "    \"L" ^ string_of_int n1 ^ ":\"\n" in
    let false_str, n' = print_code false_code n' p in
    let label2 = "    \"L" ^ string_of_int n2 ^ ":\"\n" in
    cmp ^ true_str ^ jmp ^ label1 ^ false_str ^ label2, n'
  | While cond body ->
    let n1 = n in
    let n2 = n + 1 in
    let jmp = "    \"  jmp L" ^ string_of_int n2 ^ ";\"\n" in
    let label1 = "    \"" ^ p.P.align() ^ " 16\nL" ^ string_of_int n1 ^ ":\"\n" in
    let body_str, n' = print_code body (n + 2) p in
    let label2 = "    \"" ^ p.P.align() ^ " 16\nL" ^ string_of_int n2 ^ ":\"\n" in
    let cmp = print_cmp cond n1 p in
    jmp ^ label1 ^ body_str ^ label2 ^ cmp, n'

let rec print_fn_comments = function
  | [] -> ""
  | hd::tl -> "// " ^ hd ^ "\n" ^ print_fn_comments tl

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
  if reserved_regs rRax && Some? ret_val then
    FStar.All.failwith "We require the annotation register uint64_t result(rax), but it would be ignored by gcc < 9"; 

  if inputs_use_rax && Some? ret_val then
    FStar.All.failwith "inputs are not allowed to be passed in rax when there is a return argument";


  // Signature: static inline (void | uint64_t) [name] (arg1, arg2???) {
  let header = "static inline " ^ print_rettype ret_val ^ " " ^ name ^ " (" ^ print_args args 0 arg_names ^ ") \n{\n" in

  // If we have a return value, declare a variable for it
  let ret_reg = print_register_ret reserved_regs ret_val in
  // Explicitly allocate registers when needed
  let has_explicit, explicit_regs = print_explicit_register_args n args 0 of_arg reserved_regs arg_names in

  // Start printing the code, need the asm volatile header
  let start_code = (if Some? ret_val || has_explicit then "\n" else "") ^ "  asm volatile(\n" in

  // Initially, the register names are the same as in assembly
  // This function will be modified to address arguments by their number instead of explicitly allocating them
  let init_reg_names r = "%" ^ P.print_reg_name r in

  // Each *modified* input should be specified as "+r" (name) in the output line
  // If we have a return value, it should be written only and specified as "=r" (name)
  let output_str, output_reg_names, output_nbr =  print_modified_inputs n of_arg regs_mod reserved_regs args ret_val init_reg_names 0 arg_names in
  let output_str = "  : " ^ output_str in

  // Each *non-modified* input should be specified as `"r" (name)` in the input line
  let input_str, inlined_reg_names, _ = print_nonmodified_inputs n of_arg regs_mod reserved_regs args output_reg_names output_nbr arg_names in
  let input_str = "  : " ^ input_str in

  // In inline assembly, operands are prefixed by "%%" instead of "%" in regular GCC assembly
  let printer = {P.gcc with P.print_reg_name = inlined_reg_names } in

  // The assembly should be compliant with gcc
  let (code_str, final_label) = print_code (remove_blank code) label printer in


  // Every modified register that wasn't used for the inputs/outputs should be specified in the modified line
  let modified_str = "  : " ^ print_modified_registers n ret_val of_arg regs_mod reserved_regs args in

  let close_code = "  );\n" ^ (if Some? ret_val then "\n  return " ^ Some?.v ret_val ^ ";\n" else "") ^ "}\n\n" in

  print_string (comments ^ header ^ ret_reg ^ explicit_regs ^ start_code ^ code_str ^ output_str ^ input_str ^ modified_str ^ close_code);
  final_label
