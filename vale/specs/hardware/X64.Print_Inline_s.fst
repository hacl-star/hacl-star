module X64.Print_Inline_s

open X64.Machine_s
open X64.Bytes_Semantics_s
open X64.Taint_Semantics_s
open FStar.IO
open Interop.Base
open Interop.X64
module P = X64.Print_s

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
let print_arg (a:td) (i:nat) = match a with
  | TD_Base src -> print_basetype src ^ " arg" ^ string_of_int i
  | TD_Buffer src _ _ | TD_ImmBuffer src _ _ -> print_basetype src ^ "* arg" ^ string_of_int i

// Prints a list of args with their types, separated by a comma
let rec print_args (args:list td) (i:nat) = match args with
  | [] -> ""
  | [a] -> print_arg a i
  | a::q -> print_arg a i ^ ", " ^ print_args q (i+1)

// Prints "register uint64_t* argi_r asm("[reg]") = argi;\n"
let print_register_arg (n:nat) (a:td) (i:nat{i < n}) (of_arg:reg_nat n -> reg) =
  let ty = match a with
    | TD_Base _ -> "uint64_t"
    | _ -> "uint64_t*"
  in
  "  register " ^ ty ^ " arg" ^ string_of_int i ^ "_r asm(\"" ^ P.print_reg_name (of_arg i) ^ "\") = arg" ^ string_of_int i ^ ";\n"

let rec print_register_args (n:nat) (args:list td) (i:nat{i + List.length args = n}) (of_arg:reg_nat n -> reg) = match args with
  | [] -> ""
  | a::q -> print_register_arg n a i of_arg ^ print_register_args n q (i+1) of_arg

// If we have a return parameter, print "register uint64_t* [name] asm("rax");\n"
let print_register_ret = function
  | None -> ""
  | Some name -> "  register uint64_t " ^ name ^ " asm(\"rax\");\n"

// Prints `"=r" (name)` if an output is specified
let print_output_ret = function
  | None -> []
  | Some name -> ["\"=r\" (" ^ name ^ ")"]

// If the register in which a is passed is modified, we should specify `"+r" (name)`
let print_modified_input (n:nat) (a:td) (i:nat{i < n}) (of_arg:reg_nat n -> reg) (regs_mod:reg -> bool) =
   if regs_mod (of_arg i) then ["\"+r\" (arg" ^ string_of_int i ^ "_r)"] else []

// Get a list of strings corresponding to modified inputs
let rec get_modified_input_strings (n:nat) (of_arg:reg_nat n -> reg) (regs_mod:reg -> bool) (args:list td) (i:nat{i + List.Tot.length args <= n}) (ret_val:option string) = match args with
  | [] -> print_output_ret ret_val
  | a::q -> print_modified_input n a i of_arg regs_mod @ get_modified_input_strings n of_arg regs_mod q (i+1) ret_val

// Print the list of modified inputs, separated by commas
let print_modified_inputs (n:nat) (of_arg:reg_nat n -> reg) (regs_mod:reg -> bool) (args:list td{List.Tot.length args <= n}) (ret_val:option string) =
  let rec aux = function
  | [] -> "\n"
  | [a] -> a ^ "\n"
  | a :: q -> a ^ ", " ^ aux q
  in aux (get_modified_input_strings n of_arg regs_mod args 0 ret_val)

// If the register in which an arg is passed is not modified, we should specify it as `"r" (name)`
let print_nonmodified_input (n:nat) (of_arg:reg_nat n -> reg) (regs_mod:reg -> bool) (a:td) (i:nat{i < n}) =
   if regs_mod (of_arg i) then [] else ["\"r\" (arg" ^ string_of_int i ^ "_r)"]

// Get a list of strings corresponding to modified inputs
let rec get_nonmodified_input_strings (n:nat) (of_arg:reg_nat n -> reg) (regs_mod:reg -> bool) (args:list td) (i:nat{List.Tot.length args + i <= n}) = match args with
  | [] -> []
  | a::q -> print_nonmodified_input n of_arg regs_mod a i @ get_nonmodified_input_strings n of_arg regs_mod q (i+1)

let print_nonmodified_inputs (n:nat) (of_arg:reg_nat n -> reg) (regs_mod:reg->bool) (args:list td{List.Tot.length args <= n}) =
  let rec aux = function
  | [] -> "\n"
  | [a] -> a ^ "\n"
  | a :: q -> a ^ ", " ^ aux q
  in aux (get_nonmodified_input_strings n of_arg regs_mod args 0)

// Print the list of modified registers, + memory and cc
let print_modified_registers 
  (n:nat)
  (ret_val:option string) 
  (of_arg:reg_nat n -> reg)
  (regs_mod:reg -> bool) 
  (args:list td) =
  // This register was already specified as output
  let output_register a = Some? ret_val && a = Rax in
  let rec input_register (i:nat) (a:reg) : Tot bool (decreases (n-i)) = 
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
  in aux [Rax; Rbx; Rcx; Rdx; Rsi; Rdi; Rbp; Rsp; R8; R9; R10; R11; R12; R13; R14; R15]

(* This is a copy from X64.Print_s, and should remain in sync. The difference is that
   each line should be in quotes, and end by a semicolon in inline assembly *)
let print_cmp (c:ocmp) (counter:int) (p:P.printer) : string =
  let print_ops (o1:operand) (o2:operand) : string =
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


let rec print_block (b:tainted_codes) (n:int) (p:P.printer) : string * int =
  match b with
  | Nil -> "", n
  | head :: tail ->
    let head_str, n' = print_code head n p in
    let rest, n'' = print_block tail n' p in
    head_str ^ rest, n''
and print_code (c:tainted_code) (n:int) (p:P.printer) : string * int =
  match c with
  | Ins ins -> ("    \"" ^ P.print_ins ins p ^ ";\"\n", n)
  | Block b -> print_block b n p
  | IfElse cond true_code false_code ->
    let n1 = n in
    let n2 = n + 1 in
    let cmp = print_cmp (P.cmp_not cond.o) n1 p in
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
    let cmp = print_cmp cond.o n1 p in
    jmp ^ label1 ^ body_str ^ label2 ^ cmp, n'


let print_inline 
  (name:string) 
  (label:int) 
  (ret_val:option string) 
  (n:nat)
  (args:list td{List.length args = n})
  (code:tainted_code)
  (of_arg:reg_nat (List.length args) -> reg)
  (regs_mod:reg -> bool)
  : FStar.All.ML int =
  // Signature: static inline (void | uint64_t) [name] (arg1, arg2…) {
  let header = "static inline " ^ print_rettype ret_val ^ " " ^ name ^ " (" ^ print_args args 0 ^ ") {\n" in
  
  // Arguments in registers: register uint64_t* argi_r asm("reg") = argi;
  let arg_regs = print_register_args n args 0 of_arg in
  let ret_reg = print_register_ret ret_val in

  // Start printing the code, need the __asm__ __volatile__ header
  let start_code = "\n  __asm__ __volatile__(\n" in

  // In inline assembly, operands are prefixed by "%%" instead of "%" in regular GCC assembly
  let printer = {P.gcc with P.reg_prefix = fun () -> "%%"} in

  // The assembly should be compliant with gcc
  let code_str, final_label = print_code code label printer in

  // Each *modified* input should be specified as "+r" (name) in the output line
  // If we have a return value, it should be written only and specified as "=r" (name)
  let output_str = "  : " ^ print_modified_inputs n of_arg regs_mod args ret_val in

  // Each *non-modified* input should be specified as `"r" (name)` in the input line
  let input_str = "  : " ^ print_nonmodified_inputs n of_arg regs_mod args in

  // Every modified register that wasn't used for the inputs/outputs should be specified in the modified line
  let modified_str = "  : " ^ print_modified_registers n ret_val of_arg regs_mod args in

  let close_code = "  );\n" ^ (if Some? ret_val then "\nreturn " ^ Some?.v ret_val ^ ";\n" else "") ^ "}\n\n" in

  print_string (header ^ arg_regs ^ ret_reg ^ start_code ^ code_str ^ output_str ^ input_str ^ modified_str ^ close_code);
  final_label
