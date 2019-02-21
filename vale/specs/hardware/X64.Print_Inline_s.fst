module X64.Print_Inline_s

open X64.Machine_s
open X64.Bytes_Semantics_s
open X64.Taint_Semantics_s
open FStar.IO
open Interop.Base
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

// Returns "uint8_t arg2" or "const uint64_t* arg0" for instance
let print_arg (a:td) (i:nat) = match a with
  | TD_Base src -> print_basetype src ^ " arg" ^ string_of_int i
  | TD_Buffer src _ {modified=true} -> print_basetype src ^ "* arg" ^ string_of_int i
  | TD_Buffer src _ _ | TD_ImmBuffer src _ _ -> "const " ^ print_basetype src ^ "* arg" ^ string_of_int i

// Prints a list of args with their types, separated by a comma
let rec print_args (args:list td) (i:nat) = match args with
  | [] -> ""
  | [a] -> print_arg a i
  | a::q -> print_arg a i ^ ", " ^ print_args q (i+1)

// Prints "register uint64_t* argi_r asm("[reg]") = argi;\n"
let print_register_arg (a:td) (i:nat) (of_arg:nat -> reg) =
  "  register uint64_t* arg" ^ string_of_int i ^ "_r asm(\"" ^ P.print_reg_name (of_arg i) ^ "\") = arg" ^ string_of_int i ^ ";\n"

let rec print_register_args (args:list td) (i:nat) (of_arg:nat -> reg) = match args with
  | [] -> ""
  | a::q -> print_register_arg a i of_arg ^ print_register_args q (i+1) of_arg

// If we have a return parameter, print "register uint64_t* [name] asm("rax");\n"
let print_register_ret = function
  | None -> ""
  | Some name -> "  register uint64_t* " ^ name ^ " asm(\"rax\");\n"

// Prints `"=r" (name)` if an output is specified
let print_output_ret = function
  | None -> []
  | Some name -> ["\"=r\" (" ^ name ^ ")"]

// If a is a integer or a modified buffer, we should specify `"+r" (name)`
let print_modified_input (a:td) (i:nat) = match a with
   | TD_Base _ -> ["\"+r\" (arg" ^ string_of_int i ^ "_r)"]
   | TD_Buffer _ _ {modified=true} -> ["\"+r\" (arg" ^ string_of_int i ^ "_r)"]
   | _ -> []

// Get a list of strings corresponding to modified inputs
let rec get_modified_input_strings (args:list td) (i:nat) (ret_val:option string) = match args with
  | [] -> print_output_ret ret_val
  | a::q -> print_modified_input a i @ get_modified_input_strings q (i+1) ret_val

// Print the list of modified inputs, separated by commas
let print_modified_inputs (args:list td) (ret_val:option string) =
  let rec aux = function
  | [] -> "\n"
  | [a] -> a ^ "\n"
  | a :: q -> a ^ ", " ^ aux q
  in aux (get_modified_input_strings args 0 ret_val)

// If an arg is not modified, we should specify it as `"r" (name)`
let print_nonmodified_input (a:td) (i:nat) = match a with
  | TD_Base _ -> []
  | TD_Buffer _ _ {modified=true} -> []
  | _ -> ["\"r\" (arg" ^ string_of_int i ^ "_r)"]

// Get a list of strings corresponding to modified inputs
let rec get_nonmodified_input_strings (args:list td) (i:nat) = match args with
  | [] -> []
  | a::q -> print_nonmodified_input a i @ get_nonmodified_input_strings q (i+1)

let print_nonmodified_inputs (args:list td) =
  let rec aux = function
  | [] -> "\n"
  | [a] -> a ^ "\n"
  | a :: q -> a ^ ", " ^ aux q
  in aux (get_nonmodified_input_strings args 0)

// Print the list of modified registers, + memory and cc
let print_modified_registers 
  (ret_val:option string) 
  (of_arg:nat -> reg)
  (regs_mod:reg -> bool) 
  (args:list td) =
  // This register was already specified as output
  let output_register a = Some? ret_val && a = Rax in
  let n = List.length args in
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
    else "%" ^ P.print_reg_name a ^ ", " ^ aux q
  in aux [Rax; Rbx; Rcx; Rdx; Rsi; Rdi; Rbp; Rsp; R8; R9; R10; R11; R12; R13; R14; R15]

let print_inline 
  (name:string) 
  (label:int) 
  (ret_val:option string) 
  (args:list td)
  (code:tainted_code)
  (of_arg:nat -> reg)
  (regs_mod:reg -> bool)
  : FStar.All.ML int =
  // Signature: static inline (void | uint64_t) [name] (arg1, arg2…) {
  let header = "static inline " ^ print_rettype ret_val ^ " " ^ name ^ " (" ^ print_args args 0 ^ ") {\n" in
  
  // Arguments in registers: register uint64_t* argi_r asm("reg") = argi;
  let arg_regs = print_register_args args 0 of_arg in
  let ret_reg = print_register_ret ret_val in

  // Start printing the code, need the __asm__ __volatile__ header
  let start_code = "\n  __asm__ __volatile__(\n" in

  // The assembly should be compliant with gcc
  let code_str, final_label = P.print_code code label P.gcc in

  // Each *modified* input should be specified as "+r" (name) in the output line
  // If we have a return value, it should be written only and specified as "=r" (name)
  let output_str = "  : " ^ print_modified_inputs args ret_val in

  // Each *non-modified* input should be specified as `"r" (name)` in the input line
  let input_str = "  : " ^ print_nonmodified_inputs args in

  // Every modified register that wasn't used for the inputs/outputs should be specified in the modified line
  let modified_str = "  : " ^ print_modified_registers ret_val of_arg regs_mod args in

  let close_code = "  );\n}\n" in

  print_string (header ^ arg_regs ^ ret_reg ^ start_code ^ code_str ^ output_str ^ input_str ^ modified_str ^ close_code);
  final_label
