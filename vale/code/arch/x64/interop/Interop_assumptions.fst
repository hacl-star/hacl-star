module Interop_assumptions

open FStar.HyperStack.ST
module HS = FStar.HyperStack
open Interop
open X64.Machine_s
module TS = X64.Taint_Semantics_s
module BS = X64.Bytes_Semantics_s

assume val st_put (p:HS.mem -> Type0) (f:(h0:HS.mem{p h0}) -> GTot HS.mem) : Stack unit (fun h0 -> p h0) (fun h0 _ h1 -> f h0 == h1)

//The map from buffers to addresses in the heap, that remains abstract
assume val addrs: addr_map

//The initial registers and xmms
assume val init_regs:reg -> nat64
assume val init_xmms:xmm -> quad32

// Abstract current operating system from Low*
assume val win:bool

// Callee-saved registers that must be saved through an execution
let calling_conventions (w:bool) (s0:TS.traceState) (s1:TS.traceState) =
  let s0 = s0.TS.state in
  let s1 = s1.TS.state in
  // Ensures that the execution didn't crash
  s1.BS.ok /\
  // Ensures that the callee_saved registers are correct
  (if w then (
    // Calling conventions for Windows
    s0.BS.regs Rbx == s1.BS.regs Rbx /\
    s0.BS.regs Rbp == s1.BS.regs Rbp /\
    s0.BS.regs Rdi == s1.BS.regs Rdi /\
    s0.BS.regs Rsi == s1.BS.regs Rsi /\
    s0.BS.regs Rsp == s1.BS.regs Rsp /\
    s0.BS.regs R12 == s1.BS.regs R12 /\
    s0.BS.regs R13 == s1.BS.regs R13 /\
    s0.BS.regs R14 == s1.BS.regs R14 /\
    s0.BS.regs R15 == s1.BS.regs R15 /\
    s0.BS.xmms 6 == s1.BS.xmms 6 /\
    s0.BS.xmms 7 == s1.BS.xmms 7 /\
    s0.BS.xmms 8 == s1.BS.xmms 8 /\
    s0.BS.xmms 9 == s1.BS.xmms 9 /\
    s0.BS.xmms 10 == s1.BS.xmms 10 /\
    s0.BS.xmms 11 == s1.BS.xmms 11 /\
    s0.BS.xmms 12 == s1.BS.xmms 12 /\
    s0.BS.xmms 13 == s1.BS.xmms 13 /\
    s0.BS.xmms 14 == s1.BS.xmms 14 /\
    s0.BS.xmms 15 == s1.BS.xmms 15  
  ) else (
    // Calling conventions for Linux
    s0.BS.regs Rbx == s1.BS.regs Rbx /\
    s0.BS.regs Rbp == s1.BS.regs Rbp /\
    s0.BS.regs R12 == s1.BS.regs R12 /\
    s0.BS.regs R13 == s1.BS.regs R13 /\
    s0.BS.regs R14 == s1.BS.regs R14 /\
    s0.BS.regs R15 == s1.BS.regs R15
    )
  )
