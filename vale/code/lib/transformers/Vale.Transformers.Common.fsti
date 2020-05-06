module Vale.Transformers.Common

open Vale.X64.Machine_s
open Vale.Def.PossiblyMonad
open Vale.X64.Decls

/// Common definitions amongst transformations.

let equiv_states (s1 s2:va_state) =
  let open Vale.X64.State in
  s1.vs_ok == s2.vs_ok /\
  Vale.X64.Regs.equal s1.vs_regs s2.vs_regs /\
  Vale.X64.Flags.sel fCarry s1.vs_flags == Vale.X64.Flags.sel fCarry s2.vs_flags /\
  Vale.X64.Flags.sel fOverflow s1.vs_flags == Vale.X64.Flags.sel fOverflow s2.vs_flags /\
  s1.vs_heap == s2.vs_heap /\
  s1.vs_stack == s2.vs_stack /\
  s1.vs_stackTaint == s2.vs_stackTaint
