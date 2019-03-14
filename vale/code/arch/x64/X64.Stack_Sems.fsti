module X64.Stack_Sems

open X64.Machine_s
open X64.Stack_i
module S = X64.Bytes_Semantics_s

val stack_to_s: (s:stack) -> Tot S.stack
val stack_from_s: (s:S.stack) -> Tot stack

val lemma_state_of_to (s:stack) : Lemma 
  (stack_from_s (stack_to_s s) == s)
  [SMTPat (stack_from_s (stack_to_s s))]
