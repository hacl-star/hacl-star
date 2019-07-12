module X64.Semantics_Equiv

module S = X64.Bytes_Semantics_s
open X64.Memory_s
open X64.Semantics_s

val equiv_eval_ins (s:state) (ins:S.ins) : Lemma (
   let s_hi = run (eval_ins ins) s in
   let s_bytes = S.run (S.eval_ins ins) s.state in
   s_hi.state.S.ok ==> s_hi.state == s_bytes)

val equiv_eval_code (code:code) (fuel:nat) (s:state) : Lemma
  (requires True)
  (ensures
  (let s_hi = eval_code code fuel s in
   let s_bytes = S.eval_code code fuel s.state in
   Some? s_hi /\  (Some?.v s_hi).state.S.ok ==>
   Some? s_bytes /\ (Some?.v s_hi).state == Some?.v s_bytes))
  (decreases %[fuel; code])

val equiv_eval_codes (l:codes) (fuel:nat) (s:state) : Lemma
  (requires True)
  (ensures
  (let s_hi = eval_codes l fuel s in
  let s_bytes = S.eval_codes l fuel s.state in
   Some? s_hi /\  (Some?.v s_hi).state.S.ok ==>
   Some? s_bytes /\ (Some?.v s_hi).state == Some?.v s_bytes))
  (decreases %[fuel; l])

val equiv_eval_while (b:ocmp) (c:code) (fuel:nat) (s:state) : Lemma
  (requires True)
  (ensures (
  let s_hi = eval_while b c fuel s in
  let s_bytes = S.eval_while b c fuel s.state in
   Some? s_hi /\  (Some?.v s_hi).state.S.ok ==>
   Some? s_bytes /\ (Some?.v s_hi).state == Some?.v s_bytes))
  (decreases %[fuel; c])
