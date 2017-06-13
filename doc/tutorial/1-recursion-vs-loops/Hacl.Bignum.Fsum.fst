module Hacl.Bignum.Fsum

module ST = FStar.HyperStack.ST

open FStar.HyperStack.All


open FStar.UInt64     // F* 64-bit unsigned machine integers
open FStar.HyperStack // F* memory model
open FStar.Buffer     // F* pointer arithmetic model

module U32 = FStar.UInt32 // Module alias

#set-options "--initial_fuel 1 --max_fuel 1" // Tuning verification parameters

type u32 = FStar.UInt32.t                // Type alias for uint32
type u64 = FStar.UInt64.t                // Type alias for uint64
type felem = b:buffer u64{length b = 5}  // X25519-donna bignum array


val fsum:
  a:felem -> b:felem ->
  i:u32{U32.v i <= 5} ->
  Stack unit
    (requires (fun h -> live h a /\ live h b))
    (ensures (fun h0 _ h1 -> true))
let rec fsum a b i =
  if U32.(i =^ 0ul) then ()
  else (
    let i = U32.(i -^ 1ul) in
    let ai = a.(i) in let bi = b.(i) in
    a.(i) <- ai +%^ bi;
    fsum a b i
  )
