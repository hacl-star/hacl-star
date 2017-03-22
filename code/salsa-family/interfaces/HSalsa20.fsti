module HSalsa20


open FStar.Buffer
open Spec.HSalsa20
open Hacl.Spec.Endianness


let h32     = Hacl.UInt32.t
let u32     = FStar.UInt32.t
let uint8_p = buffer Hacl.UInt8.t
let state   = b:buffer h32{length b = 16}

#reset-options "--max_fuel 0 --max_ifuel 0"

let op_String_Access h (b:uint8_p{live h b}) = reveal_sbytes (as_seq h b)

val hsalsa20:
  output:uint8_p{length output = 32} ->
  key:uint8_p{length key = 32} ->
  nonce:uint8_p{length nonce = 16} ->
  Stack unit
    (requires (fun h -> live h output /\ live h nonce /\ live h key))
    (ensures  (fun h0 _ h1 -> live h0 output /\ live h0 nonce /\ live h0 key /\
      modifies_1 output h0 h1 /\ live h1 output
      /\ (h1.[output] == hsalsa20 h0.[key] h0.[nonce])))
