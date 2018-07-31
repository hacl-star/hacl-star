module Hacl.Test.Aes128
open FStar.HyperStack.All
open C.Nullity

#set-options "--lax"

open FStar.Buffer

val main: unit -> ST C.exit_code
  (requires (fun h -> True))
  (ensures  (fun h0 r h1 -> True))
let main () =
  push_frame();
  pop_frame();
  C.EXIT_SUCCESS
