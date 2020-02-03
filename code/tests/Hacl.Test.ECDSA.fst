module Hacl.Test.ECDSA

open FStar.HyperStack.ST
open Test.Lowstarize

open Lib.IntTypes

open Hacl.Impl.ECDSA
open Spec.ECDSA.Test.Vectors

module L = Test.Lowstarize
module B = LowStar.Buffer

#set-options "--fuel 0 --ifuel 0 --z3rlimit 100"

noextract
let vectors_tmp = List.Tot.map 
  (fun x -> h x.msg, h x.qx, h x.qy, h x.r, h x.s, x.result)
  test_vectors

%splice[vectors_low] (lowstarize_toplevel "vectors_tmp" "vectors_low")

// Cheap alternative to friend Lib.IntTypes needed because Test.Lowstarize uses UInt8.t
assume val declassify_uint8: squash (uint8 == UInt8.t)

let vec8 = L.lbuffer UInt8.t

let vector = vec8 & vec8 & vec8 & vec8 & vec8 & bool

// This could replace TestLib.compare_and_print
val compare_and_print: b1:B.buffer UInt8.t -> b2:B.buffer UInt8.t -> len:UInt32.t 
  -> Stack bool
  (requires fun h0 -> B.live h0 b1 /\ B.live h0 b2 /\ B.length b1 == v len /\ B.length b2 == v len)
  (ensures  fun h0 _ h1 -> B.modifies B.loc_none h0 h1)
let compare_and_print b1 b2 len =
  push_frame();
  LowStar.Printf.(printf "Expected: %xuy\n" len b1 done);
  LowStar.Printf.(printf "Computed: %xuy\n" len b2 done);
  let b = Lib.ByteBuffer.lbytes_eq #len b1 b2 in
  if b then 
    LowStar.Printf.(printf "PASS\n" done)
  else
    LowStar.Printf.(printf "FAIL\n" done);
  pop_frame();
  b

let test_one (vec:vector) : Stack unit (requires fun _ -> True) (ensures fun _ _ _ -> True) =
  let max_msg_len = 0 in
  let LB msg_len msg, 
      LB qx_len qx, 
      LB qy_len qy, 
      LB r_len r, 
      LB s_len s, 
      result = vec 
  in
  B.recall msg;
  B.recall qx;
  B.recall qy;
  B.recall r;
  B.recall s;
  // We need to check this at runtime because Low*-ized vectors don't carry any refinements
  if not (qx_len = 32ul && qy_len = 32ul && r_len = 32ul && s_len = 32ul)
  then C.exit (-1l)
  else
    begin
    push_frame();
    let qxy = B.alloca (u8 0) 64ul in
    B.blit qx 0ul qxy 0ul 32ul;
    B.blit qy 0ul qxy 32ul 32ul;
    let result' = ecdsa_p256_sha2_verify_u8 msg_len msg qxy r s in
    if result' = result then ()
    else 
      begin
      LowStar.Printf.(printf "FAIL\n" done);
      C.exit 1l
      end;
    pop_frame()
    end


inline_for_extraction noextract
let test_many #a (label:C.String.t) 
  (f:a -> Stack unit (fun _ -> True) (fun _ _ _ -> True)) (vec: L.lbuffer a) 
=
  C.String.print label;
  C.String.(print !$"\n");
  let L.LB len vs = vec in
  let f (i:UInt32.t{0 <= v i /\ v i < v len}): Stack unit
    (requires fun h -> True)
    (ensures fun h0 _ h1 -> True)
  =
    let open LowStar.BufferOps in
    B.recall vs;
    LowStar.Printf.(printf "ECDSA Test %ul/%ul\n" (i +! 1ul) len done);
    f vs.(i)
  in
  C.Loops.for 0ul len (fun _ _ -> True) f

let main () : St C.exit_code =
  test_many C.String.(!$"[ECDSA]") test_one vectors_low;
  C.EXIT_SUCCESS

