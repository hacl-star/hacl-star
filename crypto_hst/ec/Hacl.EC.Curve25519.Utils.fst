module Hacl.EC.Curve25519.Utils

open FStar.Mul
open FStar.HST
open FStar.HyperStack
open FStar.Ghost
open FStar.Buffer
open FStar.Buffer.Quantifiers
open FStar.Math.Lib

open Hacl.UInt64

open Hacl.EC.Curve25519.Parameters
open Hacl.EC.Curve25519.Bigint

module H64 = Hacl.UInt64
module H128 = Hacl.UInt128

#reset-options "--z3timeout 20 --max_fuel 0 --initial_fuel 0 --max_ifuel 0 --initial_ifuel 0"

val update_5: 
  c:bigint ->
  c0:H64.t -> c1:H64.t -> c2:H64.t ->
  c3:H64.t -> c4:H64.t ->
  Stack unit
    (requires (fun h -> live h c))
    (ensures  (fun h0 _ h1 -> live h1 c /\ modifies_1 c h0 h1
      /\ get h1 c 0 == c0 /\ get h1 c 1 == c1 /\ get h1 c 2 == c2
      /\ get h1 c 3 == c3 /\ get h1 c 4 == c4))
let update_5 c c0 c1 c2 c3 c4 =
  c.(0ul) <- c0;
  c.(1ul) <- c1;
  c.(2ul) <- c2;
  c.(3ul) <- c3;
  c.(4ul) <- c4

val update_6:
  c:bigint{length c >= 2*norm_length-1} ->
  c0:H64.t -> c1:H64.t -> c2:H64.t ->
  c3:H64.t -> c4:H64.t -> c5:H64.t ->
  Stack unit
    (requires (fun h -> live h c))
    (ensures  (fun h0 _ h1 -> live h1 c /\ modifies_1 c h0 h1
      /\ get h1 c 0 == c0 /\ get h1 c 1 == c1 /\ get h1 c 2 == c2
      /\ get h1 c 3 == c3 /\ get h1 c 4 == c4 /\ get h1 c 5 == c5))
let update_6 c c0 c1 c2 c3 c4 c5 =
  c.(0ul) <- c0;
  c.(1ul) <- c1;
  c.(2ul) <- c2;
  c.(3ul) <- c3;
  c.(4ul) <- c4;
  c.(5ul) <- c5

val update_9: 
  c:bigint{length c >= 2*norm_length-1} ->
  c0:H64.t -> c1:H64.t -> c2:H64.t ->
  c3:H64.t -> c4:H64.t -> c5:H64.t ->
  c6:H64.t -> c7:H64.t -> c8:H64.t ->
  Stack unit
    (requires (fun h -> live h c))
    (ensures  (fun h0 _ h1 -> live h1 c /\ modifies_1 c h0 h1
      /\ get h1 c 0 == c0 /\ get h1 c 1 == c1 /\ get h1 c 2 == c2
      /\ get h1 c 3 == c3 /\ get h1 c 4 == c4 /\ get h1 c 5 == c5
      /\ get h1 c 6 == c6 /\ get h1 c 7 == c7 /\ get h1 c 8 == c8))
let update_9 c c0 c1 c2 c3 c4 c5 c6 c7 c8 =
  c.(0ul) <- c0;
  c.(1ul) <- c1;
  c.(2ul) <- c2;
  c.(3ul) <- c3;
  c.(4ul) <- c4;
  c.(5ul) <- c5;
  c.(6ul) <- c6;
  c.(7ul) <- c7;
  c.(8ul) <- c8

val update_wide_5: 
  c:bigint_wide ->
  c0:H128.t -> c1:H128.t -> c2:H128.t ->
  c3:H128.t -> c4:H128.t ->
  Stack unit
    (requires (fun h -> live h c))
    (ensures  (fun h0 _ h1 -> live h1 c /\ modifies_1 c h0 h1
      /\ get h1 c 0 == c0 /\ get h1 c 1 == c1 /\ get h1 c 2 == c2
      /\ get h1 c 3 == c3 /\ get h1 c 4 == c4))
let update_wide_5 c c0 c1 c2 c3 c4 =
  c.(0ul) <- c0;
  c.(1ul) <- c1;
  c.(2ul) <- c2;
  c.(3ul) <- c3;
  c.(4ul) <- c4

val update_wide_6:
  c:bigint_wide{length c >= 2*norm_length-1} ->
  c0:H128.t -> c1:H128.t -> c2:H128.t ->
  c3:H128.t -> c4:H128.t -> c5:H128.t ->
  Stack unit
    (requires (fun h -> live h c))
    (ensures  (fun h0 _ h1 -> live h1 c /\ modifies_1 c h0 h1
      /\ get h1 c 0 == c0 /\ get h1 c 1 == c1 /\ get h1 c 2 == c2
      /\ get h1 c 3 == c3 /\ get h1 c 4 == c4 /\ get h1 c 5 == c5))
let update_wide_6 c c0 c1 c2 c3 c4 c5 =
  c.(0ul) <- c0;
  c.(1ul) <- c1;
  c.(2ul) <- c2;
  c.(3ul) <- c3;
  c.(4ul) <- c4;
  c.(5ul) <- c5

val update_wide_9: 
  c:bigint_wide{length c >= 2*norm_length-1} ->
  c0:H128.t -> c1:H128.t -> c2:H128.t ->
  c3:H128.t -> c4:H128.t -> c5:H128.t ->
  c6:H128.t -> c7:H128.t -> c8:H128.t ->
  Stack unit
    (requires (fun h -> live h c))
    (ensures  (fun h0 _ h1 -> live h1 c /\ modifies_1 c h0 h1
      /\ get h1 c 0 == c0 /\ get h1 c 1 == c1 /\ get h1 c 2 == c2
      /\ get h1 c 3 == c3 /\ get h1 c 4 == c4 /\ get h1 c 5 == c5
      /\ get h1 c 6 == c6 /\ get h1 c 7 == c7 /\ get h1 c 8 == c8))
let update_wide_9 c c0 c1 c2 c3 c4 c5 c6 c7 c8 =
  c.(0ul) <- c0;
  c.(1ul) <- c1;
  c.(2ul) <- c2;
  c.(3ul) <- c3;
  c.(4ul) <- c4;
  c.(5ul) <- c5;
  c.(6ul) <- c6;
  c.(7ul) <- c7;
  c.(8ul) <- c8
