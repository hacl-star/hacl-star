module Lib.CreateN

open FStar.Mul
open FStar.HyperStack
open FStar.HyperStack.ST

open Lib.IntTypes
open Lib.IntVector
open Lib.Buffer

module ST = FStar.HyperStack.ST
module LSeq = Lib.Sequence

#set-options "--z3rlimit 50 --fuel 0 --ifuel 0"


let create8_st #a st v0 v1 v2 v3 v4 v5 v6 v7 =
  let h0 = ST.get () in
  st.(0ul) <- v0;
  st.(1ul) <- v1;
  st.(2ul) <- v2;
  st.(3ul) <- v3;
  st.(4ul) <- v4;
  st.(5ul) <- v5;
  st.(6ul) <- v6;
  st.(7ul) <- v7;
  let h1 = ST.get () in
  assert (LSeq.equal (as_seq h1 st) (create8 v0 v1 v2 v3 v4 v5 v6 v7))


let create16_st #w st v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 =
  let h0 = ST.get () in
  st.(0ul) <- v0;
  st.(1ul) <- v1;
  st.(2ul) <- v2;
  st.(3ul) <- v3;
  st.(4ul) <- v4;
  st.(5ul) <- v5;
  st.(6ul) <- v6;
  st.(7ul) <- v7;
  st.(8ul) <- v8;
  st.(9ul) <- v9;
  st.(10ul) <- v10;
  st.(11ul) <- v11;
  st.(12ul) <- v12;
  st.(13ul) <- v13;
  st.(14ul) <- v14;
  st.(15ul) <- v15;
  let h1 = ST.get () in
  assert (LSeq.equal (as_seq h1 st) (create16 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15))
