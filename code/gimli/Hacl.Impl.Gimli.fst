module Hacl.Impl.Gimli

open FStar.HyperStack
open FStar.HyperStack.All
open FStar.Mul

open Lib.IntTypes
open Lib.Buffer


module ST = FStar.HyperStack.ST
module LSeq = Lib.Sequence
module Loops = Lib.LoopCombinators

module S = Spec.Gimli

#set-options "--z3rlimit 50 --fuel 0 --ifuel 0"

private
unfold
let state = lbuffer uint32 12ul

(*
 * Exercise: Implement the functions below and prove functional
 *   correctness of Low* code using a pure spec `Spec.Gimli.fst`
 *
 * Local Makefile assumes that the current directory (gimli/)
 *   is a part of the hacl-star project (hacl-star/code/),
 *   so that it can use rules defined in hacl-star/Makefile.include
 *
 * Once you have the implementation, make sure that your code
 *   is valid Low* and compiles to C
 *
 * To do so, you can run `make -j N` (where N is the degree of
 *   parallelism you want) in the current directory (gimli/) and
 *   it should build the libgimli.a and gimli-test.exe files in
 *   the gimli/dist directory
 *
 * The output of ./gimli-test.exe should match with the expected
 *   result definied in test.exp
 *
 * To see the extracted C code, see dist/Hacl_Impl_Gimli.c
*)

private
val swap:
    s:state
  -> i:size_t{v i < 12}
  -> j:size_t{v j < 12} ->
  Stack unit
  (requires fun h -> live h s)
  (ensures  fun h0 _ h1 -> modifies (loc s) h0 h1 /\
    as_seq h1 s == S.swap (as_seq h0 s) (v i) (v j))

let swap s i j = admit()


private
val column_round:
    col:size_t{v col < 4}
  -> s:state ->
  Stack unit
  (requires fun h -> live h s)
  (ensures  fun h0 _ h1 -> modifies (loc s) h0 h1 /\
    as_seq h1 s == S.column_round (v col) (as_seq h0 s))

let column_round col s = admit()


private
val gimli_round:
    r:size_t{v r < 24}
  -> s:state ->
  Stack unit
  (requires fun h -> live h s)
  (ensures  fun h0 _ h1 -> modifies (loc s) h0 h1 /\
    as_seq h1 s == S.gimli_round (v r) (as_seq h0 s))

let gimli_round r s =
  let r = 24ul -. r in
  assert_norm (3 = pow2 2 - 1);
  mod_mask_lemma r 2ul;
  assert (v (mod_mask #U32 #PUB 2ul) == v 3ul);
  assert (v (r &. 3ul) == v r % 4);
  admit()


val gimli: s:state ->
  Stack unit
  (requires fun h -> live h s)
  (ensures  fun h0 _ h1 -> modifies (loc s) h0 h1 /\
    as_seq h1 s == S.gimli (as_seq h0 s))

let gimli s = admit()
