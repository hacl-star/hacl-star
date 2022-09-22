#!/bin/env bash

# To run the precomputation table, the native tactic must be compiled against
# fstar-tactics-lib, but:
# - the F* .depend is blissfully unaware of that fact and so is our makefile --
#   see below for fixed invocations (of ALL the transitive dependencies!)
# - hash of modules is inconsistent for fstar_uint64 not sure if this is normal
#   (do ocamlobjinfo on FStar/bin/{fstarlib,fstar-tactics-lib}/FStar_UInt64.cmi

ocamlfind opt -package fstar-tactics-lib -linkpkg -g -I /Users/jonathan/Code/everest/hacl-star/obj -w -8-20-26 -c obj/Lib_Exponentiation.ml -o obj/Lib_Exponentiation.cmx
ocamlfind opt -package fstar-tactics-lib -linkpkg -g -I /Users/jonathan/Code/everest/hacl-star/obj -w -8-20-26 -c obj/Lib_NatMod.ml -o obj/Lib_NatMod.cmx
ocamlfind opt -package fstar-tactics-lib -linkpkg -g -I /Users/jonathan/Code/everest/hacl-star/obj -w -8-20-26 -c obj/Lib_IntTypes.ml -o obj/Lib_IntTypes.cmx
ocamlfind opt -package fstar-tactics-lib -linkpkg -g -I /Users/jonathan/Code/everest/hacl-star/obj -w -8-20-26 -c obj/Lib_Sequence.ml -o obj/Lib_Sequence.cmx
ocamlfind opt -package fstar-tactics-lib -linkpkg -g -I /Users/jonathan/Code/everest/hacl-star/obj -w -8-20-26 -c obj/Lib_RawIntTypes.ml -o obj/Lib_RawIntTypes.cmx
ocamlfind opt -package fstar-tactics-lib -linkpkg -g -I /Users/jonathan/Code/everest/hacl-star/obj -w -8-20-26 -c obj/Lib_ByteSequence.ml -o obj/Lib_ByteSequence.cmx
ocamlfind opt -package fstar-tactics-lib -linkpkg -g -I /Users/jonathan/Code/everest/hacl-star/obj -w -8-20-26 -c obj/Spec_K256_PointOps.ml -o obj/Spec_K256_PointOps.cmx

# Then need to pass the following options to fstar.exe

--load Lib.IntTypes
--load Hacl.Spec.K256.Field52.Definitions
--load Lib.LoopCombinators
--load Lib.Exponentiation
--load Lib.NatMod
--load Lib.Sequence
--load Lib.RawIntTypes
--load Lib.ByteSequence
--load Spec.K256.PointOps
--load Meta.K256.PrecompTable

# - Then need to write quote_lib.uint32_list to run the quoting in native code
# - Then need to extend FStar.Seq to expose quote_seq_from_list to avoid copying
#   everything via super inefficient seq_of_list calls
