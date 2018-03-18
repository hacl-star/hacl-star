include $(HACL_HOME)/Makefile.include

FSTAR_ARGS=$(OTHERFLAGS)

# OCaml variables
OCAMLOPT := $(OCAMLOPT) -w -8-20-26-28-10
FSTAR_INCLUDES+=--include $(HACL_HOME)/specs/lib --include $(HACL_HOME)/specs/lemmas

EXTRACTED= FStar_Seq_Base.ml FStar_Seq.ml FStar_Seq_Properties.ml FStar_Math_Lib.ml FStar_BitVector.ml FStar_UInt.ml  FStar_Endianness.ml

NOEXTRACT=$(addprefix --no_extract FStar., Classical Ghost Int16 Int32 Int64 Int63 Int16 Int8 Int.Cast Int List.Tot.Base List.Tot List.Tot.Properties Math.Lemmas Mul StrongExcludedMiddle UInt128 UInt16 UInt32 UInt63 UInt64 UInt8) $(addprefix --no_extract Hacl., UInt64 UInt32 UInt8)

ARGS=--codegen OCaml --lax --include $(HACL_HOME)/code/lib/kremlin $(NOEXTRACT) --include $(KREMLIN_HOME)/kremlib --include ..

OCAML_INCLUDES=-I $(HACL_HOME)/code/lib/ml $(HACL_HOME)/code/lib/ml/hacllib.cmxa 

%.fst-verify: %.fst
	$(FSTAR) --include $(HACL_HOME)/code/lib/kremlin --include $(KREMLIN_HOME)/kremlib --include .. --use_hints $*.fst

lib:
	$(MAKE) -C $(HACL_HOME)/code/lib/ml MEM=HST

rsa.exe: $(HACL_HOME)/specs/lib/fst/Spec.Lib.IntTypes.fst $(HACL_HOME)/specs/lib/fst/Spec.Lib.RawIntTypes.fst $(HACL_HOME)/specs/lib/fst/Spec.Lib.IntSeq.fst $(HACL_HOME)/specs/lib/fst/Spec.Lib.Stateful.fst  $(HACL_HOME)/specs/Spec.SHA2.fst Hacl.Spec.RSA.fst Hacl.Test.RSA.fst
	$(MAKE) -C  $(HACL_HOME)/code/lib/ml
	mkdir -p rsa-spec
	$(FSTAR) --codegen OCaml --lax --extract_module Spec.Lib.IntTypes --extract_module Spec.Lib.RawIntTypes  --extract_module Spec.Lib.IntSeq --extract_module Spec.Lib.Stateful --extract_module Spec.SHA2 --extract_module Hacl.Spec.Lib --extract_module Hacl.Spec.Convert --extract_module Hacl.Spec.Comparison --extract_module Hacl.Spec.Addition --extract_module Hacl.Spec.Multiplication --extract_module Hacl.Spec.Shift --extract_module Hacl.Spec.Montgomery --extract_module Hacl.Spec.Exponentiation --extract_module Hacl.Spec.MGF --extract_module Hacl.Spec.RSA --extract_module Hacl.Test.RSA --odir rsa-spec $^
	@echo 'let _ = print_string (if test() then "SUCCESS\n" else failwith "Test failed\n")' >> rsa-spec/Hacl_Test_RSA.ml
	$(OCAMLOPT) -I rsa-spec $(OCAML_INCLUDES) rsa-spec/Spec_Lib_IntTypes.ml rsa-spec/Spec_Lib_RawIntTypes.ml rsa-spec/Spec_Lib_IntSeq.ml rsa-spec/Spec_Lib_Stateful.ml rsa-spec/Spec_SHA2.ml rsa-spec/Hacl_Spec_Lib.ml rsa-spec/Hacl_Spec_Convert.ml rsa-spec/Hacl_Spec_Comparison.ml rsa-spec/Hacl_Spec_Addition.ml rsa-spec/Hacl_Spec_Multiplication.ml rsa-spec/Hacl_Spec_Shift.ml rsa-spec/Hacl_Spec_Montgomery.ml rsa-spec/Hacl_Spec_Exponentiation.ml rsa-spec/Hacl_Spec_MGF.ml rsa-spec/Hacl_Spec_RSA.ml rsa-spec/Hacl_Test_RSA.ml -o rsa.exe
	./rsa.exe

clean:
	$(MAKE) -C $(HACL_HOME)/code/lib/ml clean
	rm -rf *.cmi *.cmo *.cmx *.o *~ *.out *.exe chacha-spec-vec3 chacha-spec-vec256 chacha-spec-vec2 chacha-spec-vec sha2-spec ed25519-spec secretbox-spec rsa-spec
