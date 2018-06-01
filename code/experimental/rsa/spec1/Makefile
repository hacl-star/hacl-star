include $(HACL_HOME)/Makefile.include

FSTAR_ARGS=$(OTHERFLAGS)

# OCaml variables
OCAMLOPT := $(OCAMLOPT) -w -8-20-26-28-10
FSTAR_INCLUDES+=--include $(HACL_HOME)/specs/lib --include $(HACL_HOME)/specs/lib/fst --include $(HACL_HOME)/specs/lemmas --expose_interfaces

EXTRACTED= FStar_Seq_Base.ml FStar_Seq.ml FStar_Seq_Properties.ml FStar_Math_Lib.ml FStar_BitVector.ml FStar_UInt.ml  FStar_Endianness.ml

NOEXTRACT=$(addprefix --no_extract FStar., Classical Ghost Int16 Int32 Int64 Int63 Int16 Int8 Int.Cast Int List.Tot.Base List.Tot List.Tot.Properties Math.Lemmas Mul StrongExcludedMiddle UInt128 UInt16 UInt32 UInt63 UInt64 UInt8) $(addprefix --no_extract Hacl., UInt64 UInt32 UInt8)

ARGS=--codegen OCaml --lax --include $(HACL_HOME)/code/lib/kremlin $(NOEXTRACT) --include $(KREMLIN_HOME)/kremlib --include ..

%.fst-verify: %.fst
	$(FSTAR) --include $(HACL_HOME)/code/lib/kremlin --include $(KREMLIN_HOME)/kremlib --include .. --use_hints $*.fst

rsa.exe: $(HACL_HOME)/specs/lib/fst/Spec.Lib.IntTypes.fst $(HACL_HOME)/specs/lib/fst/Spec.Lib.RawIntTypes.fst $(HACL_HOME)/specs/lib/fst/Spec.Lib.IntSeq.fst $(HACL_HOME)/specs/lib/fst/Spec.Lib.Stateful.fst  $(HACL_HOME)/specs/Spec.SHA2.fst Spec.Convert.fst Spec.Bignum.Base.fst Spec.Bignum.Basic.fst Spec.RSA.Bignum.fst Spec.RSA.fst Spec.RSA.Test.fst
	mkdir -p rsapss-ml
	$(FSTAR) --codegen OCaml --lax --extract_module Spec.Lib.IntTypes --extract_module Spec.Lib.RawIntTypes  --extract_module Spec.Lib.IntSeq --extract_module Spec.Lib.Stateful --extract_module Spec.SHA2  --extract_module Spec.Convert --extract_module Spec.Bignum.Base --extract_module Spec.Bignum.Basic --extract_module Spec.RSA.Bignum --extract_module Spec.RSA --extract_module Spec.RSA.Test --odir rsapss-ml $^
	@echo 'let _ = test()' >> rsapss-ml/Spec_RSA_Test.ml
	$(OCAMLOPT) -I rsapss-ml rsapss-ml/Spec_Lib_IntTypes.ml rsapss-ml/Spec_Lib_RawIntTypes.ml rsapss-ml/Spec_Lib_IntSeq.ml rsapss-ml/Spec_Lib_Stateful.ml rsapss-ml/Spec_SHA2.ml rsapss-ml/Spec_Convert.ml rsapss-ml/Spec_Bignum_Base.ml  rsapss-ml/Spec_Bignum_Basic.ml rsapss-ml/Spec_RSA_Bignum.ml rsapss-ml/Spec_RSA.ml rsapss-ml/Spec_RSA_Test.ml -o rsa.exe
	./rsa.exe

clean:
	rm -rf *.cmi *.cmo *.cmx *.o *~ *.out *.exe rsapss-ml
