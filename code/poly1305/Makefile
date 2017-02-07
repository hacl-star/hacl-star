FSTAR_HOME?=../../../dependencies/FStar
KREMLIN_HOME?=$(FSTAR_HOME)/../kremlin
HACL_HOME?=../..
include ../Makefile.include


BIGNUM= \
	../bignum/Hacl.Spec.Bignum.Field.fst \
	../bignum/Hacl.Bignum.Limb.fst \
	../bignum/Hacl.Bignum.Wide.fst \
	../bignum/Hacl.Spec.Bignum.Bigint.fst \
	../bignum/Hacl.Spec.Bignum.Fsum.fst \
	../bignum/Hacl.Spec.Bignum.Fproduct.fst \
	../bignum/Hacl.Spec.Bignum.Fmul.fst \
	../bignum/Hacl.Bignum.Fsum.fst \
	../bignum/Hacl.Bignum.Fproduct.fst \
	../bignum/Hacl.Bignum.Fmul.fst \


POLY1305_SPECIFIC= \
	Hacl.Bignum.Constants.fst \
	Hacl.Bignum.Parameters.fst \
	Hacl.Spec.Bignum.Modulo.fst \
	Hacl.Spec.Bignum.AddAndMultiply.fst \
	Hacl.Spec.Poly1305.fst \
	Hacl.Spec.Poly1305_64.fst \
	Hacl.Spe.Poly1305_64.fst \
	Hacl.Bignum.Modulo.fst \
	Hacl.Bignum.AddAndMultiply.fst \
	Hacl.Impl.Poly1305_64.fst

SLOW=

TODO=Hacl.Impl.Poly1305_64.fst \
	Hacl.Spe.Poly1305_64.fst 

POLY1305_FILES= $(BIGNUM) $(POLY1305_SPECIFIC)

FSTAR=$(FSTAR_HOME)/bin/fstar.exe --include $(FSTAR_HOME)/ulib/hyperstack \
		--include ../lib/kremlin --include ../bignum --include $(KREMLIN_HOME)/kremlib

FSTAR_CT=$(FSTAR_HOME)/bin/fstar.exe --include $(FSTAR_HOME)/ulib/hyperstack \
		--include ../lib --include ../bignum --include $(KREMLIN_HOME)/kremlib

# Lax typechecking against the restricted integer interface
%.fst-ct: %.fst
	$(FSTAR_CT) --lax $^

all-ct: $(addsuffix -ct, $(POLY1305_FILES))

# Full typechecking against the transparent integer interface
%.fst-verify: %.fst
	$(FSTAR) $^ --use_hints

all-ver: $(addsuffix -verify, $(POLY1305_FILES))

# Minimal lax typechecking, pre-requisite to any extraction
%.fst-lax: %.fst
	$(FSTAR) --lax $^

all-lax: $(addsuffix -lax, $(POLY1305_FILES))

# Hints regeneration
%.fst-hints: %.fst
	-$(FSTAR) $^ --use_hints --record_hints

all-hints: $(addsuffix -hints, $(POLY1305_SPECIFIC))

# For CI, all modules restricted from incomplete or slow ones
all-ci: $(addsuffix -verify, $(filter-out $(SLOW) $(TODO), $(POLY1305_FILES)))


extract-c:
	# Weird \* because of https://caml.inria.fr/mantis/view.php?id=7473
	mkdir -p poly-c
	$(KREMLIN_HOME)/krml -tmpdir poly-c -verbose -ccopt -std=gnu99 \
		-I ../bignum -I ../lib/kremlin \
		Poly1305_64.fst Hacl.Test.Poly1305_64.fst \
		-drop 'Hacl.Endianness' \
		-drop 'Hacl.Spec.\*' -drop 'Hacl.Spe.\*' -drop 'Hacl.Cast' -drop 'Hacl.UInt.\*' \
		-drop Prims -drop FStar -bundle 'Poly1305_64=Hacl.Bignum.*,Hacl.Impl.*' \
		$(KREMLIN_HOME)/kremlib/testlib.c -add-include '"testlib.h"' \
                -no-prefix Hacl.Test.Poly1305_64 -ldopt -flto -ccopt -march=native -o poly1305.exe
# 	$(KREMLIN_HOME)/krml -I $(FSTAR_HOME)/ulib/hyperstack -tmpdir poly-c -verbose -cc gcc \
# 		-I ../bignum -I ../lib/kremlin -I $(FSTAR_HOME)/../kremlin/kremlib \
# 		$(POLY1305_FILES) Hacl.Test.Poly1305_64.fst \
# 		-drop FStar -drop Hacl.Spec -drop Prims -drop Hacl.Cast -drop Hacl.UInt8 -drop Hacl.UInt32 -drop Hacl.UInt64 \
# 		-drop Hacl.UInt128 -drop Hacl.Bignum.Constants -drop Hacl.Bignum.Parameters -drop Hacl.Bignum.Limb -drop Hacl.Bignum.Wide \
# 		-bundle Hacl.Spec=Hacl.Spec.*,Hacl.Spe.* -bundle Poly1305=Hacl.Bignum.*,Hacl.Impl.* \
# 		$(FSTAR_HOME)/../kremlin/kremlib/testlib.c -add-include '"testlib.h"' \
# 		-ccopt -Wno-error=pointer-sign -ccopt -Wno-error=incompatible-pointer-types \
#                 -ccopt -Wno-error=format= -no-prefix Hacl.Test.Poly1305_64 -ldopt -flto -ccopt -march=native -o poly1305.exe
	./poly1305.exe
#-bundle Hacl.Poly1305=Hacl.Bignum.*,Hacl.Impl.Poly1305_64

include $(FSTAR_HOME)/src/gmake/fstar.mk
include $(FSTAR_HOME)/ulib/ml/Makefile.include
CODEGEN_ARGS=--lax --codegen OCaml --no_location_info $(FSTAR_DEFAULT_ARGS)
OCAMLOPT := $(OCAMLOPT) -w -8-20-26-28-10
POLY_EXTRACTED=Hacl_Bignum_Constants.ml Hacl_Bignum_Parameters.ml Hacl_MAC_Poly1305_64.ml

extract-ml:
	mkdir -p poly-ml
	$(FSTAR) $(CODEGEN_ARGS) --include $(FSTAR_HOME)/ulib/hyperstack --include ../bignum --include ../lib \
	--odir poly-ml $(POLY1305_FILES) \
	--no_extract FStar.Math.Lib --no_extract FStar.HyperHeap --no_extract FStar.HyperStack --no_extract FStar.ST --no_extract FStar.Seq --no_extract FStar.UInt128 --no_extract FStar.Int128  --no_extract FStar.Int64 --no_extract FStar.UInt63 --no_extract FStar.Int63 --no_extract FStar.UInt32 --no_extract FStar.Int32 --no_extract FStar.UInt31 --no_extract FStar.Int31 --no_extract FStar.UInt16 --no_extract FStar.Int16 --no_extract FStar.UInt8 --no_extract FStar.Int8 --no_extract Hacl.UInt64 --no_extract Hacl.UInt32 --no_extract Hacl.UInt128 --no_extract Hacl.UInt16 --trace_error 
	$(OCAMLOPT) -I poly-ml  -I ../lib/ml -I $(FSTAR_HOME)/ulib/ml/hyperstack -I $(FSTAR_HOME)/ulib/ml $(addprefix poly-ml/,$(POLY_EXTRACTED)) 

compile-ml:
	$(OCAMLOPT) -I poly-ml -I ../lib/ml -I $(FSTAR_HOME)/ulib/ml/hyperstack -I $(FSTAR_HOME)/ulib/ml $(addprefix poly-ml/,$(POLY_EXTRACTED)) 

clean:
	rm -rf *.exe *.exe.* *.out *~ poly-c
