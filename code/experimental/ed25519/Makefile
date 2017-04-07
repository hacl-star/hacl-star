FSTAR_HOME?=../../../dependencies/FStar
KREMLIN_HOME?=$(FSTAR_HOME)/../kremlin
HACL_HOME?=../../..
include $(HACL_HOME)/code/Makefile.include


BIGNUM= \
	../bignum/Hacl.Bignum.Limb.fst \
	../bignum/Hacl.Spec.Bignum.Field.fst \
	../bignum/Hacl.Bignum.Wide.fst \
	../bignum/Hacl.Spec.Bignum.Bigint.fst \
	../bignum/Hacl.Spec.Bignum.Fproduct.fst \
	../bignum/Hacl.Spec.Bignum.Fsum.fst \
	../bignum/Hacl.Spec.Bignum.Fdifference.fst \
	../bignum/Hacl.Spec.Bignum.Fmul.fst \
	../bignum/Hacl.Spec.Bignum.Fscalar.fst \
	../bignum/Hacl.Spec.Bignum.fst \
	../bignum/Hacl.Bignum.Fscalar.fst \
	../bignum/Hacl.Bignum.Fproduct.fst \
	../bignum/Hacl.Bignum.Fmul.fst \
	../bignum/Hacl.Bignum.fst


ED25519_SPECIFIC= \

# Files that are too slow and for which verification speed must improve
SLOW=

# Files that still have errors
TODO=

ED25519_FILES= $(BIGNUM) $(ED25519_SPECIFIC)


HINTS_ENABLED?=--use_hints --record_hints

FSTARB=$(FSTAR_HOME)/bin/fstar.exe --include $(FSTAR_HOME)/ulib/hyperstack \
		--include $(HACL_HOME)/code/lib/kremlin --include $(HACL_HOME)/code/bignum --include $(KREMLIN_HOME)/kremlib \
		 --include $(HACL_HOME)/specs \
		$(HINTS_ENABLED) $(OTHERFLAGS)

FSTAR_CT=$(FSTAR_HOME)/bin/fstar.exe --include $(FSTAR_HOME)/ulib/hyperstack \
		--include $(HACL_HOME)/code/lib --include $(HACL_HOME)/code/bignum --include $(KREMLIN_HOME)/kremlib \
		--include $(HACL_HOME)/specs

# Lax typechecking against the restricted integer interface
%.fst-ct: %.fst
	$(FSTAR_CT) --lax $^

all-ct: $(addsuffix -ct, $(ED25519_FILES))

# Full typechecking against the transparent integer interface
%.fst-verify: %.fst
	$(FSTARB) $^

all-ver: $(addsuffix -verify, $(ED25519_FILES))

# Minimal lax typechecking, pre-requisite to any extraction
%.fst-lax: %.fst
	$(FSTARB) --lax $^

all-lax: $(addsuffix -lax, $(ED25519_FILES))

# Hints regeneration
%.fst-hints: %.fst
	-$(FSTARB) $^

all-hints2: $(addsuffix -hints, $(ED25519_FILES))

all-hints:
	cp ./bignum_hints/* ../bignum/
	$(MAKE) all-hints2
	mv ../bignum/*.hints ./bignum_hints
bignum-hints:
	cp bignum_hints/* ../bignum
	$(MAKE) $(addsuffix -hints, $(BIGNUM))
	mv ../bignum/*.hints ./bignum_hints
specific-hints: $(addsuffix -hints, $(ED25519_SPECIFIC))

# For CI, all modules restricted from incomplete or slow ones
all-ci2: $(addsuffix -verify, $(filter-out $(SLOW) $(TODO), $(ED25519_FILES)))
all-ci:
	cp bignum_hints/* ../bignum
	$(MAKE) all-ci2
	mv ../bignum/*.hints ./bignum_hints
bignum-ci:
	cp bignum_hints/* ../bignum
	$(MAKE) $(addsuffix -verify, $(filter-out $(SLOW) $(TODO), $(BIGNUM)))
	mv ../bignum/*.hints ./bignum_hints
specific-ci: $(addsuffix -verify, $(filter-out $(SLOW) $(TODO), $(ED25519_SPECIFIC)))

extract-c:
	# Weird \* because of https://caml.inria.fr/mantis/view.php?id=7473
	mkdir -p x25519-c
	$(KREMLIN_HOME)/krml -tmpdir x25519-c $(KREMLIN_ARGS) \
		-I ../bignum -I ../lib/kremlin -I ../../specs \
		Curve25519.fst Hacl.Test.ED25519.fst \
		-drop 'Hacl.Spec' -drop 'Hacl.Cast' -drop 'Hacl.UInt.\*' -drop 'Hacl.Endianness' \
		-drop 'Hacl.UInt8' -drop 'Hacl.UInt16' -drop 'Hacl.UInt32' -drop 'Hacl.UInt64' -drop 'Hacl.UInt128' \
		-drop Prims -drop FStar -bundle 'Curve25519=Hacl.Bignum,Hacl.Bignum.\*,Hacl.EC,Hacl.EC.\*' \
		-bundle 'Hacl.Spec.\*' -drop "Spec.\*" \
		$(KREMLIN_HOME)/kremlib/testlib.c -add-include '"testlib.h"' \
                -no-prefix Hacl.Test.ED25519 -o x25519.exe
	./x25519.exe

clean:
	rm -rf *.exe *.exe.* *.out *~ x25519-c *.graph
