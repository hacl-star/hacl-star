FSTAR_HOME?=../../dependencies/FStar
KREMLIN_HOME?=$(FSTAR_HOME)/../kremlin
HACL_HOME?=../..
include ../Makefile.include


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


X25519_SPECIFIC= \
	Hacl.Spec.Curve25519.Lemmas.fst \
	Hacl.Bignum.Parameters.fst \
	Hacl.Spec.Bignum.Modulo.fst \
	Hacl.Spec.EC.AddAndDouble.fst \
	Hacl.Spec.Bignum.Fsquare.fst \
	Hacl.Spec.Bignum.Crecip.fst \
	Hacl.Bignum.Modulo.fst \
	Hacl.Bignum.Fsquare.fst \
	Hacl.Bignum.Crecip.fst \
	Hacl.Spec.EC.Point.fst \
	Hacl.EC.Point.fst \
	Hacl.Spec.EC.AddAndDouble2.fst \
	Hacl.Spec.EC.Format.Lemmas.fst \
	Hacl.Spec.EC.Format.fst \
	Hacl.EC.Format.fst \
	Hacl.EC.AddAndDouble.fst \
	Hacl.Spec.EC.Ladder.Lemmas.fst \
	Hacl.Spec.EC.Ladder.fst \
	Hacl.EC.Ladder.SmallLoop.fst \
	Hacl.EC.Ladder.BigLoop.fst \
	Hacl.EC.Ladder.fst \
	Hacl.Spec.EC.fst \
	Hacl.EC.fst \
	Curve25519.fst

# Files that are too slow and for which verification speed must improve
SLOW=Hacl.Spec.Bignum.Fsquare.fst

# Files that still have errors
TODO=

X25519_FILES= $(BIGNUM) $(X25519_SPECIFIC)


HINTS_ENABLED?=--use_hints --record_hints

FSTARB=$(FSTAR_HOME)/bin/fstar.exe --include $(FSTAR_HOME)/ulib/hyperstack \
		--include ../lib/kremlin --include ../bignum --include $(KREMLIN_HOME)/kremlib \
		 --include ../../specs \
		$(HINTS_ENABLED) $(OTHERFLAGS)

FSTAR_CT=$(FSTAR_HOME)/bin/fstar.exe --include $(FSTAR_HOME)/ulib/hyperstack \
		--include ../lib --include ../bignum --include $(KREMLIN_HOME)/kremlib \
		--include ../../specs

# Lax typechecking against the restricted integer interface
%.fst-ct: %.fst
	$(FSTAR_CT) --lax $^

# Using the --verify_all argument to lift abstractions, typechecks all dependencies of Curve25519.fst
all-ct:
	$(FSTAR_CT) --lax --verify_all Curve25519.fst


# Full typechecking against the transparent integer interface
%.fst-verify: %.fst
	$(FSTARB) $^
%.fsti-verify: %.fsti
	$(FSTARB) $^

all-ver: $(addsuffix -verify, $(X25519_FILES))

# Minimal lax typechecking, pre-requisite to any extraction
%.fst-lax: %.fst
	$(FSTARB) --lax $^

all-lax: $(addsuffix -lax, $(X25519_FILES))

# Hints regeneration
%.fst-hints: %.fst
	-$(FSTARB) $^

all-hints2: $(addsuffix -hints, $(X25519_FILES))

all-hints:
	cp ./bignum_hints/* ../bignum/
	$(MAKE) all-hints2
	mv ../bignum/*.hints ./bignum_hints
bignum-hints:
	cp bignum_hints/* ../bignum
	$(MAKE) $(addsuffix -hints, $(BIGNUM))
	mv ../bignum/*.hints ./bignum_hints
specific-hints: $(addsuffix -hints, $(X25519_SPECIFIC))

# For CI, all modules restricted from incomplete or slow ones
all-ci2: $(addsuffix -verify, $(filter-out $(SLOW) $(TODO), $(X25519_FILES)))
all-ci:
	cp bignum_hints/* ../bignum
	$(MAKE) all-ci2
	mv ../bignum/*.hints ./bignum_hints
bignum-ci:
	cp bignum_hints/* ../bignum
	$(MAKE) $(addsuffix -verify, $(filter-out $(SLOW) $(TODO), $(BIGNUM)))
	mv ../bignum/*.hints ./bignum_hints
specific-ci: $(addsuffix -verify, $(filter-out $(SLOW) $(TODO), $(X25519_SPECIFIC)))

extract-c:
	# Weird \* because of https://caml.inria.fr/mantis/view.php?id=7473
	mkdir -p x25519-c
	$(KREMLIN_HOME)/krml -tmpdir x25519-c $(KREMLIN_ARGS) \
		-I ../bignum -I ../lib/kremlin -I ../../specs \
		Curve25519.fst Hacl.Test.X25519.fst \
		-drop 'Hacl.Spec' -drop 'Hacl.Cast' -drop 'Hacl.UInt.\*' -drop 'Hacl.Endianness' \
		-drop 'Hacl.UInt8' -drop 'Hacl.UInt16' -drop 'Hacl.UInt32' -drop 'Hacl.UInt64' -drop 'Hacl.UInt128' \
		-drop Prims -drop FStar -bundle 'Curve25519=Hacl.Bignum,Hacl.Bignum.\*,Hacl.EC,Hacl.EC.\*' \
		-bundle 'Hacl.Spec.\*' -drop "Spec.\*" \
		$(KREMLIN_HOME)/kremlib/testlib.c -add-include '"testlib.h"' \
                -no-prefix Hacl.Test.X25519 -o x25519.exe
	./x25519.exe

X25519_LIB= \
	Hacl.Bignum.Parameters.fst \
	Hacl.Spec.Bignum.Modulo.fst \
	Hacl.Spec.EC.AddAndDouble.fst \
	Hacl.Spec.Bignum.Fsquare.fst \
	Hacl.Spec.Bignum.Crecip.fst \
	Hacl.Bignum.Modulo.fst \
	Hacl.Bignum.Fsquare.fst \
	Hacl.Bignum.Crecip.fst \
	Hacl.EC.Point.fst \
	Hacl.Spec.EC.Format.Lemmas.fst \
	Hacl.Spec.EC.Format.fst \
	Hacl.EC.Format.fst \


X25519_ONLY=Hacl.Spec.EC.Point.fst \
	Hacl.Spec.Curve25519.Lemmas.fst \
	Hacl.Spec.EC.AddAndDouble2.fst \
	Hacl.EC.AddAndDouble.fst \
	Hacl.Spec.EC.Ladder.Lemmas.fst \
	Hacl.Spec.EC.Ladder.fst \
	Hacl.EC.Ladder.SmallLoop.fst \
	Hacl.EC.Ladder.BigLoop.fst \
	Hacl.EC.Ladder.fst \
	Hacl.Spec.EC.fst \
	Hacl.EC.fst

count-line:
	@echo "X25519 LIB LOC"
	cloc --force-lang=ocaml $(X25519_LIB)
	@echo "X25519 ONLY LOC"
	cloc --force-lang=ocaml $(X25519_ONLY)

clean:
	rm -rf *.exe *.exe.* *.out *~ x25519-c 
