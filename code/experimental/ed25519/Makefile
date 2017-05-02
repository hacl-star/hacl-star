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
		 --include $(HACL_HOME)/specs  --include $(HACL_HOME)/specs/experimental \
		--include $(HACL_HOME)/code/curve25519 \
		$(HINTS_ENABLED) $(OTHERFLAGS)

FSTAR_CT=$(FSTAR_HOME)/bin/fstar.exe --include $(FSTAR_HOME)/ulib/hyperstack \
		--include $(HACL_HOME)/code/lib --include $(HACL_HOME)/code/bignum --include $(KREMLIN_HOME)/kremlib \
		--include $(HACL_HOME)/specs --include $(HACL_HOME)/specs/experimental \
		--include $(HACL_HOME)/code/curve25519


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

KEMLIN_SKIP_COMPILATION=$(KREMLIN_HOME)/krml -tmpdir ed25519-c $(KREMLIN_ARGS) \
		-I ../../bignum -I ../../lib/kremlin -I ../../../specs -I ../../curve25519 \
		-I ../../../specs/experimental -I ../hash \
		-drop 'Hacl.Spec' -drop 'Hacl.Cast' -drop 'Hacl.UInt.\*' -drop 'Hacl.Endianness' \
		-drop 'Hacl.UInt8' -drop 'Hacl.UInt16' -drop 'Hacl.UInt32' -drop 'Hacl.UInt64' -drop 'Hacl.UInt128' -drop 'Seq.\*' \
		-drop Prims -drop FStar -bundle 'Hacl.Bignum25519=Hacl.Bignum,Hacl.Bignum.\*,Hacl.EC,Hacl.EC.\*,Hacl.Impl.\*,Hacl.Lib.\*,Hacl.Bignum25519' \
		-bundle 'Hacl.Spec.\*' -drop "Spec.\*" \
		$(KREMLIN_HOME)/kremlib/testlib.c -add-include '"testlib.h"' \
		-skip-compilation

../hash/sha2-c/SHA2_512.c:
	$(MAKE) -C ../hash sha2-c/SHA2_512.c

ed25519-c/Ed25519.c: \
	Hacl.Bignum25519.fst \
	Hacl.Impl.Load56.fst \
	Hacl.Impl.Load51.fst \
	Hacl.Impl.Store51.fst \
	Hacl.Impl.BignumQ.Mul.fst \
	Hacl.Impl.SHA512.ModQ.fst \
	Hacl.Impl.Sha512.fst \
	Hacl.Impl.Ed25519.Pow2_252m2.fst \
	Hacl.Impl.Ed25519.PointAdd.fst \
	Hacl.Impl.Ed25519.PointDouble.fst \
	Hacl.Impl.Ed25519.SecretExpand.fst \
	Hacl.Impl.Ed25519.PointCompress.fst \
	Hacl.Impl.Ed25519.PointDecompress.fst \
	Hacl.Impl.Ed25519.RecoverX.fst \
	Hacl.Impl.Ed25519.Ladder.Step.fst \
	Hacl.Impl.Ed25519.Ladder.fst \
	Hacl.Impl.Ed25519.PointEqual.fst \
	Ed25519.fst
	 $(KREMLIN_HOME)/krml -tmpdir ed25519-c $(KREMLIN_ARGS) \
	 	-I ../../bignum -I ../../lib/kremlin -I ../../../specs -I ../../curve25519 \
	 	-I ../../../specs/experimental -I ../hash \
	 	$^ \
	 	-drop 'Hacl.Spec' -drop 'Hacl.Cast' -drop 'Hacl.UInt.\*' -drop 'Hacl.Endianness' \
	 	-drop 'Hacl.UInt8' -drop 'Hacl.UInt16' -drop 'Hacl.UInt32' -drop 'Hacl.UInt64' -drop 'Hacl.UInt128' -drop 'Seq.\*' \
	 	-drop Prims -drop FStar -bundle 'Ed25519=Ed25519,Hacl.EC,Hacl.EC.\*,Hacl.Impl.\*,Hacl.Lib.\*,Hacl.Bignum.\*,Hacl.Bignum25519,Hacl.Bignum' \
	 	-bundle 'Hacl.Spec.\*' -drop "Spec.\*" \
	 	$(KREMLIN_HOME)/kremlib/testlib.c -add-include '"testlib.h"' -skip-compilation

extract-c:ed25519-c/Ed25519.c

ed25519.exe: ../hash/sha2-c/SHA2_512.c ed25519-c/Ed25519.c
	 $(KREMLIN_HOME)/krml -tmpdir ed25519-c $(KREMLIN_ARGS) \
	 	-I ../../bignum -I ../../lib/kremlin -I ../../../specs -I ../../curve25519 \
	 	-I ../../../specs/experimental \
	 	$^  Hacl.Test.Ed25519.fst -no-prefix 'Hacl.Test.Ed25519' \
	 	-drop 'Hacl.Spec' -drop 'Hacl.Cast' -drop 'Hacl.UInt.\*' -drop 'Hacl.Endianness' \
	 	-drop 'Hacl.UInt8' -drop 'Hacl.UInt16' -drop 'Hacl.UInt32' -drop 'Hacl.UInt64' -drop 'Hacl.UInt128' -drop 'Seq.\*' \
	 	-drop Prims -drop FStar \
		-drop "Hacl.Bignum25519" -drop "Hacl.Impl.Ed25519.Pow2_252m2" -drop "Ed25519" \
	 	-bundle 'Hacl.Spec.\*' -drop "Spec.\*" \
	 	$(KREMLIN_HOME)/kremlib/testlib.c -add-include '"testlib.h"' -add-include '"Ed25519.h"' \
	 	-o ed25519.exe -ldopt '-lsodium'
	./ed25519.exe


clean:
	rm -rf *.exe *.exe.* *.out *~ ed25519-c *.graph
