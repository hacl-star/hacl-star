include ../../Makefile.include

P256_SPECIFIC= \
	Hacl.Impl.P256.fst

FSTS=Hacl.Test.P256.fst

# Files that are too slow and for which verification speed must improve
SLOW=

# Files that still have errors
TODO=

P256_FILES=$(P256_SPECIFIC)

FSTAR_INCLUDES+=

# Parameter for interactive mode
%.fst-in:
	@echo $(OPTIONS) --hint_info \
	$(FSTAR_INCLUDES)

ct: $(addsuffix -lax, $(P256_FILES))
	$(FSTAR) --lax --verify_all Hacl.Impl.P256.fst
all-ct: ct

bignum-ver: $(addsuffix -reloc-verify, $(BIGNUM))
specific-ver: $(addsuffix -verify, $(filter-out $(SLOW) $(TODO), $(P256_SPECIFIC)))
verify: bignum-ver specific-ver
hints: bignum-hints specific-hints
all-ver: verify

# Hints regeneration
bignum-hints: $(addsuffix .reloc.hints, $(BIGNUM))
specific-hints: $(addsuffix .hints, $(P256_SPECIFIC))
hints: bignum-hints specific-hints
all-hints: hints

# For CI, all modules restricted from incomplete or slow ones
bignum-ci: $(addsuffix -reloc-verify, $(filter-out $(SLOW) $(TODO), $(BIGNUM)))
specific-ci: $(addsuffix -verify, $(filter-out $(SLOW) $(TODO), $(P256_SPECIFIC)))
ci: bignum-ci specific-ci
all-ci: ci

KREMLIN_ARGS+=-tmpdir p256-c \
		-drop Hacl.Spec,Hacl.Cast,Hacl.UInt.*,Hacl.Endianness,Hacl.UInt8,Hacl.UInt16,Hacl.UInt32,Hacl.UInt64,Hacl.UInt128,Seq.*,Prims,Spec.* \
		-bundle Hacl.Impl.P256=Hacl.Impl.P256,Hacl.EC,Hacl.EC.*,Hacl.Impl.*,Hacl.Lib.*,Hacl.Bignum.*,Hacl.Bignum25519,Hacl.Bignum,Hacl.Spec.*,SHA2_512,Hacl.Hash.*

p256-c/out.krml: $(P256_FILES)
	 $(KREMLIN) $(KREMLIN_ARGS) $(FSTS) -skip-translation

p256-c/Hacl_Impl_P256.c: p256-c/out.krml
	 $(KREMLIN) $(KREMLIN_ARGS) $^ -skip-compilation

extract-c:p256-c/Hacl_Impl_P256.c

p256.exe: p256-c/out.krml
	$(KREMLIN) $(KREMLIN_ARGS) $^ \
	 	-no-prefix 'Hacl.Test.P256' $(KREMLIN_HOME)/kremlib/testlib.c -add-include '"testlib.h"' \
		-add-include '"Hacl_Impl_P256.h"' -o p256.exe

test: p256.exe
	./$^

blob:
	gcc-6 -I $(HACL_HOME)/code/lib/kremlin -I /home/jkz/dev/kremlin/kremlib -I $(HACL_HOME)/specs -I . -I $(KREMLIN_HOME)/kremlib -I p256-c -march=native -D_GNU_SOURCE -Wno-unused-variable -Wno-unknown-warning-option -Wno-unused-but-set-variable -g -O3 -fwrapv -fstack-check -D_BSD_SOURCE -D_DEFAULT_SOURCE -Wno-parentheses -std=c11 p256-c/FStar.o openssl_p256.c p256-c/kremlib.o p256-c/testlib.o -o p256.exe -flto
	./p256.exe

bla:
	gcc-6 -I $(HACL_HOME)/code/lib/kremlin -I /home/jkz/dev/kremlin/kremlib -I $(HACL_HOME)/specs -I . -I $(KREMLIN_HOME)/kremlib -I p256-c -march=native -D_GNU_SOURCE -Wno-unused-variable -Wno-unknown-warning-option -Wno-unused-but-set-variable -g -O3 -fwrapv -fstack-check -D_BSD_SOURCE -D_DEFAULT_SOURCE -Wno-parentheses -std=c11 p256-c/FStar.o bla.c p256-c/kremlib.o p256-c/testlib.o -o p256.exe -flto
	./p256.exe

c:
	gcc-6 -I $(HACL_HOME)/code/lib/kremlin -I /home/jkz/dev/kremlin/kremlib -I $(HACL_HOME)/specs -I . -I $(KREMLIN_HOME)/kremlib -I p256-c -march=native -D_GNU_SOURCE  -Wno-unused-variable -Wno-unknown-warning-option -Wno-unused-but-set-variable -g -O3 -fwrapv -fstack-check -D_BSD_SOURCE -D_DEFAULT_SOURCE -Wno-parentheses -std=c11 p256-c/FStar.o p256-c/Hacl_Impl_P256.c p256-c/Hacl_Test_P256.c p256-c/kremlinit.o p256-c/kremlib.o p256-c/testlib.o -o p256.exe -flto
	./p256.exe

count-line:
	cloc --force-lang=ocaml $(P256_FILES)

clean:
	rm -rf *.exe *.exe.* *.out *~ ed25519-c *.graph p256-c/out.krml
