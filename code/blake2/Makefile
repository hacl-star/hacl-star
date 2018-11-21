HACL_HOME?=../..
include $(HACL_HOME)/Makefile.include


verify: Hacl.Blake2s.fst-verify Hacl.Impl.Blake2s.fst-verify
	$(MAKE) $<

# Files for verification
KREMLIN_ARGS =-verbose $(KREMLIN_TESTLIB) \
	-drop FStar,Prims,LowStar,C,C.*,C.Loops.Spec.Loops,Spec.*,Lib.*,WasmSupport \
	-ccopt -march=native


CFLAGS=-I $(HACL_HOME)/code/lib/kremlin -I $(HACL_HOME)/specs -I $(KREMLIN_HOME)/kremlib -I $(HACL_HOME)/code/hash -I $(KREMLIN_HOME)/include

%.o: %.c
	$(CC) $(CFLAGS) -c $< -o $@

#
# Blake2 (version s)
#

BASE_OBJ = ../../lib/c/Lib_PrintBuffer.o

#$(KREMLIN_HOME)/kremlib/testlib.o $(KREMLIN_HOME)/kremlib/kremlib.o $(KREMLIN_HOME)/kremlib/kremstr.o

HACL_LIBS = ../../lib/fst/Lib.IntTypes.fst ../../lib/fst/Lib.RawIntTypes.fst ../../lib/c/Lib.Loops.fst ../../lib/fst/Lib.Buffer.fst  ../../lib/fst/Lib.ByteBuffer.fst ../../lib/Lib.PrintBuffer.fsti


blake2s-c/out.krml: $(HACL_LIBS) Hacl.Impl.Blake2s.fst Hacl.Blake2s.fst Hacl.Test.Blake2s.fst
	$(KREMLIN) $(KREMLIN_ARGS) -fsopt "--expose_interfaces" -tmpdir blake2s-c \
	-I ../../specs -I ../../lib -I ../../lib/fst -I $(KREMLIN_HOME)/include \
	-skip-translation $^


blake2s-c/Hacl_Blake2s.c: blake2s-c/out.krml
	$(KREMLIN) $(KREMLIN_ARGS) -add-include '"../../../lib/c/Lib_PrintBuffer.h"' -add-include '"C_String.h"' -fparentheses -tmpdir blake2s-c -no-prefix 'Hacl.Test.Blake2s' \
	-skip-compilation -bundle 'Hacl.Blake2s=Hacl.Impl.*,Hacl.Blake2s' \
	$^ -o $@

blake2s-c/Hacl_Test_Blake2s.c: blake2s-c/out.krml
	$(KREMLIN) $(KREMLIN_ARGS) $(KREMLIN_TESTLIB) -tmpdir blake2s-c -skip-compilation -no-prefix Hacl.Test.Blake2s \
	-bundle 'Hacl.Blake2s=Hacl.Impl.*,Hacl.Blake2s' \
	$^ -o $@


test-blake2s.exe: blake2s-c/Hacl_Blake2s.c blake2s-c/Hacl_Test_Blake2s.c $(BASE_OBJ)
	$(CC) $(CFLAGS) -I $(KREMLIN_HOME) -I $(KREMLIN_HOME)/kremlib/extracted -L $(KREMLIN_HOME)/kremlib/out -o $@ $^ -lkremlib


#
# Clean
#

clean:
	rm -rf *~ *.exe *.exe.dSYM *.checked.lax
	rm -rf blake2s-c
