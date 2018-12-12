HACL_HOME?=../../..
include $(HACL_HOME)/Makefile.include


# Files for verification
KREMLIN_ARGS =-verbose $(KREMLIN_TESTLIB) \
	-drop FStar,Prims,LowStar,C,C.*,C.Loops.Spec.Loops,Spec.*,Lib.*,WasmSupport \
	-ccopt -march=native


CFLAGS=-I $(KREMLIN_HOME)/kremlib -I $(KREMLIN_HOME)/include

%.o: %.c
	$(CC) $(CFLAGS) -c $< -o $@

#
# SHA2_256
#

BASE_OBJ = ../../../lib/c/Lib_PrintBuffer.o

HACL_LIBS = ../../../lib/fst/Lib.IntTypes.fst ../../../lib/fst/Lib.RawIntTypes.fst ../../../lib/c/Lib.Loops.fst ../../../lib/fst/Lib.Buffer.fst  ../../../lib/fst/Lib.ByteBuffer.fst ../../../lib/Lib.PrintBuffer.fsti


sha2_256-c/out.krml: $(HACL_LIBS) Hacl.Impl.SHA2_256.fst Hacl.SHA2_256.fst Test.Impl.SHA2_256.fst
	$(KREMLIN) $(KREMLIN_ARGS) -fsopt "--expose_interfaces" -tmpdir sha2_256-c \
	-I ../../../specs -I ../../../lib -I ../../../lib/fst -I $(KREMLIN_HOME)/include \
	-skip-translation $^


sha2_256-c/Hacl_SHA2_256.c: sha2_256-c/out.krml
	$(KREMLIN) $(KREMLIN_ARGS) -add-include '"../../../../lib/c/Lib_PrintBuffer.h"' -add-include '"C_String.h"' -fparentheses -tmpdir sha2_256-c -no-prefix 'Test.Impl.SHA2_256' \
	-skip-compilation -bundle 'Hacl.SHA2_256=Hacl.Impl.*,Hacl.SHA2_256' \
	$^ -o $@

sha2_256-c/Test_Impl_SHA2_256.c: sha2_256-c/out.krml
	$(KREMLIN) $(KREMLIN_ARGS) $(KREMLIN_TESTLIB) -tmpdir sha2_256-c -skip-compilation -no-prefix Test.Impl.SHA2_256 \
	-bundle 'Hacl.SHA2_256=Hacl.Impl.*,Hacl.SHA2_256' \
	$^ -o $@


test-sha2_256.exe: sha2_256-c/Hacl_SHA2_256.c sha2_256-c/Test_Impl_SHA2_256.c $(BASE_OBJ)
	$(CC) $(CFLAGS) -I $(KREMLIN_HOME) -I $(KREMLIN_HOME)/kremlib/extracted -L $(KREMLIN_HOME)/kremlib/out -o $@ $^ -lkremlib


#
# Clean
#

clean:
	rm -rf *~ *.exe *.exe.dSYM *.checked.lax
	rm -rf sha2_256-c
