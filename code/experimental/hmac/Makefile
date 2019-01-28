HACL_HOME?=../../..
include $(HACL_HOME)/Makefile.include


# Files for verification
KREMLIN_ARGS =-verbose \
	-drop FStar,Prims,LowStar,C,C.*,C.Loops.Spec.Loops,Spec.*,Lib.*,WasmSupport \
	-ccopt -march=native


CFLAGS=-I $(KREMLIN_HOME)/kremlib -I $(KREMLIN_HOME)/include

%.o: %.c
	$(CC) $(CFLAGS) -c $< -o $@

all: test

test: test-hmac_sha2_256.exe

#
# HMAC_SHA2_256
#

BASE_OBJ = ../../../lib/c/Lib_PrintBuffer.o

HACL_LIBS = ../../../lib/fst/Lib.IntTypes.fst ../../../lib/fst/Lib.RawIntTypes.fst ../../../lib/c/Lib.Loops.fst ../../../lib/fst/Lib.Buffer.fst  ../../../lib/fst/Lib.ByteBuffer.fst ../../../lib/Lib.PrintBuffer.fsti


hmac_sha2_256-c/out.krml: $(HACL_LIBS) ../sha2/Hacl.Impl.SHA2_256.fst ../sha2/Hacl.SHA2_256.fst Hacl.Impl.HMAC_SHA2_256.fst Hacl.HMAC_SHA2_256.fst Test.Impl.HMAC_SHA2_256.fst
	$(KREMLIN) $(KREMLIN_ARGS) -fsopt "--expose_interfaces" -tmpdir hmac_sha2_256-c \
	-I ../../../specs -I ../../../lib -I ../../../lib/fst -I $(KREMLIN_HOME)/include \
	-skip-translation $^


hmac_sha2_256-c/Hacl_HMAC_SHA2_256.c: hmac_sha2_256-c/out.krml
	$(KREMLIN) $(KREMLIN_ARGS) -add-include '"../../../../lib/c/Lib_PrintBuffer.h"' -add-include '"C_String.h"' -fparentheses -tmpdir hmac_sha2_256-c -no-prefix 'Test.Impl.HMAC_SHA2_256' \
	-skip-compilation -bundle 'Hacl.HMAC_SHA2_256=Hacl.Impl.*,Hacl.HMAC_SHA2_256' \
	$^ -o $@

hmac_sha2_256-c/Test_Impl_HMAC_SHA2_256.c: hmac_sha2_256-c/out.krml
	$(KREMLIN) $(KREMLIN_ARGS) $(KREMLIN_TESTLIB) -tmpdir hmac_sha2_256-c -skip-compilation -no-prefix Test.Impl.HMAC_SHA2_256 \
	-bundle 'Hacl.HMAC_SHA2_256=Hacl.Impl.*,Hacl.HMAC_SHA2_256' \
	$^ -o $@


test-hmac_sha2_256.exe: hmac_sha2_256-c/Hacl_HMAC_SHA2_256.c hmac_sha2_256-c/Test_Impl_HMAC_SHA2_256.c $(BASE_OBJ)
	$(CC) $(CFLAGS) -I $(KREMLIN_HOME) -I $(KREMLIN_HOME)/kremlib/dist/generic -L $(KREMLIN_HOME)/kremlib/dist/generic -o $@ $^ -lkremlib


#
# Clean
#

clean:
	rm -rf *~ *.exe *.exe.dSYM *.checked.lax
	rm -rf hmac_sha2_256-c
