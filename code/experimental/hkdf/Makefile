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
# HMAC_SHA2_256
#

BASE_OBJ = ../../../lib/c/Lib_PrintBuffer.o

HACL_LIBS = ../../../lib/fst/Lib.IntTypes.fst ../../../lib/fst/Lib.RawIntTypes.fst ../../../lib/c/Lib.Loops.fst ../../../lib/fst/Lib.Buffer.fst  ../../../lib/fst/Lib.ByteBuffer.fst ../../../lib/Lib.PrintBuffer.fsti


hkdf_sha2_256-c/out.krml: $(HACL_LIBS) ../sha2/Hacl.Impl.SHA2_256.fst ../sha2/Hacl.SHA2_256.fst ../hmac/Hacl.Impl.HMAC_SHA2_256.fst ../hmac/Hacl.HMAC_SHA2_256.fst Hacl.Impl.HKDF_SHA2_256.fst Hacl.HKDF_SHA2_256.fst Test.Impl.HKDF_SHA2_256.fst
	$(KREMLIN) $(KREMLIN_ARGS) -fsopt "--expose_interfaces" -tmpdir hkdf_sha2_256-c \
	-I ../../../specs -I ../../../lib -I ../../../lib/fst -I $(KREMLIN_HOME)/include \
	-skip-translation $^


hkdf_sha2_256-c/Hacl_HKDF_SHA2_256.c: hkdf_sha2_256-c/out.krml
	$(KREMLIN) $(KREMLIN_ARGS) -add-include '"../../../../lib/c/Lib_PrintBuffer.h"' -add-include '"C_String.h"' -fparentheses -tmpdir hkdf_sha2_256-c -no-prefix 'Test.Impl.HKDF_SHA2_256' \
	-skip-compilation -bundle 'Hacl.HKDF_SHA2_256=Hacl.Impl.*,Hacl.HKDF_SHA2_256' \
	$^ -o $@

hkdf_sha2_256-c/Test_Impl_HKDF_SHA2_256.c: hkdf_sha2_256-c/out.krml
	$(KREMLIN) $(KREMLIN_ARGS) $(KREMLIN_TESTLIB) -tmpdir hkdf_sha2_256-c -skip-compilation -no-prefix Test.Impl.HKDF_SHA2_256 \
	-bundle 'Hacl.HKDF_SHA2_256=Hacl.Impl.*,Hacl.HKDF_SHA2_256' \
	$^ -o $@


test-hkdf_sha2_256.exe: hkdf_sha2_256-c/Hacl_HKDF_SHA2_256.c hkdf_sha2_256-c/Test_Impl_HKDF_SHA2_256.c $(BASE_OBJ)
	$(CC) $(CFLAGS) -I $(KREMLIN_HOME) -I $(KREMLIN_HOME)/kremlib/extracted -L $(KREMLIN_HOME)/kremlib/out -o $@ $^ -lkremlib


#
# Clean
#

clean:
	rm -rf *~ *.exe *.exe.dSYM *.checked.lax
	rm -rf hkdf_sha2_256-c
