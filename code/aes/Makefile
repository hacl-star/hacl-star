include ../../Makefile.include

# Files for verification
FILES = Hacl.Impl.AES.Bitsliced.fst

KREMLIN_ARGS+=-verbose \
	-drop FStar,Prims,LowStar,C.Loops.Spec.Loops,Spec.* \
	-ccopt -march=native

CFLAGS=-I $(HACL_HOME)/specs -I $(KREMLIN_HOME)/kremlib -I $(HACL_HOME)/code/aes -I $(KREMLIN_HOME)/include

%.o: %.c
	$(CC) $(CFLAGS) -c $< -o $@


#
# AES
#

BASE_OBJ = ../../specs/lib/c/Spec_Lib_Print.o $(KREMLIN_HOME)/kremlib/testlib.o $(KREMLIN_HOME)/kremlib/kremlib.o $(KREMLIN_HOME)/kremlib/kremstr.o

HACL_LIBS = ../../specs/lib/fst/Spec.Lib.IntTypes.fst ../../specs/lib/fst/Spec.Lib.RawIntTypes.fst ../../specs/lib/c/Spec.Lib.Loops.fst ../../specs/lib/fst/Spec.Lib.IntBuf.fst  ../../specs/lib/c/Spec.Lib.Endian.fst ../../specs/lib/fst/Spec.Lib.IntBuf.LoadStore.fst


aes-c/out.krml: $(HACL_LIBS) Hacl.Impl.AES.Bitsliced.fst
	$(KREMLIN) $(KREMLIN_ARGS) -add-include '"kremlin/c_string.h"' -fsopt "--expose_interfaces" -tmpdir aes-c \
	-I ../../specs -I ../../specs/lib -I ../../specs/lib/fst -I $(KREMLIN_HOME)/include \
	-skip-translation $^


aes-c/Hacl_Impl_AES_Bitsliced.c: aes-c/out.krml
	$(KREMLIN) $(KREMLIN_ARGS) -add-include '"myvoid.h"' -add-include '"kremlin/c_string.h"' -fparentheses \
	-tmpdir aes-c -skip-compilation \
	$^ -o $@


aes_test.exe: aes-c/Hacl_Impl_AES_Bitsliced.c aes_test.c
	$(CC) $(CFLAGS) aes-c/Hacl_Impl_AES_Bitsliced.c aes_test.c -o aes_test.exe
	./aes_test.exe


extract-c: aes-c/Hacl_Impl_AES_Bitsliced.c

#
# Clean
#

clean:
	rm -rf *~ *.exe *.exe.dSYM *.checked.lax
	rm -rf aes-c
