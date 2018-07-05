include ../../Makefile.include

KREMLIN_ARGS+=-verbose \
	-drop FStar,Prims,LowStar,C,C.*,C.Loops.Spec.Loops,Spec.*,Lib.*,WasmSupport \
	-drop Hacl.Cast,Hacl.UInt8,Hacl.UInt16,Hacl.UInt32,Hacl.UInt64,Hacl.UInt128 \
	-drop Hacl.Spec.Endianness,Hacl.Endianness,Seq.Create \
	-drop Hacl.Impl.SHA2_256.Lemmas,Hacl.Impl.SHA2_384.Lemmas,Hacl.Impl.SHA2_512.Lemmas \
	-ccopt -march=native

BASE_OBJ = ../../lib/c/Lib_Print.o

HACL_LIBS = ../../lib/fst/Lib.IntTypes.fst ../../lib/fst/Lib.RawIntTypes.fst ../../lib/c/Lib.Loops.fst ../../lib/fst/Lib.Buffer.fst  ../../lib/fst/Lib.ByteBuffer.fst ../../lib/Lib.Print.fsti


frodo-c/out.krml: $(HACL_LIBS) Hacl.Impl.PQ.Lib.fst
	$(KREMLIN) $(KREMLIN_ARGS) -fsopt "--expose_interfaces" -tmpdir frodo-c \
	-I ../../specs -I ../../lib -I ../../lib/fst -I $(KREMLIN_HOME)/include \
	-skip-translation $^


frodo-c/Hacl_Impl_PQ_Lib.c: frodo-c/out.krml
	$(KREMLIN) $(KREMLIN_ARGS) -add-include '"../../../lib/c/Lib_Print.h"' -add-include '"C_String.h"' -fparentheses -tmpdir frodo-c \
	-skip-compilation \
	$^ -o $@

clean:
	rm -rf *~ *.exe *.exe.dSYM
	rm -rf frodo-c
