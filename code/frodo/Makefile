include ../../Makefile.include

KREMLIN_ARGS+=-verbose \
	-drop FStar,Prims,LowStar,C,C.*,C.Loops.Spec.Loops,Spec.*,Lib.*,WasmSupport \
	-drop Hacl.Cast,Hacl.UInt8,Hacl.UInt16,Hacl.UInt32,Hacl.UInt64,Hacl.UInt128 \
	-drop Hacl.Spec.Endianness,Hacl.Endianness,Seq.Create \
	-drop Hacl.Impl.SHA2_256.Lemmas,Hacl.Impl.SHA2_384.Lemmas,Hacl.Impl.SHA2_512.Lemmas \
	-ccopt -march=native -warn-error +9

BASE_OBJ = ../../lib/c/Lib_Print.o

HACL_LIBS = ../../lib/fst/Lib.IntTypes.fst ../../lib/fst/Lib.RawIntTypes.fst ../../lib/c/Lib.Loops.fst ../../lib/fst/Lib.Buffer.fst  ../../lib/fst/Lib.ByteBuffer.fst ../../lib/Lib.Print.fsti


frodo-c/out.krml: $(HACL_LIBS) Hacl.Impl.PQ.Lib.fst Hacl.Keccak.fsti Hacl.Impl.Frodo.fst Hacl.Test.Frodo.fst
	$(KREMLIN) $(KREMLIN_ARGS) -fsopt "--expose_interfaces" -tmpdir frodo-c -no-prefix 'Hacl.Test.Frodo' \
	-I ../../specs -I ../../lib -I ../../lib/fst -I $(KREMLIN_HOME)/include \
	-skip-translation $^

frodo-c/Hacl_Impl_Frodo.c: frodo-c/out.krml
	$(KREMLIN) $(KREMLIN_ARGS)  -fparentheses -tmpdir frodo-c -no-prefix 'Hacl.Test.Frodo' \
	-skip-compilation \
	$^ -o $@

frodo-c/Hacl_Test_Frodo.c: frodo-c/out.krml
	$(KREMLIN) $(KREMLIN_ARGS) $(KREMLIN_TESTLIB) -tmpdir frodo-c -skip-compilation -no-prefix 'Hacl.Test.Frodo' \
	$^ -o $@

clean:
	rm -rf *~ *.exe *.exe.dSYM
	rm -rf frodo-c
