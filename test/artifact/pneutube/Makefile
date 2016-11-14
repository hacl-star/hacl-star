FSTAR_HOME?=../../../../FStar
KREMLIN_HOME?=$(FSTAR_HOME)/../kremlin
ARTIFACT_HOME=..
include ../Makefile.include

tube-star.exe: Box.Ideal.fst c_bindings/PaddedFileIO_impl.c c_bindings/SocketIO_impl.c Hacl.Tube.fst tube.c
	mkdir -p tube
	$(KREMLIN) $(KREMLIN_ARGS) -I $(LIB_KRML) -I crypto $(KREMTEST)/testlib.c $^ \
		-I $(KREMLIB) -I $(KREMTEST) -I ./c_bindings -I ./tube -no-prefix Libsodium \
		-add-include '<sodium.h>' -add-include '"testlib.h"' \
		-tmpdir tube -o tube-star.exe -ldopt "-lsodium"

clean:
	rm -rf tube
	rm -f *~ *.exe
