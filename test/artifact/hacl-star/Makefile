FSTAR_HOME?=../../../../FStar
KREMLIN_HOME?=$(FSTAR_HOME)/../kremlin
ARTIFACT_HOME=..
include ../Makefile.include

tube-star.exe: crypto/Hacl.EC.Curve25519.fst pneutube/Box.Ideal.fst pneutube/c_bindings/PaddedFileIO_impl.c c_bindings/SocketIO_impl.c pneutube/Hacl.Tube.fst pneutube/tube.c
	mkdir -p tube
	$(KREMLIN) $(KREMLIN_ARGS) -I $(LIB_KRML) -I crypto $(KREMTEST)/testlib.c $^ \
		-I $(KREMLIB) -I $(KREMTEST) -I ./c_bindings -I ./tube -no-prefix Libsodium \
		-add-include '<sodium.h>' -add-include '"testlib.h"' \
		-tmpdir tube -o tube-star.exe -ldopt "-lsodium"

tube-lax: pneutube/Hacl.Tube.fst
	$(FSTAR) --include $(LIB_KRML) --include pneutube/c_bindings --include crypto_api \
		--include $(KREMLIB) --include $(KREMTEST) $^ --lax --include pneutube --include $(FSTAR_HOME)/ulib/hyperstack

tube-ver: pneutube/Hacl.Tube.fst
	$(FSTAR) --include $(LIB_KRML) --include c_bindings --include crypto_api \
		--include $(KREMLIB) --include $(KREMTEST) $^

clean:
	rm -rf tube
	rm -f *~ *.exe
