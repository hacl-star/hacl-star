FSTAR_HOME?=../../../../../FStar
KREMLIN_HOME?=$(FSTAR_HOME)/../kremlin
ARTIFACT_HOME=../..
include ../../Makefile.include

tube-star.exe: ../crypto/Hacl.EC.Curve25519.fst Box.Ideal.fst c_bindings/PaddedFileIO_impl.c c_bindings/SocketIO_impl.c Hacl.Tube.Send.fst Hacl.Tube.Receive.fst tube.c
	mkdir -p tube
	$(KREMLIN) $(KREMLIN_ARGS) -I $(LIB_KRML) -I ../crypto $(KREMTEST)/testlib.c $^ \
		-I $(KREMLIB) -I $(KREMTEST) -I c_bindings \
		-no-prefix Libsodium -add-include '<sodium.h>' -add-include '"testlib.h"' \
		-tmpdir tube -o tube-star.exe -ldopt "-lsodium"

tube-lax: Hacl.Tube.fst
	$(FSTAR) --include $(LIB_KRML) --include c_bindings --include ../crypto_api \
		--include $(KREMLIB) --include $(KREMTEST) $^ --lax --include $(FSTAR_HOME)/ulib/hyperstack

tube-ver: Hacl.Tube.fst
	$(FSTAR) --include $(LIB_KRML) --include c_bindings --include ../crypto_api \
		--include $(KREMLIB) --include $(KREMTEST) --include $(FSTAR_HOME)/ulib/hyperstack $^

send-ver: Hacl.Tube.Send.fst
	$(FSTAR) --include $(LIB_KRML) --include c_bindings --include ../crypto_api \
		--include $(KREMLIB) --include $(KREMTEST) --include $(FSTAR_HOME)/ulib/hyperstack $^

send-lax: Hacl.Tube.Send.fst
	$(FSTAR) --include $(LIB_KRML) --include c_bindings --include ../crypto_api --lax \
		--include $(KREMLIB) --include $(KREMTEST) --include $(FSTAR_HOME)/ulib/hyperstack $^

receive-ver: Hacl.Tube.Receive.fst
	$(FSTAR) --include $(LIB_KRML) --include c_bindings --include ../crypto_api \
		--include $(KREMLIB) --include $(KREMTEST) --include $(FSTAR_HOME)/ulib/hyperstack $^

receive-lax: Hacl.Tube.Receive.fst
	$(FSTAR) --include $(LIB_KRML) --include c_bindings --include ../crypto_api --lax \
		--include $(KREMLIB) --include $(KREMTEST) --include $(FSTAR_HOME)/ulib/hyperstack $^ 


clean:
	rm -rf tube
	rm -f *~ *.exe
