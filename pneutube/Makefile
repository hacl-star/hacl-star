FSTAR_HOME?=../../FStar
KREMLIN_HOME?=$(FSTAR_HOME)/../kremlin
HACL_HOME=..
include ../lib/hyperstack/Makefile.include

tube-star.exe: ../crypto/ec/Hacl.EC.Curve25519.fst Box.Ideal.fst c_bindings/PaddedFileIO_impl.c c_bindings/SocketIO_impl.c Hacl.Tube.Send.fst Hacl.Tube.Receive.fst tube.c
	mkdir -p tube
	$(KREMLIN) $(KREMLIN_ARGS) -I $(HACL_KREMLIN) -I ../crypto $(KREMTEST)/testlib.c $^ \
		-I $(KREMLIB) -I $(KREMTEST) -I c_bindings -I ../crypto/ec -I ../crypto/symmetric \
		-no-prefix Libsodium -add-include '<sodium.h>' -add-include '"testlib.h"' \
		-tmpdir tube -o tube-star.exe -ldopt "-lsodium"

tube-lax: Hacl.Tube.Receive.fst
	$(FSTAR) -I $(HACL_KREMLIN) -I c_bindings -I ../crypto/api \
		-I $(KREMLIB) -I $(KREMTEST) $^ -fsopt "--lax" -I $(FSTAR_HOME)/ulib/hyperstack

tube-ver: send-ver receive-ver

send-ver: Hacl.Tube.Send.fst
	$(FSTAR) -I $(HACL_KREMLIN) -I c_bindings -I ../crypto/api --use_hints \
		-I $(KREMLIB) -I $(KREMTEST) -I $(FSTAR_HOME)/ulib/hyperstack $^

send-lax: Hacl.Tube.Send.fst
	$(FSTAR) -I $(HACL_KREMLIN) -I c_bindings -I ../crypto/api -fstop "--lax" \
		-I $(KREMLIB) -I $(KREMTEST) -I $(FSTAR_HOME)/ulib/hyperstack $^

receive-ver: Hacl.Tube.Receive.fst
	$(FSTAR) -I $(HACL_KREMLIN) -I c_bindings -I ../crypto/api --use_hints  \
		-I $(KREMLIB) -I $(KREMTEST) -I $(FSTAR_HOME)/ulib/hyperstack $^

receive-lax: Hacl.Tube.Receive.fst
	$(FSTAR) -I $(HACL_KREMLIN) -I c_bindings -I ../crypto/api -fsopt "--lax" \
		-I $(KREMLIB) -I $(KREMTEST) -I $(FSTAR_HOME)/ulib/hyperstack $^ 


clean:
	rm -rf tube
	rm -rf *~ *.exe *.dSYM
