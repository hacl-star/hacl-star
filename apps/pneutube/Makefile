FSTAR_HOME?=../../FStar
KREMLIN_HOME?=$(FSTAR_HOME)/../kremlin
HACL_HOME=..
include ../lib/hyperstack/Makefile.include

tube-star.exe: ../crypto/ec/Hacl.EC.Curve25519.fst Box.Ideal.fst ../lib/io/c_bindings/PaddedFileIO_impl.c ../lib/io/c_bindings/SocketIO_impl.c Hacl.Tube.Send.fst Hacl.Tube.Receive.fst tube.c
	mkdir -p tube
	$(KREMLIN) $(KREMLIN_ARGS) -I $(HACL_KREMLIN) -I ../crypto $(KREMTEST)/testlib.c $^ \
		-I $(KREMLIB) -I $(KREMTEST) -I ../lib/io -I ../lib/io/c_bindings -I ../crypto/ec -I ../crypto/symmetric \
		-no-prefix Libsodium -add-include '<sodium.h>' -add-include '"testlib.h"' \
		-tmpdir tube -o tube-star.exe -ldopt "-lsodium"

tube-lax: Hacl.Tube.Receive.fst
	$(FSTAR) -I $(HACL_KREMLIN) -I ../lib/io -I ../lib/io/c_bindings -I ../crypto/api \
		-I $(KREMLIB) -I $(KREMTEST) $^ -fsopt "--lax" -I $(FSTAR_HOME)/ulib/hyperstack

tube-ver: send-ver receive-ver

tube-test: tube-star.exe
	mkdir -p send receive
	cd receive && ../tube-star.exe receive 5001 -k dfcf8b782a2a72f65ee24f85fa68ab1a10b3b555751283c5f0bcdb20e1a6e4a8 -p 4d187de7a95fe760ba7ffc9a1ba4229eea9cd1136fe609bdc58816e3cf4d3350 &
	cd send && echo "banana" > banana.txt; ../tube-star.exe send banana.txt localhost:5001 -k 4d922658eb6d4aef64a83644a18e60e61a57c245aa8e5e9a93926cb2b317ffd7 -p 223fc224f2c9906fd4bbb1313236ecc4f36ed2f7e95b5fb1deafc459b19ab069
	lsof -i tcp:5001 | awk 'NR!=1 {print $$2}' | xargs kill
	@rm -r send receive


send-ver: Hacl.Tube.Send.fst
	$(FSTAR) -I $(HACL_KREMLIN) -I ../lib/io -I ../lib/io/c_bindings -I ../crypto/api --use_hints \
		-I $(KREMLIB) -I $(KREMTEST) -I $(FSTAR_HOME)/ulib/hyperstack $^

send-lax: Hacl.Tube.Send.fst
	$(FSTAR) -I $(HACL_KREMLIN) -I ../lib/io -I ../lib/io/c_bindings -I ../crypto/api -fstop "--lax" \
		-I $(KREMLIB) -I $(KREMTEST) -I $(FSTAR_HOME)/ulib/hyperstack $^

receive-ver: Hacl.Tube.Receive.fst
	$(FSTAR) -I $(HACL_KREMLIN) -I ../lib/io -I ../lib/io/c_bindings -I ../crypto/api --use_hints  \
		-I $(KREMLIB) -I $(KREMTEST) -I $(FSTAR_HOME)/ulib/hyperstack $^

receive-lax: Hacl.Tube.Receive.fst
	$(FSTAR) -I $(HACL_KREMLIN) -I ../lib/io -I ../lib/io/c_bindings -I ../crypto/api -fsopt "--lax" \
		-I $(KREMLIB) -I $(KREMTEST) -I $(FSTAR_HOME)/ulib/hyperstack $^ 


clean:
	rm -rf tube
	rm -rf *~ *.exe *.dSYM
