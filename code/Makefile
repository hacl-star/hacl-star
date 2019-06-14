KREMLIN_HOME ?= ../../kremlin
HACL_HOME    ?= ..

.PHONY: dump-%
dump-%:
	mkdir -p dump
	GENERATED_DIR=$(HACL_HOME)/code/dump make -C $* stage1
	rm -f dump/Makefile.*

snapshot: dump-poly1305 dump-chacha20 dump-curve25519
	cp $(HACL_HOME)/lib/c/vec-intrin.h dump
	cp $(KREMLIN_HOME)/kremlib/dist/generic/libkremlib.a dump
	cp $(KREMLIN_HOME)/kremlib/dist/generic/TestLib.h dump
	cp $(KREMLIN_HOME)/kremlib/dist/generic/FStar_UInt_8_16_32_64.h dump
	cp $(KREMLIN_HOME)/include/kremlib.h dump
	cp -r $(KREMLIN_HOME)/include/kremlin dump/kremlin
	cp curve25519/vale_25519.h dump
	cp curve25519/rfc7748_25519.h dump

	mkdir -p dump/test
	cp poly1305/poly1305_test.c dump/test
	cp chacha20/chacha20*-test.c dump/test
	mkdir -p dump/test/hacl-c
	cp $(HACL_HOME)/snapshots/hacl-c/Hacl_Chacha20_Vec128.[ch] dump/test/hacl-c
	cp $(HACL_HOME)/snapshots/hacl-c/Hacl_Chacha20.[ch] dump/test/hacl-c
	cp $(HACL_HOME)/snapshots/hacl-c/vec128.h dump/test/hacl-c
	cp curve25519/curve51-test.c dump/test
	cp curve25519/curve64-test.c dump/test
	cp curve25519/curve64-rfc-test.c dump/test
	cp curve25519/vale/obj/curve25519-x86_64-darwin.S dump/test
	cp -r curve25519/rfc7748_src dump/test
	cp Makefile.snapshot dump/Makefile

tezos-snapshot: snapshot
	make -C snapshot

test-snapshot: snapshot
	make -C dump test-snapshot

test-tezos-snapshot: tezos-snapshot
	make -C dump test-tezos-snapshot

clean:
	rm -rf dump
