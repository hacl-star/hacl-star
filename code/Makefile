KREMLIN_HOME ?= ../../kremlin
HACL_HOME    ?= ..
BUILD_DIR = $(HACL_HOME)/build/c


.PHONY: extract-%
extract-%:
	mkdir -p $(BUILD_DIR)
	GENERATED_DIR=$(BUILD_DIR) make -C $* stage1
	rm -f $(BUILD_DIR)/Makefile.*

extract: extract-poly1305 extract-chacha20 extract-curve25519 extract-blake2s extract-sha3
	$(MAKE) extract-chacha20poly1305

snapshot: extract-poly1305 extract-chacha20 extract-curve25519 extract-blake2s extract-sha3
	$(MAKE) extract-chacha20poly1305
	cp $(HACL_HOME)/lib/c/vec-intrin.h $(BUILD_DIR)
	cp $(KREMLIN_HOME)/kremlib/dist/generic/libkremlib.a $(BUILD_DIR)
	cp $(KREMLIN_HOME)/kremlib/dist/generic/TestLib.h $(BUILD_DIR)
	cp $(KREMLIN_HOME)/kremlib/dist/generic/FStar_UInt_8_16_32_64.h $(BUILD_DIR)
	cp $(KREMLIN_HOME)/include/kremlib.h $(BUILD_DIR)
	cp -r $(KREMLIN_HOME)/include/kremlin $(BUILD_DIR)/kremlin
	cp curve25519/vale_25519.h $(BUILD_DIR)
	cp curve25519/rfc7748_25519.h $(BUILD_DIR)

	mkdir -p $(BUILD_DIR)/test
	cp poly1305/poly1305_test.c $(BUILD_DIR)/test
	cp chacha20/chacha20*-test.c $(BUILD_DIR)/test
	mkdir -p $(BUILD_DIR)/test/hacl-c
	cp $(HACL_HOME)/snapshots/hacl-c/Hacl_Chacha20_Vec128.[ch] $(BUILD_DIR)/test/hacl-c
	cp $(HACL_HOME)/snapshots/hacl-c/Hacl_Chacha20.[ch] $(BUILD_DIR)/test/hacl-c
	cp $(HACL_HOME)/snapshots/hacl-c/vec128.h $(BUILD_DIR)/test/hacl-c
	cp curve25519/curve51-test.c $(BUILD_DIR)/test
	cp curve25519/curve64-test.c $(BUILD_DIR)/test
	cp curve25519/curve64-rfc-test.c $(BUILD_DIR)/test
	cp curve25519/vale/obj/curve25519-x86_64-darwin.S $(BUILD_DIR)/test
	cp -r curve25519/rfc7748_src $(BUILD_DIR)/test
	cp Makefile.snapshot $(BUILD_DIR)/Makefile

tezos-snapshot: snapshot
	make -C snapshot

test-snapshot: snapshot
	make -C $(BUILD_DIR) test-snapshot

test-tezos-snapshot: tezos-snapshot
	make -C $(BUILD_DIR) test-tezos-snapshot

clean:
	rm -rf $(BUILD_DIR)
