HACL_HOME=../..
include $(HACL_HOME)/Makefile.common

HPKE_TEST_DIR=hpke

test_hpke: $(HPKE_TEST_DIR)/test_hpke.exe
	$(HPKE_TEST_DIR)/test_hpke.exe

$(HPKE_TEST_DIR)/test_hpke.exe: $(HACL_HOME)/obj/libhaclml.cmxa $(HPKE_TEST_DIR)/Test_Spec_Agile_HPKE.ml
	$(OCAMLOPT) $^ -o $@

