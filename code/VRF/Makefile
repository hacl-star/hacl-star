include ../../Makefile.include

FSTAR_INCLUDES+=--include $(HACL_HOME)/code/bignum  --include $(HACL_HOME)/code/curve25519 --include $(HACL_HOME)/code/hash --include $(HACL_HOME)/code/ed25519

%.fst-ver: %.fst 
	$(FSTAR) $(addprefix -fsopt , $(FSTAR_OPTIONS_VER)) $(FSTAR_INCLUDES)  --record_hints --verify_module $(basename $(notdir $@)) $^

%.fst-verR: %.fst
	$(FSTAR) $(addprefix -fsopt , $(FSTAR_OPTIONS_VER)) $(FSTAR_INCLUDES)  --record_hints --hint_info  --verify_module $(basename $(notdir $@)) $^
