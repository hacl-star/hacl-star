FSTAR_HOME=../../../../../FStar
KREMLIN_HOME=../../../../../kremlin
HACL_HOME=../../../..
FSTAR=$(FSTAR_HOME)/bin/fstar.exe

FSTAR_INCLUDES= --include $(HACL_HOME)/specs --include $(HACL_HOME)/specs/experimental --include $(HACL_HOME)/secure_api/utils --include $(HACL_HOME)/code/lib --include $(KREMLIN_HOME)/kremlib/

VERIFY= \
	Box.AE

Box.AE_INCLUDES= --include ../Box.Key_impl --include ../Box.Plain_impl

all: $(addsuffix .fsti-ver, $(VERIFY)) $(addsuffix .fst-ver, $(VERIFY))

fst-ver: $(addsuffix .fst-ver, $(VERIFY))

fsti-ver: $(addsuffix .fsti-ver, $(VERIFY))

%.fst-ver:
	$(FSTAR) \
	$(FSTAR_INCLUDES) \
	$($(basename $@)_INCLUDES) \
	$(basename $@).fst

%.fsti-ver:
	$(FSTAR) \
	$(FSTAR_INCLUDES) \
	$($(basename $@)_INCLUDES) \
	$(basename $@).fsti

%.fst-in:
	@echo $(FSTAR_INCLUDES) \
	$($(basename $@)_INCLUDES)

%.fsti-in:
	@echo $(FSTAR_INCLUDES) \
	$($(basename $@)_INCLUDES)
