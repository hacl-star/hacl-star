FSTAR_HOME=../../../../FStar
KREMLIN_HOME=../../../../kremlin
HACL_HOME=../../..
FSTAR=$(FSTAR_HOME)/bin/fstar.exe

FSTAR_INCLUDES=--include $(HACL_HOME)/specs --include $(HACL_HOME)/specs/experimental --include $(HACL_HOME)/secure_api/utils --include $(HACL_HOME)/code/lib --include $(KREMLIN_HOME)/kremlib/

VERIFY= \
	Box.Key \
	Box.ODH

all: $(addsuffix .fst-ver, $(VERIFY))

%.fst-ver:
	$(FSTAR) \
	$(FSTAR_INCLUDES) \
	$(basename $@).fst
