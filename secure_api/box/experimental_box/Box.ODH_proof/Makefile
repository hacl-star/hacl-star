FSTAR_HOME=../../../../../FStar
KREMLIN_HOME=../../../../../kremlin
HACL_HOME=../../../..
FSTAR=$(FSTAR_HOME)/bin/fstar.exe

FSTAR_INCLUDES=--include $(HACL_HOME)/specs --include $(HACL_HOME)/specs/experimental --include $(HACL_HOME)/secure_api/utils --include $(HACL_HOME)/code/lib --include $(KREMLIN_HOME)/kremlib/

VERIFY= \
	Box.ODH\
	Box.Key

mkfile_path := $(abspath $(lastword $(MAKEFILE_LIST)))
current_dir := $(notdir $(patsubst %/,%,$(dir $(mkfile_path))))

Box.ODH_INCLUDES=--include ../Box.Key_impl

all: $(addsuffix .fsti-ver, $(VERIFY)) \


fsti-ver: $(addsuffix .fsti-ver, $(VERIFY))

%.fsti-ver:
	cd ../$(addsuffix _impl, $(basename $@)); \
	$(FSTAR) \
	$(FSTAR_INCLUDES) \
	../$(current_dir)/$(basename $@).fsti \
	$(basename $@).fst

