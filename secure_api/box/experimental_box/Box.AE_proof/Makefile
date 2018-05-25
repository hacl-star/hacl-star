FSTAR_HOME=../../../../../FStar
KREMLIN_HOME=../../../../../kremlin
HACL_HOME=../../../..
FSTAR=$(FSTAR_HOME)/bin/fstar.exe

FSTAR_INCLUDES=--include $(HACL_HOME)/specs --include $(HACL_HOME)/specs/experimental --include $(HACL_HOME)/secure_api/utils --include $(HACL_HOME)/code/lib --include $(KREMLIN_HOME)/kremlib/

VERIFY= \
	Box.AE \
	Box.Key

#FSTI_DIR=$(shell pwd)
mkfile_path := $(abspath $(lastword $(MAKEFILE_LIST)))
current_dir := $(notdir $(patsubst %/,%,$(dir $(mkfile_path))))

Box.AE_INCLUDES=--include ../Box.Key_impl

all: $(addsuffix .fsti-ver, $(VERIFY)) \
	 $(addsuffix .fsti-impl-ver, $(VERIFY)) \
#    $(addsuffix .fst-ver, $(VERIFY)) 

#fst-ver: $(addsuffix .fst-ver, $(VERIFY))

fsti-ver: $(addsuffix .fsti-ver, $(VERIFY))

fsti-impl-ver: $(addsuffix .fsti-impl-ver, $(VERIFY))

#%.fst-ver:
#	$(FSTAR) \
#	$(FSTAR_INCLUDES) \
#	$($(basename $@)_INCLUDES) \
#	$(basename $@).fst

%.fsti-ver:
	$(FSTAR) \
	$(FSTAR_INCLUDES) \
	$($(basename $@)_INCLUDES) \
	--include ../$(addsuffix _impl, $(basename $@)) \
	$(basename $@).fsti

%.fsti-impl-ver:
	cd ../$(addsuffix _impl, $(basename $@)); \
	$(FSTAR) \
	$(FSTAR_INCLUDES) \
	../$(current_dir)/$(basename $@).fsti \
	$(basename $@).fst
