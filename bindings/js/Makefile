# JP: this is a local Makefile to debug those bindings... use at your own risk!
# - It is not integrated with the rest of the build system
# - It does not re-extract the WASM files via krml
# - It copies all of the required files

.PHONY: all

SHELL=/bin/bash

ifeq (,$(KRML_HOME))
$(error Please define KRML_HOME)
endif

all:
	cp $(KRML_HOME)/krmllib/js/loader.js .
	cp ../../dist/wasm/*.{wasm,js,html} .
	cp ../../dist/wasm/layouts.json .

	node api_test.js
	node test2.js
