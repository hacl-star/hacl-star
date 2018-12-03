HACL_HOME=..
IMPL_CHOICE=runtime_switch

include $(HACL_HOME)/secure_api/Makefile.extract

.PHONY: clean
clean:
	rm -rf .depend.extract out/* vale/asm/*.o

SHELL=/bin/bash

.PHONY: clean-c
clean-c:
	rm -rf out/*/{extracted,crypto}/*.{c,h}
