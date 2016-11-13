FSTAR_HOME?=../../../../../FStar
KREMLIN_HOME=$(FSTAR_HOME)/../kremlin
HACL_HOME=../../../..
include $(HACL_HOME)/lib/hyperstack/Makefile.include

MODULES=Hacl.Symmetric.Poly1305_64.Parameters \
	Hacl.Symmetric.Poly1305_64.Bigint \
	Hacl.Symmetric.Poly1305_64 \
	Hacl.SecretBox \
	Hacl.Box \

INCLUDES=$(addprefix --include , $(HACL_LIB))

ver: $(addsuffix .fst-ver, $(MODULES))
