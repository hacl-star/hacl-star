HACL_HOME=..

# The main Makefile that knows which combinations of targets are possible/valid.
all: runtime_switch vale_aes_concrete_id hacl_aes_concrete_id vale_aes_abstract_id hacl_aes_abstract_id

runtime_switch:
	IMPL_CHOICE=runtime_switch $(MAKE) -f Makefile.extract all test out/vale.a

vale_aes_concrete_id:
	IMPL_CHOICE=vale_aes_concrete_id $(MAKE) -f Makefile.extract krml-test

hacl_aes_concrete_id:
	IMPL_CHOICE=hacl_aes_concrete_id $(MAKE) -f Makefile.extract krml-test

vale_aes_abstract_id:
	IMPL_CHOICE=vale_aes_abstract_id $(MAKE) -f Makefile.extract standalone

hacl_aes_abstract_id:
	IMPL_CHOICE=hacl_aes_abstract_id $(MAKE) -f Makefile.extract standalone

clean:
	$(MAKE) -f Makefile.extract clean

include $(HACL_HOME)/secure_api/Makefile.common
