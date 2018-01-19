# The main Makefile that knows which combinations of targets are possible/valid.
all:
	IMPL_CHOICE=runtime_switch $(MAKE) -f Makefile.extract all test out/vale.a
	IMPL_CHOICE=vale_aes_concrete_id $(MAKE) -f Makefile.extract krml-test
	IMPL_CHOICE=hacl_aes_concrete_id $(MAKE) -f Makefile.extract krml-test
	IMPL_CHOICE=vale_aes_abstract_id $(MAKE) -f Makefile.extract standalone
	IMPL_CHOICE=hacl_aes_abstract_id $(MAKE) -f Makefile.extract standalone

runtime_switch:
	IMPL_CHOICE=runtime_switch $(MAKE) -f Makefile.extract all test out/vale.a

clean:
	$(MAKE) -f Makefile.extract clean
