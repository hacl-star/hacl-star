# The main Makefile that knows which combinations of targets are possible/valid.

all:
	IMPL_CHOICE=runtime_switch $(MAKE) -f Makefile.extract all test
	IMPL_CHOICE=vale_aes_concrete_id $(MAKE) -f Makefile.extract test
	IMPL_CHOICE=hacl_aes_concrete_id $(MAKE) -f Makefile.extract test
	IMPL_CHOICE=vale_aes_abstract_id $(MAKE) -f Makefile.extract standalone
	IMPL_CHOICE=hacl_aes_abstract_id $(MAKE) -f Makefile.extract standalone
