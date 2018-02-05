HACL_HOME=..

# The main Makefile that knows which combinations of targets are possible/valid.
all: check
	rm -f .depend.*
	$(MAKE) runtime_switch vale_aes_concrete_id hacl_aes_concrete_id vale_aes_abstract_id hacl_aes_abstract_id

check:
ifeq (,$(findstring shortest-stem,$(.FEATURES)))
	@echo "ERROR: This Makefile requires GNU Make >= 3.82"
	@exit 1
endif

# The following targets are not parallel and must occur at most once in
# parallel:
# - quicprovider-test (a dependency of test)
# - vale
# The reason is that they generate object files in the current directory, as
# opposed to copying the source files into their out/$(IMPL_CHOICE) private
# directory, and building there.

runtime_switch:
	IMPL_CHOICE=runtime_switch $(MAKE) -f Makefile.extract all concrete test vale

vale_aes_concrete_id:
	IMPL_CHOICE=vale_aes_concrete_id $(MAKE) -f Makefile.extract krml-test

hacl_aes_concrete_id:
	IMPL_CHOICE=hacl_aes_concrete_id $(MAKE) -f Makefile.extract krml-test

vale_aes_abstract_id:
	IMPL_CHOICE=vale_aes_abstract_id $(MAKE) -f Makefile.extract abstract

hacl_aes_abstract_id:
	IMPL_CHOICE=hacl_aes_abstract_id $(MAKE) -f Makefile.extract abstract

clean:
	rm -rf .depend.extract out/* vale/asm/*.o LowCProvider/*.{cm*,o,a}

include $(HACL_HOME)/secure_api/Makefile.common
