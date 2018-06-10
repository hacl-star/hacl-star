-include Makefile.include 

KREMLIN_HOME?=../../../../kremlin
EVERCRYPT_HOME=../../out
MLCRYPTO_HOME?=../../../../MLCrypto
OPENSSL_HOME=$(MLCRYPTO_HOME)/openssl

FILES = $(basename $(ALL_C_FILES))
CFLAGS = -I $(KREMLIN_HOME)/include
LDFLAGS = -L $(EVERCRYPT_HOME) -levercrypt

ifeq (,$(EVEREST_WINDOWS))
LDFLAGS += -L$(OPENSSL_HOME) -lcrypto
else
LDFLAGS += -lbcrypt
endif

# See https://www.gnu.org/software/make/manual/html_node/Automatic-Prerequisites.html
%.d: %.c
	@set -e; rm -f $@; \
	  $(CC) -MM $(CFLAGS) $< > $@.$$$$; \
	  sed 's,\($(notdir $*)\)\.o[ :]*,$(dir $@)\1.o $@ : ,g' < $@.$$$$ > $@; \
	  rm -f $@.$$$$

-include $(addsuffix .d,$(FILES))

Test.exe: $(addsuffix .o,$(FILES)) $(KREMLIN_HOME)/kremlib/testlib.c $(KREMLIN_HOME)/kremlib/kremstr.c $(KREMLIN_HOME)/kremlib/kremlib.c 
	$(CC) $^ -o $@ $(LDFLAGS) -I $(KREMLIN_HOME)/include

test: Test.exe
