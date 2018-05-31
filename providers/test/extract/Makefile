-include Makefile.include 

EVERCRYPT_HOME=../../out
FILES = $(basename $(ALL_C_FILES))
CFLAGS = -I $(KREMLIN_HOME)/include

# See https://www.gnu.org/software/make/manual/html_node/Automatic-Prerequisites.html
%.d: %.c
	@set -e; rm -f $@; \
	  $(CC) -MM $(CFLAGS) $< > $@.$$$$; \
	  sed 's,\($(notdir $*)\)\.o[ :]*,$(dir $@)\1.o $@ : ,g' < $@.$$$$ > $@; \
	  rm -f $@.$$$$

-include $(addsuffix .d,$(FILES))

Test.exe: $(addsuffix .o,$(FILES)) $(KREMLIN_HOME)/kremlib/testlib.c $(KREMLIN_HOME)/kremlib/kremstr.c $(KREMLIN_HOME)/kremlib/kremlib.c 
	$(CC) $^ -o $@ -levercrypt -L $(EVERCRYPT_HOME) -I $(KREMLIN_HOME)/include

test: Test.exe
