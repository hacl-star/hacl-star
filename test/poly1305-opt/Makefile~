ifeq ($(wildcard asmopt.mak),)
$(error Run ./configure first)
endif

include asmopt.mak

##########################
# set up variables
#

BASEDIR = .
BINDIR = bin
BUILDDIR = build
BUILDDIRUTIL = build_util
INCLUDE = $(addprefix -I$(BASEDIR)/,$(appdir)/extensions $(appdir)/include framework/include framework/driver framework/driver/$(ARCH))
CINCLUDE = $(INCLUDE)
ASMINCLUDE = $(INCLUDE)

# yasm doesn't need includes passed to the assembler
ifneq ($(AS),yasm)
COMMA := ,
ASMINCLUDE += $(addprefix -Wa$(COMMA),$(INCLUDE))
endif

###########################
# define recursive wildcard: $(call rwildcard, basepath, globs)
#
rwildcard = $(foreach d, $(wildcard $(1)*), $(call rwildcard, $(d)/, $(2)) $(filter $(subst *, %, $(2)), $(d)))

SRCDRIVER = $(wildcard framework/driver/*.c)
SRCEXT = $(call rwildcard, $(appdir)/extensions/, *.c)
SRCASM =
SRCMAIN = $(appdir)/main.c
SRCUTIL = framework/main_util.c framework/bench.c framework/fuzz.c
SRCSHARED = framework/main_shared.c


# do we have an assembler?
ifeq ($(HAVEAS),yes)

# grab all the assembler files
SRCASM = $(call rwildcard, $(appdir)/extensions/, *.S)

# add asm for the appropriate arch
SRCASM += $(call rwildcard, $(addsuffix $(ARCH),framework/driver/), *.S)

endif

##########################
# expand all source file paths in to object files in $(BUILDDIR)/$(BUILDDIRUTIL)
#
OBJDRIVER = $(patsubst %.c, $(BUILDDIR)/%.o, $(SRCDRIVER))
OBJEXT = $(patsubst %.c, $(BUILDDIR)/%.o, $(SRCEXT))
OBJASM = $(patsubst %.S, $(BUILDDIR)/%.o, $(SRCASM))
OBJMAIN = $(patsubst %.c, $(BUILDDIR)/%.o, $(SRCMAIN))
OBJUTIL = $(patsubst %.c, $(BUILDDIRUTIL)/%.o, $(SRCUTIL))
OBJEXTUTIL = $(patsubst %.c, $(BUILDDIRUTIL)/%.o, $(SRCEXT))
OBJSHARED = $(patsubst %.c, $(BUILDDIR)/%.o, $(SRCSHARED))

##########################
# non-file targets
#
.PHONY: all
.PHONY: default
.PHONY: makebin
.PHONY: exe
.PHONY: lib
.PHONY: shared
.PHONY: util

.PHONY: install-shared
.PHONY: install-generic
.PHONY: install-lib
.PHONY: uninstall

.PHONY: clean
.PHONY: distclean


all: default

default: lib

makebin:
	@mkdir -p $(BINDIR)

exe: makebin $(BINDIR)/$(PROJECTNAME)$(EXE)
	@echo built [$(BINDIR)/$(PROJECTNAME)$(EXE)]

install-generic:
	$(INSTALL) -d $(includedir)/lib$(PROJECTNAME)
	$(INSTALL) -d $(libdir)
	$(INSTALL) -m 644 $(appdir)/include/*.h $(includedir)/lib$(PROJECTNAME)

lib: makebin $(BINDIR)/$(PROJECTNAME)$(STATICLIB)
	@echo built [$(BINDIR)/$(PROJECTNAME)$(STATICLIB)]

install-lib: lib install-generic
	$(INSTALL) -m 644 $(BINDIR)/$(PROJECTNAME)$(STATICLIB) $(libdir)
	$(if $(RANLIB), $(RANLIB) $(libdir)/$(PROJECTNAME)$(STATICLIB))

util: makebin $(BINDIR)/$(PROJECTNAME)-util$(EXE)
	@echo built [$(BINDIR)/$(PROJECTNAME)-util$(EXE)]

ifeq ($(HAVESHARED),yes)
shared: makebin $(BINDIR)/$(SONAME)
	@echo built [$(BINDIR)/$(SONAME)]

install-shared: shared install-generic
ifneq ($(SOIMPORT),)
	$(INSTALL) -d $(bindir)
	$(INSTALL) -m 755 $(BINDIR)/$(SONAME) $(bindir)
	$(INSTALL) -m 644 $(BINDIR)/$(SOIMPORT) $(libdir)
else ifneq ($(SONAME),)
	$(INSTALL) -m 755 $(BINDIR)/$(SONAME) $(libdir)
	ln -f -s $(libdir)/$(SONAME) $(libdir)/lib$(PROJECTNAME).$(SOSUFFIX)
endif
else
shared:
	@echo project must be /configured with --pic

install-shared:
	@echo project must be /configured with --pic
endif # HAVESHARED

uninstall:
	rm -rf $(includedir)/lib$(PROJECTNAME)
	rm -f $(libdir)/$(PROJECTNAME)$(STATICLIB)
ifneq ($(SOIMPORT),)
	rm -f $(bindir)/$(SONAME) $(libdir)/lib$(SOIMPORT)
else ifneq ($(SONAME),)
	rm -f $(libdir)/$(SONAME) $(libdir)/lib$(PROJECTNAME).$(SOSUFFIX)
endif

clean:
	@echo cleaning project [$(PROJECTNAME)]
	@rm -rf $(BUILDDIR)/*
	@rm -rf $(BUILDDIRUTIL)/*
	@rm -rf $(BINDIR)/*

distclean: clean
	@rm asmopt.mak
	@rm config.log

##########################
# build rules for files
#

# use $(BASEOBJ) in build rules to grab the base path/name of the object file, without an extension
BASEOBJ = $(BUILDDIR)/$*
BASEOBJUTIL = $(BUILDDIRUTIL)/$*

# building .S (assembler) files
$(BUILDDIR)/%.o: %.S
	@mkdir -p $(dir $@)
# yasm needs one pass to compile, and one to generate dependencies
ifeq ($(AS),yasm)
	$(AS) $(ASFLAGS) $(ASMINCLUDE) -o $@ $<
	@$(AS) $(ASFLAGS) $(ASMINCLUDE) -o $@ -M $< >$(BASEOBJ).temp
else
	$(AS) $(ASFLAGS) $(ASMINCLUDE) $(DEPMM) $(DEPMF) $(BASEOBJ).temp -D BUILDING_ASM -c -o $(BASEOBJ).o $<
endif
	@cp $(BASEOBJ).temp $(BASEOBJ).P
	@sed \
	-e 's/^[^:]*: *//' \
	-e 's/ *\\$$//' \
	-e '/^$$/ d' \
	-e 's/$$/ :/' \
	< $(BASEOBJ).temp >> $(BASEOBJ).P
	@rm -f $(BASEOBJ).temp

# building .c (C) files
$(BUILDDIR)/%.o: %.c
	@mkdir -p $(dir $@)
	$(CC) $(CFLAGS) $(CINCLUDE) $(DEPMM) $(DEPMF) $(BASEOBJ).temp -c -o $(BASEOBJ).o $<
	@cp $(BASEOBJ).temp $(BASEOBJ).P
	@sed \
	-e 's/#.*//' \
	-e 's/^[^:]*: *//' \
	-e 's/ *\\$$//' \
	-e '/^$$/ d' \
	-e 's/$$/ :/' \
	< $(BASEOBJ).temp >> $(BASEOBJ).P
	@rm -f $(BASEOBJ).temp

# building .c (C) files for fuzzing/benching
$(BUILDDIRUTIL)/%.o: %.c
	@mkdir -p $(dir $@)
	$(CC) $(CFLAGS) $(CINCLUDE) $(DEPMM) $(DEPMF) $(BASEOBJUTIL).temp -DUTILITIES -c -o $(BASEOBJUTIL).o $<
	@cp $(BASEOBJUTIL).temp $(BASEOBJUTIL).P
	@sed \
	-e 's/#.*//' \
	-e 's/^[^:]*: *//' \
	-e 's/ *\\$$//' \
	-e '/^$$/ d' \
	-e 's/$$/ :/' \
	< $(BASEOBJUTIL).temp >> $(BASEOBJUTIL).P
	@rm -f $(BASEOBJUTIL).temp


##########################
# include all auto-generated dependencies
#

-include $(OBJDRIVER:%.o=%.P)
-include $(OBJEXT:%.o=%.P)
-include $(OBJASM:%.o=%.P)
-include $(OBJMAIN:%.o=%.P)
-include $(OBJUTIL:%.o=%.P)
-include $(OBJEXTUTIL:%.o=%.P)
-include $(OBJSHARED:%.o=%.P)

##########################
# final build targets
#
$(BINDIR)/$(PROJECTNAME)$(EXE): $(OBJDRIVER) $(OBJEXT) $(OBJASM) $(OBJMAIN)
	$(CC) $(CFLAGS) -o $@ $(OBJDRIVER) $(OBJEXT) $(OBJASM) $(OBJMAIN)

$(BINDIR)/$(PROJECTNAME)$(STATICLIB): $(OBJDRIVER) $(OBJEXT) $(OBJASM)
	rm -f $(PROJECTNAME)$(STATICLIB)
	$(AR)$@ $(OBJDRIVER) $(OBJEXT) $(OBJASM)
	$(if $(RANLIB), $(RANLIB) $@)

$(BINDIR)/$(PROJECTNAME)-util$(EXE): $(OBJDRIVER) $(OBJEXTUTIL) $(OBJASM) $(OBJUTIL)
	$(CC) $(CFLAGS) -o $@ $(OBJDRIVER) $(OBJEXTUTIL) $(OBJASM) $(OBJUTIL)

ifeq ($(HAVESHARED),yes)
$(BINDIR)/$(SONAME): $(OBJDRIVER) $(OBJEXT) $(OBJASM) $(OBJSHARED)
	$(LD)$@ $(OBJDRIVER) $(OBJEXT) $(OBJASM) $(OBJSHARED) $(SOFLAGS) $(LDFLAGS)
endif
