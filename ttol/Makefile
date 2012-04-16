HEADERS=camlib.h
SOURCES=camlib.c
EXES=camlib
LIBS=slz

# libslz.a is default target.
camlib: camlib.o

include config.mk


# Pattern rules
%.o: %.c flags
	@echo "   CC	$<"
	$(CC) $(CFLAGS) -c $< -o $@

$(EXES): %:
	@echo "   LD	$@"
	$(CCLD) $(LDFLAGS) -o $@ $^

%.tar.gz:
	@echo "   TAR	$@"
	ln -sf ./ $*
	tar czf $@ $(addprefix $*/,$^)
	rm $*

%.tar.bz2:
	@echo "   TAR	$@"
	ln -sf ./ $*
	tar cjf $@ $(addprefix $*/,$^)
	rm $*


# Used to force recompile if we change flags or makefiles.
.PHONY: FORCE
FORCE:

flags: new_flags FORCE
	@{ test -f $@ && diff -q $@ $< >/dev/null; } || \
	{ echo "Flags and makefiles changed; remaking."; cp $< $@; }
	@rm new_flags

new_flags:
	@echo CC="$(CC)" > $@
	@echo CFLAGS="$(CFLAGS)" >> $@
	@echo CCLD="$(CCLD)" >> $@
	@echo LDFLAGS="$(LDFLAGS)" >> $@
	@md5sum Makefile >> $@


# Cleaning stuff.
CLEAN_RULES=nodeps clean pristine
.PHONY: $(CLEAN_RULES)

nodeps:
	./depclean

clean:
	find . -name '*.o' -delete
	rm -f $(LIBS) $(EXES) slz-*.tar.*

pristine: clean nodeps
	rm -f flags new_flags


# Automatic dependency generation.

# Empty dep files indicate a deleted source file; we should get rid of them.
$(shell find . -name '*.dep' -empty -print0 | xargs -0 rm -f)

%.dep: %.c flags
	@echo "   DEP	$<"
	set -e; $(CC) -MM -MT $< $(filter-out -pedantic,$(CFLAGS)) $< |\
	sed 's,\($*\)\.c *:,\1.o $@ :,' > $@

CFILES=$(shell find . -name '*.c')

# Only include dep files in certain circumstances.
NODEP_RULES=$(CLEAN_RULES)

ifneq (,$(filter-out $(NODEP_RULES), $(MAKECMDGOALS)))
include $(CFILES:.c=.dep)
else ifeq (,$(MAKECMDGOALS))
include $(CFILES:.c=.dep)
else
endif
