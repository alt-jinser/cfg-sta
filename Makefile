# Build every file, then check the repository gates.
VFILES := protocol_lib mutex mutex_grammar mutex_param mutex_waitqueue \
          buffer guard_demo rcu rwlock spin rwmutex
SOURCES := $(addsuffix .v,$(VFILES))

all:
	nix develop ./nix -c bash -c 'set -e; $(foreach f,$(VFILES),rocq compile $(f).v &&) true'

check: all
	@test $$(grep -l "Theorem gen_iff_accepts" $(SOURCES) | wc -l) -eq 1
	@! grep -n "Admitted\|admit()\|assume()\|external_body" $(SOURCES)
	@echo "build + gates OK"

.PHONY: all check
