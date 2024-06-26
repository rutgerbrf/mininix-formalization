# Modified from the Logical Foundations Makefile

COQMFFLAGS := -Q . mininix

ALLVFILES := maptools.v relations.v expr.v shared.v binop.v matching.v sem.v \
             interpreter.v complete.v sound.v correct.v semprop.v

build: Makefile.coq
	$(MAKE) -f Makefile.coq

clean::
	if [ -e Makefile.coq ]; then $(MAKE) -f Makefile.coq cleanall; fi
	$(RM) $(wildcard Makefile.coq Makefile.coq.conf)

Makefile.coq:
	coq_makefile $(COQMFFLAGS) -o Makefile.coq $(ALLVFILES)

-include Makefile.coq

.PHONY: build clean
