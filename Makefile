all: theories examples

theories: Makefile.coq
	$(MAKE) -f Makefile.coq

install: Makefile.coq
	$(MAKE) -f Makefile.coq install

clean: Makefile.coq
	$(MAKE) -f Makefile.coq clean

uninstall: Makefile.coq
	$(MAKE) -f Makefileq.coq uninstall

Makefile.coq: _CoqProject
	coq_makefile -f _CoqProject -o Makefile.coq


.PHONY: all clean dist theories examples
