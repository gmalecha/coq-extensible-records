all: Makefile.coq
	$(MAKE) -f Makefile.coq

clean: Makefile.coq
	$(MAKE) -f Makefile.coq clean

Makefile.coq: _CoqProject
	@ coq_makefile -f _CoqProject > Makefile.coq

.PHONY: all clean
