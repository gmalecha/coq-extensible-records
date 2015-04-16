all: Makefile.coq
	$(MAKE) -f Makefile.coq

clean: Makefile.coq
	$(MAKE) -f Makefile.coq clean

Makefile.coq: _CoqProject *.v
	@ coq_makefile -f _CoqProject > Makefile.coq
