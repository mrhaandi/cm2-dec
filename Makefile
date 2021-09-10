all: Makefile.coq
	export TIMED
	@+$(MAKE) -f Makefile.coq all

Makefile.coq: _CoqProject
	coq_makefile -f _CoqProject -o Makefile.coq
