SUB = impredicative_set

all: Makefile.coq
	$(MAKE) -f Makefile.coq all
	$(MAKE) -C $(SUB) all

clean: Makefile.coq
	$(MAKE) -f Makefile.coq cleanall
	$(MAKE) -C $(SUB) clean

Makefile.coq: _CoqProject
	coq_makefile -f _CoqProject -o Makefile.coq

_CoqProject Makefile: ;

%: Makefile.coq
	$(MAKE) -f Makefile.coq $@

.PHONY: all clean

install_full: all
	$(MAKE) install
	$(MAKE) -C impredicative_set install

# This last entry is only to support work-in-progress.

COQ5 = coqc -w -notation-overridden -R . monae

sect5: all
	$(COQ5) fmt_lifting.v
	$(COQ5) parametricity_codensity.v

clean5:
	rm -f *.vo *.glob *.vok *.vos
