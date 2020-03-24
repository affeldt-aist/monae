all: Makefile.coq
	$(MAKE) -f Makefile.coq all

clean: Makefile.coq
	$(MAKE) -f Makefile.coq cleanall
	rm -f Makefile.coq Makefile.coq.conf

Makefile.coq: _CoqProject
	coq_makefile -f _CoqProject -o Makefile.coq

_CoqProject Makefile: ;

%: Makefile.coq
	$(MAKE) -f Makefile.coq $@

.PHONY: all clean

# This last entry is only to support work-in-progress.

COQ5 = coqc -w -notation-overridden -R . monae

sect5: all
	$(COQ5) mmt_sect5.v
	$(COQ5) parametricity.v

clean5:
	rm -f monae_lib.vo monad.vo fail_monad.vo state_monad.vo trace_monad.vo monad_model.vo monad_transformer.vo mmt_sect5.vo
