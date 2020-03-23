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
# It recompiles that part of monae necessary to compile
# mmt_sect5.v with impredicativity (it looks like
# -type-in-type need not be applied to all files).

COQ5 = coqc -w -notation-overridden -type-in-type -R . monae

sect5:
#	$(COQ5) monae_lib.v
#	$(COQ5) monad.v
#	$(COQ5) fail_monad.v
#	$(COQ5) state_monad.v
#	$(COQ5) trace_monad.v
#	$(COQ5) monad_model.v
#	$(COQ5) monad_transformer.v
	$(COQ5) mmt_sect5.v
	$(COQ5) parametricity.v

clean5:
	rm -f monae_lib.vo monad.vo fail_monad.vo state_monad.vo trace_monad.vo monad_model.vo monad_transformer.vo mmt_sect5.vo
