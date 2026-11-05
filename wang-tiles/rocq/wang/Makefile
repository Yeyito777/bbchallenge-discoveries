# Inspired from https://github.com/palmskog/coq-program-verification-template (as Coq-BB5)
# make        everything (needs the n = 7 data files: tools/make_n7.sh CERTDIR)
# make small  n = 5, 6 and 8 only (WangTiles_Theorem.v), no n = 7 data needed

all: Makefile.coq
	@+$(MAKE) -f Makefile.coq all

small: Makefile.small.coq
	@+$(MAKE) -f Makefile.small.coq all

clean: Makefile.coq Makefile.small.coq
	@+$(MAKE) -f Makefile.coq cleanall
	@+$(MAKE) -f Makefile.small.coq cleanall
	@rm -f Makefile.coq Makefile.coq.conf Makefile.small.coq Makefile.small.coq.conf

Makefile.coq: _CoqProject
	$(COQBIN)coq_makefile -f _CoqProject -o Makefile.coq

Makefile.small.coq: _CoqProject.small
	$(COQBIN)coq_makefile -f _CoqProject.small -o Makefile.small.coq

force _CoqProject _CoqProject.small Makefile: ;

%: Makefile.coq force
	@+$(MAKE) -f Makefile.coq $@

.PHONY: all small clean force
