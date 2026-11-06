# make            the rule map, the checker and the statement (Rocq 8.20.1), about a minute on one core
# make extract    the OCaml checker (extract/check)
# make demo       one chunk of the chain checked inside the kernel with native_compute, about two minutes
COQMF := Makefile.coq
all: $(COQMF)
	$(MAKE) -f $(COQMF)
	coqc -Q busycoq BusyCoq -Q theories BB6 demo/Axioms.v
$(COQMF): _CoqProject
	coq_makefile -f _CoqProject -o $(COQMF)
extract: all
	bash extract/build.sh
demo: all
	time coqc -Q busycoq BusyCoq -Q theories BB6 -native-compiler ondemand demo/KernelDemo.v
clean:
	-$(MAKE) -f $(COQMF) cleanall
	rm -f $(COQMF) $(COQMF).conf demo/*.vo* demo/*.glob demo/.*.aux extract/check extract/checker.ml extract/checker.mli
.PHONY: all extract demo clean
