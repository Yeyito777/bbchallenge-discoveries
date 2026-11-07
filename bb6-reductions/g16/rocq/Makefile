# make    all proofs and Print Assumptions
COQMF := Makefile.coq
all: $(COQMF)
	$(MAKE) -f $(COQMF)
	coqc -Q busycoq BusyCoq -Q theories G16 demo/Axioms.v
$(COQMF): _CoqProject
	coq_makefile -f _CoqProject -o $(COQMF)
clean:
	-$(MAKE) -f $(COQMF) cleanall
	rm -f $(COQMF) $(COQMF).conf demo/*.vo* demo/*.glob demo/.*.aux
.PHONY: all clean
