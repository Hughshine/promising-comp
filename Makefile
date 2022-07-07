COQMODULE    := CompOptCert
COQTHEORIES  := \
	src/lib/*.v \
	src/rtl/*.v \
	src/promising/lang/*.v \
	src/promising/wwrf/*.v \
	src/promising/prop/Cover.v \
	src/promising/prop/MemoryReorder.v \
	src/promising/prop/MemoryMerge.v \
	src/promising/prop/MemorySplit.v \
	src/promising/prop/FulfillStep.v \
	src/promising/prop/PromiseConsistent.v \
	src/promising/prop/ReorderPromise.v \
	src/promising/prop/ReorderCancel.v \
	src/promising/prop/MemoryProps.v \
	src/result/*.v \
	src/non-preemptive/*.v \
	src/proofs/*.v \
	src/proofs/general-prop/*.v \
	src/proofs/ps-np-equivalence/*.v \
	src/proofs/sim-compositionality/*.v \
	src/proofs/wwRF-preservation/*.v \
	src/simulation/*.v \
	src/promising/prop/ReorderReserve.v \
	src/rtl/optimizer/*.v 

.PHONY: all theories clean

all: quick

build: Makefile.coq
	$(MAKE) -f Makefile.coq all

quick: Makefile.coq
	$(MAKE) -f Makefile.coq quick

html: Makefile.coq
	$(MAKE) -f Makefile.coq html

Makefile.coq: Makefile $(COQTHEORIES)
	(echo "-R src/promising/lang $(COQMODULE)"; \
	echo "-R src/promising/wwrf $(COQMODULE)"; \
	echo "-R src/promising/prop $(COQMODULE)"; \
	echo "-R src/lib $(COQMODULE)"; \
	echo "-R src/rtl $(COQMODULE)"; \
	echo "-R src/result $(COQMODULE)"; \
	echo "-R src/non-preemptive $(COQMODULE)"; \
	echo "-R src/proofs $(COQMODULE)"; \
	echo "-R src/proofs/general-prop $(COQMODULE)"; \
	echo "-R src/proofs/ps-np-equivalence $(COQMODULE)"; \
	echo "-R src/proofs/sim-compositionality $(COQMODULE)"; \
	echo "-R src/simulation $(COQMODULE)"; \
	echo "-R src/proofs/wwRF-preservation $(COQMODULE)"; \
   \
   echo $(COQTHEORIES)) > _CoqProject
	coq_makefile -f _CoqProject -o Makefile.coq

%.vo: Makefile.coq
	$(MAKE) -f Makefile.coq "$@"

%.vio: Makefile.coq
	$(MAKE) -f Makefile.coq "$@"

clean:
	$(MAKE) -f Makefile.coq cleanall
	rm -f _CoqProject Makefile.coq Makefile.coq.conf
