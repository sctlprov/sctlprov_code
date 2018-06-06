all:
	$(CADP)/src/com/cadp_cc -O3 -c bcg_interface_stubs.c -I$(CADP)/incl -L$(CADP)/bin.`$(CADP)/com/arch` -lBCG_IO -lBCG -lm
	ocamlmklib -failsafe -custom -o cbcg bcg_interface_stubs.o -I $(CADP)/incl -L$(CADP)/bin.`$(CADP)/com/arch` -lBCG_IO -lBCG -lm
	ocamlopt -a -o obcg.cmxa -cc "$(CADP)/src/com/cadp_cc -O3" bcg_interface.ml -cclib libcbcg.a -ccopt -L$(CADP)/bin.`$(CADP)/com/arch` -ccopt -L$(CADP)/bin.`$(CADP)/com/arch` -cclib -lBCG_IO -cclib -lBCG
	ocamlfind ocamlopt -cc "$(CADP)/src/com/cadp_cc -O3" -o sctl -linkpkg -g obcg.cmxa ks_bcg.ml formula_bcg.ml prover_bcg.ml bcg.ml


clean:
	rm -f *.so
	rm -f *.a
	rm -f *.cm[ioxa]
	rm -f *.cmxa
	rm -f *.output
	rm -f *.o
	rm -f obcg
	rm -f test
	rm -f sctlbcg
	rm -f evaluator
