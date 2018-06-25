all:
	make -C utils all
	ocamlopt -c ast.ml
	menhir --infer --explain parser.mly
	ocamllex lexer.mll
	ocamlyacc fixed_state/fparser.mly
	ocamllex fixed_state/flexer.mll
	$(CADP)/src/com/cadp_cc  -c bcg/bcg_interface_stubs.c -I$(CADP)/incl -L$(CADP)/bin.`$(CADP)/com/arch` -lBCG_IO -lBCG -lm
	ocamlmklib -failsafe -custom -o cbcg bcg_interface_stubs.o -I $(CADP)/incl -L$(CADP)/bin.`$(CADP)/com/arch` -lBCG_IO -lBCG -lm
	ocamlopt -a -o obcg.cmxa -cc "$(CADP)/src/com/cadp_cc" bcg/bcg_interface.ml -cclib libcbcg.a -ccopt -L$(CADP)/bin.`$(CADP)/com/arch` -ccopt -L$(CADP)/bin.`$(CADP)/com/arch` -cclib -lBCG_IO -cclib -lBCG
	ocamlfind ocamlopt -cc "$(CADP)/src/com/cadp_cc -O3" -thread -I utils -I fixed_state -I bcg -o sctl utils.cmxa obcg.cmxa -package cudd -package yojson -linkpkg -g ast.cmx print.ml parser.mli parser.ml lexer.ml \
	  typechecker.ml expr.ml formula.ml dep.ml interp.ml BDD.ml flags.ml merge.ml prover.ml communicate.ml prover_visualization.ml \
	  fixed_state/fbdd.ml fixed_state/fterm.ml fixed_state/fformula.ml fixed_state/fmodul.ml fixed_state/fprover.ml fixed_state/fprover_bdd.ml fixed_state/fprover_output.ml \
	  fixed_state/fcommunicate.ml fixed_state/fprover_visualization.ml fixed_state/fparser.mli fixed_state/fparser.ml fixed_state/flexer.ml \
	  bcg/ks_bcg.ml bcg/formula_bcg.ml bcg/prover_bcg.ml \
	  main.ml

no-bcg:
	make -C utils all
	ocamlopt -c ast.ml
	menhir --infer --explain parser.mly
	ocamllex lexer.mll
	ocamlyacc fixed_state/fparser.mly
	ocamllex fixed_state/flexer.mll
	ocamlfind ocamlopt -thread -I utils -I fixed_state -o sctl utils.cmxa -package cudd -package yojson -linkpkg -g ast.cmx print.ml parser.mli parser.ml lexer.ml \
	  typechecker.ml expr.ml formula.ml dep.ml interp.ml BDD.ml flags.ml merge.ml prover.ml communicate.ml prover_visualization.ml \
	  fixed_state/fbdd.ml fixed_state/fterm.ml fixed_state/fformula.ml fixed_state/fmodul.ml fixed_state/fprover.ml fixed_state/fprover_bdd.ml fixed_state/fprover_output.ml \
	  fixed_state/fcommunicate.ml fixed_state/fprover_visualization.ml fixed_state/fparser.mli fixed_state/fparser.ml fixed_state/flexer.ml \
	  no_bcg.ml

clean:
	make -C utils clean
	make -C fixed_state clean
	make -C bcg clean
	rm -f *.cm[ioxa]
	rm -f *.o
	rm -f *.a
	rm -f *.cmx[as]
	rm -f sctl
	rm -f sctl.exe
	rm -f ./examples/*.typed
	rm -f ./examples/*.origin
	rm -f .origin
	rm -f .typed
	rm -f *.origin
	rm -f *.typed
	rm -f *.conflicts