all:
	make -C utils opt
	ocamlopt -c ast.ml
	menhir --infer --explain parser.mly
	ocamllex lexer.mll
	ocamlyacc opt/oparser.mly
	ocamllex opt/olexer.mll
	$(CADP)/src/com/cadp_cc  -c bcg/bcg_interface_stubs.c -I$(CADP)/incl -L$(CADP)/bin.`$(CADP)/com/arch` -lBCG_IO -lBCG -lm
	ocamlmklib -failsafe -custom -o cbcg bcg_interface_stubs.o -I $(CADP)/incl -L$(CADP)/bin.`$(CADP)/com/arch` -lBCG_IO -lBCG -lm
	ocamlopt -a -o obcg.cmxa -cc "$(CADP)/src/com/cadp_cc" bcg/bcg_interface.ml -cclib libcbcg.a -ccopt -L$(CADP)/bin.`$(CADP)/com/arch` -ccopt -L$(CADP)/bin.`$(CADP)/com/arch` -cclib -lBCG_IO -cclib -lBCG
	ocamlfind ocamlopt -cc "$(CADP)/src/com/cadp_cc -O3" -thread -I utils -I opt -I bcg -o sctl utils.cmxa obcg.cmxa -package cudd -package yojson -linkpkg -g ast.cmx print.ml parser.mli parser.ml lexer.ml \
	  typechecker.ml expr.ml formula.ml dep.ml interp.ml BDD.ml flags.ml merge.ml prover.ml communicate.ml prover_visualization.ml \
	  opt/obdd.ml opt/oterm.ml opt/oformula.ml opt/omodul.ml opt/oprover.ml opt/oprover_bdd.ml opt/oprover_output.ml \
	  opt/ocommunicate.ml opt/oprover_visualization.ml opt/oparser.mli opt/oparser.ml opt/olexer.ml \
	  bcg/ks_bcg.ml bcg/formula_bcg.ml bcg/prover_bcg.ml \
	  main.ml

testing:
	make -C utils opt
	ocamlopt -c ast.ml
	menhir --infer --explain parser.mly
	ocamllex lexer.mll
	ocamlyacc opt/oparser.mly
	ocamllex opt/olexer.mll
	$(CADP)/src/com/cadp_cc  -c bcg/bcg_interface_stubs.c -I$(CADP)/incl -L$(CADP)/bin.`$(CADP)/com/arch` -lBCG_IO -lBCG -lm
	ocamlmklib -failsafe -custom -o cbcg bcg_interface_stubs.o -I $(CADP)/incl -L$(CADP)/bin.`$(CADP)/com/arch` -lBCG_IO -lBCG -lm
	ocamlopt -a -o obcg.cmxa -cc "$(CADP)/src/com/cadp_cc" bcg/bcg_interface.ml -cclib libcbcg.a -ccopt -L$(CADP)/bin.`$(CADP)/com/arch` -ccopt -L$(CADP)/bin.`$(CADP)/com/arch` -cclib -lBCG_IO -cclib -lBCG
	ocamlfind ocamlopt -cc "$(CADP)/src/com/cadp_cc -O3" -thread -I utils -I opt -I bcg -o testing utils.cmxa obcg.cmxa -package cudd -package yojson -package oUnit -linkpkg -g ast.cmx print.ml parser.mli parser.ml lexer.ml \
	  typechecker.ml expr.ml formula.ml dep.ml interp.ml BDD.ml flags.ml merge.ml prover.ml communicate.ml prover_visualization.ml \
	  opt/obdd.ml opt/oterm.ml opt/oformula.ml opt/omodul.ml opt/oprover.ml opt/oprover_bdd.ml opt/oprover_output.ml \
	  opt/ocommunicate.ml opt/oprover_visualization.ml opt/oparser.mli opt/oparser.ml opt/olexer.ml \
	  bcg/ks_bcg.ml bcg/formula_bcg.ml bcg/prover_bcg.ml \
	  test.ml

all-in-one: new-lib opt-lib bcg-lib
	ocamlfind ocamlopt.opt -o sctl -thread -I utils -I bcg -linkpkg -package cudd -package yojson -plugin new.cmxs -plugin optlib.cmxs obcg.cmxa main.ml

new-lib:
	make -C utils opt
	ocamlopt -c ast.ml
	menhir --infer parser.mly
	ocamllex lexer.mll
	ocamlfind ocamlopt -o new.cmxa -ocamlopt -thread -I utils -thread -package cudd -package yojson \
	 utils/options.cmx utils/pairs.cmx utils/refpairs.cmx utils/lists.cmx ast.cmx print.ml parser.mli parser.ml lexer.ml \
	 typechecker.ml expr.ml formula.ml dep.ml interp.ml BDD.ml flags.ml merge.ml prover.ml communicate.ml prover_visualization.ml
	
opt-lib:
	ocamlyacc oparser.mly
	ocamllex olexer.mll
	ocamlfind ocamlopt -o optlib.cmxs -thread -package cudd -package yojson -shared \
	 obdd.ml oterm.ml oformula.ml omodul.ml oprover.ml oprover_bdd.ml oprover_output.ml \
	 ocommunicate.ml oprover_visualization.ml oparser.mli oparser.ml  olexer.ml

bcg-lib:
	$(CADP)/src/com/cadp_cc -O3 -c bcg/bcg_interface_stubs.c -I$(CADP)/incl -L$(CADP)/bin.`$(CADP)/com/arch` -lBCG_IO -lBCG -lm
	ocamlmklib -failsafe -custom -o cbcg bcg_interface_stubs.o -I $(CADP)/incl -L$(CADP)/bin.`$(CADP)/com/arch` -lBCG_IO -lBCG -lm
	ocamlopt -a -o obcg.cmxa -cc "$(CADP)/src/com/cadp_cc -O3" -I bcg bcg/bcg_interface.ml bcg/ks_bcg.ml bcg/formula_bcg.ml bcg/prover_bcg.ml \
	 -cclib libcbcg.a -ccopt -L$(CADP)/bin.`$(CADP)/com/arch` -ccopt -L$(CADP)/bin.`$(CADP)/com/arch` -cclib -lBCG_IO -cclib -lBCG
	
lib:
	make -C utils all

lib-opt:
	make -C utils opt

parser: 
	menhir --infer --explain parser.mly

clean:
	make -C utils clean
	make -C opt clean
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