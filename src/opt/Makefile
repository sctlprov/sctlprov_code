# all: 
# 	ocamllex olexer.mll       
# 	ocamlyacc oparser.mly 
# 	ocamlfind ocamlopt  -a -thread -package cudd -package yojson -linkpkg -g  obdd.ml oterm.ml oformula.ml omodul.ml oprover.ml oprover_bdd.ml oprover_output.ml ocommunicate.ml oprover_visualization.ml oparser.mli oparser.ml olexer.ml -o opt.cmxa
	# main.ml


# linux: bdd.ml term.ml formula.ml modul.ml prover.ml prover_bdd.ml prover_output.ml lexer.mll parser.mly main.ml
# 	ocamllex lexer.mll       
# 	ocamlyacc parser.mly 
# 	ocamlfind ocamlopt -thread -o sctl -package cudd -package yojson -linkpkg -g bdd.ml term.ml formula.ml modul.ml prover.ml prover_bdd.ml prover_output.ml communicate.ml prover_visualization.ml parser.mli parser.ml lexer.ml main.ml

# win: bdd.ml term.ml formula.ml modul.ml prover.ml prover_bdd.ml prover_output.ml lexer.mll parser.mly main.ml
# 	ocamllex lexer.mll       
# 	ocamlyacc parser.mly 
# 	ocamlfind ocamlopt -o sctl.exe -package cudd yojson -linkpkg -g bdd.ml term.ml formula.ml modul.ml prover.ml prover_bdd.ml prover_output.ml communicate.ml prover_visualization.ml parser.mli parser.ml lexer.ml main.ml

opt-lib:
	ocamlyacc oparser.mly
	ocamllex olexer.mll
	ocamlfind ocamlopt -o optlib.cmxs -thread -package cudd -package yojson -shared \
	 obdd.ml oterm.ml oformula.ml omodul.ml oprover.ml oprover_bdd.ml oprover_output.ml \
	 ocommunicate.ml oprover_visualization.ml oparser.mli oparser.ml  olexer.ml
	mv optlib.cmxs ../optlib.cmxs

clean:
	rm -f *.cm[ioax]
	rm -f *.o
	rm -f *.a
	rm -f olexer.ml oparser.mli oparser.ml
	rm -f *.annot
	rm -f *.bak
	rm -f sctl
	rm -f sctl.exe
	rm -f *.cmx[as]

