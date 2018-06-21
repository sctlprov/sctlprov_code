
all:
	ocamlyacc fparser.mly
	ocamllex flexer.mll
	ocamlfind ocamlopt -o sctl -thread -package cudd -package yojson -linkpkg -g \
	 fbdd.ml fterm.ml fformula.ml fmodul.ml fprover.ml fprover_bdd.ml fprover_output.ml \
	 fcommunicate.ml fprover_visualization.ml fparser.mli fparser.ml  flexer.ml fmain.ml

# opt-lib:
# 	ocamlyacc oparser.mly
# 	ocamllex olexer.mll
# 	ocamlfind ocamlopt -o optlib.cmxs -thread -package cudd -package yojson -shared \
# 	 obdd.ml oterm.ml oformula.ml omodul.ml oprover.ml oprover_bdd.ml oprover_output.ml \
# 	 ocommunicate.ml oprover_visualization.ml oparser.mli oparser.ml  olexer.ml
# 	mv optlib.cmxs ../optlib.cmxs

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


