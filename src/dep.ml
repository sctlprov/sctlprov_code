open Ast

type dep_graph = Leaf of string | Node of string * (dep_graph list)

(* string * (dep_graph list) *)

let rec dep_graph_of_pmodul modul moduls =
	let m = Hashtbl.find moduls modul in
	let imported = m.imported in
	match imported with
	| [] -> Leaf modul
	| _ -> Node (modul, List.map (fun mname -> dep_graph_of_pmodul mname moduls) imported)
	

