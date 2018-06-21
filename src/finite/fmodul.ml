open Fterm
open Fformula

module Key = 
	struct
		type t = int array
		let compare = Pervasives.compare
	end;;

module State_set = Set.Make(Key)

(** Stage 0 -- 5 of the interpretation of modules in the input file. **)
(** Stage 0: honestly generate all modules according to the semantics. **)
type modul0 = 
{
	name : string;
	parameter_list : (string * expr_type) list;
	var_list : (string * expr_type) list;
	symbol_tbl : (string, expr) Hashtbl.t;
	init_assign : expr_module_instance list;
	transitions : (expr * ((expr * expr) list)) list;
	fairness: formula list;
	atomic_tbl : (string, expr) Hashtbl.t;
	spec_list : (string * formula) list;
}

let output0 out (modul:modul0) is_model = 
	(if is_model then output_string out ("Model name: " ^ modul.name ^ "\n{\n") else output_string out ("Module name: " ^ modul.name ^ "\n{\n"));
	output_string out ("\tFormal parameters:\n");
	List.iter (fun a -> output_string out ("\t\t"^(fst a)^" : "^ (str_expr_type (snd a))^";\n")) modul.parameter_list;
	output_string out ("\n\tState variable definitions:\n");
	List.iter (fun a -> output_string out ("\t\t"^(fst a)^" : "^ (str_expr_type (snd a))^";\n")) modul.var_list;
	output_string out ("\n\tUser defined symbols:\n");
	Hashtbl.iter (fun a b -> output_string out ("\t\t"^a^" := "^ (str_expr b)^";\n")) modul.symbol_tbl;
	output_string out ("\n\tInitial state definition:\n");
	for i=0 to (List.length modul.init_assign - 1) do
			output_string out ("\t\t"^(fst (List.nth modul.var_list i)) ^ " := " ^ (str_expr_module_instance (List.nth modul.init_assign i))^";\n")
	done;
	output_string out ("\n\tTransition relation definition:\n");
	List.iter (fun a -> output_string out ("\t\t"^(str_expr (fst a))^" : "^"{"^(str_state_reste (snd a))^"};\n")) modul.transitions;
	if is_model then
	begin
		output_string out ("\n\tFairness definitions:\n");
		List.iter (fun a -> output_string out ("\t\t"^(fml_to_string a)^";\n")) modul.fairness;
		output_string out ("\n\tAtomic formula definitions:\n");
		Hashtbl.iter (fun a b -> output_string out ("\t\t"^a^" := "^(str_expr b)^";\n")) modul.atomic_tbl;
		output_string out ("\n\tSpecifications:\n");
		List.iter (fun a -> output_string out ("\t\t"^(fst a)^" := "^(fml_to_string (snd a))^";\n")) modul.spec_list
	end;
	output_string out "}\n"



(** Stage 1: expand all the definition of user defined symbols. **)
type modul1 = 
{
	name : string;
	parameter_list : (string * expr_type) list;
	var_list : (string * expr_type) list;
	init_assign : expr_module_instance list;
	transitions : (expr * ((expr * expr) list)) list;
	fairness: formula list;
	atomic_tbl : (string, expr) Hashtbl.t;
	spec_list : (string * formula) list;
}

let modul021 (m0:modul0) = 
{
	name = m0.name;
	parameter_list = m0.parameter_list;
	var_list = m0.var_list;
	init_assign = List.map (fun a -> 
			match a with
			| Expr e -> Expr (expand_symbol_expr e (m0.symbol_tbl))
			| Module_instance (s, el) -> Module_instance (s, expand_symbol_expr_list el m0.symbol_tbl)
			) m0.init_assign;
	transitions = List.map (fun a -> (expand_symbol_expr (fst a) m0.symbol_tbl, List.map (fun b -> (expand_symbol_expr (fst b) m0.symbol_tbl, expand_symbol_expr (snd b) m0.symbol_tbl)) (snd a))) m0.transitions;
	fairness = m0.fairness;
	atomic_tbl = (Hashtbl.iter (fun a b -> Hashtbl.replace m0.atomic_tbl a (expand_symbol_expr b m0.symbol_tbl)) m0.atomic_tbl; m0.atomic_tbl);
	spec_list = m0.spec_list;
}

let output1 out (modul:modul1) is_model = 
	(if is_model then output_string out ("Model name: " ^ modul.name ^ "\n{\n") else output_string out ("Module name: " ^ modul.name ^ "\n{\n"));
	output_string out ("\tFormal parameters:\n");
	List.iter (fun a -> output_string out ("\t\t"^(fst a)^" : "^ (str_expr_type (snd a))^";\n")) modul.parameter_list;
	output_string out ("\n\tState variable definitions:\n");
	List.iter (fun a -> output_string out ("\t\t"^(fst a)^" : "^ (str_expr_type (snd a))^";\n")) modul.var_list;
	output_string out ("\n\tInitial state definition:\n");
	for i=0 to (List.length modul.init_assign - 1) do
			output_string out ("\t\t"^(fst (List.nth modul.var_list i)) ^ " := " ^ (str_expr_module_instance (List.nth modul.init_assign i))^";\n")
	done;
	output_string out ("\n\tTransition relation definition:\n");
	List.iter (fun a -> output_string out ("\t\t"^(str_expr (fst a))^" : "^"{"^(str_state_reste (snd a))^"};\n")) modul.transitions;
	if is_model then
	begin	
		output_string out ("\n\tFairness definitions:\n");
		List.iter (fun a -> output_string out ("\t\t"^(fml_to_string a)^";\n")) modul.fairness;
		output_string out ("\n\tAtomic formula definitions:\n");
		Hashtbl.iter (fun a b -> output_string out ("\t\t"^a^" := "^(str_expr b)^";\n")) modul.atomic_tbl;
		output_string out ("\n\tSpecifications:\n");
		List.iter (fun a -> output_string out ("\t\t"^(fst a)^" := "^(fml_to_string (snd a))^";\n")) modul.spec_list
	end;
	output_string out "}\n"


(** Stage 2: apply the actural parameters to modules. **)
type modul2 = 
{
	name : string;
	var_list : (string * expr_type) list;
	init_assign : expr_module_instance list;
	transitions : (expr * ((expr * expr) list)) list;
	fairness: formula list;
	atomic_tbl : (string, expr) Hashtbl.t;
	spec_list : (string * formula) list;
	modul_tbl : (string, modul2) Hashtbl.t;
}

let rec modul122 (m1:modul1) actural_paras modul_tbl = 
	let actural_moduls = Hashtbl.create 10 in
	let actural_paras_length = List.length actural_paras in
	let m2:modul2 = 
	{
		name = m1.name;
		var_list = 
			(let tmp_var_list = ref (m1.var_list) in
			for i = 0 to actural_paras_length - 1 do
				tmp_var_list := List.map (fun a -> (fst a, replace_parameter_expr_type (snd a) (fst (List.nth m1.parameter_list i)) (List.nth actural_paras i))) !tmp_var_list
			done; !tmp_var_list);
		init_assign = 
			(let tmp_init_assign = ref (m1.init_assign) in
			for i = 0 to actural_paras_length - 1 do
				tmp_init_assign := List.map (fun a -> replace_parameter_expr_module_instance a (fst (List.nth m1.parameter_list i)) (List.nth actural_paras i)) !tmp_init_assign
			done; !tmp_init_assign);
		transitions =
			(let tmp_transitions = ref (m1.transitions) in
			for i = 0 to actural_paras_length - 1 do
				let pvi = fst (List.nth m1.parameter_list i) and ei = (List.nth actural_paras i) in
				tmp_transitions := List.map (fun a -> (replace_parameter_expr (fst a) pvi ei, List.map (fun b -> (replace_parameter_expr (fst b) pvi ei, replace_parameter_expr (snd b) pvi ei)) (snd a))) !tmp_transitions
			done; !tmp_transitions);
		fairness = m1.fairness;
		atomic_tbl = 
			(
			for i = 0 to actural_paras_length - 1 do
				Hashtbl.iter (fun a b -> Hashtbl.replace m1.atomic_tbl a (replace_parameter_expr b (fst (List.nth m1.parameter_list i)) (List.nth actural_paras i))) m1.atomic_tbl
			done; m1.atomic_tbl);
		spec_list = m1.spec_list;
		modul_tbl = actural_moduls;
	} in
	for i = 0 to (List.length m2.var_list) - 1 do
		match (List.nth m2.init_assign i) with
		| Module_instance (s, el) -> let pm1 = Hashtbl.find modul_tbl s and el' = eval_expr_list el in
			let pm2 = modul122 pm1 el' modul_tbl in
			let pvi2 = fst (List.nth m2.var_list i) in
			Hashtbl.add actural_moduls pvi2 pm2
		| _ -> ()
	done; m2

let rec output2 out (modul:modul2) prefix_str is_model = 
	(if is_model then output_string out (prefix_str^"Model name: " ^ modul.name ^ "\n"^prefix_str^"{\n") else output_string out (prefix_str^"Module name: " ^ modul.name ^ "\n"^prefix_str^"{\n"));
	(*output_string out (prefix_str^"\tFormal parameters:\n");
	List.iter (fun a -> output_string out (prefix_str^"\t\t"^(fst a)^" : "^ (str_expr_type (snd a))^";\n")) modul.parameter_list;*)
	output_string out (prefix_str^"\n");
	output_string out (prefix_str^"\tState variable definitions:\n");
	List.iter (fun a -> output_string out (prefix_str^"\t\t"^(fst a)^" : "^ (str_expr_type (snd a))^";\n")) modul.var_list;
	output_string out (prefix_str^"\n");
	output_string out (prefix_str^"\tInitial state definition:\n");
	for i=0 to (List.length modul.init_assign - 1) do
			output_string out (prefix_str^"\t\t"^(fst (List.nth modul.var_list i)) ^ " := " ^ (str_expr_module_instance (List.nth modul.init_assign i))^";\n")
	done;
	output_string out (prefix_str^"\n");
	output_string out (prefix_str^"\tTransition relation definition:\n");
	List.iter (fun a -> output_string out (prefix_str^"\t\t"^(str_expr (fst a))^" : "^"{"^(str_state_reste (snd a))^"};\n")) modul.transitions;
	if is_model then
	begin	
		output_string out (prefix_str^"\n");
		output_string out (prefix_str^"\tFairness definitions:\n");
		List.iter (fun a -> output_string out (prefix_str^"\t\t"^(fml_to_string a)^";\n")) modul.fairness;
		output_string out (prefix_str^"\n");
		output_string out (prefix_str^"\tAtomic formula definitions:\n");
		Hashtbl.iter (fun a b -> output_string out (prefix_str^"\t\t"^a^" := "^(str_expr b)^";\n")) modul.atomic_tbl;
		output_string out (prefix_str^"\n");
		output_string out (prefix_str^"\tSpecifications:\n");
		List.iter (fun a -> output_string out (prefix_str^"\t\t"^(fst a)^" := "^(fml_to_string (snd a))^";\n")) modul.spec_list
	end;
	output_string out (prefix_str^"\n");
	output_string out (prefix_str^"\tSub modules:\n");
	Hashtbl.iter (fun a b -> output_string out (prefix_str^"\t\t"^a^" := \n"); output2 out b (prefix_str^"\t\t") false) modul.modul_tbl;
	output_string out (prefix_str^"}\n")


(** Stage 3: expand the array definition. **)
type modul3 = 
{
	name : string;
	var_list : (string * expr_type) list;
	init_assign : expr_module_instance list;
	transitions : (expr * ((expr * expr) list)) list;
	fairness: formula list;
	atomic_tbl : (string, expr) Hashtbl.t;
	spec_list : (string * formula) list;
	modul_tbl : (string, modul3) Hashtbl.t;
}

let rec modul223 (m2:modul2) = 
{
	name = m2.name;
	var_list = 
		begin
			let tmp_var_list = ref [] in
			List.iter (fun a ->
				match a with
				| (s, Array_type (et, e)) -> (
					let e1 = eval_expr e in
					match e1 with
					| Const c -> for i = 0 to c - 1 do
									tmp_var_list := !tmp_var_list @ [(s^"_"^(string_of_int i), et)]
								 done
					| _ -> print_endline ("Size of array is not integer: "^(str_expr e1)); exit 1)
				| _ -> tmp_var_list := !tmp_var_list @ [a]
				) m2.var_list;
			!tmp_var_list
		end;
	init_assign = 
		begin
			let tmp_init_assign = ref [] in
			List.iter (fun a -> 
				match a with
				| Expr (Aray el) -> List.iter (fun b -> tmp_init_assign := !tmp_init_assign @ [Expr (eval_expr b)]) el
				| Expr e -> tmp_init_assign := !tmp_init_assign @ [Expr (eval_expr e)]
				| Module_instance (s, el) -> tmp_init_assign := !tmp_init_assign @ [Module_instance (s, eval_expr_list el)]
				) m2.init_assign;
			!tmp_init_assign
		end;
	transitions = m2.transitions;
	fairness = m2.fairness;
	atomic_tbl = m2.atomic_tbl;
	spec_list = m2.spec_list;
	modul_tbl = 
		begin
			let tmp_modul_tbl = Hashtbl.create (Hashtbl.length m2.modul_tbl) in
			Hashtbl.iter (fun a b -> Hashtbl.add tmp_modul_tbl a (modul223 b)) m2.modul_tbl;
			tmp_modul_tbl		
		end;
}

let rec output3 out (modul:modul3) prefix_str is_model = 
	(if is_model then output_string out (prefix_str^"Model name: " ^ modul.name ^ "\n"^prefix_str^"{\n") else output_string out (prefix_str^"Module name: " ^ modul.name ^ "\n"^prefix_str^"{\n"));
	(*output_string out (prefix_str^"\tFormal parameters:\n");
	List.iter (fun a -> output_string out (prefix_str^"\t\t"^(fst a)^" : "^ (str_expr_type (snd a))^";\n")) modul.parameter_list;*)
	output_string out (prefix_str^"\n");
	output_string out (prefix_str^"\tState variable definitions:\n");
	List.iter (fun a -> output_string out (prefix_str^"\t\t"^(fst a)^" : "^ (str_expr_type (snd a))^";\n")) modul.var_list;
	output_string out (prefix_str^"\n");
	output_string out (prefix_str^"\tInitial state definition:\n");
(*	print_endline ("Var list size: "^(string_of_int (List.length modul.var_list))^", Init assign size: "^ (string_of_int (List.length modul.init_assign)));*)
	assert (List.length modul.init_assign = List.length modul.var_list);
	for i=0 to (List.length modul.init_assign - 1) do
		output_string out (prefix_str^"\t\t"^(fst (List.nth modul.var_list i)) ^ " := " ^ (str_expr_module_instance (List.nth modul.init_assign i))^";\n")
	done;
	output_string out (prefix_str^"\n");
	output_string out (prefix_str^"\tTransition relation definition:\n");
	List.iter (fun a -> output_string out (prefix_str^"\t\t"^(str_expr (fst a))^" : "^"{"^(str_state_reste (snd a))^"};\n")) modul.transitions;
	if is_model then
	begin	
		output_string out (prefix_str^"\n");
		output_string out (prefix_str^"\tFairness definitions:\n");
		List.iter (fun a -> output_string out (prefix_str^"\t\t"^(fml_to_string a)^";\n")) modul.fairness;
		output_string out (prefix_str^"\n");
		output_string out (prefix_str^"\tAtomic formula definitions:\n");
		Hashtbl.iter (fun a b -> output_string out (prefix_str^"\t\t"^a^" := "^(str_expr b)^";\n")) modul.atomic_tbl;
		output_string out (prefix_str^"\n");
		output_string out (prefix_str^"\tSpecifications:\n");
		List.iter (fun a -> output_string out (prefix_str^"\t\t"^(fst a)^" := "^(fml_to_string (snd a))^";\n")) modul.spec_list
	end;
	output_string out (prefix_str^"\n");
	output_string out (prefix_str^"\tSub modules:\n");
	Hashtbl.iter (fun a b -> output_string out (prefix_str^"\t\t"^a^" := \n"); output3 out b (prefix_str^"\t\t") false) modul.modul_tbl;
	output_string out (prefix_str^"}\n")

	
(** Stage 4: convert separation definitions of modules to one single definition. **)
type modul4 = 
{
	name : string;
	var_list : (string * expr_type) list;
	var_index_tbl : (string, int) Hashtbl.t;
	init_assign : expr list;
	transitions : (expr * ((expr * expr) list)) list;
	fairness : formula list;
	atomic_tbl : (string, expr) Hashtbl.t;
	spec_list : (string * formula) list;
}

let rec modul324 (m3:modul3) = 
	let tmp_var_list = ref [] 
	and tmp_var_index_tbl = Hashtbl.create (List.length m3.var_list)
	and tmp_init_assign = ref []
	and tmp_transitions = ref m3.transitions
(*	and tmp_atomic_tbl = Hashtbl.create (Hashtbl.length m3.atomic_tbl) *)in
	let add_prefix_transitions trans prefix = 
		List.map (fun a -> (add_prefix_expr (fst a) prefix, List.map (fun b -> (add_prefix_expr (fst b) prefix, add_prefix_expr (snd b) prefix)) (snd a))) trans in
	let product_transitions trans1 trans2 = 
		let tmptmp_transitions = ref [] in
		List.iter (fun a -> List.iter (fun b -> tmptmp_transitions := !tmptmp_transitions @ [(Ando (fst a, fst b), (snd a) @ (snd b))]) trans2) trans1; !tmptmp_transitions in
	let rec expand_modul_def () = 
		for i = 0 to (List.length m3.var_list - 1) do
			let (s, et) = List.nth m3.var_list i in
			match et with
			| Module_type m -> (try 
				let internal_modul = modul324 (Hashtbl.find m3.modul_tbl s) in
					tmp_var_list := !tmp_var_list @ (List.map (fun a -> (s^"."^(fst a), snd a)) internal_modul.var_list);
					tmp_init_assign := !tmp_init_assign @ (List.map (fun a -> add_prefix_expr a (s^".")) internal_modul.init_assign);
					tmp_transitions := product_transitions !tmp_transitions (add_prefix_transitions internal_modul.transitions (s^"."))
				with Not_found -> print_endline ("Module "^m^" in the definition of state variable "^s^" is not found."); exit 1)
			| _ -> tmp_var_list := !tmp_var_list @ [(s, et)]; tmp_init_assign := !tmp_init_assign @ 
				[
				match (List.nth m3.init_assign i) with
				| Expr e1 -> e1
				| _ -> print_endline "module instance is not expression"; exit 1
				]
		done in
	expand_modul_def ();
	for i = 0 to (List.length !tmp_var_list - 1) do
		Hashtbl.add tmp_var_index_tbl (fst (List.nth !tmp_var_list i)) i
	done;
	{
		name = m3.name;
		var_list = !tmp_var_list;
		var_index_tbl = tmp_var_index_tbl;
		init_assign = !tmp_init_assign;
		transitions = !tmp_transitions;
		fairness = m3.fairness;
		atomic_tbl = m3.atomic_tbl;
		spec_list = m3.spec_list;
	}

let rec output4 out (modul:modul4) prefix_str is_model = 
	(if is_model then output_string out (prefix_str^"Model name: " ^ modul.name ^ "\n"^prefix_str^"{\n") else output_string out (prefix_str^"Module name: " ^ modul.name ^ "\n"^prefix_str^"{\n"));
	(*output_string out (prefix_str^"\tFormal parameters:\n");
	List.iter (fun a -> output_string out (prefix_str^"\t\t"^(fst a)^" : "^ (str_expr_type (snd a))^";\n")) modul.parameter_list;*)
	output_string out (prefix_str^"\n");
	output_string out (prefix_str^"\tState variable definitions:\n");
	List.iter (fun a -> output_string out (prefix_str^"\t\t"^(fst a)^" : "^ (str_expr_type (snd a))^";\n")) modul.var_list;
	output_string out (prefix_str^"\n");
	output_string out (prefix_str^"\tState variable indics:\n");
	Hashtbl.iter (fun a b -> output_string out (prefix_str ^ "\t\t" ^a ^" : " ^ (string_of_int b) ^ ";\n")) modul.var_index_tbl;
	output_string out (prefix_str^"\n");
	output_string out (prefix_str^"\tInitial state definition:\n");
(*	print_endline ("Var list size: "^(string_of_int (List.length modul.var_list))^", Init assign size: "^ (string_of_int (List.length modul.init_assign)));
	assert (List.length modul.init_assign = List.length modul.var_list);*)
	for i=0 to (List.length modul.init_assign - 1) do
		output_string out (prefix_str^"\t\t"^(fst (List.nth modul.var_list i)) ^ " := " ^ (str_expr (List.nth modul.init_assign i))^";\n")
	done;

	output_string out (prefix_str^"\n");
	output_string out (prefix_str^"\tTransition relation definition:\n");
	List.iter (fun a -> output_string out (prefix_str^"\t\t"^(str_expr (fst a))^" : "^"{"^(str_state_reste (snd a))^"};\n")) modul.transitions;
	if is_model then
	begin	
		output_string out (prefix_str^"\n");
		output_string out (prefix_str^"\tFairness definitions:\n");
		List.iter (fun a -> output_string out (prefix_str^"\t\t"^(fml_to_string a)^";\n")) modul.fairness;
		output_string out (prefix_str^"\n");
		output_string out (prefix_str^"\tAtomic formula definitions:\n");
		Hashtbl.iter (fun a b -> output_string out (prefix_str^"\t\t"^a^" := "^(str_expr b)^";\n")) modul.atomic_tbl;
		output_string out (prefix_str^"\n");
		output_string out (prefix_str^"\tSpecifications:\n");
		List.iter (fun a -> output_string out (prefix_str^"\t\t"^(fst a)^" := "^(fml_to_string (snd a))^";\n")) modul.spec_list
	end;
(*	output_string out (prefix_str^"\n");
	output_string out (prefix_str^"\tSub modules:\n");
	Hashtbl.iter (fun a b -> output_string out (prefix_str^"\t\t"^a^" := \n"); output3 out b (prefix_str^"\t\t") false) modul.modul_tbl;*)
	output_string out (prefix_str^"}\n")

(** Stage 5: conver variables of string format to ones with integer format. **)
type modul5 = 
{
	name : string;
	var_list : (string * expr_type) list;
	var_index_tbl : (string, int) Hashtbl.t;
	init_assign : int array;
	transitions : (expr * ((expr * expr) list)) list;
	fairness : formula list;
	atomic_tbl : (string, expr) Hashtbl.t;
	spec_list : (string * formula) list;
}

let modul425 (m4:modul4) = 
{
	name = m4.name;
	var_list = m4.var_list;
	var_index_tbl = m4.var_index_tbl;
	init_assign = 
		begin
			let tmp_ary_length = List.length m4.var_list in
			let tmp_ary = Array.make tmp_ary_length 0 in
			for i = 0 to tmp_ary_length - 1 do
				match (eval_expr (List.nth m4.init_assign i)) with
				| Const c -> tmp_ary.(i) <- c
				| e -> print_endline ("Invalid initial assignment: "^(str_expr e)); exit 1
			done;
			tmp_ary
		end;
	transitions = List.map (fun a -> (var_str_to_int_expr (eval_expr (fst a)) m4.var_index_tbl, List.map (fun b -> (var_str_to_int_expr (eval_expr (fst b)) m4.var_index_tbl, var_str_to_int_expr (eval_expr (snd b)) m4.var_index_tbl)) (snd a))) m4.transitions;
	fairness = m4.fairness;
	atomic_tbl = (Hashtbl.iter (fun a b -> Hashtbl.replace m4.atomic_tbl a (var_str_to_int_expr (eval_expr b) m4.var_index_tbl)) m4.atomic_tbl; m4.atomic_tbl);
	spec_list = m4.spec_list;
}

let rec output5 out (modul:modul5) prefix_str is_model = 
	(if is_model then output_string out (prefix_str^"Model name: " ^ modul.name ^ "\n"^prefix_str^"{\n") else output_string out (prefix_str^"Module name: " ^ modul.name ^ "\n"^prefix_str^"{\n"));
	(*output_string out (prefix_str^"\tFormal parameters:\n");
	List.iter (fun a -> output_string out (prefix_str^"\t\t"^(fst a)^" : "^ (str_expr_type (snd a))^";\n")) modul.parameter_list;*)
	output_string out (prefix_str^"\n");
	output_string out (prefix_str^"\tState variable definitions:\n");
	List.iter (fun a -> output_string out (prefix_str^"\t\t"^(fst a)^" : "^ (str_expr_type (snd a))^";\n")) modul.var_list;
	output_string out (prefix_str^"\n");
	output_string out (prefix_str^"\tState variable indics:\n");
	Hashtbl.iter (fun a b -> output_string out (prefix_str ^ "\t\t" ^a ^" : " ^ (string_of_int b) ^ ";\n")) modul.var_index_tbl;
	output_string out (prefix_str^"\n");
	output_string out (prefix_str^"\tInitial state definition:\n");
(*	print_endline ("Var list size: "^(string_of_int (List.length modul.var_list))^", Init assign size: "^ (string_of_int (List.length modul.init_assign)));
	assert (List.length modul.init_assign = List.length modul.var_list);*)
	for i=0 to (List.length modul.var_list - 1) do
		output_string out (prefix_str^"\t\t"^(fst (List.nth modul.var_list i)) ^ " := " ^ (string_of_int (modul.init_assign.(i)))^";\n")
	done;

	output_string out (prefix_str^"\n");
	output_string out (prefix_str^"\tTransition relation definition:\n");
	List.iter (fun a -> output_string out (prefix_str^"\t\t"^(str_expr (fst a))^" : "^"{"^(str_state_reste (snd a))^"};\n")) modul.transitions;
	if is_model then
	begin	
		output_string out (prefix_str^"\n");
		output_string out (prefix_str^"\tFairness definitions:\n");
		List.iter (fun a -> output_string out (prefix_str^"\t\t"^(fml_to_string a)^";\n")) modul.fairness;
		output_string out (prefix_str^"\n");
		output_string out (prefix_str^"\tAtomic formula definitions:\n");
		Hashtbl.iter (fun a b -> output_string out (prefix_str^"\t\t"^a^" := "^(str_expr b)^";\n")) modul.atomic_tbl;
		output_string out (prefix_str^"\n");
		output_string out (prefix_str^"\tSpecifications:\n");
		List.iter (fun a -> output_string out (prefix_str^"\t\t"^(fst a)^" := "^(fml_to_string (snd a))^";\n")) modul.spec_list
	end;
(*	output_string out (prefix_str^"\n");
	output_string out (prefix_str^"\tSub modules:\n");
	Hashtbl.iter (fun a b -> output_string out (prefix_str^"\t\t"^a^" := \n"); output3 out b (prefix_str^"\t\t") false) modul.modul_tbl;*)
	output_string out (prefix_str^"}\n")

type model = modul5

let rec get_new_constant_array ia rests cia var_index_tbl = 
	match rests with
	| [] -> cia
	| (e1, e2) :: rests' -> match e1 with
							| Var i -> (match eval_with_array e2 (ia) var_index_tbl with
										| Const c -> get_new_constant_array ia rests' (cia.(i) <- c; cia) var_index_tbl
										| _ -> print_endline "error constructing new states."; exit 1)
							| _ -> (match (var_str_to_int_expr (eval_with_array e1 ia var_index_tbl) var_index_tbl) with
									| Var j -> (match eval_with_array e2 (ia) var_index_tbl with
												| Const c -> get_new_constant_array ia rests' (cia.(j) <- c; cia) var_index_tbl
												| _ -> print_endline "error constructing new states."; exit 1)
									| _ -> print_endline ("can not find position of "^(str_expr (e1))); print_endline (str_expr (eval_with_array e1 ia var_index_tbl)); exit 1)


(*computing next state, new version*)
let rec next ia trans var_index_tbl = 
	let ss = ref (State_set.empty) in
	let rec eval_trans trans = 
	match trans with
	| (e, rests) :: trans' -> (match (eval_with_array e ia var_index_tbl) with
								| Const 1 -> ss := State_set.add (get_new_constant_array ia rests (Array.copy ia) var_index_tbl ) !ss; eval_trans trans'
								| Const (0) -> eval_trans trans'
								| _ -> print_endline ("error evaluating expression "^(str_expr e)^"."); exit 1)
	| [] -> () in
	eval_trans trans; 
	if State_set.is_empty !ss then begin
		print_endline ("deadlock detected in state "^(str_state (State ia)));
		exit 1
	end;
	(* if State_set.is_empty !ss then ss := State_set.singleton ia; *)
	(*print_endline ((string_of_int (State_set.cardinal !ss)) ^ "\tnext states.");*)
	!ss



let apply_atomic e sl var_index_tbl = 
	let b = eval_expr_with_states e sl var_index_tbl in
	match b with
	| Const 1 -> Top
	| Const (0) -> Bottom
	| _ -> print_endline ((str_expr b)^" is not a constant, in apply atomic."); exit 1 

let str_modl_state vt sa = 
	let rec str_type_value vt ia i = 
		match vt with
		| [] -> ""
		| [(v, t)] -> (match t with
						| Int_type (i1, i2) -> (v^":="^(string_of_int (ia.(i))))
						| Bool_type -> (v^":="^(if (ia.(i)=1) then "true" else (if (ia.(i)=(0)) then "false" else "unknown_bool_value")))
						| Scalar_type sl -> (v^":="^(List.nth sl (ia.(i))))
						| Module_type m -> print_endline "Error: submodule not expanded."; exit (-1)
						| Array_type (_, _) -> print_endline "Error: array not expanded."; exit (-1))
		| (v, t) :: vt' -> (match t with
						| Int_type (i1, i2) -> (v^":="^(string_of_int (ia.(i)))^";")
						| Bool_type -> (v^":="^(if (ia.(i)=1) then "true" else (if (ia.(i)=(0)) then "false" else "unknown_bool_value"))^";")
						| Scalar_type sl -> (v^":="^(List.nth sl (ia.(i)))^";")
						| Module_type m -> print_endline "Error: state not expanded."; exit (-1)
						| Array_type (_, _) -> print_endline "Error: state not expanded."; exit (-1)) ^ (str_type_value vt' ia (i+1)) in
	"{"^(str_type_value vt sa 0)^"}"

let str_modl_state_or_var vt st = 
	match st with
	| SVar v -> v
	| State sa -> str_modl_state vt sa

let rec str_modl_state_or_var_list vt sts = 
	match sts with
	| [] -> ""
	| [st] -> str_modl_state_or_var vt st
	| st :: sts' -> (str_modl_state_or_var vt st) ^","^(str_modl_state_or_var_list vt sts')

let rec str_modl_fml vt fml = 
	match fml with
	| Top -> "TRUE"
	| Bottom -> "FALSE"
	| Atomic (e, sl) -> (e) ^ "("^ (str_modl_state_or_var_list vt sl) ^")"
	| Neg fml1 -> "(not " ^ (str_modl_fml vt fml1) ^ ")"
	| And (fml1, fml2) -> (str_modl_fml vt fml1) ^ "/\\" ^ (str_modl_fml vt fml2)
	| Or (fml1, fml2) -> (str_modl_fml vt fml1) ^ "\\/" ^ (str_modl_fml vt fml2)
	| AX (s, fml1, s') -> "AX(" ^ (str_state s) ^ ", (" ^ (str_modl_fml vt fml1) ^ "), " ^ (str_modl_state_or_var vt s') ^ ")"
	| EX (s, fml1, s') -> "EX(" ^ (str_state s) ^ ", (" ^ (str_modl_fml vt fml1) ^ "), " ^ (str_modl_state_or_var vt s') ^ ")"
	| AF (s, fml1, s') -> "AF(" ^ (str_state s) ^ ", (" ^ (str_modl_fml vt fml1) ^ "), " ^ (str_modl_state_or_var vt s') ^ ")"
	| EG (s, fml1, s') -> "EG(" ^ (str_state s) ^ ", (" ^ (str_modl_fml vt fml1) ^ "), " ^ (str_modl_state_or_var vt s') ^ ")"
	| AR (s, s', fml1, fml2, s'') -> "AR(" ^ (str_state s) ^ ", " ^ (str_modl_state_or_var vt s') ^ ", (" ^ (fml_to_string fml1) ^ "), (" ^ (fml_to_string fml2) ^ "), " ^ (str_modl_state_or_var vt s'') ^ ")"
	| EU (s, s', fml1, fml2, s'') -> "EU(" ^ (str_state s) ^ ", " ^ (str_modl_state_or_var vt s') ^ ", (" ^ (fml_to_string fml1) ^ "), (" ^ (fml_to_string fml2) ^ "), " ^ (str_modl_state_or_var vt s'') ^ ")"



	
