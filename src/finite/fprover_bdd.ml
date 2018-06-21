open Fterm
open Fformula
open Fmodul
open Fbdd 


(***normal to binary***)
let ia_bin_size = ref 0
let var_bin_size_ary = ref (Array.make 0 0)
let var_base_val_ary = ref (Array.make 0 0)
let flag = ref false
(*module BDD = Obdd.BDD (struct let nv = 24 end)*)

let rec get_bin_attr modl = 
	let var_list_size = (List.length modl.var_list) in
	let bin_size = ref 0 
	and bin_size_ary =  (Array.make var_list_size 0)
	and var_base_ary =  (Array.make var_list_size 0) 
	and index = ref 0 in
	List.iter (fun a -> 
		(match a with
		| (s, Int_type (i1, i2)) -> let bs = (int_size (i2-i1+1)) in bin_size := !bin_size + bs; bin_size_ary.(!index) <- bs; var_base_ary.(!index) <- i1
		| (s, Scalar_type ss) -> let bs = int_size (List.length ss) in bin_size := !bin_size + bs; bin_size_ary.(!index) <- bs
		| (s, _) -> bin_size := !bin_size + 1; bin_size_ary.(!index) <- 1
		); incr index
		) modl.var_list; (ia_bin_size := !bin_size; var_bin_size_ary := bin_size_ary; var_base_val_ary := var_base_ary; flag := true)
	
and int_size i = 
	let tmp = ref 2
	and index = ref 1 in
	while (i) >= !tmp do
		incr index;
		tmp := 2 * !tmp
	done; !index
	
and int_to_binary i =
	let tmp_list = ref [] 
	and tmp_i = ref i in
	if i = 0 then [0] else
	begin
		while !tmp_i > 0 do
			tmp_list := (!tmp_i mod 2) :: !tmp_list;
			tmp_i := !tmp_i / 2
		done; !tmp_list
	end

let rec ia_to_bin ia modl = 
try
	if !flag = true then
		begin
			let tmp_ary = Array.make !ia_bin_size 0 
			and index = ref 0 in
			for i=0 to (Array.length ia) - 1 do
				if (!var_bin_size_ary.(i) < 2) then (tmp_ary.(!index) <- ia.(i); incr index) else 
				begin
					let bin_lst = int_to_binary (ia.(i) - !var_base_val_ary.(i)) in
					let tmp_index = ref (!index + !var_bin_size_ary.(i) - 1) in
					List.iter (fun a -> tmp_ary.(!tmp_index) <- a; decr tmp_index) (List.rev bin_lst);
					index := !index + !var_bin_size_ary.(i)
				end
			done; tmp_ary
		end
	else
		begin
			ia_to_bin ia modl
		end
with _ -> print_endline "exception encountered in ia_to_bin."; exit (-1)
(*****)

type fairs = (formula * State_set.t) list

type continuation = 
      Basic of bool
    | Cont of State_set.t * fairs * string * formula * continuation * continuation * ((string * (int array)) list) * ((string * (int array)) list)

exception Error_proving_atomic
exception Unable_to_prove


let rec list_conditional lst c f = 
	match lst with
	| [] -> c
	| elem :: lst' -> if f elem = c then list_conditional lst' c f else not c

let fresh_fairs fairs = 
    List.map (fun (e, ss) -> (e, State_set.empty)) fairs

let orig_fairs = ref []
let has_fairs = ref false

let fresh_fairs_modl modl =
	let fairs = modl.fairness in
	if fairs = [] then [] else
	(
		has_fairs := true;
		List.map (fun (e) -> (e, State_set.empty)) fairs
	)

(****************************)
let true_merge = Hashtbl.create 10
let false_merge = Hashtbl.create 10

let is_in_true_merge s levl modl = 
	try
		let bs = ia_to_bin s modl in
		Fbdd.int_array_satisfy bs (Hashtbl.find true_merge levl)
	with Not_found -> print_endline ("level not found in finding true merge: "^levl); exit 1

let is_in_false_merge s levl modl = 
	let bs = ia_to_bin s modl in
	Fbdd.int_array_satisfy bs (Hashtbl.find false_merge levl)

let add_to_true_merge s levl modl = 
	try
		let bss = Hashtbl.find true_merge levl 
		and bs = ia_to_bin s modl in
		Hashtbl.replace true_merge levl (Fbdd.add_int_array bs bss)
	with Not_found -> print_endline ("level not found in finding true merge: "^levl); exit 1
let add_to_false_merge s levl modl = 
	try
		let bss = Hashtbl.find false_merge levl 
		and bs = ia_to_bin s modl in
		Hashtbl.replace false_merge levl (Fbdd.add_int_array bs bss)
	with Not_found -> print_endline ("level not found in finding false merge: "^levl); exit 1

let add_true_to_cont levl s cont = 
	match cont with
	| Cont (gamma, fairs, cont_levl, fml, contl, contr, ts, fs) -> Cont (gamma, fairs, cont_levl, fml, contl, contr, (levl, s)::ts, fs)
	| _ -> cont

let add_false_to_cont levl s cont = 
	match cont with
	| Cont (gamma, fairs, cont_levl, fml, contl, contr, ts, fs) -> Cont (gamma, fairs, cont_levl, fml, contl, contr, ts, (levl, s)::fs)
	| _ -> cont

(****************************)

	(*whether state s is already in an existing merge*)
let merges = Hashtbl.create 10
let pre_process_merges sub_fml_tbl = 
	Hashtbl.iter (fun a b -> Hashtbl.add merges a (!(Fbdd.leaf_false))) sub_fml_tbl;
	Hashtbl.iter (fun a b -> Hashtbl.add true_merge a (!(Fbdd.leaf_false))) sub_fml_tbl;
	Hashtbl.iter (fun a b -> Hashtbl.add false_merge a (!(Fbdd.leaf_false))) sub_fml_tbl

let in_global_merge s level modl = 
	let bs = ia_to_bin s modl in
    let sts = Hashtbl.find merges level in Fbdd.int_array_satisfy bs sts

let add_to_global_merge ss level modl = 
	let sts = Hashtbl.find merges level in
	Hashtbl.replace merges level (State_set.fold (fun elem b -> let bs = ia_to_bin elem modl in Fbdd.add_int_array bs b) ss sts)

let clear_global_merge level = 
	Hashtbl.replace merges level (!(Fbdd.leaf_false))
let get_global_merge level = 
	Hashtbl.find merges level


let generate_EX_cont gamma fairs levl x fml next contl contr = 
    State_set.fold (fun elem b ->
        Cont (State_set.empty, fresh_fairs fairs, levl^"1", And (subst_s fml x (State elem), EG (SVar "y", Top, State elem)), contl, b, [], [])) next contr

let generate_AX_cont gamma fairs levl x fml next contl contr = 
    State_set.fold (fun elem b ->
        Cont (State_set.empty, fresh_fairs fairs, levl^"1", Or (subst_s fml x (State elem), Neg (EG (SVar "y", Top, State elem))), b, contr, [], [])) next contl

let generate_EG_cont gamma fairs level x fml s next contl contr =
	let level1 = level^"1" in
    let nested = State_set.fold 
        (fun elem b -> 
            Cont (State_set.add s gamma, fairs, level, EG(x, fml, State elem), contl, add_false_to_cont level elem b, [], [])) next contr in
	Cont (State_set.empty, fresh_fairs fairs, level1, subst_s fml x (State s), nested, contr, [], [])

let generate_AF_cont gamma fairs levl x fml s next contl contr =
	let level1 = levl^"1" in 
    let nested = State_set.fold
        (fun elem b ->
            Cont (State_set.add s gamma, fairs, levl, AF(x, fml, State elem), add_true_to_cont levl elem b, contr, [], [])) next contl in
	Cont (State_set.empty, fresh_fairs fairs, level1, subst_s fml x (State s), contl, nested, [], [])

let generate_EU_cont gamma fairs levl x y fml1 fml2 s next contl contr = 
	let levl1 = levl^"1"
	and levl2 = levl^"2" in
	let fresh_fairs = (if !orig_fairs = [] then fresh_fairs fairs else !orig_fairs) in
	(*let mk_fair_contl s1 cl cr = Cont (State_set.empty, fresh_fairs, "-1", EG (SVar "e", Top, (State s1)), cl, cr) in *)
    let nested = State_set.fold
        (fun elem b -> 
            Cont (State_set.singleton s, fairs, levl, EU(x, y, fml1, fml2, State elem), contl, b, [], [])) next contr in
		if !has_fairs then 
			Cont (State_set.empty, fresh_fairs, levl2, subst_s fml2 y (State s), 
			Cont (State_set.empty, fresh_fairs, "-1", EG (SVar "e", Top, (State s)), contl, contr, [], []),
			Cont (State_set.empty, fresh_fairs, levl1, subst_s fml1 x (State s),
				nested,
				contr, 
				[], []),
			[], [])
		else
			Cont (State_set.empty, fresh_fairs, levl2, subst_s fml2 y (State s), 
			contl,
			Cont (State_set.empty, fresh_fairs, levl1, subst_s fml1 x (State s),
				nested,
				contr, 
				[], []),
			[], [])

let generate_AR_cont gamma fairs levl x y fml1 fml2 s next contl contr = 
	let levl1 = levl^"1"
	and levl2 = levl^"2" in
	let fresh_fairs = (if !orig_fairs = [] then fresh_fairs fairs else !orig_fairs) in
    let nested = State_set.fold
        (fun elem b ->
			Cont (State_set.singleton s, fairs, levl, AR (x, y, fml1, fml2, State elem), b, contr, [], [])) next contl in
		if !has_fairs then 
			Cont (State_set.empty, fresh_fairs, levl2, subst_s fml2 y (State s),
			Cont (State_set.empty, fresh_fairs, levl1, subst_s fml1 x (State s), 
				contl,
				nested,
				[], []),
			Cont (State_set.empty, fresh_fairs, "-1", EG (SVar "e", Top, (State s)), 
				contr, 
				contl,
				[], []),
			[], [])
		else
			Cont (State_set.empty, fresh_fairs, levl2, subst_s fml2 y (State s),
			Cont (State_set.empty, fresh_fairs, levl1, subst_s fml1 x (State s), 
				contl,
				nested,
				[], []),
			contr,
			[], [])

let rec satisfy_fair fml s modl =
	prove_fairs (Cont(State_set.empty, [], "0", subst_s fml (SVar "s") (State s), Basic true, Basic false, [], [])) modl

    (* match (apply_atomic exp [s] modl.var_index_tbl) with
    | Top -> true
    | Bottom -> false
    | _ -> raise Error_proving_atomic
 *)
and prove_atomic s sl modl = 
	match s with
	| "has_next" -> State_set.is_empty (next (get_array_from_state (List.hd sl)) modl.transitions modl.var_index_tbl)
	| _ -> (try (match apply_atomic (Hashtbl.find modl.atomic_tbl s) sl modl.var_index_tbl with
			| Top -> true
			| Bottom -> false
			| _ -> raise Error_proving_atomic) with Not_found -> print_endline ("Did not find atomic formula: "^s); exit 1) 

and prove_fairs cont modl = 
    match cont with 
    | Basic b -> b
    | Cont (gamma, fairs, levl, fml, contl, contr, ts, fs) ->
		(
			List.iter (fun (a, b) -> if a<>"-1" then add_to_true_merge b a modl) ts;
			List.iter (fun (a, b) -> if a<>"-1" then add_to_false_merge b a modl) fs
		);
        begin
            match fml with
            | Top -> prove_fairs contl modl
            | Bottom -> prove_fairs contr modl
            | Atomic (s, sl) -> if prove_atomic s sl modl then prove_fairs contl modl else prove_fairs contr modl
			| Neg (Atomic (s, sl)) -> if prove_atomic s sl modl then prove_fairs contr modl else prove_fairs contl modl
            | Neg fml1 -> prove_fairs (Cont (gamma, fairs, levl^"1", fml1, contr, contl, [], [])) modl
            | And (fml1, fml2) -> 
                prove_fairs (Cont (State_set.empty, fresh_fairs fairs, levl^"1", fml1, 
                                Cont (State_set.empty, fresh_fairs fairs, levl^"2", fml2,
                                    contl, 
                                    contr, 
									[],[]), 
                                contr,
								[],[])) modl
            | Or (fml1, fml2) -> 
                prove_fairs (Cont (State_set.empty, fresh_fairs fairs, levl^"1", fml1,
                                contl,
                                Cont (State_set.empty, fresh_fairs fairs, levl^"2", fml2,
                                    contl,
                                    contr, [],[]),[],[])) modl
            | AX (x, fml1, State s) -> 
                let next = next s modl.transitions modl.var_index_tbl in
                prove_fairs (generate_AX_cont gamma fairs levl x fml1 next contl contr) modl
            | EX (x, fml1, State s) -> 
                let next = next s modl.transitions modl.var_index_tbl in
                prove_fairs (generate_EX_cont gamma fairs levl x fml1 next contl contr) modl
            | EG (x, fml1, State s) -> 
				if (levl <> "-1") && (is_in_true_merge s levl modl) then prove_fairs contl modl else
				if (levl <> "-1") && (is_in_true_merge s levl modl) then prove_fairs contr modl else 
                if State_set.mem s gamma 
                then  
                    let is_fair = list_conditional fairs true (fun (e, ss) -> State_set.mem s ss) in
                    if is_fair = true then prove_fairs contl modl else ((*print_endline "EG merge, but not fair";*) prove_fairs contr modl)
                else
                    let next = next s modl.transitions modl.var_index_tbl in
                    (*let fairs_new = List.map (fun (e, ss) -> if satisfy_fair e (State s) modl then (e, State_set.add s ss) else (e,ss)) fairs in*)
					let fairs_new = List.map (fun (e, ss) -> 
						if satisfy_fair e s modl then (e, State_set.add s gamma) else (e,ss)) fairs in

						(* if eval_with_array e s modl.var_index_tbl = (Const 1) then (e, State_set.add s gamma) else (e,ss)) fairs in *)
					(*List.iter (fun (e, ss) -> print_endline ((str_expr e)^"-->"^(string_of_int (State_set.cardinal ss)))) fairs_new;*)
                    prove_fairs (generate_EG_cont gamma fairs_new levl x fml1 s next contl contr) modl
            | AF (x, fml1, State s) -> 
				if is_in_true_merge s levl modl then prove_fairs contl modl else
				if is_in_false_merge s levl modl then prove_fairs contr modl else
				begin
					if State_set.mem s gamma
					then 
						let is_fair = list_conditional fairs true (fun (e, ss) -> State_set.mem s ss) in
						if is_fair = true then prove_fairs contr modl else (prove_fairs contl modl)
					else 
						begin
							let next = next s modl.transitions modl.var_index_tbl in
							let fairs_new = List.map (fun (e, ss) -> if satisfy_fair e s modl then (e, State_set.add s gamma) else (e,ss)) fairs in
							(*List.iter (fun (e, ss) -> print_endline ((str_expr e)^"-->"^(string_of_int (State_set.cardinal ss)))) fairs_new;*)
							prove_fairs (generate_AF_cont gamma fairs_new levl x fml1 s next contl contr) modl
						end
				end
            | EU (x, y, fml1, fml2, State s) -> 
					if State_set.is_empty gamma 
					then clear_global_merge levl 
					else add_to_global_merge gamma levl modl;
					if in_global_merge s levl modl
					then
						prove_fairs contr modl
					else
						let next = next s modl.transitions modl.var_index_tbl in
						prove_fairs (generate_EU_cont gamma fairs levl x y fml1 fml2 s next contl contr) modl
            | AR (x, y, fml1, fml2, State s) ->
					if State_set.is_empty gamma
					then clear_global_merge levl
					else add_to_global_merge gamma levl modl;		
					if in_global_merge s levl modl
					then 
						prove_fairs contl modl
					else
						let next = next s modl.transitions modl.var_index_tbl in
						prove_fairs (generate_AR_cont gamma fairs levl x y fml1 fml2 s next contl contr) modl
			| _ -> (print_endline ("Unable to prove: "^(fml_to_string fml)); raise Unable_to_prove)
        end

	let rec prove_model modl = 
		get_bin_attr modl;
		Fbdd.init !ia_bin_size;
		orig_fairs := fresh_fairs_modl modl;
		let spec_lst = modl.spec_list in 
		let rec prove_lst lst = 
		match lst with
		| [] -> ()
		| (s, fml) :: lst' -> 
			((let nnf_fml = nnf fml in 
			print_endline (fml_to_string (nnf_fml));
			pre_process_merges (select_sub_fmls (sub_fmls nnf_fml "1"));
			let b = (prove_fairs (Cont (State_set.empty, List.map (fun e -> (e, State_set.empty)) modl.fairness, "1", Fformula.subst_s (nnf_fml) (SVar "ini") (State modl.init_assign), Basic true, Basic false, [], [])) modl) in
			 print_endline (s ^ ": " ^ (string_of_bool b)));
			 prove_lst lst') in prove_lst spec_lst






