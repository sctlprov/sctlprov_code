open Expr
open Formula
open Interp
open Printf
open Merge


let searched_state = ref (State_set.empty)

let next s runtime modul = 
	(* searched_state := State_set.add s !searched_state; *)
	let model = runtime.model in 
	let ctx, _ = get_matched_pattern s [(fst model.transition, Int 0)] in
	let nexts = snd model.transition in
	let next_states = ref State_set.empty in begin
		match nexts with
		| Case case_nexts ->
			List.iter (fun (e1, e2) -> 
			match evaluate e1 ctx runtime modul with
			| VBool true -> next_states := State_set.add (evaluate e2 ctx runtime modul) !next_states 
			| VBool false -> ()
			| _ -> printf "%s should evaluate to a boolean value" (str_expr e1); exit 1) case_nexts
		| No_case no_case_nexts -> begin
				match evaluate no_case_nexts ctx runtime modul with
				| VLst vl -> 
					next_states := State_set.of_list vl
				| v -> print_endline ("should be a list of states: "^(str_value v)); exit 1
			end
	end;
	(* searched_state := State_set.union !searched_state !next_states; *)
	!next_states
	

type fairs = (formula * State_set.t) list

type continuation = 
      Basic of bool
    | Cont of State_set.t * fairs * string * formula * continuation * continuation * ((string * (value)) list) * ((string * (value)) list)

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

let fresh_fairs_modl runtime =
	let fairs = runtime.model.fairness in
	if fairs = [] then [] else
	(
		has_fairs := true;
		List.map (fun (e) -> (e, State_set.empty)) fairs
	)


let add_true_to_cont levl s cont = 
	match cont with
	| Cont (gamma, fairs, cont_levl, fml, contl, contr, ts, fs) -> Cont (gamma, fairs, cont_levl, fml, contl, contr, (levl, s)::ts, fs)
	| _ -> cont

let add_false_to_cont levl s cont = 
	match cont with
	| Cont (gamma, fairs, cont_levl, fml, contl, contr, ts, fs) -> Cont (gamma, fairs, cont_levl, fml, contl, contr, ts, (levl, s)::fs)
	| _ -> cont

(****************************)


let generate_EX_cont gamma fairs levl x fml next contl contr = 
	(* State_set.fold (fun elem b ->
			Cont (State_set.empty, fresh_fairs fairs, levl^"1", And (subst_s fml x (State elem), EG (SVar "y", Top, State elem)), contl, b, [], [])) next contr *)
	let ffairs = fresh_fairs fairs in
	if !has_fairs then
		State_set.fold (fun elem b ->
			Cont (State_set.empty, ffairs, levl^"1", subst_s fml x (State elem), Cont(State_set.empty, ffairs, "-1", EG("y", Top, State elem), contl, b, [], []), b, [], [])
		) next contr
	else
		State_set.fold (fun elem b ->
			Cont(State_set.empty, ffairs, levl^"1", subst_s fml x (State elem), contl, b, [], [])
		) next contr


let generate_AX_cont gamma fairs levl x fml next contl contr = 
	(* State_set.fold (fun elem b ->
			Cont (State_set.empty, fresh_fairs fairs, levl^"1", Or (subst_s fml x (State elem), Neg (EG (SVar "y", Top, State elem))), b, contr, [], [])) next contl *)
	let ffairs = fresh_fairs fairs in
	if !has_fairs then
		State_set.fold (fun elem b ->
			Cont (State_set.empty, ffairs, levl^"1", subst_s fml x (State elem), b, Cont(State_set.empty, ffairs, "-1", EG("y", Top, State elem), contr, b, [], []), [], [])
		) next contl
	else 
		State_set.fold ( fun elem b ->
			Cont(State_set.empty, ffairs, levl^"1", subst_s fml x (State elem), b, contr, [], [])
		) next contl
	
(* 
let generate_EX_cont gamma fairs levl x fml next contl contr = 
	let ff = fresh_fairs fairs in
	State_set.fold (fun elem b ->
		Cont (State_set.empty, ff, levl^"1", subst_s fml x (State elem), Cont (State_set.empty, ff, "-1", EG("y", Top, State elem), contl, b, [], []), b, [], [])
		(* Cont (State_set.empty, fresh_fairs fairs, levl^"1", And (subst_s fml x (State elem), EG ("y", Top, State elem)), contl, b, [], []) *)
		) next contr

let generate_AX_cont gamma fairs levl x fml next contl contr = 
	let ff = fresh_fairs fairs in
    State_set.fold (fun elem b ->
		Cont (State_set.empty, ff, levl^"1", subst_s fml x (State elem), b, Cont (State_set.empty, ff, "-1", EG ("y", Top, State elem), b, contr, [], []), [], [])	
	(* Cont (State_set.empty, fresh_fairs fairs, levl^"1", Or (subst_s fml x (State elem), Neg (EG ("y", Top, State elem))), b, contr, [], []) *)
		) next contl *)

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
			Cont (State_set.empty, fresh_fairs, "-1", EG ("e", Top, (State s)), contl, contr, [], []),
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
			Cont (State_set.empty, fresh_fairs, "-1", EG ("e", Top, (State s)), 
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

let prove_atomic s sl runtime modul =
	let args = List.map (fun st ->
		match st with
		| SVar _ -> raise Error_proving_atomic
		| State value -> value
	) sl in
	try
		let (paras, expr) = Hashtbl.find runtime.model.atomic s in
		let ctx = Lists.zip_to_refpairs paras args in
		match evaluate expr ctx runtime modul with
		| VBool b -> b
		| _ -> raise (Error_proving_atomic)
	with Not_found -> print_endline ("definition of atomic function "^s^" is missing."); exit 1

let rec satisfy_fair fml s runtime modul =
	prove_fairs (Cont(State_set.empty, [], "0", subst_s fml ("s") (State s), Basic true, Basic false, [], [])) runtime modul

and prove_fairs cont runtime modul = 
    match cont with 
    | Basic b -> b
    | Cont (gamma, fairs, levl, fml, contl, contr, ts, fs) ->
		(
			List.iter (fun (a, b) -> if a<>"-1" then add_to_true_merge b a) ts;
			List.iter (fun (a, b) -> if a<>"-1" then add_to_false_merge b a) fs
		);
		(* print_endline ("proving formula "^(str_fml fml)); *)
		
        begin
            match fml with
            | Top -> prove_fairs contl runtime modul
            | Bottom -> prove_fairs contr runtime modul
			| Atomic (s, sl) -> 
				(* print_endline ("proving formula "^(str_fml fml)); *)
				if prove_atomic s sl runtime modul then prove_fairs contl runtime modul else prove_fairs contr runtime modul
			| Neg (Atomic (s, sl)) -> if prove_atomic s sl runtime modul then prove_fairs contr runtime modul else prove_fairs contl runtime modul
            | Neg fml1 -> prove_fairs (Cont (gamma, fairs, levl^"1", fml1, contr, contl, [], [])) runtime modul
            | And (fml1, fml2) -> 
                prove_fairs (Cont (State_set.empty, fresh_fairs fairs, levl^"1", fml1, 
                                Cont (State_set.empty, fresh_fairs fairs, levl^"2", fml2,
                                    contl, 
                                    contr, 
									[],[]), 
                                contr,
								[],[])) runtime modul
            | Or (fml1, fml2) -> 
                prove_fairs (Cont (State_set.empty, fresh_fairs fairs, levl^"1", fml1,
                                contl,
                                Cont (State_set.empty, fresh_fairs fairs, levl^"2", fml2,
                                    contl,
                                    contr, [],[]),[],[])) runtime modul
            | AX (x, fml1, State s) -> 
                let next = next s runtime modul in
                prove_fairs (generate_AX_cont gamma fairs levl x fml1 next contl contr) runtime modul
            | EX (x, fml1, State s) -> 
                let next = next s runtime modul in
                prove_fairs (generate_EX_cont gamma fairs levl x fml1 next contl contr) runtime modul
            | EG (x, fml1, State s) -> 
				if (levl <> "-1") && (is_in_true_merge s levl) then prove_fairs contl runtime modul else
				if (levl <> "-1") && (is_in_false_merge s levl) then prove_fairs contr runtime modul else 
                if State_set.mem s gamma 
                then  
                    let is_fair = list_conditional fairs true (fun (e, ss) -> State_set.mem s ss) in
                    if is_fair = true then prove_fairs contl runtime modul else ((*print_endline "EG merge, but not fair";*) prove_fairs contr runtime modul)
                else
                    let next = next s runtime modul in
                    (*let fairs_new = List.map (fun (e, ss) -> if satisfy_fair e (State s) modl then (e, State_set.add s ss) else (e,ss)) fairs in*)
					let fairs_new = List.map (fun (e, ss) -> 
						if satisfy_fair e s runtime modul then (e, State_set.add s gamma) else (e,ss)) fairs in

						(* if eval_with_array e s modl.var_index_tbl = (Const 1) then (e, State_set.add s gamma) else (e,ss)) fairs in *)
					(*List.iter (fun (e, ss) -> print_endline ((str_expr e)^"-->"^(string_of_int (State_set.cardinal ss)))) fairs_new;*)
                    prove_fairs (generate_EG_cont gamma fairs_new levl x fml1 s next contl contr) runtime modul
            | AF (x, fml1, State s) -> 
				if is_in_true_merge s levl then prove_fairs contl runtime modul else
				if is_in_false_merge s levl then prove_fairs contr runtime modul else
				begin
					if State_set.mem s gamma
					then 
						let is_fair = list_conditional fairs true (fun (e, ss) -> State_set.mem s ss) in
						if is_fair = true then prove_fairs contr runtime modul else (prove_fairs contl runtime modul)
					else 
						begin
							let next = next s runtime modul in
							let fairs_new = List.map (fun (e, ss) -> if satisfy_fair e s runtime modul then (e, State_set.add s gamma) else (e,ss)) fairs in
							(*List.iter (fun (e, ss) -> print_endline ((str_expr e)^"-->"^(string_of_int (State_set.cardinal ss)))) fairs_new;*)
							prove_fairs (generate_AF_cont gamma fairs_new levl x fml1 s next contl contr) runtime modul
						end
				end
            | EU (x, y, fml1, fml2, State s) -> 
				 (
					if State_set.is_empty gamma 
					then clear_false_merge levl 
					else 
						(
							State_set.iter (fun s -> add_to_false_merge s levl) gamma
						);
					if is_in_false_merge s levl
					then
						prove_fairs contr runtime modul
					else
						let next = State_set.filter (fun s -> not (is_in_false_merge s levl)) (next s runtime modul) in
						prove_fairs (generate_EU_cont gamma fairs levl x y fml1 fml2 s next contl contr) runtime modul
				) 
            | AR (x, y, fml1, fml2, State s) ->
				 (
					(* print_endline ("AR merge size: "^(string_of_int (State_set.cardinal (Hashtbl.find merges levl))));					 *)
					(if State_set.is_empty gamma
					then clear_true_merge levl
					else 
						(
							State_set.iter (fun s -> add_to_true_merge s levl) gamma
						)
					);		
					if is_in_true_merge s levl
					then 
						prove_fairs contl runtime modul
					else begin
						let next = State_set.filter (fun s -> not (is_in_true_merge s levl)) (next s runtime modul) in
						(* State_set.iter (fun a -> 
						if (not (in_global_merge a levl)) then print_endline ((str_value (a)))) next; *)
						prove_fairs (generate_AR_cont gamma fairs levl x y fml1 fml2 s next contl contr) runtime modul
					end
				) 
			| _ -> (print_endline ("Unable to prove: "^(str_fml fml)); raise Unable_to_prove)
        end

and prove_fairsb cont runtime modul = 
	match cont with 
	| Basic b -> b
	| Cont (gamma, fairs, levl, fml, contl, contr, ts, fs) ->
	(
		List.iter (fun (a, b) -> if a<>"-1" then add_to_true_mergeb b a) ts;
		List.iter (fun (a, b) -> if a<>"-1" then add_to_false_mergeb b a) fs
	);
	(* print_endline ("proving formula "^(str_fml fml)); *)

			begin
					match fml with
					| Top -> prove_fairsb contl runtime modul
					| Bottom -> prove_fairsb contr runtime modul
		| Atomic (s, sl) -> 
			(* print_endline ("proving formula "^(str_fml fml)); *)
			if prove_atomic s sl runtime modul then prove_fairsb contl runtime modul else prove_fairsb contr runtime modul
		| Neg (Atomic (s, sl)) -> if prove_atomic s sl runtime modul then prove_fairsb contr runtime modul else prove_fairsb contl runtime modul
		| Neg fml1 -> prove_fairsb (Cont (gamma, fairs, levl^"1", fml1, contr, contl, [], [])) runtime modul
		| And (fml1, fml2) -> 
				prove_fairsb (Cont (State_set.empty, fresh_fairs fairs, levl^"1", fml1, 
												Cont (State_set.empty, fresh_fairs fairs, levl^"2", fml2,
														contl, 
														contr, 
					[],[]), 
												contr,
				[],[])) runtime modul
		| Or (fml1, fml2) -> 
				prove_fairsb (Cont (State_set.empty, fresh_fairs fairs, levl^"1", fml1,
												contl,
												Cont (State_set.empty, fresh_fairs fairs, levl^"2", fml2,
														contl,
														contr, [],[]),[],[])) runtime modul
		| AX (x, fml1, State s) -> 
				let next = next s runtime modul in
				prove_fairsb (generate_AX_cont gamma fairs levl x fml1 next contl contr) runtime modul
		| EX (x, fml1, State s) -> 
				let next = next s runtime modul in
				prove_fairsb (generate_EX_cont gamma fairs levl x fml1 next contl contr) runtime modul
		| EG (x, fml1, State s) -> 
			if (levl <> "-1") && (is_in_true_mergeb s levl) then prove_fairsb contl runtime modul else
			if (levl <> "-1") && (is_in_false_mergeb s levl) then prove_fairsb contr runtime modul else 
					if State_set.mem s gamma 
					then  
							let is_fair = list_conditional fairs true (fun (e, ss) -> State_set.mem s ss) in
							if is_fair = true then prove_fairsb contl runtime modul else ((*print_endline "EG merge, but not fair";*) prove_fairsb contr runtime modul)
					else
							let next = next s runtime modul in
							(*let fairs_new = List.map (fun (e, ss) -> if satisfy_fair e (State s) modl then (e, State_set.add s ss) else (e,ss)) fairs in*)
		let fairs_new = List.map (fun (e, ss) -> 
			if satisfy_fair e s runtime modul then (e, State_set.add s gamma) else (e,ss)) fairs in

			(* if eval_with_array e s modl.var_index_tbl = (Const 1) then (e, State_set.add s gamma) else (e,ss)) fairs in *)
		(*List.iter (fun (e, ss) -> print_endline ((str_expr e)^"-->"^(string_of_int (State_set.cardinal ss)))) fairs_new;*)
							prove_fairsb (generate_EG_cont gamma fairs_new levl x fml1 s next contl contr) runtime modul
			| AF (x, fml1, State s) -> 
				if is_in_true_mergeb s levl then prove_fairsb contl runtime modul else
				if is_in_false_mergeb s levl then prove_fairsb contr runtime modul else
				begin
					if State_set.mem s gamma
					then 
						let is_fair = list_conditional fairs true (fun (e, ss) -> State_set.mem s ss) in
						if is_fair = true then prove_fairsb contr runtime modul else (prove_fairsb contl runtime modul)
					else 
						begin
							let next = next s runtime modul in
							let fairs_new = List.map (fun (e, ss) -> if satisfy_fair e s runtime modul then (e, State_set.add s gamma) else (e,ss)) fairs in
							(*List.iter (fun (e, ss) -> print_endline ((str_expr e)^"-->"^(string_of_int (State_set.cardinal ss)))) fairs_new;*)
							prove_fairsb (generate_AF_cont gamma fairs_new levl x fml1 s next contl contr) runtime modul
						end
				end
			| EU (x, y, fml1, fml2, State s) -> 
				(
				if State_set.is_empty gamma then 
					clear_false_mergeb levl 
				else 
					(
						State_set.iter (fun s -> add_to_false_mergeb s levl) gamma
					);
				if is_in_false_mergeb s levl then
					prove_fairsb contr runtime modul
				else
					let next = State_set.filter (fun s -> not (is_in_false_mergeb s levl)) (next s runtime modul) in
					prove_fairsb (generate_EU_cont gamma fairs levl x y fml1 fml2 s next contl contr) runtime modul
				) 
			| AR (x, y, fml1, fml2, State s) ->
				(
				(* print_endline ("AR merge size: "^(string_of_int (State_set.cardinal (Hashtbl.find merges levl))));					 *)
				(if State_set.is_empty gamma
				then clear_true_mergeb levl
				else 
					(
						State_set.iter (fun s -> add_to_true_mergeb s levl) gamma
					)
				);		
				if is_in_true_mergeb s levl
				then 
					prove_fairsb contl runtime modul
				else begin
					let next = State_set.filter (fun s -> not (is_in_true_mergeb s levl)) (next s runtime modul) in
					prove_fairsb (generate_AR_cont gamma fairs levl x y fml1 fml2 s next contl contr) runtime modul
				end
			) 
		| _ -> (print_endline ("Unable to prove: "^(str_fml fml)); raise Unable_to_prove)
			end
		

let rec prove_model runtime modul = 
	orig_fairs := fresh_fairs_modl runtime;
	let spec_lst = runtime.model.properties in 
	let rec prove_lst lst = 
	match lst with
	| [] -> ()
	| (s, fml) :: lst' -> 
		((let nnf_fml = nnf fml in 
		print_endline (str_fml_ptyp (nnf_fml) runtime.model.state_type);
		pre_process_merges (select_sub_fmls (sub_fmls nnf_fml "1"));
		let b = (
			Merge.get_bin_attr runtime.model;
			if !Flags.using_bdd && !Merge.flag then
				prove_fairsb (Cont (State_set.empty, List.map (fun e -> (e, State_set.empty)) runtime.model.fairness, "1", (nnf_fml), Basic true, Basic false, [], [])) runtime modul
			else
				prove_fairs (Cont (State_set.empty, List.map (fun e -> (e, State_set.empty)) runtime.model.fairness, "1", (nnf_fml), Basic true, Basic false, [], [])) runtime modul) in
			print_endline (s ^ ": " ^ (string_of_bool b)));
			prove_lst lst') in prove_lst spec_lst

let rec prove_modelb runtime modul = 
	orig_fairs := fresh_fairs_modl runtime;
	let s, fml = List.hd runtime.model.properties in 
	let nnf_fml = nnf fml in 
	(* print_endline (str_fml_ptyp (nnf_fml) runtime.model.state_type); *)
	pre_process_merges (select_sub_fmls (sub_fmls nnf_fml "1"));
	let b = (
		Merge.get_bin_attr runtime.model;
		if !Flags.using_bdd && !Merge.flag then
			prove_fairsb (Cont (State_set.empty, List.map (fun e -> (e, State_set.empty)) runtime.model.fairness, "1", (nnf_fml), Basic true, Basic false, [], [])) runtime modul
		else
			prove_fairs (Cont (State_set.empty, List.map (fun e -> (e, State_set.empty)) runtime.model.fairness, "1", (nnf_fml), Basic true, Basic false, [], [])) runtime modul) in
	b