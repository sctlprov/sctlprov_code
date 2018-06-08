open Printf
open Formula_bcg
open Ks_bcg

exception Deadlock of kstate

type continuation = 
      Basic of bool
    | Cont of State_set.t * string * formula * continuation * continuation * ((string * (kstate)) list) * ((string * (kstate)) list)

exception Error_proving_atomic
exception Unable_to_prove

(* let rec list_conditional lst c f = 
	match lst with
	| [] -> c
	| elem :: lst' -> if f elem = c then list_conditional lst' c f else not c *)

let true_merge = Hashtbl.create 10
let false_merge = Hashtbl.create 10

let is_in_true_merge s levl modl = 
	try
		State_set.mem s.state (Hashtbl.find true_merge levl)
	with Not_found -> print_endline ("level not found in finding true merge: "^levl); exit 1

let is_in_false_merge s levl modl = 
	State_set.mem s.state (Hashtbl.find false_merge levl)

let add_to_true_merge s levl modl = 
	try
		let bss = Hashtbl.find true_merge levl in
		(* if is_state s then *)
		Hashtbl.replace true_merge levl (State_set.add s.state bss)
	with Not_found -> print_endline ("level not found in finding true merge: "^levl); exit 1
let add_to_false_merge s levl modl = 
	try
		let bss = Hashtbl.find false_merge levl in
		(* if is_state s then *)
		Hashtbl.replace false_merge levl (State_set.add s.state bss)
	with Not_found -> print_endline ("level not found in finding false merge: "^levl); exit 1

let add_true_to_cont levl s cont = 
	match cont with
	| Cont (gamma, cont_levl, fml, contl, contr, ts, fs) -> Cont (gamma, cont_levl, fml, contl, contr, (levl, s)::ts, fs)
	| _ -> cont

let add_false_to_cont levl s cont = 
	match cont with
	| Cont (gamma, cont_levl, fml, contl, contr, ts, fs) -> Cont (gamma, cont_levl, fml, contl, contr, ts, (levl, s)::fs)
	| _ -> cont

(****************************)

	(*whether state s is already in an existing merge*)
let merges = Hashtbl.create 10
let pre_process_merges sub_fml_tbl = 
	Hashtbl.iter (fun a b -> Hashtbl.add merges a (State_set.empty)) sub_fml_tbl;
	Hashtbl.iter (fun a b -> Hashtbl.add true_merge a (State_set.empty)) sub_fml_tbl;
	Hashtbl.iter (fun a b -> Hashtbl.add false_merge a (State_set.empty)) sub_fml_tbl

let get_merge levl = 
	Hashtbl.find merges levl

let in_global_merge s level modl = 
	State_set.mem s.state (Hashtbl.find merges level)

let add_to_global_merge ss level modl = 
	let sts = Hashtbl.find merges level in
	Hashtbl.replace merges level (State_set.fold (fun elem b -> State_set.add elem b) ss sts)
    
let clear_global_merge level = 
	Hashtbl.replace merges level (State_set.empty)
let get_global_merge level = 
	Hashtbl.find merges level


let generate_EX_cont gamma levl x fml next contl contr = 
    State_label_set.fold (fun elem b ->
        Cont (State_set.empty, levl^"1", And (subst_s fml x (State elem), EG (SVar "y", Top, State elem)), contl, b, [], [])) next contr

let generate_AX_cont gamma levl x fml next contl contr = 
  State_label_set.fold (fun elem b ->
        Cont (State_set.empty, levl^"1", Or (subst_s fml x (State elem), Neg (EG (SVar "y", Top, State elem))), b, contr, [], [])) next contl 

let generate_EG_cont gamma level x fml s next contl contr =
	let level1 = level^"1" in
    let nested = State_label_set.fold
        (fun elem b -> 
            Cont (State_set.add s.state gamma, level, EG(x, fml, State elem), contl, add_false_to_cont level elem b, [], [])) next contr in
	Cont (State_set.empty, level1, subst_s fml x (State s), nested, contr, [], [])

let generate_AF_cont gamma levl x fml s next contl contr =
	let level1 = levl^"1" in 
    let nested = State_label_set.fold
        (fun elem b ->
            Cont (State_set.add s.state gamma, levl, AF(x, fml, State elem), add_true_to_cont levl elem b, contr, [], [])) next contl in
	Cont (State_set.empty, level1, subst_s fml x (State s), contl, nested, [], [])

let generate_EU_cont gamma levl x y fml1 fml2 s next contl contr = 
	let levl1 = levl^"1"
	and levl2 = levl^"2" in
	let nested = State_label_set.fold
			(fun elem b -> 
					Cont (State_set.singleton s.state, levl, EU(x, y, fml1, fml2, State elem), contl, b, [], [])) next contr in
		Cont (State_set.empty, levl2, subst_s fml2 y (State s), 
		contl,
		Cont (State_set.empty, levl1, subst_s fml1 x (State s),
			nested,
			contr, 
			[], []),
		[], [])

let generate_AR_cont gamma levl x y fml1 fml2 s next contl contr = 
	let levl1 = levl^"1"
	and levl2 = levl^"2" in
	let nested = State_label_set.fold
		(fun elem b ->
	Cont (State_set.singleton s.state, levl, AR (x, y, fml1, fml2, State elem), b, contr, [], [])) next contl in
	Cont (State_set.empty, levl2, subst_s fml2 y (State s),
	Cont (State_set.empty, levl1, subst_s fml1 x (State s), 
		contl,
		nested,
		[], []),
	contr,
	[], [])

and prove_atomic s sl modl = 
	match s with
	| "has_tau" -> begin
			match (List.hd sl) with
			| State ss -> has_tau ss
			| _ -> false
		end
	| "is_deadlock" -> begin
			match (List.hd sl) with
			| State ss -> is_deadlock ss
			| _ -> false
		end
	| _ -> printf "Unknown atomic predicate: %s\n" s; exit 1

let rec prove cont modl deadlock ignore_label = 
    match cont with 
    | Basic b -> b
    | Cont (gamma, levl, fml, contl, contr, ts, fs) ->
		(
			List.iter (fun (a, b) -> if a<>"-1" then add_to_true_merge b a modl) ts;
			List.iter (fun (a, b) -> if a<>"-1" then add_to_false_merge b a modl) fs
		);
		begin
			(* print_endline("proving fml: "^(fml_to_string fml)); *)
				match fml with
				| Top -> prove contl modl deadlock ignore_label
				| Bottom -> prove contr modl deadlock ignore_label
				| Atomic (s, sl) -> if prove_atomic s sl modl then prove contl modl deadlock ignore_label else prove contr modl deadlock ignore_label
				| Neg (Atomic (s, sl)) -> if prove_atomic s sl modl then prove contr modl deadlock ignore_label else prove contl modl deadlock ignore_label
				| Neg fml1 -> prove (Cont (gamma, levl^"1", fml1, contr, contl, [], [])) modl deadlock ignore_label
				| And (fml1, fml2) -> 
						prove (Cont (State_set.empty, levl^"1", fml1, 
														Cont (State_set.empty, levl^"2", fml2,
																contl, 
																contr, 
							[],[]), 
														contr,
						[],[])) modl deadlock ignore_label
				| Or (fml1, fml2) -> 
						prove (Cont (State_set.empty, levl^"1", fml1,
														contl,
														Cont (State_set.empty, levl^"2", fml2,
																contl,
																contr, [],[]),[],[])) modl deadlock ignore_label
				| AX (x, fml1, State s) -> 
						let next = next modl s ignore_label in
						if State_label_set.is_empty next && deadlock then
							raise (Deadlock s)
						else
							prove (generate_AX_cont gamma levl x fml1 next contl contr) modl deadlock ignore_label
				| EX (x, fml1, State s) -> 
						let next = next modl s ignore_label in
						if State_label_set.is_empty next && deadlock then
							raise (Deadlock s)
						else
							prove (generate_EX_cont gamma levl x fml1 next contl contr) modl deadlock ignore_label
				| EG (x, fml1, State s) -> 
						if (is_in_true_merge s levl modl) then prove contl modl deadlock ignore_label else
						if (is_in_false_merge s levl modl) then prove contr modl deadlock ignore_label else 
							if (State_set.mem s.state gamma) && (has_tau s) 
							then begin
                (* List.iter (fun s -> )   *)
                (* print_endline "EG merge:";
                State_set.iter (fun s -> print_int s; print_string ",") gamma;
                print_endline ""; *)
                prove contl modl deadlock ignore_label
							end else
									let next = next modl s ignore_label in
									if State_label_set.is_empty next && deadlock then
										raise (Deadlock s)
									else 
										prove (generate_EG_cont gamma levl x fml1 s next contl contr) modl deadlock ignore_label
				| AF (x, fml1, State s) -> 
						if is_in_true_merge s levl modl then prove contl modl deadlock ignore_label else
						if is_in_false_merge s levl modl then prove contr modl deadlock ignore_label else
						begin
							if State_set.mem s.state gamma
							then 
								prove contr modl deadlock ignore_label
							else 
								begin
									let next = next modl s ignore_label in
									if State_label_set.is_empty next && deadlock then
										raise (Deadlock s)
									else
										prove (generate_AF_cont gamma levl x fml1 s next contl contr) modl deadlock ignore_label
								end
						end
				| EU (x, y, fml1, fml2, State s) -> 
					(
						if State_set.is_empty gamma 
						then clear_global_merge levl 
						else add_to_global_merge gamma levl modl;
						if in_global_merge s levl modl
						then
							prove contr modl deadlock ignore_label
						else
							let next = next modl s ignore_label in
							if State_label_set.is_empty next && deadlock then
								raise (Deadlock s)
							else
                (* let new_next = State_set.diff next (get_merge levl) in *)
                let new_next = State_label_set.filter (fun s -> not (in_global_merge s levl modl)) next in
								prove (generate_EU_cont gamma levl x y fml1 fml2 s new_next contl contr) modl deadlock ignore_label
					) 
				| AR (x, y, fml1, fml2, State s) ->
					(
						(if State_set.is_empty gamma
						then clear_global_merge levl
						else add_to_global_merge gamma levl modl;
						(*print_endline ("AR merge size: "^(string_of_int (State_set.cardinal (Hashtbl.find merges levl))))*)
						);		
						if in_global_merge s levl modl
						then 
							prove contl modl deadlock ignore_label
						else
							let next = next modl s ignore_label in
							if State_label_set.is_empty next && deadlock then
								raise (Deadlock s)
              else
                let new_next = State_label_set.filter (fun s -> not (in_global_merge s levl modl)) next in
								prove (generate_AR_cont gamma levl x y fml1 fml2 s new_next contl contr) modl deadlock ignore_label
					) 
				| _ -> (print_endline ("Unable to prove: "^(fml_to_string fml)); raise Unable_to_prove)
		end

	let rec prove_model modl spec_lst deadlock ignore_label = 
		let rec prove_lst lst = 
		match lst with
		| [] -> ()
		| (s, fml) :: lst' -> 
			((let nnf_fml = nnf fml in 
			print_endline (fml_to_string (nnf_fml));
			pre_process_merges (select_sub_fmls (sub_fmls nnf_fml "1"));
			begin try
				let b = (prove (Cont (State_set.empty, "1", subst_s (nnf_fml) (SVar "ini") (State modl.init), Basic true, Basic false, [], [])) modl deadlock ignore_label) in
				print_endline (s ^ ": " ^ (string_of_bool b))
			with Deadlock s ->
				print_endline "deadlock detected!!!"	
			end);
			 prove_lst lst') 
		in prove_lst spec_lst
			 






