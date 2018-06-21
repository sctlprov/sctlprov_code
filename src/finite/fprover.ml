open Fterm
open Fformula
open Fmodul
(* open Bdd *)


(***normal to binary***)
let rec get_bin_attr modl = 
	let var_list_size = (List.length modl.var_list) in
	let bin_size = ref 0 
	and bin_size_ary =  (Array.make var_list_size 0)
	and var_base_ary =  (Array.make var_list_size 0) 
	and index = ref 0 in
	List.iter (fun a -> 
		(match a with
		| (s, Int_type (i1, i2)) -> let bs = (int_size (i2-i1+1)) in bin_size := !bin_size + bs; bin_size_ary.(!index) <- bs; var_base_ary.(!index) <- i1
		| (s, Scalar_type ss) -> let bs = int_size (List.length ss) in bin_size := !bin_size + bs; bin_size_ary.(!index) <- bs; var_base_ary.(!index) <- 0
		| (s, _) -> bin_size := !bin_size + 1; bin_size_ary.(!index) <- 1
		); incr index
		) modl.var_list; (!bin_size, bin_size_ary, var_base_ary)
	
and int_size i = 
	let tmp = ref 2
	and index = ref 1 in
	while (i) >= !tmp do
		incr index;
		tmp := 2 * !tmp
	done; 
	!index
	
and int_to_binary i =
	let tmp_list = ref [] 
	and tmp_i = ref i in
	if i = 0 then [0] else
	begin
		while !tmp_i > 0 do
			tmp_list := (!tmp_i mod 2) :: !tmp_list;
			tmp_i := !tmp_i / 2
		done; tmp_list := !tmp_list; 
		!tmp_list
	end

let ia_bin_size = ref 0
let var_bin_size_ary = ref (Array.make 0 0)
let var_base_val_ary = ref (Array.make 0 0)
let flag = ref false

let rec ia_to_bin ia modl = 
try
	if !flag = true then
		begin
			let tmp_ary = Array.make !ia_bin_size 0 
			and index = ref 0 in
			for i=0 to (Array.length ia) - 1 do
				if (!var_bin_size_ary.(i) < 2) then (tmp_ary.(!index) <- ia.(i); incr index) else 
				begin
					(*print_endline ("converting: "^(string_of_int (ia.(i) - !var_base_val_ary.(i))));*)
					let bin_lst = int_to_binary (ia.(i) - !var_base_val_ary.(i)) in
					let tmp_index = ref (!index + !var_bin_size_ary.(i) - 1) in
					List.iter (fun a -> tmp_ary.(!tmp_index) <- a; decr tmp_index) (List.rev bin_lst);
					index := !index + !var_bin_size_ary.(i)
				end
			done; 
			tmp_ary
		end
	else
		begin
			let (ibs, vba, fbva) = get_bin_attr modl in
			ia_bin_size := ibs;
			var_bin_size_ary := vba;
			var_base_val_ary := fbva;
			flag := true;
			ia_to_bin ia modl
		end
with _ -> print_endline "exception encountered in ia_to_bin."; exit (-1)
(*****)

module SetKey = 
	struct
		type t = State_set.t * (int array)
		let compare = Pervasives.compare
	end;;

module Merge_set = Set.Make(SetKey)


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

let add_true_to_cont levl s cont = 
	match cont with
	| Cont (gamma, fairs, cont_levl, fml, contl, contr, ts, fs) -> Cont (gamma, fairs, cont_levl, fml, contl, contr, (levl, s)::ts, fs)
	| _ -> cont

let add_false_to_cont levl s cont = 
	match cont with
	| Cont (gamma, fairs, cont_levl, fml, contl, contr, ts, fs) -> Cont (gamma, fairs, cont_levl, fml, contl, contr, ts, (levl, s)::fs)
	| _ -> cont

(****************************)


let merges = Hashtbl.create 10
let true_merge = Hashtbl.create 10
let false_merge = Hashtbl.create 10
let true_tmp_merge = Hashtbl.create 10
let false_tmp_merge = Hashtbl.create 10
let pre_process_merges sub_fml_tbl = 
	Hashtbl.iter (fun a b -> Hashtbl.add merges a (State_set.empty)) sub_fml_tbl;
	Hashtbl.iter (fun a b -> Hashtbl.add true_merge a (State_set.empty)) sub_fml_tbl;
	Hashtbl.iter (fun a b -> Hashtbl.add false_merge a (State_set.empty)) sub_fml_tbl;
	Hashtbl.iter (fun a b -> Hashtbl.add true_tmp_merge a (Merge_set.empty)) sub_fml_tbl;
	Hashtbl.iter (fun a b -> Hashtbl.add false_tmp_merge a (Merge_set.empty)) sub_fml_tbl


let is_in_true_merge s levl = 
	try
		State_set.mem s (Hashtbl.find true_merge levl)
	with Not_found -> print_endline ("level not found in finding true merge: "^levl); exit 1

let is_in_false_merge s levl = 
	State_set.mem s (Hashtbl.find false_merge levl)

let add_to_true_merge s levl = 
	try
		let bss = Hashtbl.find true_merge levl in
		Hashtbl.replace true_merge levl (State_set.add s bss)
	with Not_found -> print_endline ("level not found in finding true merge: "^levl); exit 1
let union_to_true_merge ss levl =  Hashtbl.replace true_merge levl (State_set.union ss (Hashtbl.find true_merge levl))
let minus_from_true_merge ss levl = Hashtbl.replace true_merge levl (State_set.diff (Hashtbl.find true_merge levl) ss)
let clear_true_merge levl = Hashtbl.replace true_merge levl State_set.empty
let add_to_false_merge s levl = 
	try
		let bss = Hashtbl.find false_merge levl in
		Hashtbl.replace false_merge levl (State_set.add s bss)
	with Not_found -> print_endline ("level not found in finding false merge: "^levl); exit 1
let union_to_false_merge ss levl = Hashtbl.replace false_merge levl (State_set.union ss (Hashtbl.find false_merge levl))
let minus_from_false_merge ss levl = Hashtbl.replace false_merge levl (State_set.diff (Hashtbl.find false_merge levl) ss)
let clear_false_merge levl = Hashtbl.replace false_merge levl State_set.empty


let add_to_true_tmp_merge merge state levl = 
	if not (State_set.is_empty merge) then begin
		let old_tmp_merge = ref (Hashtbl.find true_tmp_merge levl) in begin
		match Merge_set.find_first_opt (fun (m,s) -> State_set.mem state m) !old_tmp_merge with
		| Some ms -> old_tmp_merge := Merge_set.remove ms !old_tmp_merge; old_tmp_merge := Merge_set.add (State_set.union merge (fst ms), snd ms) !old_tmp_merge 
		| None -> old_tmp_merge := Merge_set.add (merge,state) !old_tmp_merge
		end;
		Hashtbl.replace true_tmp_merge levl !old_tmp_merge
	end

let clear_true_tmp_merge levl =
	Merge_set.iter (fun (m,s) -> if is_in_false_merge s levl then union_to_false_merge m levl else union_to_true_merge m levl) (Hashtbl.find true_tmp_merge levl);
	Hashtbl.replace true_tmp_merge levl (Merge_set.empty)

let is_in_true_tmp_merge s levl = 
	match Merge_set.find_first_opt (fun (m,st) -> State_set.mem s m) (Hashtbl.find true_tmp_merge levl) with
	| None -> false
	| _ -> true


let add_to_false_tmp_merge merge state levl = 
	if not (State_set.is_empty merge) then begin
		let old_tmp_merge = ref (Hashtbl.find false_tmp_merge levl) in begin
		match Merge_set.find_first_opt (fun (m,s) -> State_set.mem state m) !old_tmp_merge with
		| Some ms -> old_tmp_merge := Merge_set.remove ms !old_tmp_merge; old_tmp_merge := Merge_set.add (State_set.union merge (fst ms), snd ms) !old_tmp_merge 
		| None -> old_tmp_merge := Merge_set.add (merge,state) !old_tmp_merge
		end;
		Hashtbl.replace false_tmp_merge levl !old_tmp_merge
	end

let clear_false_tmp_merge levl =
	Merge_set.iter (fun (m,s) -> if is_in_true_merge s levl then union_to_true_merge m levl else union_to_false_merge m levl) (Hashtbl.find false_tmp_merge levl);
	Hashtbl.replace false_tmp_merge levl (Merge_set.empty)

let is_in_false_tmp_merge s levl = 
	match Merge_set.find_first_opt (fun (m,st) -> State_set.mem s m) (Hashtbl.find false_tmp_merge levl) with
	| None -> false
	| _ -> true


let in_global_merge s level = 
	State_set.mem s (Hashtbl.find merges level)

let add_to_global_merge ss level = 
	let sts = Hashtbl.find merges level in
	Hashtbl.replace merges level (State_set.fold (fun elem b -> State_set.add elem b) ss sts)
    
let clear_global_merge level = 
	Hashtbl.replace merges level (State_set.empty)
let get_global_merge level = 
	Hashtbl.find merges level


let generate_EX_cont gamma fairs levl x fml next contl contr = 
    (* State_set.fold (fun elem b ->
        Cont (State_set.empty, fresh_fairs fairs, levl^"1", And (subst_s fml x (State elem), EG (SVar "y", Top, State elem)), contl, b, [], [])) next contr *)
		let ffairs = fresh_fairs fairs in
		if !has_fairs then
			State_set.fold (fun elem b ->
				Cont (State_set.empty, ffairs, levl^"1", subst_s fml x (State elem), Cont(State_set.empty, ffairs, "-1", EG(SVar "y", Top, State elem), contl, b, [], []), b, [], [])
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
				Cont (State_set.empty, ffairs, levl^"1", subst_s fml x (State elem), b, Cont(State_set.empty, ffairs, "-1", EG(SVar "y", Top, State elem), contr, b, [], []), [], [])
			) next contl
		else 
			State_set.fold ( fun elem b ->
				Cont(State_set.empty, ffairs, levl^"1", subst_s fml x (State elem), b, contr, [], [])
			) next contl
		

let generate_EG_cont gamma fairs level x fml s next contl contr =
	let level1 = level^"1" in
    let nested = State_set.fold 
        (fun elem b -> 
            Cont (State_set.add s gamma, fairs, level, EG(x, fml, State elem), contl,  b, [], [])) next (add_false_to_cont level (s) contr) in
	Cont (State_set.empty, fresh_fairs fairs, level1, subst_s fml x (State s), nested, add_false_to_cont level (s) contr, [], [])

let generate_AF_cont gamma fairs levl x fml s next contl contr =
	let level1 = levl^"1" in 
    let nested = State_set.fold
        (fun elem b ->
            Cont (State_set.add s gamma, fairs, levl, AF(x, fml, State elem), b, contr, [], [])) next (add_true_to_cont levl (s) contl) in
	Cont (State_set.empty, fresh_fairs fairs, level1, subst_s fml x (State s), add_true_to_cont levl (s) contl, nested, [], [])

let generate_EU_cont gamma fairs levl x y fml1 fml2 s next contl contr = 
	let levl1 = levl^"1"
	and levl2 = levl^"2" in
	let fresh_fairs = (if !orig_fairs = [] then fresh_fairs fairs else !orig_fairs) in
	(* let gamma' = State_set.add s gamma in *)
	(*let mk_fair_contl s1 cl cr = Cont (State_set.empty, fresh_fairs, "-1", EG (SVar "e", Top, (State s1)), cl, cr) in *)
	(* let contr = add_false_to_cont levl s contr in *)
    let nested = State_set.fold
        (fun elem b -> 
            Cont (State_set.singleton s, fairs, levl, EU(x, y, fml1, fml2, State elem), add_true_to_cont levl elem contl, b, [], [])) next contr in
		if !has_fairs then 
			Cont (State_set.empty, fresh_fairs, levl2, subst_s fml2 y (State s), 
			Cont (State_set.empty, fresh_fairs, "-1", EG (SVar "e", Top, (State s)), add_true_to_cont levl s contl, contr, [], []),
			Cont (State_set.empty, fresh_fairs, levl1, subst_s fml1 x (State s),
				nested,
				contr, 
				[], []),
			[], [])
		else
			Cont (State_set.empty, fresh_fairs, levl2, subst_s fml2 y (State s), 
			add_true_to_cont levl s contl,
			Cont (State_set.empty, fresh_fairs, levl1, subst_s fml1 x (State s),
				nested,
				contr, 
				[], []),
			[], [])

let generate_AR_cont gamma fairs levl x y fml1 fml2 s next contl contr = 
	let levl1 = levl^"1"
	and levl2 = levl^"2" in
	let fresh_fairs = (if !orig_fairs = [] then fresh_fairs fairs else !orig_fairs) in
	(* let gamma' = State_set.add s gamma in *)
	(* let contl = add_true_to_cont levl s contl in *)
    let nested = State_set.fold
        (fun elem b ->
			Cont (State_set.singleton s, fairs, levl, AR (x, y, fml1, fml2, State elem), b, add_false_to_cont levl elem contr, [], [])) next contl in
		if !has_fairs then 
			Cont (State_set.empty, fresh_fairs, levl2, subst_s fml2 y (State s),
			Cont (State_set.empty, fresh_fairs, levl1, subst_s fml1 x (State s), 
				contl,
				nested,
				[], []),
			Cont (State_set.empty, fresh_fairs, "-1", EG (SVar "e", Top, (State s)), 
			add_false_to_cont levl s contr, 
				contl,
				[], []),
			[], [])
		else
			Cont (State_set.empty, fresh_fairs, levl2, subst_s fml2 y (State s),
			Cont (State_set.empty, fresh_fairs, levl1, subst_s fml1 x (State s), 
				contl,
				nested,
				[], []),
			add_false_to_cont levl s contr,
			[], [])

let rec satisfy_fair fml s modl =
	prove_fairs (Cont(State_set.empty, [], "0", subst_s fml (SVar "s") (State s), Basic true, Basic false, [], [])) modl

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
			List.iter (fun (a, b) -> if a<>"-1" then add_to_true_merge b a ) ts;
			List.iter (fun (a, b) -> if a<>"-1" then add_to_false_merge b a ) fs
		);
		(* print_endline (levl^"<-->"^(fml_to_string fml)); *)
		begin match fml with
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
				if (levl <> "-1") && (is_in_true_merge s levl) then begin
					union_to_true_merge gamma levl;
					prove_fairs contl modl 
				end else if (levl <> "-1") && (is_in_false_merge s levl) then 
					prove_fairs contr modl 
				else if State_set.mem s gamma then  
					let is_fair = list_conditional fairs true (fun (e, ss) -> State_set.mem s ss) in
					if is_fair = true then begin
						(if levl <> "-1" then union_to_true_merge gamma levl);
						prove_fairs contl modl
					end else begin
						(* union_to_true_merge gamma levl; *)
						prove_fairs contr modl
					end
				else
					let next = next s modl.transitions modl.var_index_tbl in
					let fairs_new = List.map (fun (e, ss) -> 
						if satisfy_fair e s modl then (e, State_set.add s gamma) else (e,ss)) fairs in
              prove_fairs (generate_EG_cont gamma fairs_new levl x fml1 s next contl contr) modl
		| AF (x, fml1, State s) -> 
				if is_in_true_merge s levl then prove_fairs contl modl else
				if is_in_false_merge s levl then begin 
					union_to_false_merge gamma levl;
					prove_fairs contr modl 
				end else begin if State_set.mem s gamma then 
					let is_fair = list_conditional fairs true (fun (e, ss) -> State_set.mem s ss) in
					if is_fair = true then begin 
						union_to_false_merge gamma levl;
						prove_fairs contr modl
					end else (prove_fairs contl modl)
				else begin
							let next = next s modl.transitions modl.var_index_tbl in
							let fairs_new = List.map (fun (e, ss) -> if satisfy_fair e s modl then (e, State_set.add s gamma) else (e,ss)) fairs in
							prove_fairs (generate_AF_cont gamma fairs_new levl x fml1 s next contl contr) modl
					end
				end
		| EU (x, y, fml1, fml2, State s) -> 
				if State_set.is_empty gamma then begin
					clear_false_merge levl;
				end else
					(*union_to_false_merge gamma levl*)();
				if is_in_true_merge s levl then
					prove_fairs contl modl
				else if (is_in_false_merge s levl) then begin
					(* union_to_false_merge gamma levl; *)
					prove_fairs contr modl
				end else 
					(add_to_false_merge s levl;
					let fm = Hashtbl.find false_merge levl in
					let next = State_set.filter (fun st -> not (State_set.mem st fm)) (next s modl.transitions modl.var_index_tbl) in
					(* let next = next s modl.transitions modl.var_index_tbl in *)
					prove_fairs (generate_EU_cont gamma fairs levl x y fml1 fml2 s next contl contr) modl)
		| AR (x, y, fml1, fml2, State s) ->
				if State_set.is_empty gamma then
					clear_true_merge levl
				else
					(*union_to_true_merge gamma levl*)();
				if is_in_false_merge s levl then
					prove_fairs contr modl
				else if (is_in_true_merge s levl)then begin
					(* union_to_true_merge gamma levl; *)
					prove_fairs contl modl
				end else 
					(add_to_true_merge s levl;
					let tm = Hashtbl.find true_merge levl in
					let next = State_set.filter (fun st -> not (State_set.mem st tm)) (next s modl.transitions modl.var_index_tbl) in
					(* let next = next s modl.transitions modl.var_index_tbl in *)
					prove_fairs (generate_AR_cont gamma fairs levl x y fml1 fml2 s next contl contr) modl)
		| _ -> (print_endline ("Unable to prove: "^(fml_to_string fml)); raise Unable_to_prove)
		end

let rec prove_model modl = 
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
			 
let rec prove_modelb modl = 
	orig_fairs := fresh_fairs_modl modl;
	let s, fml = List.hd modl.spec_list in 
	let nnf_fml = nnf fml in 
	pre_process_merges (select_sub_fmls (sub_fmls nnf_fml "1"));
	let b = (prove_fairs (Cont (State_set.empty, List.map (fun e -> (e, State_set.empty)) modl.fairness, "1", Fformula.subst_s (nnf_fml) (SVar "ini") (State modl.init_assign), Basic true, Basic false, [], [])) modl) in
	b




