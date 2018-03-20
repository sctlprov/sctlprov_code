open Printf
open Oterm
open Oformula
open Omodul
open Ocommunicate

type continuation = 
	| Basic of bool
	| Cont of State_set.t * formula * int * string * (unit -> continuation) * (unit -> continuation)

type fml_state_tbl = (string, State_set.t) Hashtbl.t

exception Error_proving_atomic
exception Unable_to_prove

(*functions for the output*)
let proof_session_id = ref ""
let state_session_id = ref ""
let sequents = Hashtbl.create 100
let proof = Hashtbl.create 100
let counterexample = Hashtbl.create 100
let output_result b s seqts prof out vt = 
	output_string out (if b then ("proof for "^ s ^":\r\n") else ("counterexample for "^s^":\r\n"));
	let tmp_queue = ref [0] in
	let rec str_int_list il = 
		(match il with
		| [] -> ""
		| [i] -> string_of_int i
		| i :: il' -> (string_of_int i)^", "^(str_int_list il')) in
	let rec str_sequent seqt = 
		(let gamma = fst seqt and fml = snd seqt in
			let str_gamma = (State_set.fold (fun a b -> (str_modl_state vt a)^"\r\n"^b) gamma "") in
			(if str_gamma = "" then "" else str_gamma^"") ^"|- "^(str_modl_fml vt fml)) in
	let rec output_tmp_queue () = 
		if (List.length !tmp_queue > 0) then 
			(let h = List.hd !tmp_queue in 
			output_string out ((string_of_int h)^": "^(str_sequent (try Hashtbl.find sequents h with Not_found -> print_endline ("not found sequent wit index "^(string_of_int h)); exit 1))^"\t\t"); 			
			output_string out ("["^(str_int_list (try Hashtbl.find (prof) h with Not_found -> []))^"]\r\n\r\n"); 
			tmp_queue := (List.tl !tmp_queue) @ (try Hashtbl.find prof h with Not_found -> []); 
			output_tmp_queue ()) in
	output_tmp_queue ()
let current_id = ref 0
let new_id () = current_id := !current_id + 1; !current_id

(*whether state s is already in an existing merge*)
let merges = Hashtbl.create 10
let pre_process_merges sub_fml_tbl = 
	Hashtbl.iter (fun a b -> Hashtbl.add merges a State_set.empty) sub_fml_tbl
let post_process_merges () = 
	Hashtbl.iter (fun a b -> print_endline (a ^ ": " ^ (string_of_int (State_set.cardinal b)))) merges

let state_in_merge merg fml st = 
	let sts = Hashtbl.find merg fml in State_set.mem st sts
let add_merge merg fml sts = 
	let sts' = Hashtbl.find merg fml in
	Hashtbl.replace merg fml (State_set.union sts sts')

let add_premises prf fid pid = 
	try
		Hashtbl.replace prf fid (pid :: (Hashtbl.find prf fid))
	with Not_found -> Hashtbl.add prf fid [pid]

let state_tbl : ((int array, int)Hashtbl.t) = Hashtbl.create 100
let state_struct_tbl = Hashtbl.create 100
let current_state_id = ref 0
let new_state_id () = incr current_state_id; !current_state_id 

(* produce new continuations *)
let rec make_ax_cont gamma s fml id levl sl contl contr = 
	let rec tmp_ax_cont sts = 
		State_set.fold (fun a b -> let nid = new_id() in (fun () -> Cont (gamma, Oformula.subst_s fml s (State a), (nid), levl, (fun () -> add_premises proof id nid; b()), (fun () -> add_premises counterexample id nid; contr ())))) sts contl in
	tmp_ax_cont sl 

let rec make_ex_cont gamma s fml id levl sl contl contr =
	let rec tmp_ex_cont sts = 
		State_set.fold (fun a b -> let nid = new_id() in (fun () -> Cont (gamma, Oformula.subst_s fml s (State a), (nid), levl, (fun () -> add_premises proof id nid; contl ()), (fun () -> add_premises counterexample id nid; b())))) sts contr in
	tmp_ex_cont sl

let rec make_af_cont gamma s fml id levl sl contl contr =
	let rec tmp_af_cont sts = 
		State_set.fold (fun a b -> let nid = new_id() in (fun () -> Cont (gamma, AF (s, fml, (State a)), (nid), levl, (fun () -> add_premises proof id nid; b()), (fun () -> add_premises counterexample id nid; contr ())))) sts contl in 
	tmp_af_cont sl


let rec make_eg_cont gamma s fml id levl sl contl contr =
	let rec tmp_eg_cont sts = 
		State_set.fold (fun a b -> let nid = new_id() in (fun () -> Cont (gamma, EG (s, fml, (State a)), (nid), levl, (fun () -> add_premises proof id nid; contl ()), (fun () -> add_premises counterexample id nid; b())))) sts contr in
	tmp_eg_cont sl

let rec make_ar_cont gamma s s' fml1 fml2 id levl sl contl contr =
	let rec tmp_ar_cont sts = 
		State_set.fold (fun a b -> let nid = new_id() in (fun () -> Cont (gamma, AR (s, s', fml1, fml2, (State a)), (nid), levl, (fun () -> add_premises proof id nid; b()), (fun () -> add_premises counterexample id nid; contr ())))) sts contl in 
	tmp_ar_cont sl


let rec make_eu_cont gamma s s' fml1 fml2 id levl sl contl contr =
	let rec tmp_eu_cont sts = 
		State_set.fold (fun a b -> let nid = new_id() in (fun () -> Cont (gamma, EU (s, s', fml1, fml2, (State a)), (nid), levl, (fun () -> add_premises proof id nid; contl ()), (fun () -> add_premises counterexample id nid; b())))) sts contr in
	tmp_eu_cont sl

let add_next_to_state_tbl id_sa nexts = 
	State_set.iter (
				fun a ->
					try
						let id_of_a = Hashtbl.find state_tbl a in
						Hashtbl.replace state_struct_tbl id_sa (id_of_a :: (Hashtbl.find state_struct_tbl id_sa))
					with Not_found -> begin
						let new_id_a = new_state_id() in
						Hashtbl.add state_tbl a new_id_a;
						Hashtbl.add state_struct_tbl new_id_a [];
						Hashtbl.add state_struct_tbl id_sa (new_id_a :: (Hashtbl.find state_struct_tbl id_sa))
					end
			) nexts
let rec prove cont modl = 
	match cont with
	| Basic b -> b
	| Cont (gamma, fml, id, levl, contl, contr) -> 
		(Hashtbl.add sequents id (gamma, fml));
		(match fml with
		| Top -> prove (contl()) modl
		| Bottom -> prove (contr()) modl
		| Atomic (s, sl) -> 
			let v = apply_atomic (Hashtbl.find modl.atomic_tbl s) sl modl.var_index_tbl in
			if v = Top then 
				(prove (contl()) modl) 
			else 
				if v = Bottom then 
					prove (contr()) modl 
				else 
					raise Error_proving_atomic
		| Neg Atomic (s, sl) -> 
			let v = apply_atomic (Hashtbl.find modl.atomic_tbl s) sl modl.var_index_tbl in
			if v = Top then 
				prove (contr()) modl 
			else 
				if v = Bottom then 
					prove (contl()) modl 
				else 
					raise Error_proving_atomic
		| And (fml1, fml2) -> 
			let id1 = new_id() 
			and id2 = new_id() in
			prove (Cont (State_set.empty, fml1, (id1), (levl^"1"), (fun () -> Cont (State_set.empty, fml2, (id2), (levl^"2"), (fun () -> add_premises proof id (id1); add_premises proof id (id2); contl()), (fun () -> add_premises counterexample id (id2); contr()))), (fun () -> add_premises counterexample id (id1); contr()))) modl
		| Or (fml1, fml2) -> 
			let id1 = new_id() 
			and id2 = new_id() in
			prove (Cont (State_set.empty, fml1, (id1), (levl^"1"), (fun () -> add_premises proof id (id1); contl()), (fun () -> Cont (State_set.empty, fml2, (id2), (levl^"2"), (fun () -> add_premises proof id (id2); contl()), (fun () -> add_premises counterexample id (id1); add_premises counterexample id (id2); contr()))))) modl
		| AX (s, fml1, State sa) -> 
			let nexts = ((next sa modl.transitions modl.var_index_tbl)) in
			add_next_to_state_tbl (Hashtbl.find state_tbl sa) nexts;
			prove ((make_ax_cont State_set.empty s fml1 id (levl^"1") nexts contl contr)()) modl
		| EX (s, fml1, State sa) -> 
			let nexts = ((next sa modl.transitions modl.var_index_tbl)) in
			add_next_to_state_tbl (Hashtbl.find state_tbl sa) nexts;
			prove ((make_ex_cont State_set.empty s fml1 id (levl^"1") nexts contl contr)()) modl
		| AF (s, fml1, State sa) -> 
			if State_set.mem sa gamma then 
				(add_merge merges levl gamma; prove (contr()) modl) 
			else 
				(if state_in_merge merges levl sa then 
					prove (contr()) modl 
				else begin
					let id1 = new_id() in
					let nexts = ((next sa modl.transitions modl.var_index_tbl)) in
					add_next_to_state_tbl (Hashtbl.find state_tbl sa) nexts;
					prove (Cont (State_set.empty, Oformula.subst_s fml1 s (State sa), (id1), (levl^"1"), (fun () -> add_premises proof id (id1); contl()), (fun () -> add_premises counterexample id (id1); (make_af_cont (State_set.add sa gamma) s fml1 id levl nexts contl contr)()))) modl
				end
				)
		| EG (s, fml1, State sa) -> 
			if State_set.mem sa gamma then 
				(add_merge merges levl gamma; prove (contl()) modl) 
			else
				(if state_in_merge merges levl sa then 
					prove (contl()) modl 
				else begin
					let id1 = new_id() in
					let nexts = ((next sa modl.transitions modl.var_index_tbl)) in
					add_next_to_state_tbl (Hashtbl.find state_tbl sa) nexts;
					prove (Cont (State_set.empty, Oformula.subst_s fml1 s (State sa), (id1), (levl^"1"), (fun () -> add_premises proof id (id1);(make_eg_cont (State_set.add sa gamma) s fml1 id levl nexts contl contr)()), (fun () -> add_premises counterexample id (id1); contr()))) modl
				end
				)
		| AR(x, y, fml1, fml2, State sa) -> 
			if (State_set.is_empty gamma) then 
				Hashtbl.replace merges levl State_set.empty 
			else 
				add_merge merges levl gamma; 
			if State_set.mem sa gamma then 
				(add_merge merges levl gamma; prove (contl()) modl) 
			else 
				(if state_in_merge merges levl sa then 
					prove (contl()) modl 
				else begin
					let id1 = new_id() and id2 = new_id() in
					let nexts = ((next sa modl.transitions modl.var_index_tbl)) in
					add_next_to_state_tbl (Hashtbl.find state_tbl sa) nexts;
					prove (Cont (State_set.empty, Oformula.subst_s fml2 y (State sa), (id2), (levl^"2"), (fun () -> Cont (State_set.empty, Oformula.subst_s fml1 x (State sa), (id1), (levl^"1"), (fun () -> add_premises proof id (id1); add_premises proof id (id2); contl()), (fun () -> add_premises counterexample id (id1); (make_ar_cont (State_set.singleton sa) x y fml1 fml2 id levl nexts contl contr)()))), (fun () -> add_premises counterexample id (id+2); contr()))) modl
				end
				)
		| EU (s, s', fml1, fml2, State sa) -> 
			if (State_set.is_empty gamma) then 
				Hashtbl.replace merges levl State_set.empty 
			else add_merge merges levl gamma; 
			if State_set.mem sa gamma then 
				(prove (contr()) modl) 
			else
				(if state_in_merge merges levl sa then 
					prove (contr()) modl 
				else begin
					let id1 = new_id() and id2 = new_id() in
					let nexts = ((next sa modl.transitions modl.var_index_tbl)) in
					add_next_to_state_tbl (Hashtbl.find state_tbl sa) nexts;
					((prove (Cont (State_set.empty, Oformula.subst_s fml2 s' (State sa), (id2), (levl^"2"), (fun () -> add_premises proof id (id2); contl()), (fun () -> Cont (State_set.empty, Oformula.subst_s fml1 s (State sa), (id1), (levl^"1"), (fun () -> add_premises proof id (id1); (make_eu_cont (State_set.singleton sa) s s' fml1 fml2 id levl nexts contl contr)()), (fun () -> add_premises counterexample id (id1); add_premises counterexample id (id2); contr()))))) modl))
				end
				)  
		| _ -> raise Unable_to_prove
		)

let send_proof_tree id vt = 
	proof_session_id := id;
	create_proof_session id;
	(*let rec str_sequent seqt = 
		(let gamma = fst seqt and fml = snd seqt in
			let str_gamma = (State_set.fold (fun a b -> (str_modl_state vt a)^"\r\n"^b) gamma "") in
			(if str_gamma = "" then "" else str_gamma^"") ^"|- "^(str_modl_fml vt fml)) in
	Hashtbl.iter (fun a b -> add_node id (string_of_int a) (str_sequent b) "Proved") sequents;*)
	let rec str_sequent seqt = 
		(let gamma = fst seqt and fml = snd seqt in
			let str_gamma = (State_set.fold (fun a b -> (str_modl_state vt a)^" "^b) gamma "") in
			(if str_gamma = "" then "" else str_gamma^"") ^"|- "^(str_modl_fml vt fml)) in
	let tmp_fmls = ref [0] in
	while !tmp_fmls <> [] do
		try
		let current_id = List.hd !tmp_fmls in
		let tmp_is = Hashtbl.find proof current_id in
		add_node id (string_of_int current_id) (str_sequent (Hashtbl.find sequents current_id)) "Proved"; 
		List.iter (fun a -> 
			add_node id (string_of_int a) (str_sequent (Hashtbl.find sequents a)) "Proved";
			add_edge (id) (string_of_int current_id) (string_of_int a) ""
		) tmp_is;
		tmp_fmls := tmp_is @ (List.tl !tmp_fmls) 
		with Not_found -> (tmp_fmls := List.tl !tmp_fmls)
	done


let send_state_graph id vt = 
	state_session_id := id;
	create_state_session id;
	Hashtbl.iter (fun a b -> add_node id (string_of_int b) (str_modl_state vt a) "") state_tbl;
	Hashtbl.iter (fun a b ->
		List.iter (fun c -> add_edge id (string_of_int a) (string_of_int c) "") b
	) state_struct_tbl

let parse msg = 
    match msg with
    | Highlight_node (sid, nid) -> 
		feedback_ok sid;
        printf "Highlight node %s in session %s\n" nid sid;
		let fml = snd (Hashtbl.find sequents (int_of_string nid)) in
		let ias = ias_in_fml fml in
		List.iter (fun a ->
			let id_a = Hashtbl.find state_tbl a in
			highlight_node !state_session_id (string_of_int id_a)
		) ias;
        flush stdout
	| Unhighlight_node (sid, nid) ->
		feedback_ok sid;
        printf "Unhighlight node %s in session %s\n" nid sid;
		let fml = snd (Hashtbl.find sequents (int_of_string nid)) in
		let ias = ias_in_fml fml in
		List.iter (fun a ->
			let id_a = Hashtbl.find state_tbl a in
			unhighlight_node !state_session_id (string_of_int id_a)
		) ias;
        flush stdout
        
    | Feedback_ok sid ->
        printf "Feedback OK received from %s\n" sid;
        flush stdout

	| Clear_color sid ->
		feedback_ok sid;
		let new_sid = if sid = !proof_session_id then !state_session_id else !proof_session_id in
		clear_color new_sid
    | _ -> 
        printf "Not supposed to recieve this message %s\n" (str_msg msg);
        flush stdout



let rec prove_model modl visualize_addr = 
	let spec_lst = modl.spec_list in
	let rec prove_lst lst = 
	match lst with
	| [] -> ()
	| (s, fml) :: lst' -> 
		((let nnf_fml = nnf fml in 
			print_endline (s^": "^(str_modl_fml modl.var_list (nnf_fml)));
			pre_process_merges (select_sub_fmls (sub_fmls nnf_fml "1"));
			let init_state_id = new_state_id() in
			Hashtbl.add state_tbl modl.init_assign init_state_id;
			Hashtbl.add state_struct_tbl init_state_id [];
			print_endline (s^": "^(string_of_bool (prove (Cont (State_set.empty, Oformula.subst_s (nnf_fml) (SVar "ini") (State modl.init_assign), 0, "1", (fun () -> Basic true), (fun () -> Basic false))) modl)));
				(*print_endline (s ^ " is " ^ (if b then "true, proof output to \""^outname^"\"." else "false, counterexample output to \""^outname^"\".")); *)
				(*output_result b s sequents (if b then proof else counterexample) out modl.var_list; 
				output_string out "***********************************ouput complete**************************************";
				flush out; *)
				let i,o = Ocommunicate.init visualize_addr in
				ignore(Thread.create (fun o -> sending o) o);
				send_proof_tree s modl.var_list;
				send_state_graph modl.name modl.var_list;
				receiving i parse
				(*Hashtbl.clear sequents; 
				Hashtbl.clear proof*)
				);
				prove_lst lst') in prove_lst spec_lst
