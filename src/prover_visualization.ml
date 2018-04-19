open Expr
open Formula
open Interp
open Printf
open Communicate

module State_key = struct
	type t = value
	let compare = Pervasives.compare
end;;
module State_set = Set.Make(State_key)


let next s runtime modul = 
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
	(*if State_set.is_empty !next_states then
		next_states := State_set.singleton s;*)
	if State_set.is_empty !next_states then begin
		print_endline ("deadlock detected in state: "^(str_value s));
		exit 1
	end;
	!next_states

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
			let str_gamma = (State_set.fold (fun a b -> (str_state (State a))^" "^b) gamma "") in
			(if str_gamma = "" then "" else str_gamma^"") ^"|- "^(str_fml fml)) in
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

let state_tbl : ((value, int)Hashtbl.t) = Hashtbl.create 100
let state_struct_tbl = Hashtbl.create 100
let current_state_id = ref 0
let new_state_id () = incr current_state_id; !current_state_id 

(* produce new continuations *)
let rec make_ax_cont gamma s fml id levl sl contl contr = 
	let rec tmp_ax_cont sts = 
		State_set.fold (fun a b -> let nid = new_id() in (fun () -> Cont (gamma, Formula.subst_s fml s (State a), (nid), levl, (fun () -> add_premises proof id nid; b()), (fun () -> add_premises counterexample id nid; contr ())))) sts contl in
	tmp_ax_cont sl 

let rec make_ex_cont gamma s fml id levl sl contl contr =
	let rec tmp_ex_cont sts = 
		State_set.fold (fun a b -> let nid = new_id() in (fun () -> Cont (gamma, Formula.subst_s fml s (State a), (nid), levl, (fun () -> add_premises proof id nid; contl ()), (fun () -> add_premises counterexample id nid; b())))) sts contr in
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

let rec prove cont runtime modul = 
	match cont with
	| Basic b -> b
	| Cont (gamma, fml, id, levl, contl, contr) -> 
		(Hashtbl.add sequents id (gamma, fml));
		(match fml with
		| Top -> prove (contl()) runtime modul
		| Bottom -> prove (contr()) runtime modul
		| Atomic (s, sl) -> 
			if prove_atomic s sl runtime modul then prove (contl()) runtime modul else prove (contr()) runtime modul
		| Neg Atomic (s, sl) -> 
			if prove_atomic s sl runtime modul then prove (contr()) runtime modul else prove (contl()) runtime modul
		| And (fml1, fml2) -> 
			let id1 = new_id() 
			and id2 = new_id() in
			prove (Cont (State_set.empty, fml1, (id1), (levl^"1"), (fun () -> Cont (State_set.empty, fml2, (id2), (levl^"2"), (fun () -> add_premises proof id (id1); add_premises proof id (id2); contl()), (fun () -> add_premises counterexample id (id2); contr()))), (fun () -> add_premises counterexample id (id1); contr()))) runtime modul
		| Or (fml1, fml2) -> 
			let id1 = new_id() 
			and id2 = new_id() in
			prove (Cont (State_set.empty, fml1, (id1), (levl^"1"), (fun () -> add_premises proof id (id1); contl()), (fun () -> Cont (State_set.empty, fml2, (id2), (levl^"2"), (fun () -> add_premises proof id (id2); contl()), (fun () -> add_premises counterexample id (id1); add_premises counterexample id (id2); contr()))))) runtime modul
		| AX (s, fml1, State sa) -> 
			let nexts = ((next sa runtime modul)) in
			add_next_to_state_tbl (Hashtbl.find state_tbl sa) nexts;
			prove ((make_ax_cont State_set.empty s fml1 id (levl^"1") nexts contl contr)()) runtime modul
		| EX (s, fml1, State sa) -> 
			let nexts = ((next sa runtime modul)) in
			add_next_to_state_tbl (Hashtbl.find state_tbl sa) nexts;
			prove ((make_ex_cont State_set.empty s fml1 id (levl^"1") nexts contl contr)()) runtime modul
		| AF (s, fml1, State sa) -> 
			if State_set.mem sa gamma then 
				(add_merge merges levl gamma; prove (contr()) runtime modul) 
			else 
				(if state_in_merge merges levl sa then 
					prove (contr()) runtime modul 
				else begin
					let id1 = new_id() in
					let nexts = ((next sa runtime modul)) in
					add_next_to_state_tbl (Hashtbl.find state_tbl sa) nexts;
					prove (Cont (State_set.empty, Formula.subst_s fml1 s (State sa), (id1), (levl^"1"), (fun () -> add_premises proof id (id1); contl()), (fun () -> add_premises counterexample id (id1); (make_af_cont (State_set.add sa gamma) s fml1 id levl nexts contl contr)()))) runtime modul
				end
				)
		| EG (s, fml1, State sa) -> 
			if State_set.mem sa gamma then 
				(add_merge merges levl gamma; prove (contl()) runtime modul) 
			else
				(if state_in_merge merges levl sa then 
					prove (contl()) runtime modul 
				else begin
					let id1 = new_id() in
					let nexts = ((next sa runtime modul)) in
					add_next_to_state_tbl (Hashtbl.find state_tbl sa) nexts;
					prove (Cont (State_set.empty, Formula.subst_s fml1 s (State sa), (id1), (levl^"1"), (fun () -> add_premises proof id (id1);(make_eg_cont (State_set.add sa gamma) s fml1 id levl nexts contl contr)()), (fun () -> add_premises counterexample id (id1); contr()))) runtime modul
				end
				)
		| AR(x, y, fml1, fml2, State sa) -> 
			if (State_set.is_empty gamma) then 
				Hashtbl.replace merges levl State_set.empty 
			else 
				add_merge merges levl gamma; 
			if State_set.mem sa gamma then 
				(add_merge merges levl gamma; prove (contl()) runtime modul) 
			else 
				(if state_in_merge merges levl sa then 
					prove (contl()) runtime modul 
				else begin
					let id1 = new_id() and id2 = new_id() in
					let nexts = ((next sa runtime modul)) in
					add_next_to_state_tbl (Hashtbl.find state_tbl sa) nexts;
					prove (Cont (State_set.empty, Formula.subst_s fml2 y (State sa), (id2), (levl^"2"), (fun () -> Cont (State_set.empty, Formula.subst_s fml1 x (State sa), (id1), (levl^"1"), (fun () -> add_premises proof id (id1); add_premises proof id (id2); contl()), (fun () -> add_premises counterexample id (id1); (make_ar_cont (State_set.singleton sa) x y fml1 fml2 id levl nexts contl contr)()))), (fun () -> add_premises counterexample id (id+2); contr()))) runtime modul
				end
				)
		| EU (s, s', fml1, fml2, State sa) -> 
			if (State_set.is_empty gamma) then 
				Hashtbl.replace merges levl State_set.empty 
			else add_merge merges levl gamma; 
			if State_set.mem sa gamma then 
				(prove (contr()) runtime modul) 
			else
				(if state_in_merge merges levl sa then 
					prove (contr()) runtime modul 
				else begin
					let id1 = new_id() and id2 = new_id() in
					let nexts = ((next sa runtime modul)) in
					add_next_to_state_tbl (Hashtbl.find state_tbl sa) nexts;
					((prove (Cont (State_set.empty, Formula.subst_s fml2 s' (State sa), (id2), (levl^"2"), (fun () -> add_premises proof id (id2); contl()), (fun () -> Cont (State_set.empty, Formula.subst_s fml1 s (State sa), (id1), (levl^"1"), (fun () -> add_premises proof id (id1); (make_eu_cont (State_set.singleton sa) s s' fml1 fml2 id levl nexts contl contr)()), (fun () -> add_premises counterexample id (id1); add_premises counterexample id (id2); contr()))))) runtime modul))
				end
				)  
		| _ -> raise Unable_to_prove
		)

let send_proof_tree id = 
	proof_session_id := id;
	Communicate.create_proof_session id;
	(*let rec str_sequent seqt = 
		(let gamma = fst seqt and fml = snd seqt in
			let str_gamma = (State_set.fold (fun a b -> (str_state a)^"\r\n"^b) gamma "") in
			(if str_gamma = "" then "" else str_gamma^"") ^"|- "^(str_fml fml)) in
	Hashtbl.iter (fun a b -> add_node id (string_of_int a) (str_sequent b) "Proved") sequents;*)
	let rec str_sequent seqt = 
		(let gamma = fst seqt and fml = snd seqt in
			let str_gamma = (State_set.fold (fun a b -> (str_state (State a))^" "^b) gamma "") in
			(if str_gamma = "" then "" else str_gamma^"") ^"|- "^(str_fml fml)) in
	(* let raw_out = open_out "raw_tree.txt" in
	output_string raw_out "TREE\n";
	Hashtbl.iter (fun id seqt -> output_string raw_out ((string_of_int id)^":"^(str_sequent seqt)^"\n")) sequents;
	Hashtbl.iter (fun id hyps -> 
		output_string raw_out ((string_of_int id)^"-->");
		List.iter (fun hid-> output_string raw_out ((string_of_int hid)^" ")) hyps;
		output_string raw_out "\n") proof;
	flush raw_out;
	print_endline "output to raw_tree.txt complete"; *)
	let tmp_fmls = ref [0] in
	while !tmp_fmls <> [] do
		try
		let current_id = List.hd !tmp_fmls in
		let tmp_is = Hashtbl.find proof current_id in
		Communicate.add_node id (string_of_int current_id) (str_sequent (Hashtbl.find sequents current_id)) "Proved"; 
		List.iter (fun a -> 
			Communicate.add_node id (string_of_int a) (str_sequent (Hashtbl.find sequents a)) "Proved";
			Communicate.add_edge (id) (string_of_int current_id) (string_of_int a) ""
		) tmp_is;
		tmp_fmls := tmp_is @ (List.tl !tmp_fmls) 
		with Not_found -> (tmp_fmls := List.tl !tmp_fmls)
	done

let rec states_in_fml fml = 
	match fml with
	| Atomic (_, ss) -> 
		let tmp_states = ref [] in
		List.iter (fun s ->
			match s with
			| State st -> tmp_states := st :: !tmp_states
			| _ -> ()
		) ss;
		!tmp_states
	| And (fml1, fml2) -> (states_in_fml fml1) @ (states_in_fml fml2)
	| Or (fml1, fml2) -> (states_in_fml fml1) @ (states_in_fml fml2)
	| AX (x, fml1, State st) -> [st]
	| EX (x, fml1, State st) -> [st]
	| AF (x, fml1, State st) -> [st]
	| EG (x, fml1, State st) -> [st]
	| AR (x, y, fml1, fml2, State st) -> [st]
	| EU (x, y, fml1, fml2, State st) -> [st]
	| _ -> []


let send_state_graph id = 
	state_session_id := id;
	Communicate.create_state_session id;
	(* let raw_out = open_out "raw_digraph.txt" in
	output_string raw_out "DIGRAPH\n";
	Hashtbl.iter (fun a b -> output_string raw_out ((string_of_int b)^":"^(str_state (State a))^"\n")) state_tbl;
	Hashtbl.iter (fun a b -> 
		output_string raw_out ((string_of_int a)^"-->");
		List.iter (fun c-> output_string raw_out ((string_of_int c)^" ")) b;
		output_string raw_out "\n"
		) state_struct_tbl;
	flush raw_out;
	print_endline "output to raw_digraph.txt complete"; *)
	Hashtbl.iter (fun a b -> Communicate.add_node id (string_of_int b) (str_state (State a)) "") state_tbl;
	Hashtbl.iter (fun a b ->
		List.iter (fun c -> Communicate.add_edge id (string_of_int a) (string_of_int c) "") b
	) state_struct_tbl

let parse runtime modul msg = 
    match msg with
    | Highlight_node (sid, nid) -> 
		feedback_ok sid;
        printf "Highlight node %s in session %s\n" nid sid;
		let fml = snd (Hashtbl.find sequents (int_of_string nid)) in
		let ias = states_in_fml fml in
		List.iter (fun a ->
			let id_a = Hashtbl.find state_tbl a in
			highlight_node !state_session_id (string_of_int id_a)
		) ias;
        flush stdout
	| Unhighlight_node (sid, nid) ->
		feedback_ok sid;
        printf "Unhighlight node %s in session %s\n" nid sid;
		let fml = snd (Hashtbl.find sequents (int_of_string nid)) in
		let ias = states_in_fml fml in
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
	| Request (sid, attris) ->
		feedback_ok sid;
		let nids = ref [] in
		Hashtbl.iter (fun id (gamma, fml) -> 
			let states = states_in_fml fml in
			let satisfy_attributes = List.exists (fun state -> 
				List.fold_left (fun acc attri ->
					if not acc then acc 
					else begin
						if String.get attri 0 = '!' then
							let neg_attri = String.sub attri 1 (List.length attri - 1) in
							if not (prove_atomic neg_attri [state]) then true else false
						else 
							prove_atomic attri [state]
					end
				) true attris
			) states in
			if satisfy_attributes then
				nids := (string_of_int id) :: !nids
		) sequents;
		response sid attris !nids

	(* | Response (sid, attris, nids) -> *)

    | _ -> 
        printf "Not supposed to recieve this message %s\n" (str_msg msg);
        flush stdout


let rec get_init_state_in_fml fml = 
	match fml with
	| And (fml1, fml2) | Or (fml1, fml2) -> get_init_state_in_fml fml1
	| AX (x, fml1, State st) -> st
	| EX (x, fml1, State st) -> st
	| AF (x, fml1, State st) -> st
	| EG (x, fml1, State st) -> st
	| AR (x, y, fml1, fml2, State st) -> st
	| EU (x, y, fml1, fml2, State st) -> st
	| _ -> print_endline "cannot find init state"; exit 1

let rec prove_model runtime modul visualize_addr = 
	let spec_lst = runtime.model.properties in
	let rec prove_lst lst = 
	match lst with
	| [] -> ()
	| (s, fml) :: lst' -> 
		((let nnf_fml = nnf fml in 
		print_endline (str_fml (nnf_fml));
		pre_process_merges (select_sub_fmls (sub_fmls nnf_fml "1"));
		let init_state_id = new_state_id() in
		Hashtbl.add state_tbl (get_init_state_in_fml nnf_fml) init_state_id;
		Hashtbl.add state_struct_tbl init_state_id [];
		let b = (prove (Cont (State_set.empty, (nnf_fml), 0, "1", (fun () -> Basic true), (fun () -> Basic false))) runtime modul) in
			print_endline (s^": "^(string_of_bool b));
			(*print_endline (s ^ " is " ^ (if b then "true, proof output to \""^outname^"\"." else "false, counterexample output to \""^outname^"\".")); *)
			(*output_result b s sequents (if b then proof else counterexample) out modl.var_list; 
			output_string out "***********************************ouput complete**************************************";
			flush out; *)
			let i,o = Communicate.init visualize_addr in
			ignore(Thread.create (fun o -> sending o) o);
			send_proof_tree s;
			send_state_graph ("State graph for "^s);
			receiving i (parse runtime modul)
			(*Hashtbl.clear sequents; 
			Hashtbl.clear proof*)
			);
			prove_lst lst') in prove_lst spec_lst
