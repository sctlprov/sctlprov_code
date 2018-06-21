open Fterm
open Fformula
open Fmodul

module type Prover =
	sig
		type continuation = 
		| Basic of bool
		| Cont of State_set.t * formula * int * string * (unit -> continuation) * (unit -> continuation)


		type fml_state_tbl = (string, State_set.t) Hashtbl.t

		exception Error_proving_atomic
		exception Unable_to_prove

		val sequents : (int, (State_set.t * formula)) Hashtbl.t
		val proof : (int, int list) Hashtbl.t
		val counterexample : (int, int list) Hashtbl.t
		val output_result : bool -> string -> (int, (State_set.t * formula)) Hashtbl.t -> (int, int list) Hashtbl.t -> out_channel -> (string * expr_type) list -> unit
		val current_id : int ref
		val new_id : unit -> int
		
		val merges : fml_state_tbl
		val pre_process_merges : (string, formula) Hashtbl.t -> unit
		val post_process_merges : unit -> unit
		
		val state_in_merge : fml_state_tbl -> string -> (int array) -> bool
		val add_merge : fml_state_tbl -> string -> State_set.t -> unit

		val add_premises : (int, int list) Hashtbl.t -> int -> int -> unit
		val prove : continuation -> (Fmodul.model) -> bool
		val prove_model : Fmodul.model -> out_channel -> string -> unit
		val make_ax_cont : State_set.t -> state -> formula -> int -> string -> State_set.t -> (unit -> continuation) -> (unit -> continuation) -> (unit -> continuation)
		val make_ex_cont : State_set.t -> state -> formula -> int -> string -> State_set.t -> (unit -> continuation) -> (unit -> continuation) -> (unit -> continuation)
		val make_af_cont : State_set.t -> state -> formula -> int -> string -> State_set.t -> (unit -> continuation) -> (unit -> continuation) -> (unit -> continuation)
		val make_eg_cont : State_set.t -> state -> formula -> int -> string -> State_set.t -> (unit -> continuation) -> (unit -> continuation) -> (unit -> continuation)
		val make_ar_cont : State_set.t -> state -> state -> formula -> formula -> int -> string -> State_set.t -> (unit -> continuation) -> (unit -> continuation) -> (unit -> continuation)
		val make_eu_cont : State_set.t -> state -> state -> formula -> formula -> int -> string -> State_set.t -> (unit -> continuation) -> (unit -> continuation) -> (unit -> continuation)
	end

module Seq_Prover : Prover = 
	struct
	type continuation = 
		| Basic of bool
		| Cont of State_set.t * formula * int * string * (unit -> continuation) * (unit -> continuation)

	type fml_state_tbl = (string, State_set.t) Hashtbl.t

	exception Error_proving_atomic
	exception Unable_to_prove

	(*functions for the output*)
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
			(let gamma = fst seqt 
			and fml = snd seqt in
			let str_gamma = (State_set.fold (fun a b -> (str_modl_state vt a)^"\r\n"^b) gamma "") in
				(if str_gamma = "" then "" else str_gamma^"") ^"|- "^(str_modl_fml vt (if b then fml else nnf (Neg fml)))) in
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

	(* produce new continuations *)
	let rec make_ax_cont gamma s fml id levl sl contl contr = 
		let rec tmp_ax_cont sts = 
			State_set.fold (fun a b -> let nid = new_id() in (fun () -> Cont (gamma, Fformula.subst_s fml s (State a), (nid), levl, (fun () -> add_premises proof id nid; b()), (fun () -> add_premises counterexample id nid; contr ())))) sts contl in
(*			match sts with
			| [] -> contl
			| st :: sts' -> (fun () -> Cont (gamma, Fformula.subst_s fml s (State st), (tmp_id := !tmp_id + 1; !tmp_id), levl, (fun () -> add_premises proof id !tmp_id; (tmp_ax_cont sts')()), (fun () -> add_premises counterexample id !tmp_id; contr ()))) in*)
		tmp_ax_cont sl 

	(*	State_set.fold (fun a c -> Cont (gamma, Fformula.subst_s fml s (State a), levl, c, contr)) sl contl *)
	let rec make_ex_cont gamma s fml id levl sl contl contr =
		let rec tmp_ex_cont sts = 
			State_set.fold (fun a b -> let nid = new_id() in (fun () -> Cont (gamma, Fformula.subst_s fml s (State a), (nid), levl, (fun () -> add_premises proof id nid; contl ()), (fun () -> add_premises counterexample id nid; b())))) sts contr in
(*			match sts with
			| [] -> contr
			| st :: sts' -> (fun () -> Cont (gamma, Fformula.subst_s fml s (State st), (tmp_id := !tmp_id + 1; !tmp_id), levl, (fun () -> add_premises proof id !tmp_id; contl ()), (fun () -> add_premises counterexample id !tmp_id; (tmp_ex_cont sts')()))) in *)
		tmp_ex_cont sl

	(*	State_set.fold (fun a c -> Cont (gamma, Fformula.subst_s fml s (State a), levl, contl, c)) sl contr *)
	let rec make_af_cont gamma s fml id levl sl contl contr =
		let rec tmp_af_cont sts = 
			State_set.fold (fun a b -> let nid = new_id() in (fun () -> Cont (gamma, AF (s, fml, (State a)), (nid), levl, (fun () -> add_premises proof id nid; b()), (fun () -> add_premises counterexample id nid; contr ())))) sts contl in 
	(*		match sts with
			| [] -> contl
			| st :: sts' -> (fun () -> Cont (gamma, AF (s, fml, (State st)), (tmp_id := !tmp_id + 1; !tmp_id), levl, (fun () -> add_premises proof id !tmp_id; (tmp_af_cont sts')()), (fun () -> add_premises counterexample id !tmp_id; contr ()))) in *)
		tmp_af_cont sl


	(*	State_set.fold (fun a c -> Cont (gamma, AF (s, fml, (State a)), levl, c, contr)) sl contl *)
	let rec make_eg_cont gamma s fml id levl sl contl contr =
		let rec tmp_eg_cont sts = 
			State_set.fold (fun a b -> let nid = new_id() in (fun () -> Cont (gamma, EG (s, fml, (State a)), (nid), levl, (fun () -> add_premises proof id nid; contl ()), (fun () -> add_premises counterexample id nid; b())))) sts contr in
	(*		match sts with
			| [] -> contr
			| st :: sts' -> (fun () -> Cont (gamma, EG (s, fml, (State st)), (tmp_id := !tmp_id + 1; !tmp_id), levl, (fun () -> add_premises proof id !tmp_id; contl ()), (fun () -> add_premises counterexample id !tmp_id; (tmp_eg_cont sts')()))) in *)
		tmp_eg_cont sl

		(*State_set.fold (fun a c -> Cont (gamma, EG (s, fml, (State a)), levl, contl, c)) sl contr *)
	let rec make_ar_cont gamma s s' fml1 fml2 id levl sl contl contr =
		let rec tmp_ar_cont sts = 
			State_set.fold (fun a b -> let nid = new_id() in (fun () -> Cont (gamma, AR (s, s', fml1, fml2, (State a)), (nid), levl, (fun () -> add_premises proof id nid; b()), (fun () -> add_premises counterexample id nid; contr ())))) sts contl in 
	(*		match sts with
			| [] -> contl
			| st :: sts' -> (fun () -> Cont (gamma, AR (s, s', fml1, fml2, (State st)), (tmp_id := !tmp_id + 1; !tmp_id), levl, (fun () -> add_premises proof id !tmp_id; (tmp_ar_cont sts')()), (fun () -> add_premises counterexample id !tmp_id; contr ()))) in *)
		tmp_ar_cont sl


		(*State_set.fold (fun a c -> Cont (gamma, AR (s, s', fml1, fml2, (State a)), levl, c, contr)) sl contl *)
	let rec make_eu_cont gamma s s' fml1 fml2 id levl sl contl contr =
		let rec tmp_eu_cont sts = 
			State_set.fold (fun a b -> let nid = new_id() in (fun () -> Cont (gamma, EU (s, s', fml1, fml2, (State a)), (nid), levl, (fun () -> add_premises proof id nid; contl ()), (fun () -> add_premises counterexample id nid; b())))) sts contr in
		(*	match sts with
			| [] -> contr
			| st :: sts' -> (fun () -> Cont (gamma, EU (s, s', fml1, fml2, (State st)), (tmp_id := !tmp_id + 1; !tmp_id), levl, (fun () -> add_premises proof id !tmp_id; contl ()), (fun () -> add_premises counterexample id !tmp_id; (tmp_eu_cont sts')()))) in *)
		tmp_eu_cont sl

		(*State_set.fold (fun a c -> Cont (gamma, EU (s, s', fml1, fml2, (State a)), levl, contl, c)) sl contr*)

	(* proving function, two parameters, first a continuation, second a atomic formula context *)
	let rec prove cont modl = 
		match cont with
		| Basic b -> b
		| Cont (gamma, fml, id, levl, contl, contr) -> (Hashtbl.add sequents id (gamma, fml));(
			match fml with
			| Top -> prove (contl()) modl
			| Bottom -> prove (contr()) modl
			| Atomic (s, sl) -> let v = apply_atomic (Hashtbl.find modl.atomic_tbl s) sl modl.var_index_tbl in
									if v = Top then (prove (contl()) modl) else if v = Bottom then prove (contr()) modl else raise Error_proving_atomic
			| Neg Atomic (s, sl) -> let v = apply_atomic (Hashtbl.find modl.atomic_tbl s) sl modl.var_index_tbl in
										if v = Top then prove (contr()) modl else if v = Bottom then prove (contl()) modl else raise Error_proving_atomic
			| And (fml1, fml2) -> let id1 = new_id() and id2 = new_id() in
				prove (Cont (State_set.empty, fml1, (id1), (levl^"1"), (fun () -> Cont (State_set.empty, fml2, (id2), (levl^"2"), (fun () -> add_premises proof id (id1); add_premises proof id (id2); contl()), (fun () -> add_premises counterexample id (id2); contr()))), (fun () -> add_premises counterexample id (id1); contr()))) modl
			| Or (fml1, fml2) -> let id1 = new_id() and id2 = new_id() in
				prove (Cont (State_set.empty, fml1, (id1), (levl^"1"), (fun () -> add_premises proof id (id1); contl()), (fun () -> Cont (State_set.empty, fml2, (id2), (levl^"2"), (fun () -> add_premises proof id (id2); contl()), (fun () -> add_premises counterexample id (id1); add_premises counterexample id (id2); contr()))))) modl
			| AX (s, fml1, State sa) -> prove ((make_ax_cont State_set.empty s fml1 id (levl^"1") ((next sa modl.transitions modl.var_index_tbl)) contl contr)()) modl
			| EX (s, fml1, State sa) -> prove ((make_ex_cont State_set.empty s fml1 id (levl^"1") ((next sa modl.transitions modl.var_index_tbl)) contl contr)()) modl
			| AF (s, fml1, State sa) -> if State_set.mem sa gamma then 
									(add_merge merges levl gamma; prove (contr()) modl) else 
									(if state_in_merge merges levl sa then prove (contr()) modl else 
									let id1 = new_id() in
									prove (Cont (State_set.empty, Fformula.subst_s fml1 s (State sa), (id1), (levl^"1"), (fun () -> add_premises proof id (id1); contl()), (fun () -> add_premises counterexample id (id1); (make_af_cont (State_set.add sa gamma) s fml1 id levl (((next sa modl.transitions modl.var_index_tbl))) contl contr)()))) modl)
			| EG (s, fml1, State sa) -> if State_set.mem sa gamma then 
									(add_merge merges levl gamma; prove (contl()) modl) else
									(if state_in_merge merges levl sa then prove (contl()) modl else 
									let id1 = new_id() in
									prove (Cont (State_set.empty, Fformula.subst_s fml1 s (State sa), (id1), (levl^"1"), (fun () -> add_premises proof id (id1);(make_eg_cont (State_set.add sa gamma) s fml1 id levl (((next sa modl.transitions modl.var_index_tbl))) contl contr)()), (fun () -> add_premises counterexample id (id1); contr()))) modl)
			| AR(x, y, fml1, fml2, State sa) -> if (State_set.is_empty gamma) then Hashtbl.replace merges levl State_set.empty else add_merge merges levl gamma; if State_set.mem sa gamma then 
											(add_merge merges levl gamma; prove (contl()) modl) else 
											(if state_in_merge merges levl sa then prove (contl()) modl else
				let id1 = new_id() and id2 = new_id() in
				prove (Cont (State_set.empty, Fformula.subst_s fml2 y (State sa), (id2), (levl^"2"), (fun () -> Cont (State_set.empty, Fformula.subst_s fml1 x (State sa), (id1), (levl^"1"), (fun () -> add_premises proof id (id1); add_premises proof id (id2); contl()), (fun () -> add_premises counterexample id (id1); (make_ar_cont (State_set.singleton sa) x y fml1 fml2 id levl (((next sa modl.transitions modl.var_index_tbl))) contl contr)()))), (fun () -> add_premises counterexample id (id+2); contr()))) modl)
			(*| AR(x, y, fml1, fml2, State sa) -> if (State_set.is_empty gamma) then Hashtbl.replace merges levl State_set.empty; if State_set.mem sa gamma then 
											(add_merge merges levl gamma; prove (contl()) modl) else 
											(if state_in_merge merges levl sa then prove (contl()) modl else
				let id1 = new_id() and id2 = new_id() in
				prove (Cont (State_set.empty, Fformula.subst_s fml2 y (State sa), (id2), (levl^"2"), (fun () -> Cont (State_set.empty, Fformula.subst_s fml1 x (State sa), (id1), (levl^"1"), (fun () -> add_premises proof id (id1); add_premises proof id (id2); contl()), (fun () -> add_premises counterexample id (id1); (make_ar_cont (State_set.add sa gamma) x y fml1 fml2 id levl (((next sa modl.transitions modl.var_index_tbl))) contl contr)()))), (fun () -> add_premises counterexample id (id+2); contr()))) modl) *)
			| EU (s, s', fml1, fml2, State sa) -> if (State_set.is_empty gamma) then Hashtbl.replace merges levl State_set.empty else add_merge merges levl gamma; if State_set.mem sa gamma then 
												(prove (contr()) modl) else
												( if state_in_merge merges levl sa then prove (contr()) modl else
									let id1 = new_id() and id2 = new_id() in
									((prove (Cont (State_set.empty, Fformula.subst_s fml2 s' (State sa), (id2), (levl^"2"), (fun () -> add_premises proof id (id2); contl()), (fun () -> Cont (State_set.empty, Fformula.subst_s fml1 s (State sa), (id1), (levl^"1"), (fun () -> add_premises proof id (id1); (make_eu_cont (State_set.singleton sa) s s' fml1 fml2 id levl (((next sa modl.transitions modl.var_index_tbl))) contl contr)()), (fun () -> add_premises counterexample id (id1); add_premises counterexample id (id2); contr()))))) modl)))  
			(*| EU (s, s', fml1, fml2, State sa) -> if (State_set.is_empty gamma) then Hashtbl.replace merges levl State_set.empty; if State_set.mem sa gamma then 
												(add_merge merges levl gamma; prove (contr()) modl) else
												( if state_in_merge merges levl sa then prove (contr()) modl else
									let id1 = new_id() and id2 = new_id() in
									((prove (Cont (State_set.empty, Fformula.subst_s fml2 s' (State sa), (id2), (levl^"2"), (fun () -> add_premises proof id (id2); contl()), (fun () -> Cont (State_set.empty, Fformula.subst_s fml1 s (State sa), (id1), (levl^"1"), (fun () -> add_premises proof id (id1); (make_eu_cont (State_set.add sa gamma) s s' fml1 fml2 id levl (((next sa modl.transitions modl.var_index_tbl))) contl contr)()), (fun () -> add_premises counterexample id (id1); add_premises counterexample id (id2); contr()))))) modl)))  *)
			| _ -> raise Unable_to_prove
			)
	
	let rec prove_model modl out outname = 
		let spec_lst = modl.spec_list in
		let rec prove_lst lst = 
		match lst with
		| [] -> ()
		| (s, fml) :: lst' -> 
			((let nnf_fml = nnf fml in 
				print_endline (s^": "^(str_modl_fml modl.var_list (nnf_fml)));
				pre_process_merges (select_sub_fmls (sub_fmls nnf_fml "1"));
				let b = (prove (Cont (State_set.empty, Fformula.subst_s (nnf_fml) (SVar "ini") (State modl.init_assign), 0, "1", (fun () -> Basic true), (fun () -> Basic false))) modl) in
					print_endline (s ^ " is " ^ (if b then "true, proof output to \""^outname^"\"." else "false, counterexample output to \""^outname^"\".")); 
					output_result b s sequents (if b then proof else counterexample) out modl.var_list; 
					output_string out "***********************************ouput complete**************************************";
					flush out; 
					Hashtbl.clear sequents; 
					Hashtbl.clear proof);
					prove_lst lst') in prove_lst spec_lst

	end







