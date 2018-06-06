open Oterm

type formula = 
	  Top
	| Bottom
	| Atomic of string * (state list)
	| Neg of formula
	| And of formula * formula
	| Or of formula * formula
	| AX of state * formula * state
	| EX of state * formula * state
	| AF of state * formula * state
	| EG of state * formula * state
	| AR of state * state * formula * formula * state
	| EU of state * state * formula * formula * state

(* substitute expression in formula *)
let rec subst_e fml e1 e2 = 
	match fml with
	| Top | Bottom -> fml
	| Atomic (s, sl) ->  fml
	| Neg fml1 -> Neg (subst_e fml1 e1 e2)
	| And (fml1, fml2) -> And (subst_e fml1 e1 e2, subst_e fml2 e1 e2)
	| Or (fml1, fml2) -> Or (subst_e fml1 e1 e2, subst_e fml2 e1 e2)
	| AX (s, fml1, s') -> AX (s, subst_e fml1 e1 e2, s')
	| EX (s, fml1, s') -> EX (s, subst_e fml1 e1 e2, s')
	| AF (s, fml1, s') -> AF (s, subst_e fml1 e1 e2, s')
	| EG (s, fml1, s') -> EG (s, subst_e fml1 e1 e2, s')
	| AR (s, s', fml1, fml2, s'') -> AR (s, s', subst_e fml1 e1 e2, subst_e fml2 e1 e2, s'')
	| EU (s, s', fml1, fml2, s'') -> EU (s, s', subst_e fml1 e1 e2, subst_e fml2 e1 e2, s'')

(* substitute state in formula*)
let rec subst_s fml s1 s2 = 
	match fml with
	| Top | Bottom -> fml
	| Atomic (e, sl) ->  Atomic (e, subst_s_in_list sl s1 s2)
	| Neg fml1 -> Neg (subst_s fml1 s1 s2)
	| And (fml1, fml2) -> And (subst_s fml1 s1 s2, subst_s fml2 s1 s2)
	| Or (fml1, fml2) -> Or (subst_s fml1 s1 s2, subst_s fml2 s1 s2)
	| AX (s, fml1, s') -> AX (s, subst_s fml1 s1 s2, (if compare_state s1 s' = 0 then s2 else s'))
	| EX (s, fml1, s') -> EX (s, subst_s fml1 s1 s2, (if compare_state s1 s' = 0 then s2 else s'))
	| AF (s, fml1, s') -> AF (s, subst_s fml1 s1 s2, (if compare_state s1 s' = 0 then s2 else s'))
	| EG (s, fml1, s') -> EG (s, subst_s fml1 s1 s2, (if compare_state s1 s' = 0 then s2 else s'))
	| AR (s, s', fml1, fml2, s'') -> AR (s, s', subst_s fml1 s1 s2, subst_s fml2 s1 s2, (if compare_state s1 s'' = 0 then s2 else s''))
	| EU (s, s', fml1, fml2, s'') -> EU (s, s', subst_s fml1 s1 s2, subst_s fml2 s1 s2, (if compare_state s1 s'' = 0 then s2 else s''))
and subst_s_in_list sl s1 s2 = 
	match sl with
	| [] -> sl
	| s :: sl' -> if compare_state s s1 = 0 then s2 :: (subst_s_in_list sl' s1 s2) else s :: (subst_s_in_list sl' s1 s2)

(* negative normal form *)
let rec nnf fml = 
	match fml with
	| Top | Bottom | Atomic _ -> fml
	| Neg fml1 -> neg (nnf fml1)
	| And (fml1, fml2) -> And (nnf fml1, nnf fml2)
	| Or (fml1, fml2) -> Or (nnf fml1, nnf fml2)
	| AX (s, fml1, s') -> AX (s, nnf fml1, s')
	| EX (s, fml1, s') -> EX (s, nnf fml1, s')
	| AF (s, fml1, s') -> AF (s, nnf fml1, s')
	| EG (s, fml1, s') -> EG (s, nnf fml1, s')
	| AR (s, s', fml1, fml2, s'') -> AR (s, s', nnf fml1, nnf fml2, s'')
	| EU (s, s', fml1, fml2, s'') -> EU (s, s', nnf fml1, nnf fml2, s'')
and neg fml = 
	match fml with
	| Top -> Bottom
	| Bottom -> Top
	| Atomic _ -> Neg fml
	| Neg (Atomic (e, sl)) -> Atomic (e, sl)
	| Neg fml1 -> fml1
	| And (fml1, fml2) -> Or (neg fml1, neg fml2)
	| Or (fml1, fml2) -> And (neg fml1, neg fml2)
	| AX (s, fml1, s') -> EX (s, neg fml1, s')
	| EX (s, fml1, s') -> AX (s, neg fml1, s')
	| AF (s, fml1, s') -> EG (s, neg fml1, s')
	| EG (s, fml1, s') -> AF (s, neg fml1, s')
	| AR (s, s', fml1, fml2, s'') -> EU (s, s', neg fml1, neg fml2, s'')
	| EU (s, s', fml1, fml2, s'') -> AR (s, s', neg fml1, neg fml2, s'')
	
(* formula to string *)
let rec fml_to_string fml = 
	match fml with
	| Top -> "TRUE"
	| Bottom -> "FALSE"
	| Atomic (e, sl) -> (e) ^ "("^ (str_state_list sl) ^")"
	| Neg fml1 -> "(not " ^ (fml_to_string fml1) ^ ")"
	| And (fml1, fml2) -> (fml_to_string fml1) ^ "/\\" ^ (fml_to_string fml2)
	| Or (fml1, fml2) -> (fml_to_string fml1) ^ "\\/" ^ (fml_to_string fml2)
	| AX (s, fml1, s') -> "AX(" ^ (str_state s) ^ ", (" ^ (fml_to_string fml1) ^ "), " ^ (str_state s') ^ ")"
	| EX (s, fml1, s') -> "EX(" ^ (str_state s) ^ ", (" ^ (fml_to_string fml1) ^ "), " ^ (str_state s') ^ ")"
	| AF (s, fml1, s') -> "AF(" ^ (str_state s) ^ ", (" ^ (fml_to_string fml1) ^ "), " ^ (str_state s') ^ ")"
	| EG (s, fml1, s') -> "EG(" ^ (str_state s) ^ ", (" ^ (fml_to_string fml1) ^ "), " ^ (str_state s') ^ ")"
	| AR (s, s', fml1, fml2, s'') -> "AR(" ^ (str_state s) ^ ", " ^ (str_state s') ^ ", (" ^ (fml_to_string fml1) ^ "), (" ^ (fml_to_string fml2) ^ "), " ^ (str_state s'') ^ ")"
	| EU (s, s', fml1, fml2, s'') -> "EU(" ^ (str_state s) ^ ", " ^ (str_state s') ^ ", (" ^ (fml_to_string fml1) ^ "), (" ^ (fml_to_string fml2) ^ "), " ^ (str_state s'') ^ ")"


let rec sub_fmls fml levl =
	let fml_levl_tbl = Hashtbl.create 10 
	and add_tbl tbl1 tbl2 = 
	Hashtbl.iter (fun a b -> Hashtbl.add tbl1 a b) tbl2 in
	Hashtbl.add fml_levl_tbl levl fml;
	match fml with
	(*| Atomic _ -> Hashtbl.add fml_levl_tbl levl *)
	(*| Neg fml1 -> add_tbl fml_levl_tbl (sub_fmls fml1 (levl^"1")); fml_levl_tbl*)
	| And (fml1, fml2) -> add_tbl fml_levl_tbl (sub_fmls fml1 (levl^"1")); add_tbl fml_levl_tbl (sub_fmls fml2 (levl^"2")); fml_levl_tbl
	| Or (fml1, fml2) -> add_tbl fml_levl_tbl (sub_fmls fml1 (levl^"1")); add_tbl fml_levl_tbl (sub_fmls fml2 (levl^"2")); fml_levl_tbl
	| AX (s, fml1, s') -> add_tbl fml_levl_tbl (sub_fmls fml1 (levl^"1")); fml_levl_tbl
	| EX (s, fml1, s') -> add_tbl fml_levl_tbl (sub_fmls fml1 (levl^"1")); fml_levl_tbl
	| AF (s, fml1, s') -> add_tbl fml_levl_tbl (sub_fmls fml1 (levl^"1")); fml_levl_tbl
	| EG (s, fml1, s') -> add_tbl fml_levl_tbl (sub_fmls fml1 (levl^"1")); fml_levl_tbl
	| AR (s, s', fml1, fml2, s'') -> add_tbl fml_levl_tbl (sub_fmls fml1 (levl^"1")); add_tbl fml_levl_tbl (sub_fmls fml2 (levl^"2")); fml_levl_tbl
	| EU (s, s', fml1, fml2, s'') -> add_tbl fml_levl_tbl (sub_fmls fml1 (levl^"1")); add_tbl fml_levl_tbl (sub_fmls fml2 (levl^"2")); fml_levl_tbl
	| _ -> fml_levl_tbl

let select_sub_fmls fml_levl_tbl = 
	let filter fml  = 
	(match fml with
	| AF _ -> true
	| EG _ -> true
	| AR _ -> true
	| EU _ -> true
	| AX _ -> true
	| EX _ -> true
	| Atomic _ -> true
	| Neg (Atomic _) -> true
	| _ -> false) in
	Hashtbl.iter (fun a b -> if (filter b = false) then Hashtbl.remove fml_levl_tbl a else ()) fml_levl_tbl; 
	(* Hashtbl.iter (fun a b -> print_endline (a^"--"^(fml_to_string b))) fml_levl_tbl; *)
	fml_levl_tbl

let rec ias_in_fml fml = 
	match fml with
	| And (fml1, fml2) -> (ias_in_fml fml1) @ (ias_in_fml fml2)
	| Or (fml1, fml2) -> (ias_in_fml fml1) @ (ias_in_fml fml2)
	| AX (x, fml1, State ia) -> ia::(ias_in_fml fml1)
	| EX (x, fml1, State ia) -> ia::(ias_in_fml fml1)
	| AF (x, fml1, State ia) -> ia::(ias_in_fml fml1)
	| EG (x, fml1, State ia) -> ia::(ias_in_fml fml1)
	| AR (x, y, fml1, fml2, State ia) -> (ia::(ias_in_fml fml1))@(ias_in_fml fml2)
	| EU (x, y, fml1, fml2, State ia) -> (ia::(ias_in_fml fml1))@(ias_in_fml fml2)
	| _ -> []







