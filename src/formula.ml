open Expr
open Ast

type state = 
	  SVar of string
	| State of value


let str_state s = 
	match s with
	| SVar str -> str
	| State value -> str_value value

let str_state_list sl = 
	if List.length sl = 1 then
		str_state (List.hd sl)
	else 
		let tmp_str = ref (str_state (List.hd sl)) in
		List.iter (fun s -> tmp_str := !tmp_str^", "^(str_state s)) (List.tl sl);
		!tmp_str


let str_state_ptyp s ptyp = 
	match s, ptyp with
	| SVar str, _ -> str
	| State (VRecord str_vals), PTRecord str_ptyps -> 
		begin
			let tmp_str = ref "{" in
			List.iter (
				fun (sv, sp) -> 
				let strval = 
				match snd sv, (snd sp) with
				| (VInt i, PTScalar strs) -> (fst sv)^"=#"^(List.nth strs i)
					(* let strval = 
						begin match value,ptyp with
						| VInt i, PTScalar strs -> s1^"=#"^(List.nth strs i)
						| _,_ -> s1^"="^(str_value value) 
						end  *)
				| _,_ -> (fst sv)^"="^(str_value (snd sv)) in
				tmp_str := !tmp_str^strval^";") (List.combine str_vals str_ptyps);
			!tmp_str^"}"
		end
	| State value, _ -> str_value value

let str_state_list_ptyp sl ptyp = 
	if List.length sl = 1 then
		str_state (List.hd sl)
	else 
		let tmp_str = ref (str_state_ptyp (List.hd sl) ptyp) in
		List.iter (fun s -> tmp_str := !tmp_str^", "^(str_state_ptyp s ptyp)) (List.tl sl);
		!tmp_str

type formula = 
	  Top
	| Bottom
	| Atomic of string * (state list)
	| Neg of formula
	| And of formula * formula
	| Or of formula * formula
	| AX of string * formula * state
	| EX of string * formula * state
	| AF of string * formula * state
	| EG of string * formula * state
	| AR of string * string * formula * formula * state
	| EU of string * string * formula * formula * state


let rec subst_s fml str value = 
	match fml with
	| Top | Bottom -> fml
	| Atomic (s, es) -> 
		let rec replace_symbol es str value =
			match es with
			| [] -> []
			| (SVar s) :: es' -> if str = s then value :: (replace_symbol es' str value) else (SVar s) :: (replace_symbol es' str value) 
			| e :: es' ->  e :: (replace_symbol es' str value) in
		Atomic (s, replace_symbol es str value)
	| Neg fml1 -> Neg (subst_s fml1 str value)
	| And (fml1, fml2) -> And (subst_s fml1 str value, subst_s fml2 str value)
	| Or (fml1, fml2) -> Or (subst_s fml1 str value, subst_s fml2 str value)
	| AX (s1, fml1, e1) -> AX (s1, (if s1 = str then fml1 else subst_s fml1 str value), (if e1 = SVar str then value else e1))
	| EX (s1, fml1, e1) -> EX (s1, (if s1 = str then fml1 else subst_s fml1 str value), (if e1 = SVar str then value else e1))
	| AF (s1, fml1, e1) -> AF (s1, (if s1 = str then fml1 else subst_s fml1 str value), (if e1 = SVar str then value else e1))
	| EG (s1, fml1, e1) -> EG (s1, (if s1 = str then fml1 else subst_s fml1 str value), (if e1 = SVar str then value else e1))
	| AR (s1, s2, fml1, fml2, e1) -> AR (s1, s2, (if s1 = str then fml1 else subst_s fml1 str value), (if s2 = str then fml2 else subst_s fml2 str value), (if e1 = SVar str then value else e1))
	| EU (s1, s2, fml1, fml2, e1) -> EU (s1, s2, (if s1 = str then fml1 else subst_s fml1 str value), (if s2 = str then fml2 else subst_s fml2 str value), (if e1 = SVar str then value else e1))

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
let rec str_fml fml = 
	match fml with
	| Top -> "TRUE"
	| Bottom -> "FALSE"
	| Atomic (e, sl) -> let str = (e) ^" ("^ (str_state_list sl)^")" in String.trim str
	| Neg fml1 -> "(not " ^ (str_fml fml1) ^ ")"
	| And (fml1, fml2) -> (str_fml fml1) ^ "/\\" ^ (str_fml fml2)
	| Or (fml1, fml2) -> (str_fml fml1) ^ "\\/" ^ (str_fml fml2)
	| AX (s, fml1, s') -> "AX(" ^ (s) ^ ", (" ^ (str_fml fml1) ^ "), " ^ (str_state s') ^ ")"
	| EX (s, fml1, s') -> "EX(" ^ (s) ^ ", (" ^ (str_fml fml1) ^ "), " ^ (str_state s') ^ ")"
	| AF (s, fml1, s') -> "AF(" ^ (s) ^ ", (" ^ (str_fml fml1) ^ "), " ^ (str_state s') ^ ")"
	| EG (s, fml1, s') -> "EG(" ^ (s) ^ ", (" ^ (str_fml fml1) ^ "), " ^ (str_state s') ^ ")"
	| AR (s, s', fml1, fml2, s'') -> "AR(" ^ (s) ^ ", " ^ (s') ^ ", (" ^ (str_fml fml1) ^ "), (" ^ (str_fml fml2) ^ "), " ^ (str_state s'') ^ ")"
	| EU (s, s', fml1, fml2, s'') -> "EU(" ^ (s) ^ ", " ^ (s') ^ ", (" ^ (str_fml fml1) ^ "), (" ^ (str_fml fml2) ^ "), " ^ (str_state s'') ^ ")"

let rec str_fml_ptyp fml ptyp = 
	match fml with
	| Top -> "TRUE"
	| Bottom -> "FALSE"
	| Atomic (e, sl) -> let str = (e) ^" ("^ (str_state_list sl)^")" in String.trim str
	| Neg fml1 -> "(not " ^ (str_fml_ptyp fml1 ptyp) ^ ")"
	| And (fml1, fml2) -> (str_fml_ptyp fml1 ptyp) ^ "/\\" ^ (str_fml_ptyp fml2 ptyp)
	| Or (fml1, fml2) -> (str_fml_ptyp fml1 ptyp) ^ "\\/" ^ (str_fml_ptyp fml2 ptyp)
	| AX (s, fml1, s') -> "AX(" ^ (s) ^ ", (" ^ (str_fml_ptyp fml1 ptyp) ^ "), " ^ (str_state_ptyp s' ptyp) ^ ")"
	| EX (s, fml1, s') -> "EX(" ^ (s) ^ ", (" ^ (str_fml_ptyp fml1 ptyp) ^ "), " ^ (str_state_ptyp s' ptyp) ^ ")"
	| AF (s, fml1, s') -> "AF(" ^ (s) ^ ", (" ^ (str_fml_ptyp fml1 ptyp) ^ "), " ^ (str_state_ptyp s' ptyp) ^ ")"
	| EG (s, fml1, s') -> "EG(" ^ (s) ^ ", (" ^ (str_fml_ptyp fml1 ptyp) ^ "), " ^ (str_state_ptyp s' ptyp) ^ ")"
	| AR (s, s', fml1, fml2, s'') -> "AR(" ^ (s) ^ ", " ^ (s') ^ ", (" ^ (str_fml_ptyp fml1 ptyp) ^ "), (" ^ (str_fml_ptyp fml2 ptyp) ^ "), " ^ (str_state_ptyp s'' ptyp) ^ ")"
	| EU (s, s', fml1, fml2, s'') -> "EU(" ^ (s) ^ ", " ^ (s') ^ ", (" ^ (str_fml_ptyp fml1 ptyp) ^ "), (" ^ (str_fml_ptyp fml2 ptyp) ^ "), " ^ (str_state_ptyp s'' ptyp) ^ ")"
	

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
	Hashtbl.iter (fun a b -> if (filter b = false) then Hashtbl.remove fml_levl_tbl a else ()) fml_levl_tbl; fml_levl_tbl