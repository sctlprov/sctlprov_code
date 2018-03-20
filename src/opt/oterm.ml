
type expr = 
(*	  Parameter of string	
	| Symbol of string *)
	| Vars of string
	| Nested_vars of expr * expr
	| Vars_index of string * expr
	| Var of int
	| State_expr of int * expr
(*	| Var_index of int * expr*)
	| Const of int
	| Aray of expr list
	| Negi of expr	
	| Add of expr * expr
	| Minus of expr * expr
	| Mult of expr * expr
	| Ando of expr * expr
	| Oro of expr * expr
	| Negb of expr
	| Equal of expr * expr
	| Mod of expr * expr
	| LT of expr * expr
	| GT of expr * expr
	| LE of expr * expr
	| GE of expr * expr
and expr_type = 
	  Int_type of int * int
	| Bool_type
	| Scalar_type of string list
	| Array_type of expr_type * expr
	| Module_type of string 
and expr_module_instance = 
	  Expr of expr
	| Module_instance of string * (expr list)
and state = 
	  SVar of string
	| State of int array

(* expr to string *)
let rec str_expr e = 
	match e with
(*	| Parameter s -> s
	| Symbol s -> "(Symbol "^s^")"*)
	| Vars s -> s
	| Nested_vars (e1, e2) -> (str_expr e1)^"."^(str_expr e2)
	| Vars_index (s, e1) -> s^"["^(str_expr e1)^"]" 
	| Var i -> "(var "^(string_of_int i)^")"
	| State_expr (i, e1) -> (string_of_int i)^"("^(str_expr e1)^")"
	| Const i -> string_of_int i
	| Aray es -> "{"^(str_expr_list es)^"}"
	| Negi e1 -> "(- "^(str_expr e1)^")"
	| Add (e1, e2) -> "("^(str_expr e1)^"+"^(str_expr e2)^")"
	| Minus (e1, e2) -> "("^(str_expr e1)^"-"^(str_expr e2)^")"
	| Mult (e1, e2) -> "("^(str_expr e1)^"*"^(str_expr e2)^")"
	| Ando (e1, e2) -> "("^(str_expr e1)^"&&"^(str_expr e2)^")"
	| Oro (e1, e2) -> "("^(str_expr e1)^"||"^(str_expr e2)^")"
	| Negb e1 -> "(Negb "^(str_expr e1)^")"
	| Equal (e1, e2) -> "("^(str_expr e1)^"="^(str_expr e2)^")"
	| Mod (e1, e2) -> "("^(str_expr e1)^" mod "^(str_expr e2)^")"
	| LT (e1, e2) -> "("^(str_expr e1)^"<"^(str_expr e2)^")"
	| GT (e1, e2) -> "("^(str_expr e1)^">"^(str_expr e2)^")"
	| LE (e1, e2) -> "("^(str_expr e1)^"<="^(str_expr e2)^")"
	| GE (e1, e2) -> "("^(str_expr e1)^">="^(str_expr e2)^")"
and str_expr_list es = 
	match es with	
	| [] -> ""
	| [e] -> str_expr e
	| e :: es' -> (str_expr e)^","^(str_expr_list es')

let rec str_expr_type et = 
	match et with
	| Int_type (i1, i2) -> "int("^(string_of_int i1)^", "^(string_of_int i2)^")"
	| Bool_type -> "bool"
	| Scalar_type sl -> let rec str_str_list strs = if List.length strs <> 0 then (List.hd strs)^(str_str_list (List.tl strs)^" ") else "" in "{"^(str_str_list sl)^"}"
	| Array_type (t, len) -> (str_expr_type t)^"["^(str_expr len)^"]"	
	| Module_type m -> m

let str_expr_module_instance emi = 
	match emi with
	| Expr e -> str_expr e
	| Module_instance (s, el) -> s^"("^(str_expr_list el)^")"

let rec str_state_resti strest = 
	match strest with
	| [] -> ""
	| (i, e) :: strest' -> (string_of_int i)^":="^(str_expr e)^"; "^(str_state_resti strest')

let rec str_state_rests strest = 
	match strest with
	| [] -> ""
	| (s, e) :: strest' -> (s)^":="^(str_expr e)^"; "^(str_state_rests strest')

let rec str_state_reste strest = 
	match strest with
	| [] -> ""
	| (s, e) :: strest' -> (str_expr s)^":="^(str_expr e)^"; "^(str_state_reste strest')



module Key = 
	struct
		type t = int array
		let compare = Pervasives.compare
	end;;

module State_set = Set.Make(Key)


let get_array_from_state s = 
	match s with
	| SVar v -> Array.make 1 0
	| State ia -> ia

(*replace parameters by instances*)
let rec replace_parameter_expr exp pv e = 
	match exp with
	| Vars s -> if pv = s then e else exp
	| Nested_vars (e1, e2) -> Nested_vars (replace_parameter_expr e1 pv e, replace_parameter_expr e2 pv e)
	| State_expr (i, e1) -> State_expr (i, replace_parameter_expr e1 pv e)
	| Vars_index (s, e1) -> Vars_index (s, replace_parameter_expr e1 pv e)
	| Aray el -> Aray (replace_parameter_expr_list el pv e)
(*	| Var_index (i, idx) -> Var_index (i, replace_parameter_expr idx pv e)*)
	| Negi e1 -> Negi (replace_parameter_expr e1 pv e)
	| Negb e1 -> Negb (replace_parameter_expr e1 pv e)
	| Add (e1, e2) -> Add (replace_parameter_expr e1 pv e, replace_parameter_expr e2 pv e)
	| Minus (e1, e2) -> Minus (replace_parameter_expr e1 pv e, replace_parameter_expr e2 pv e)
	| Mult (e1, e2) -> Mult (replace_parameter_expr e1 pv e, replace_parameter_expr e2 pv e)
	| Ando (e1, e2) -> Ando (replace_parameter_expr e1 pv e, replace_parameter_expr e2 pv e)
	| Oro (e1, e2) -> Oro (replace_parameter_expr e1 pv e, replace_parameter_expr e2 pv e)
	| Equal (e1, e2) -> Equal (replace_parameter_expr e1 pv e, replace_parameter_expr e2 pv e)
	| Mod (e1, e2) -> Mod (replace_parameter_expr e1 pv e, replace_parameter_expr e2 pv e)	
	| LT (e1, e2) -> LT (replace_parameter_expr e1 pv e, replace_parameter_expr e2 pv e)
	| GT (e1, e2) -> GT (replace_parameter_expr e1 pv e, replace_parameter_expr e2 pv e)
	| LE (e1, e2) -> LE (replace_parameter_expr e1 pv e, replace_parameter_expr e2 pv e)
	| GE (e1, e2) -> GE (replace_parameter_expr e1 pv e, replace_parameter_expr e2 pv e)
	| _ -> exp
and replace_parameter_expr_list expl pv e = 
	match expl with
	| [] -> []
	| exp :: expl' -> (replace_parameter_expr exp pv e) :: (replace_parameter_expr_list expl' pv e)
and replace_parameter_expr_type et pv e = 
	match et with
	| Array_type (et1, e1) -> Array_type (replace_parameter_expr_type et1 pv e, replace_parameter_expr e1 pv e)
	| _ -> et
and replace_parameter_expr_module_instance em pv e = 
	match em with
	| Expr e1 -> Expr (replace_parameter_expr e1 pv e)
	| Module_instance (s, el) -> Module_instance (s, replace_parameter_expr_list el pv e)

(*expand symbol definition*)
let rec expand_symbol_expr e stbl = 
	match e with
(*	| Symbol s -> let se = Hashtbl.find stbl s in expand_symbol_expr se stbl*)
	| Vars s -> (try let se = Hashtbl.find stbl s in expand_symbol_expr se stbl with Not_found -> e)
	| Nested_vars (e1, e2) -> Nested_vars (expand_symbol_expr e1 stbl, expand_symbol_expr e2 stbl)
	| State_expr (i, e1) -> State_expr (i, expand_symbol_expr e1 stbl)
	| Vars_index (s, e1) -> Vars_index (s, expand_symbol_expr e1 stbl)
	| Aray el -> Aray (expand_symbol_expr_list el stbl)
	| Negi e1 -> Negi (expand_symbol_expr e1 stbl)
	| Negb e1 -> Negb (expand_symbol_expr e1 stbl)
	| Add (e1, e2) -> Add (expand_symbol_expr e1 stbl, expand_symbol_expr e2 stbl)
	| Minus (e1, e2) -> Minus (expand_symbol_expr e1 stbl, expand_symbol_expr e2 stbl)
	| Mult (e1, e2) -> Mult (expand_symbol_expr e1 stbl, expand_symbol_expr e2 stbl)
	| Ando (e1, e2) -> Ando (expand_symbol_expr e1 stbl, expand_symbol_expr e2 stbl)
	| Oro (e1, e2) -> Oro (expand_symbol_expr e1 stbl, expand_symbol_expr e2 stbl)
	| Equal (e1, e2) -> Equal (expand_symbol_expr e1 stbl, expand_symbol_expr e2 stbl)
	| Mod (e1, e2) -> Mod (expand_symbol_expr e1 stbl, expand_symbol_expr e2 stbl)
	| LT (e1, e2) -> LT (expand_symbol_expr e1 stbl, expand_symbol_expr e2 stbl)
	| GT (e1, e2) -> GT (expand_symbol_expr e1 stbl, expand_symbol_expr e2 stbl)
	| LE (e1, e2) -> LE (expand_symbol_expr e1 stbl, expand_symbol_expr e2 stbl)
	| GE (e1, e2) -> GE (expand_symbol_expr e1 stbl, expand_symbol_expr e2 stbl)
	| _ -> e
and expand_symbol_expr_list el stbl = 
	match el with
	| [] -> []
	| e :: el' -> (expand_symbol_expr e stbl) :: (expand_symbol_expr_list el' stbl)
  
(*raise index of variables*)
let rec raise_var_index_expr e i = 
	match e with
	| Var vi -> Var (vi+i)
	| State_expr (si, e1) -> State_expr (si, raise_var_index_expr e1 i)
	| Negi e1 -> Negi (raise_var_index_expr e1 i)
	| Negb e1 -> Negb (raise_var_index_expr e1 i)
	| Add (e1, e2) -> Add (raise_var_index_expr e1 i, raise_var_index_expr e2 i)	
	| Minus (e1, e2) -> Minus (raise_var_index_expr e1 i, raise_var_index_expr e2 i)
	| Mult (e1, e2) -> Mult (raise_var_index_expr e1 i, raise_var_index_expr e2 i)
	| Ando (e1, e2) -> Ando (raise_var_index_expr e1 i, raise_var_index_expr e2 i)
	| Oro (e1, e2) -> Oro (raise_var_index_expr e1 i, raise_var_index_expr e2 i)
	| Equal (e1, e2) -> Equal (raise_var_index_expr e1 i, raise_var_index_expr e2 i)
	| Mod (e1, e2) -> Mod (raise_var_index_expr e1 i, raise_var_index_expr e2 i)
	| LT (e1, e2) -> LT (raise_var_index_expr e1 i, raise_var_index_expr e2 i)
	| GT (e1, e2) -> GT (raise_var_index_expr e1 i, raise_var_index_expr e2 i)
	| LE (e1, e2) -> LE (raise_var_index_expr e1 i, raise_var_index_expr e2 i)
	| GE (e1, e2) -> GE (raise_var_index_expr e1 i, raise_var_index_expr e2 i)
	| _ -> e

let rec raise_var_index_expr_list es i = 
	match es with
	| [] -> []
	| e :: es' -> (raise_var_index_expr e i) :: (raise_var_index_expr_list es' i)

let rec add_prefix_expr e prefix =
	match e with
	| Vars s -> Vars (prefix ^ s)
	| Vars_index (s, e1) -> Vars_index (prefix^s, add_prefix_expr e1 prefix)
	| Nested_vars (e1, e2) -> Nested_vars (add_prefix_expr e1 prefix, e2)
	| State_expr (i, e1) -> State_expr (i, add_prefix_expr e1 prefix)
	| Aray el -> Aray (List.map (fun a -> add_prefix_expr a prefix) el)
	| Negi e1 -> Negi (add_prefix_expr e1 prefix)
	| Negb e1 -> Negb (add_prefix_expr e1 prefix)
	| Add (e1, e2) -> Add (add_prefix_expr e1 prefix, add_prefix_expr e2 prefix)
	| Minus (e1, e2) -> Minus (add_prefix_expr e1 prefix, add_prefix_expr e2 prefix)
	| Mult (e1, e2) -> Mult (add_prefix_expr e1 prefix, add_prefix_expr e2 prefix)
	| Ando (e1, e2) -> Ando (add_prefix_expr e1 prefix, add_prefix_expr e2 prefix)
	| Oro (e1, e2) -> Oro (add_prefix_expr e1 prefix, add_prefix_expr e2 prefix)
	| Equal (e1, e2) -> Equal (add_prefix_expr e1 prefix, add_prefix_expr e2 prefix)
	| Mod (e1, e2) -> Mod (add_prefix_expr e1 prefix, add_prefix_expr e2 prefix)
	| LT (e1, e2) -> LT (add_prefix_expr e1 prefix, add_prefix_expr e2 prefix)
	| GT (e1, e2) -> GT (add_prefix_expr e1 prefix, add_prefix_expr e2 prefix)
	| LE (e1, e2) -> LE (add_prefix_expr e1 prefix, add_prefix_expr e2 prefix)
	| GE (e1, e2) -> GE (add_prefix_expr e1 prefix, add_prefix_expr e2 prefix)
	| _ -> e


(* state to string *)
let str_state st = 
	let rec str_int_array ia = 
		let al = Array.length ia in
			if al = 0 then "" else 
				if al = 1 then string_of_int (ia.(0)) else (string_of_int (ia.(0)))^","^(str_int_array (Array.sub ia 1 (al-1))) in 
	match st with
	| SVar sv -> sv
	| State ia -> "["^str_int_array ia^"]"

let rec str_state_list sts = 
	match sts with
	| [] -> ""
	| [st] -> str_state st
	| st :: sts' -> (str_state st)^","^(str_state_list sts')

(* expression equal*)
let compare_expr e1 e2 = Pervasives.compare e1 e2
let compare_state s1 s2 = 
	match (s1, s2) with
	| (SVar sv1, SVar sv2) -> String.compare sv1 sv2
	| (State ia1, State ia2) -> Pervasives.compare ia1 ia2
	| _ -> -1


(* regular evaluating expressions *)
let rec eval_expr e = 
	match e with
	| Vars_index (s, e1) -> let e2 = eval_expr e1 in Vars_index (s, e2)
	| Aray el -> Aray (eval_expr_list el)
	| Nested_vars (e1, e2) -> Nested_vars (eval_expr e1, eval_expr e2)
	| Negi e1 -> 
		let e2 = eval_expr e1 in 
		(match e2 with
		| Const i -> Const (-i)
		| Negi e3 -> e3
		| _ -> Negi e2
		)
	| Add (e1, e2) -> 
		let e3 = eval_expr e1 
		and e4 = eval_expr e2 in
		(match (e3, e4) with
		| (Const i1, Const i2) -> Const (i1 + i2)
		| _ -> Add (e3, e4)
		)
	| Minus (e1, e2) -> 
		let e3 = eval_expr e1 
		and e4 = eval_expr e2 in
		(match (e3, e4) with
		| (Const i1, Const i2) -> Const (i1 - i2)
		| _ -> Minus (e3, e4)
		)
	| Mult (e1, e2) -> 
		let e3 = eval_expr e1 
		and e4 = eval_expr e2 in
		(match (e3, e4) with
		| (Const i1, Const i2) -> Const (i1 * i2)
		| _ -> Mult (e3, e4)
		)
	| Negb e1 -> 
		let e2 = eval_expr e1 in
		(match e2 with
		| Const i -> Const (1-i)
		| Negb e3 -> e3
		| _ -> Negb e2
		)
	| Ando (e1, e2) -> 
		let e3 = eval_expr e1 
		and e4 = eval_expr e2 in
		(match (e3, e4) with
		| (Const i1, Const i2) -> Const (if i1 > i2 then i2 else i1)
		| _ -> Ando (e3, e4)
		)
	| Oro (e1, e2) -> 
		let e3 = eval_expr e1 
		and e4 = eval_expr e2 in
		(match (e3, e4) with
		| (Const i1, Const i2) -> Const (if i1 < i2 then i2 else i1)
		| _ -> Oro (e3, e4)
		)
	(*need to be carefully checked*)
	| Equal (e1, e2) -> 
		let e3 = eval_expr e1 
		and e4 = eval_expr e2 in
		(
		match (e3, e4) with
		| (Const i1, Const i2) -> if i1 = i2 then (Const 1) else (Const (0))
		| (Var i1, Var i2) -> if i1 = i2 then (Const 1) else Equal (e3, e4)
		| _ -> Equal (e3, e4)
		)
						(*if compare_expr e3 e4 = 0 then Const 1 else Const (0) *)
	| Mod (e1, e2) -> 
		let e3 = eval_expr e1 
		and e4 = eval_expr e2 in
		(match (e3, e4) with
		| (Const i1, Const i2) -> Const (i1 mod i2)
		| _ -> Mod (e3, e4)
		)
	| LT (e1, e2) -> 
		let e3 = eval_expr e1 
		and e4 = eval_expr e2 in
		(match (e3, e4) with
		| (Const i1, Const i2) -> Const (if i1 < i2 then 1 else (0))
		| _ -> LT (e3, e4)
		)
	| GT (e1, e2) -> 
		let e3 = eval_expr e1 
		and e4 = eval_expr e2 in
		(match (e3, e4) with
		| (Const i1, Const i2) -> Const (if i1 > i2 then 1 else (0))
		| _ -> GT (e3, e4)
		)
	| LE (e1, e2) -> 
		let e3 = eval_expr e1 
		and e4 = eval_expr e2 in
		(match (e3, e4) with
		| (Const i1, Const i2) -> Const (if i1 <= i2 then 1 else (0))
		| _ -> LE (e3, e4)
		)
	| GE (e1, e2) -> 
		let e3 = eval_expr e1 
		and e4 = eval_expr e2 in
		(match (e3, e4) with
		| (Const i1, Const i2) -> Const (if i1 >= i2 then 1 else (0))
		| _ -> GE (e3, e4)
		)
	| _ -> e
and eval_expr_list el = 
	match el with
	| [] -> []
	| e :: el' -> (eval_expr e) :: (eval_expr_list el')

let rec expr_to_vars e = 
	match e with
	| Nested_vars (e1, e2) -> 
		let e3 = expr_to_vars e1 and e4 = expr_to_vars e2 in
		(match (e3, e4) with
		| (Vars s1, Vars s2) -> Vars (s1^"."^s2)
		| _ -> Nested_vars (e3, e4)
		)
	| Vars_index (s, Const i) -> Vars (s^"_"^(string_of_int i))
	| Vars_index (s, e1) -> Vars_index (s, expr_to_vars e1)
	| _ -> e

let rec var_str_to_int_expr e var_index_tbl = 
	match e with
	| Vars s -> (try Var (Hashtbl.find var_index_tbl s) with Not_found -> print_endline ("Variable "^s^ " is not found in the state variable definitions."); exit 1)
	| State_expr (i, e1) -> State_expr (i, var_str_to_int_expr e1 var_index_tbl)
(*	| Vars_index (s, e1) -> Vars_index (s, var_str_to_int_expr e1 var_index_tbl)*)
	| Vars_index (s, Const i) -> (try Var (Hashtbl.find var_index_tbl (s^"_"^(string_of_int i))) with Not_found -> print_endline ("Variable "^(s^"_"^(string_of_int i))^ " is not found in the state variable definitions."); exit 1)
	| Vars_index (s, e1) -> Vars_index (s, var_str_to_int_expr e1 var_index_tbl)
	| Negi e1 -> Negi (var_str_to_int_expr e1 var_index_tbl)
	| Add (e1, e2) -> Add (var_str_to_int_expr e1 var_index_tbl, var_str_to_int_expr e2 var_index_tbl)
	| Minus (e1, e2) -> Minus (var_str_to_int_expr e1 var_index_tbl, var_str_to_int_expr e2 var_index_tbl)
	| Mult (e1, e2) -> Mult (var_str_to_int_expr e1 var_index_tbl, var_str_to_int_expr e2 var_index_tbl)
	| Ando (e1, e2) -> Ando (var_str_to_int_expr e1 var_index_tbl, var_str_to_int_expr e2 var_index_tbl)
	| Oro (e1, e2) -> Oro (var_str_to_int_expr e1 var_index_tbl, var_str_to_int_expr e2 var_index_tbl)
	| Negb e1 -> Negb (var_str_to_int_expr e1 var_index_tbl)
	| Equal (e1, e2) -> Equal (var_str_to_int_expr e1 var_index_tbl, var_str_to_int_expr e2 var_index_tbl)
	| Mod (e1, e2) -> Mod (var_str_to_int_expr e1 var_index_tbl, var_str_to_int_expr e2 var_index_tbl)
	| LT (e1, e2) -> LT (var_str_to_int_expr e1 var_index_tbl, var_str_to_int_expr e2 var_index_tbl)
	| GT (e1, e2) -> GT (var_str_to_int_expr e1 var_index_tbl, var_str_to_int_expr e2 var_index_tbl)
	| LE (e1, e2) -> LE (var_str_to_int_expr e1 var_index_tbl, var_str_to_int_expr e2 var_index_tbl)
	| GE (e1, e2) -> GE (var_str_to_int_expr e1 var_index_tbl, var_str_to_int_expr e2 var_index_tbl)
	| _ -> let e1 = expr_to_vars e in
		(match e1 with
		| Vars s -> (try Var (Hashtbl.find var_index_tbl s) with Not_found -> print_endline ("Variable "^s^ " is not found in the state variable definitions."); exit 1)
		| _ -> e1)
		

(* useful in evaluating expressions in atomic formulae *)
let rec eval_expr_with_states e sts var_index_tbl = 
	match e with
	| State_expr (v1, e1) -> 
		eval_with_state e1 (List.nth sts v1) var_index_tbl
	| Vars_index (s, e1) -> 
		let e2 = eval_expr_with_states e1 sts var_index_tbl in
		(match e2 with
		| Const i -> Vars (s^"_"^(string_of_int i))
		| _ -> Vars_index (s, e2))
	| Nested_vars (e1, e2) -> 
		let e3 = eval_expr_with_states e1 sts var_index_tbl 
		and e4 = eval_expr_with_states e2 sts var_index_tbl in
		(match (e3, e4) with
		| (Vars s1, Vars s2) -> Vars (s1^"."^s2)
		| _ -> Nested_vars (e3, e4)
		)
	| Negi e1 -> 
		let e2 = eval_expr_with_states e1 sts var_index_tbl in
		(match e2 with
		| Const i -> Const (-i)
		| Negi e3 -> e3
		| _ -> Negi e2
		)
	| Add (e1, e2) -> 
		let e3 = eval_expr_with_states e1 sts var_index_tbl 
		and e4 = eval_expr_with_states e2 sts var_index_tbl in
		(match (e3, e4) with
		| (Const i1, Const i2) -> Const (i1 + i2)
		| _ -> Add (e3, e4)
		)
	| Minus (e1, e2) -> 
		let e3 = eval_expr_with_states e1 sts var_index_tbl 
		and e4 = eval_expr_with_states e2 sts var_index_tbl in
		(match (e3, e4) with
		| (Const i1, Const i2) -> Const (i1 - i2)
		| _ -> Minus (e3, e4)
		)
	| Mult (e1, e2) -> 
		let e3 = eval_expr_with_states e1 sts var_index_tbl 
		and e4 = eval_expr_with_states e2 sts var_index_tbl in
		(match (e3, e4) with
		| (Const i1, Const i2) -> Const (i1 * i2)
		| _ -> Mult (e3, e4)
		)
	| Negb e1 -> 
		let e2 = eval_expr_with_states e1 sts var_index_tbl in
		(match e2 with
		| Const i -> Const (1-i)
		| Negb e3 -> e3
		| _ -> Negb e2
		)
	| Ando (e1, e2) -> 
		let e3 = eval_expr_with_states e1 sts var_index_tbl 
		and e4 = eval_expr_with_states e2 sts var_index_tbl in
		(match (e3, e4) with
		| (Const i1, Const i2) -> Const (if i1 > i2 then i2 else i1)
		| _ -> Ando (e3, e4)
		)
	| Oro (e1, e2) -> 
		let e3 = eval_expr_with_states e1 sts var_index_tbl 
		and e4 = eval_expr_with_states e2 sts var_index_tbl in
		(match (e3, e4) with
		| (Const i1, Const i2) -> Const (if i1 < i2 then i2 else i1)
		| _ -> Oro (e3, e4)
		)
	(*need to be carefully checked*)
	| Equal (e1, e2) -> 
		let e3 = eval_expr_with_states e1 sts var_index_tbl 
		and e4 = eval_expr_with_states e2 sts var_index_tbl in
		if compare_expr e3 e4 = 0 then Const 1 else Const (0) 
	| Mod (e1, e2) -> 
		let e3 = eval_expr_with_states e1 sts var_index_tbl 
		and e4 = eval_expr_with_states e2 sts var_index_tbl in
		(match (e3, e4) with
		| (Const i1, Const i2) -> Const (i1 mod i2)
		| _ -> Mod (e3, e4)
		)
	| LT (e1, e2) -> 
		let e3 = eval_expr_with_states e1 sts var_index_tbl 
		and e4 = eval_expr_with_states e2 sts var_index_tbl in
		(match (e3, e4) with
		| (Const i1, Const i2) -> Const (if i1 < i2 then 1 else (0))
		| _ -> LT (e3, e4)
		)
	| GT (e1, e2) -> 
		let e3 = eval_expr_with_states e1 sts var_index_tbl 
		and e4 = eval_expr_with_states e2 sts var_index_tbl in
		(match (e3, e4) with
		| (Const i1, Const i2) -> Const (if i1 > i2 then 1 else (0))
		| _ -> GT (e3, e4)
		)
	| LE (e1, e2) -> 
		let e3 = eval_expr_with_states e1 sts var_index_tbl 
		and e4 = eval_expr_with_states e2 sts var_index_tbl in
		(match (e3, e4) with
		| (Const i1, Const i2) -> Const (if i1 <= i2 then 1 else (0))
		| _ -> LE (e3, e4)
		)
	| GE (e1, e2) -> 
		let e3 = eval_expr_with_states e1 sts var_index_tbl 
		and e4 = eval_expr_with_states e2 sts var_index_tbl in
		(match (e3, e4) with
		| (Const i1, Const i2) -> Const (if i1 >= i2 then 1 else (0))
		| _ -> GE (e3, e4)
		)
	| _ -> e
and eval_with_state e st var_index_tbl = 
	match st with
	| State ia -> eval_with_array e ia var_index_tbl
	| SVar sv -> e

and eval_with_array e ia var_index_tbl = 
	match e with
	| Var i -> Const (ia.(i))
	| Vars s -> 
		(try 
			Const (ia.(Hashtbl.find var_index_tbl s)) 
		with 
			Not_found -> (print_endline ("variable "^s^" is not in the current state!!!"); exit 1))
	| Vars_index (s, e1) -> let e2 = eval_with_array e1 ia var_index_tbl in Vars_index (s, e2)
	| Nested_vars (e1, e2) -> 
		let s = expand_nested_vars (get_vars e ia var_index_tbl) in 
		(try 
			Const (ia.(Hashtbl.find var_index_tbl s)) 
		with 
			Not_found -> (print_endline ("variable "^s^" is not in the current state!!!"); exit 1))
	| Negi e1 -> 
		let e2 = eval_with_array e1 ia var_index_tbl in 
		(match e2 with
		| Const i -> Const (-i)
		| Negi e3 -> e3
		| _ -> Negi e2)
	| Add (e1, e2) -> 
		let e3 = eval_with_array e1 ia var_index_tbl 
		and e4 = eval_with_array e2 ia var_index_tbl in
		(match (e3, e4) with
		| (Const i1, Const i2) -> Const (i1+i2)
		| _ -> Add (e3, e4))
	| Minus (e1, e2) -> 
		let e3 = eval_with_array e1 ia var_index_tbl 
		and e4 = eval_with_array e2 ia var_index_tbl in
		(match (e3, e4) with
		| (Const i1, Const i2) -> Const (i1-i2)
		| _ -> Minus (e3, e4))
	| Mult (e1, e2) -> 
		let e3 = eval_with_array e1 ia var_index_tbl 
		and e4 = eval_with_array e2 ia var_index_tbl in
		(match (e3, e4) with
		| (Const i1, Const i2) -> Const (i1*i2)
		| _ -> Mult (e3, e4))
	| Negb e1 -> 
		let e2 = eval_with_array e1 ia var_index_tbl in 
		(match e2 with
		| Const i -> Const (1-i)
		| Negb e3 -> e3
		| _ -> Negb e2)
	| Ando (e1, e2) -> 
		let e3 = eval_with_array e1 ia var_index_tbl 
		and e4 = eval_with_array e2 ia var_index_tbl in
		(match (e3, e4) with
		| (Const i1, Const i2) -> Const (if i1 > i2 then i2 else i1)
		| _ -> Ando (e3, e4)
		)
	| Oro (e1, e2) -> 
		let e3 = eval_with_array e1 ia var_index_tbl 
		and e4 = eval_with_array e2 ia var_index_tbl in
		(match (e3, e4) with
		| (Const i1, Const i2) -> Const (if i1 < i2 then i2 else i1)
		| _ -> Oro (e3, e4)
		)
	(*need to be carefully checked*)
	| Equal (e1, e2) -> 
		let e3 = eval_with_array e1 ia var_index_tbl 
		and e4 = eval_with_array e2 ia var_index_tbl in
		if compare_expr e3 e4 = 0 then Const 1 else Const (0) 
	| Mod (e1, e2) -> 
		let e3 = eval_with_array e1 ia var_index_tbl 
		and e4 = eval_with_array e2 ia var_index_tbl in
		(match (e3, e4) with
		| (Const i1, Const i2) -> Const (i1 mod i2)
		| _ -> Mod (e3, e4))
	| LT (e1, e2) -> 
		let e3 = eval_with_array e1 ia var_index_tbl 
		and e4 = eval_with_array e2 ia var_index_tbl in
		(match (e3, e4) with
		| (Const i1, Const i2) -> Const (if i1 < i2 then 1 else (0))
		| _ -> LT (e3, e4)
		)
	| GT (e1, e2) -> 
		let e3 = eval_with_array e1 ia var_index_tbl 
		and e4 = eval_with_array e2 ia var_index_tbl in
		(match (e3, e4) with
		| (Const i1, Const i2) -> Const (if i1 > i2 then 1 else (0))
		| _ -> GT (e3, e4)
		)
	| LE (e1, e2) -> 
		let e3 = eval_with_array e1 ia var_index_tbl 
		and e4 = eval_with_array e2 ia var_index_tbl in
		(match (e3, e4) with
		| (Const i1, Const i2) -> Const (if i1 <= i2 then 1 else (0))
		| _ -> LE (e3, e4)
		)
	| GE (e1, e2) -> 
		let e3 = eval_with_array e1 ia var_index_tbl 
		and e4 = eval_with_array e2 ia var_index_tbl in
		(match (e3, e4) with
		| (Const i1, Const i2) -> Const (if i1 >= i2 then 1 else (0))
		| _ -> GE (e3, e4)
		)
	| _ -> e

and get_vars e ia var_index_tbl = 
	match e with
	| Nested_vars (e1, e2) -> 
		Nested_vars (get_vars e1 ia var_index_tbl, get_vars e2 ia var_index_tbl)
	| Vars_index (s, e1) -> 
		let e2 = eval_with_array e1 ia var_index_tbl in
		(match e2 with
		| Const i -> Vars (s^"_"^(string_of_int i))
		| _ -> Vars_index (s, e2))
	| _ -> e
and expand_nested_vars e = 
	match e with
	| Nested_vars (e1, e2) -> (expand_nested_vars e1)^"."^(expand_nested_vars e2)
	| _ -> "not expanded"






















