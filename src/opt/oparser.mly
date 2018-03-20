%{
open Lexing
open Oterm
open Oformula
open Omodul

let parse_error s = ()


(********helper varaiables and functions for the parser*********)
let tmp_parameter_list = ref [] 
let tmp_var_list = ref []
let tmp_symbol_tbl = ref (Hashtbl.create 10)
let tmp_init_assign = ref [] 
let tmp_transitions = ref []
let tmp_fairness = ref []
let tmp_atomic_tbl = ref (Hashtbl.create 5)
let tmp_spec_list = ref []

let clear_tmps () = 
	tmp_parameter_list := [];
	tmp_var_list := [];
	tmp_symbol_tbl := Hashtbl.create 10;
	tmp_init_assign := [];
	tmp_transitions := [];
	tmp_fairness := [];
	tmp_atomic_tbl := Hashtbl.create 5;
	tmp_spec_list := []

let tmp_state_var_list = ref []

let module_tbl = Hashtbl.create 5
let modl = ref {name="";
		parameter_list=[];
		var_list=[];
		symbol_tbl=Hashtbl.create 0;
		init_assign=[];
		transitions=[];
		fairness=[];
		atomic_tbl=Hashtbl.create 0;
		spec_list=[];}

let position_in_var_list v vl = 
  let rec position_from_start v1 vl1 i = 
    match vl1 with
    | [] -> -1
    | (s, e) :: vl1' -> if v1 = s then i else position_from_start v1 vl1' (i+1)
  in position_from_start v vl 0

let position_in_state_var_list sv svl = 
  let rec position_from_start v vl i = 
    match vl with
    | [] -> -1
    | s :: vl' -> if v = s then i else position_from_start v vl' (i+1)
  in position_from_start sv svl 0

(*******tmp function*******)
let rec str_str_list sl = 
	match sl with
	| [] -> ""
	| [s] -> s
	| s :: sl' -> s^","^(str_str_list sl')

(**************************)


let rec find_scalar_position sc vtl = 
  let rec find_str_position s sl i = 
    match sl with
    | [] -> -1
    | s' :: sl' -> if s = s' then i else find_str_position s sl' (i+1) in 
  match vtl with
  | [] -> -1	
  | (s, Scalar_type sl) :: vtl' -> 
     let i1 = find_str_position sc sl 0 in 
     begin
		(*print_endline ("finding the position of "^sc^" in "^(str_str_list sl)^" and result is "^(string_of_int i1));*)
       if i1 = -1 then find_scalar_position sc vtl'
       else i1
     end
  | (s, et) :: vtl' -> find_scalar_position sc vtl'

let rec check_current_symbols stbl = 
  let tmp_s = ref "" in 
  let rec check_symbol s = 
    try
      match s with
      | Const i -> true
(*      | Parameter p -> true*)
      | Var v -> true
(*      | Symbol s1 -> Hashtbl.mem stbl s1*)
			| Vars s1 -> Hashtbl.mem stbl s1
      | Add (e1, e2) -> (check_symbol e1) && (check_symbol e2)
      | Negi e1 -> check_symbol e1
      | Minus (e1, e2) -> (check_symbol e1) && (check_symbol e2)
      | Mult (e1, e2) -> (check_symbol e1) && (check_symbol e2)
      | Negb e1 -> check_symbol e1
      | Ando (e1, e2) -> (check_symbol e1) && (check_symbol e2)
      | Oro (e1, e2) -> (check_symbol e1) && (check_symbol e2)
      | Equal (e1, e2) -> (check_symbol e1) && (check_symbol e2)
      | _ -> false
    with
      Not_found -> false in
  Hashtbl.iter
    (fun a b -> if (!tmp_s = "") then (if not (check_symbol b) then tmp_s := a)) 
    stbl;
  !tmp_s
(***************************************************************)
(* let parse_error s = print_endline s *)
%}

%token Module Model Var Define Init Transition Fairness Atomic Spec 
%token Int Bool Top Bottom AX EX AF EG AR EU Neg
%token Colon Semicolon Comma Dot LB1 RB1 LB2 RB2 LB3 RB3
%token And Or Equal Assigno Add Minus Mult DotDot Scalar Nego Ando Oro Non_equal Mod LT GT LE GE
%token File_end
%token <string>Id 
%token <int>I 
%token <bool>B

//%left Add Minus Mult Ando Oro Nego Mod Neg Equal And Or Scalar
%nonassoc DotDot
%left Or
%left And
%left Oro
%left Ando
%left Add Minus
%left Mult
%left Equal Non_equal LT GT LE GE Mod
%left Nego Neg
%left Dot


%start input
%type <(((string, Omodul.modul0) Hashtbl.t) * Omodul.modul0)>input

%%
input: inputs File_end	{(module_tbl, !modl)}
;

  inputs: 
   | /*empty input*/	{}
   | inputs Module Id LB1 parameters RB1 LB3 var_decl init_decl trans_decl RB3
       {tmp_parameter_list := $5; 
	Hashtbl.add module_tbl $3 
	  {name = $3;
	   parameter_list = !tmp_parameter_list;
	   var_list = !tmp_var_list;
	   symbol_tbl = Hashtbl.create 0;
	   init_assign = !tmp_init_assign;
	   transitions = !tmp_transitions; 
	   fairness = [];
	   atomic_tbl = !tmp_atomic_tbl;
	   spec_list = !tmp_spec_list
	  };
	clear_tmps ()}
   | inputs Module Id LB1 parameters RB1 LB3 var_decl symbol_decl init_decl trans_decl RB3
       {tmp_parameter_list := $5;
	Hashtbl.add module_tbl $3 
	  {name = $3;
	   parameter_list = !tmp_parameter_list;
	   var_list = !tmp_var_list;
	   symbol_tbl = !tmp_symbol_tbl; 
	   init_assign = !tmp_init_assign;
	   transitions = !tmp_transitions;
	   fairness = [];
	   atomic_tbl = !tmp_atomic_tbl;
	   spec_list = !tmp_spec_list
	  }; 
	clear_tmps ()}
   | inputs Model Id LB1 parameters RB1 LB3 var_decl init_decl trans_decl atomic_decl spec_decl RB3
       {tmp_parameter_list := $5; 
	modl := {name = $3;
		 parameter_list = !tmp_parameter_list;
		 var_list = !tmp_var_list;
		 symbol_tbl = Hashtbl.create 0;
		 init_assign = !tmp_init_assign;
		 transitions = !tmp_transitions;
		 fairness = [];
		 atomic_tbl = !tmp_atomic_tbl;
		 spec_list = !tmp_spec_list
		}; (*Hashtbl.add module_tbl $3 !modl;*)
	clear_tmps ()}
   | inputs Model Id LB1 parameters RB1 LB3 var_decl symbol_decl init_decl trans_decl atomic_decl spec_decl RB3	
       {tmp_parameter_list := $5;
	modl := {name = $3;
		 parameter_list = !tmp_parameter_list;
		 var_list = !tmp_var_list; 
		 symbol_tbl = !tmp_symbol_tbl; 
		 init_assign = !tmp_init_assign;
		 transitions = !tmp_transitions; 
		 fairness = [];
		 atomic_tbl = !tmp_atomic_tbl;
		 spec_list = !tmp_spec_list
		}; (*Hashtbl.add module_tbl $3 !modl;*)
	clear_tmps ()}
	| inputs Model Id LB1 parameters RB1 LB3 var_decl init_decl trans_decl atomic_decl fairness_decl spec_decl RB3
       {tmp_parameter_list := $5; 
	modl := {name = $3;
		 parameter_list = !tmp_parameter_list;
		 var_list = !tmp_var_list;
		 symbol_tbl = Hashtbl.create 0;
		 init_assign = !tmp_init_assign;
		 transitions = !tmp_transitions;
		 fairness = !tmp_fairness;
		 atomic_tbl = !tmp_atomic_tbl;
		 spec_list = !tmp_spec_list
		}; (*Hashtbl.add module_tbl $3 !modl;*)
	clear_tmps ()}
   | inputs Model Id LB1 parameters RB1 LB3 var_decl symbol_decl init_decl trans_decl atomic_decl fairness_decl spec_decl RB3	
       {tmp_parameter_list := $5;
	modl := {name = $3;
		 parameter_list = !tmp_parameter_list;
		 var_list = !tmp_var_list; 
		 symbol_tbl = !tmp_symbol_tbl; 
		 init_assign = !tmp_init_assign;
		 transitions = !tmp_transitions; 
		 fairness = !tmp_fairness;
		 atomic_tbl = !tmp_atomic_tbl;
		 spec_list = !tmp_spec_list
		}; (*Hashtbl.add module_tbl $3 !modl;*)
	clear_tmps ()}
;

parameters:
   | /*empty para*/ {[]}
   | Id Colon expr_type	{[($1, $3)]}
   | Id Colon expr_type Comma parameters {($1, $3)::$5}
;

expr_type:
   | LB1 I DotDot I RB1	{Int_type ($2, $4)}
   | Bool	{Bool_type}
   | LB3 scalars RB3	{Scalar_type $2}
   | Id
       {try
	  (let m = Hashtbl.find module_tbl $1 in (Module_type m.name))
	 with Not_found -> (print_endline ("module "^($1)^" is not defined."); exit 1)}
;

scalars: 	
   | {[]}
   | Scalar Id	{[$2]}
   | Scalar Id Comma scalars	{$2 :: $4}
;

var_decl: Var LB3 vars RB3 {tmp_var_list := $3}
;

vars: 	{[]}
	| Id Colon expr_type Semicolon vars	{($1, $3)::$5}
	| Id Colon expr_type LB2 exp RB2 Semicolon vars	{($1, Array_type ($3, $5)) :: $8}
/*		
{	let tmp_vt = ref [] in
			for i=0 to ($5 - 1) do 
				tmp_vt := ($1 ^ "_" ^  (string_of_int i), $3) :: !tmp_vt
			done; !tmp_vt @ $8
		}
*/
;

symbol_decl: Define LB3 symbols RB3	{}
/*
  {let undef_s = check_current_symbols !tmp_symbol_tbl in
   if undef_s = "" then ()
   else print_endline (undef_s^" is not defined."); 
   exit 1}
*/
;

symbols: 	{}
	| symbols Id Assigno dexp Semicolon	{Hashtbl.add !tmp_symbol_tbl $2 $4}
;

dexp:
	| I	{Const $1}
	| B	{Const (if $1 then 1 else 0)}
	| Id	{Vars $1}
	| Id LB2 dexp RB2	{Vars_index ($1, $3)}
/*	    
{let i1 = position_in_var_list $1 !tmp_parameter_list in 
	     if (i1 <> -1) then (Parameter $1) 
	     else 
	       let i2 = position_in_var_list $1 !tmp_var_list in 
	       if(i2 <> -1) then (Var i2) 
	       else (Symbol $1)}
*/
	| dnested_var 	{$1}
	| Scalar Id
	    {let i = find_scalar_position $2 !tmp_var_list in 
	     (if i = -1 then (print_endline ("unknown type for "^$2); exit 1)
	      else Const i)}
	| Minus dexp	{Negi $2}
	| Nego dexp	{Negb $2}
	| dexp Equal dexp	{Equal ($1, $3)}
	| dexp Non_equal dexp	{Negb (Equal ($1, $3))}
	| dexp Ando dexp	{Ando ($1, $3)}
	| dexp Oro dexp 	{Oro ($1, $3)}
	| dexp Add dexp         {Add ($1, $3)}
	| dexp Minus dexp	{Minus ($1, $3)}
	| dexp Mult dexp	{Mult ($1, $3)}
	| dexp Mod dexp	{Mod ($1, $3)}
	| dexp LT dexp	{LT ($1, $3)}
	| dexp GT dexp	{GT ($1, $3)}
	| dexp LE dexp	{LE ($1, $3)}
	| dexp GE dexp	{GE ($1, $3)}
	| LB1 dexp RB1	        {$2}
;	

dnested_var: Id Dot Id	{Nested_vars (Vars $1, Vars $3)}
	| Id LB2 dexp RB2 Dot Id	{Nested_vars (Vars_index ($1, $3), Vars $6)}
	| Id Dot Id LB2 dexp RB2	{Nested_vars (Vars $1, Vars_index ($3, $5))}
	| Id LB2 dexp RB2 Dot Id LB2 dexp RB2	{Nested_vars (Vars_index ($1, $3), Vars_index ($6, $8))}
	| Id Dot dnested_var		{Nested_vars (Vars $1, $3)}
	| Id LB2 dexp RB2 Dot dnested_var	{Nested_vars (Vars_index ($1, $3), $6)}
//	| LB1 dnested_var RB1	{$2}
;

init_decl: Init LB3 inis RB3
  {tmp_init_assign := $3}
;

inis: 	{[]}
	| Id Assigno exp Semicolon inis	{(Expr $3) :: $5}
	| Id Assigno LB3 exps RB3 Semicolon inis	{(Expr (Aray $4)) :: $7}
	| Id Assigno LB3 exp RB3 Semicolon inis 	{(Expr (Aray [$4])) :: $7}
	| Id Assigno Id LB1 exps RB1 Semicolon inis {(Module_instance ($3, $5)) :: $8}
	| Id Assigno Id LB1 exp RB1 Semicolon inis {(Module_instance ($3, [$5])) :: $8}
	| Id Assigno Id LB1 RB1 Semicolon inis {(Module_instance ($3, [])) :: $7}
;

exps: exp Comma exp	{[$1; $3]}
	| exp Comma exps	{$1 :: $3}
	/* | exp Comma exps {$1 :: $3} */
;

state_expr: 
		  I	{Const $1}
		| B	{Const (if $1 then 1 else 0)}
		| Id LB1 exp RB1	{let i1 = position_in_state_var_list $1 !tmp_state_var_list in 
								if (i1 = -1) then
								begin
								print_endline ("state variable "^$1^" is not defined."); 
								exit 1;
								end;
								State_expr (i1, $3)}
		| Minus state_expr	{Negi $2}
		| Nego state_expr {Negb $2}
		| state_expr Equal state_expr	{Equal ($1, $3)}
		| state_expr Non_equal state_expr	{Negb (Equal ($1, $3))}
		| state_expr Ando state_expr	{Ando ($1, $3)}
		| state_expr Oro state_expr	{Oro ($1, $3)}
		| state_expr Add state_expr	{Add ($1, $3)}
		| state_expr Minus state_expr	{Minus ($1, $3)}
		| state_expr Mult state_expr	{Mult ($1, $3)}
		| state_expr Mod state_expr	{Mod ($1, $3)}
		| state_expr LT state_expr	{LT ($1, $3)}
		| state_expr GT state_expr	{GT ($1, $3)}
		| state_expr LE state_expr	{LE ($1, $3)}
		| state_expr GE state_expr	{GE ($1, $3)}
		| LB1 state_expr RB1	{$2}
;

exp:	
	| I	{Const $1}
	| B	{Const (if $1 then 1 else 0)}
	| Id	{Vars $1}
	| Id LB2 exp RB2	{Vars_index ($1, $3)}
	| nested_var 	{$1}
	| Scalar Id	
	    {let i = find_scalar_position $2 !tmp_var_list in
	     if i = -1 then (print_endline ("unknown type for "^$2); exit 1)
	     else (Const i)}
	| Minus exp		{Negi $2}
	| Nego exp		{Negb $2}
	| exp Equal exp	{Equal ($1, $3)}
	| exp Non_equal exp	{Negb (Equal ($1, $3))}
	| exp Ando exp	{Ando ($1, $3)}
	| exp Oro exp	{Oro ($1, $3)}
	| exp Add exp	{Add ($1, $3)}
	| exp Minus exp	{Minus ($1, $3)}
	| exp Mult exp	{Mult ($1, $3)}
	| exp Mod exp	{Mod ($1, $3)}
	| exp LT exp	{LT ($1, $3)}
	| exp GT exp	{GT ($1, $3)}
	| exp LE exp	{LE ($1, $3)}
	| exp GE exp	{GE ($1, $3)}
	| LB1 exp RB1	{$2}
;

nested_var: Id Dot Id	{Nested_vars (Vars $1, Vars $3)}
	| Id LB2 exp RB2 Dot Id	{Nested_vars (Vars_index ($1, $3), Vars $6)}
	| Id Dot Id LB2 exp RB2	{Nested_vars (Vars $1, Vars_index ($3, $5))}
	| Id LB2 exp RB2 Dot Id LB2 exp RB2	{Nested_vars (Vars_index ($1, $3), Vars_index ($6, $8))}
	| Id Dot nested_var		{Nested_vars (Vars $1, $3)}
	| Id LB2 exp RB2 Dot nested_var	{Nested_vars (Vars_index ($1, $3), $6)}
//	| LB1 nested_var RB1	{$2}
;

trans_decl: Transition LB3 trans RB3	
  {tmp_transitions := $3}
;

trans: 	{[]}
	| exp Colon LB3 rests RB3 Semicolon trans	{($1, $4) :: $7}
;

rests: 	{[]}
	| Id Assigno exp Semicolon rests	{(Vars $1, $3) :: $5}
	| Id LB2 exp RB2 Assigno exp Semicolon rests	{(Vars_index ($1, $3), $6) :: $8}
/*
	    {let i = position_in_var_list $1 !tmp_var_list in
	     (if i = -1 then (print_endline ($1^" is not defined."); exit 1); (i, $3) :: $5 )}
*/
;

fairness_decl: Fairness LB3 fairness RB3	{tmp_fairness := $3}
;

fairness:	{[]}
	/* | Id LB1 Id RB1 Semicolon fairness	{(Atomic($1, [SVar $3])) :: $6} */
	| fml Semicolon fairness	{$1 :: $3}
;

/*
fairness_decl: Fairness LB3 fairness RB3	{tmp_fairness := $3}
;

fairness:	{[]}
	| exp Semicolon fairness	{$1 :: $3}
;
*/

atomic_decl: Atomic LB3 atomics RB3
  {tmp_state_var_list := []}
;

atomics: 	{}
	| atomics Id LB1 bound_var RB1 Assigno state_expr Semicolon	
	    {Hashtbl.add !tmp_atomic_tbl $2 $7}
;

bound_var: bound_vars	{tmp_state_var_list := $1}
;

bound_vars: 	{[]}
	| Id	{[$1]}
	| Id Comma bound_vars 	{$1 :: $3}
;

spec_decl: Spec LB3 specs RB3	
  {tmp_spec_list := $3}
;

specs: 	{[]}
	| Id Assigno fml Semicolon specs	{($1, $3) :: $5}
;

fml: 	Top	{Top}
	| Bottom	{Bottom}
	| Id LB1 atom_fml_para RB1	{Atomic ($1, $3)}
	| Id LB1 RB1	{Atomic ($1, [])}
	| Id LB1 Id RB1	{Atomic ($1, [SVar $3])}
	| Neg fml	{Neg $2}
	| fml And fml	{And ($1, $3)}
	| fml Or fml	{Or ($1, $3)}
	| AX LB1 Id Comma fml Comma Id RB1	{AX (SVar $3, $5, SVar $7)}
	| EX LB1 Id Comma fml Comma Id RB1	{EX (SVar $3, $5, SVar $7)}
	| AF LB1 Id Comma fml Comma Id RB1	{AF (SVar $3, $5, SVar $7)}
	| EG LB1 Id Comma fml Comma Id RB1	{EG (SVar $3, $5, SVar $7)}
	| AR LB1 Id Comma Id Comma fml Comma fml Comma Id RB1
	    {AR (SVar $3, SVar $5, $7, $9, SVar $11)}
	| EU LB1 Id Comma Id Comma fml Comma fml Comma Id RB1
	    {EU (SVar $3, SVar $5, $7, $9, SVar $11)}
	| LB1 fml RB1 	{$2}
; 

atom_fml_para: Id Comma Id 	{[(SVar $1); (SVar $3)]}
	| Id Comma atom_fml_para	{(SVar $1) :: $3}
;

%%

