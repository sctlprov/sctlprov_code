open Ast

type expr = 
      Symbol of string list
    | Let of pattern * expr
    | Int of int
    (* | Scalar of int *)
    | Float of float
    | Unt
    | Aray of (expr list)
    | Lst of (expr list)
    | Op of string * (expr list)
    | Bool of bool
    | Tuple of (expr list)
    | Record of ((string * expr) list)
    | IF of expr * expr * (expr option)
    | While of expr * expr
    | For of string * expr * expr * expr
    | Seq of expr list
    | Assign of expr * expr
    | Match of expr * ((pattern * expr) list)
    | With of expr * ((string * expr) list)
    | Constr of string * (expr option)
and pattern =
      Pat_Symbol of string
    | Pat_Int of int
    (* | Pat_Scalar of int *)
    | Pat_Float of float
    | Pat_Unt
    | Pat_Aray of (pattern list)
    | Pat_Lst of (pattern list)
    | Pat_Lst_Cons of pattern * pattern
    | Pat_Underline
    | Pat_Tuple of (pattern list)
    (* | Pat_Record of ((string, pattern) array) *)
    | Pat_Constr of string * (pattern option)
and value = 
  | VInt of int
  (* | VScalar of int *)
  | VFloat of float
  | VUnt
  | VBool of bool
  | VAray of (value list)
  | VLst of (value list)
  | VTuple of (value list)
  | VRecord of (string * value) list
  | VConstr of string * (value option)

let rec str_expr e = 
  match e with
  | Symbol str_list -> 
      let rec str_strs strs = 
          match strs with
          | [] -> "<empty_str>"
          | [str] -> str
          | str::strs' -> str^"."^(str_strs strs') in
      str_strs str_list
  | Let (p, e1) -> "let "^(str_pat p)^" = "^(str_expr e1) 
  | Int i -> (string_of_int i)
  (* | Scalar i -> (string_of_int i) *)
  | Float f -> (string_of_float f)
  | Unt -> "()"
  | Aray pel_list -> "[|" ^ (List.fold_left (fun s pel -> s^";"^(str_expr pel)) "" pel_list) ^ "|]"
  | Lst pel_list -> "[" ^ (List.fold_left (fun s pel -> s^";"^(str_expr pel)) "" pel_list) ^ "]"
  | Op (op, pel_list) -> begin
        match op, pel_list with
        | "[]",[pel1; pel2] -> (str_expr pel1)^"["^(str_expr pel2)^"]"
        | "::",[e1; e2] -> (str_expr e1)^" :: "^(str_expr e2)
        | "@", [e1; e2] -> (str_expr e1)^" @ "^(str_expr e2)
        | "!",[pel1] -> "(! "^(str_expr pel1)^")"
        | "&&",[pel1; pel2] -> "("^(str_expr pel1)^"&&"^(str_expr pel2)^")"
        | "||",[pel1; pel2] -> "("^(str_expr pel1)^"||"^(str_expr pel2)^")"
        | "-",[pel1] -> "(- "^(str_expr pel1)^")"
        | "-.",[pel1] -> "(-. "^(str_expr pel1)^")"
        | "+", [pel1; pel2] -> "("^(str_expr pel1)^"+"^(str_expr pel2)^")"
        | "+.", [pel1; pel2] -> "("^(str_expr pel1)^"+."^(str_expr pel2)^")"
        | "-.",[pel1; pel2] -> "("^(str_expr pel1)^"-."^(str_expr pel2)^")"
        | "-",[pel1; pel2] -> "("^(str_expr pel1)^"-"^(str_expr pel2)^")"
        | "*",[pel1; pel2] -> "("^(str_expr pel1)^"*"^(str_expr pel2)^")"
        | "*.",[pel1; pel2] -> "("^(str_expr pel1)^"*."^(str_expr pel2)^")"
        | "=",[pel1; pel2] -> "("^(str_expr pel1)^"="^(str_expr pel2)^")"
        | "!=",[pel1; pel2] -> "("^(str_expr pel1)^"!="^(str_expr pel2)^")"
        | "<",[pel1; pel2] -> "("^(str_expr pel1)^"<"^(str_expr pel2)^")"
        | "<=",[pel1; pel2] -> "("^(str_expr pel1)^"<="^(str_expr pel2)^")"
        | ">",[pel1; pel2] -> "("^(str_expr pel1)^">"^(str_expr pel2)^")"
        | ">=",[pel1; pel2] -> "("^(str_expr pel1)^">="^(str_expr pel2)^")"
        | str, _ -> 
            let tmp_str = ref (str) in
            List.iter (fun pel->tmp_str:= !tmp_str^" "^(str_expr pel)) pel_list;
            !tmp_str
    end
  | Bool b -> string_of_bool b
  | Tuple pel_list ->
      let tmp_str = ref "(" in
      tmp_str := !tmp_str ^ (str_expr (List.hd pel_list));
      List.iter (fun pel -> tmp_str := !tmp_str^","^(str_expr pel)) (List.tl pel_list);
      tmp_str := !tmp_str ^ ")";
      !tmp_str
  | Record str_pel_list -> 
      let tmp_str = ref "{" in
      List.iter (fun (str, pel) -> tmp_str := !tmp_str^str^"="^(str_expr pel)^";") (str_pel_list);
      tmp_str := !tmp_str ^ "}";
      !tmp_str
  | IF (pel1, pel2, opel3) -> begin
          match opel3 with
          | None -> "if "^(str_expr pel1)^" then ("^(str_expr pel2)^")"
          | Some pel3 -> "if "^(str_expr pel1)^" then ("^(str_expr pel2)^") else ("^(str_expr pel3)^")"
      end
  | While (pel1, pel2) -> "while "^(str_expr pel1)^" do \n("^(str_expr pel2)^")\ndone"
  | For (str, pel1, pel2, pel3) -> "for "^str^" from "^(str_expr pel1)^" to "^(str_expr pel2)^" do\n("^(str_expr pel3)^")\ndone"
  | Seq pel_list -> List.fold_left (fun s pel -> s^(str_expr pel)^";\n") "" pel_list
  | Assign (pel1, pel2) -> (str_expr pel1)^" <- "^(str_expr pel2)
  | Match (pel1, ppatl_pel_list) ->
      let tmp_str = ref "match " in
      tmp_str := !tmp_str ^ (str_expr pel1) ^" with\n";
      List.iter (fun (ppatl, pel) -> tmp_str:= !tmp_str^"| "^(str_pat ppatl)^" -> "^(str_expr pel)^"\n") ppatl_pel_list;
      tmp_str := !tmp_str^"\n";
      !tmp_str
  | With (pel1, str_pel_list) ->
      let tmp_str = ref ((str_expr pel1)^" with {") in
      List.iter (fun (str, pel) -> tmp_str := !tmp_str^str^"="^(str_expr pel)^";") str_pel_list;
      tmp_str := !tmp_str^"}";
      !tmp_str
  | Constr (str, None) -> str
  | Constr (str, Some pel1) -> str^" "^(str_expr pel1)
      
and str_pat pat = 
    match pat with
    | Pat_Symbol str -> str
    | Pat_Int i -> string_of_int i
    (* | Pat_Scalar i -> string_of_int i *)
    | Pat_Float f -> string_of_float f
    | Pat_Unt -> "()"
    | Pat_Aray ppatl_list -> 
        if List.length ppatl_list = 0 then 
            "[||]"
        else begin
            let tmp_str = ref "[|" in
            tmp_str := !tmp_str ^ (str_pat (List.hd ppatl_list));
            List.iter (fun ppatl->tmp_str := !tmp_str^";"^(str_pat ppatl)) (List.tl ppatl_list);
            tmp_str := !tmp_str^"|]";
            !tmp_str
        end
    | Pat_Lst ppatl_list -> 
        if List.length ppatl_list = 0 then 
            "[]"
        else begin
            let tmp_str = ref "[" in
            tmp_str := !tmp_str ^ (str_pat (List.hd ppatl_list));
            List.iter (fun ppatl->tmp_str := !tmp_str^";"^(str_pat ppatl)) (List.tl ppatl_list);
            tmp_str := !tmp_str^"]";
            !tmp_str
        end
    | Pat_Lst_Cons (ppatl1, ppatl2) ->
        (str_pat ppatl1)^" :: (" ^(str_pat ppatl2)^")"
    | Pat_Underline -> "_"
    | Pat_Tuple ppatl_list ->
        begin
            let tmp_str = ref "(" in
            tmp_str := !tmp_str ^ (str_pat (List.hd ppatl_list));
            List.iter (fun ppatl->tmp_str := !tmp_str^";"^(str_pat ppatl)) (List.tl ppatl_list);
            tmp_str := !tmp_str^")";
            !tmp_str
        end
    | Pat_Constr (str, oppatl) -> begin
            match oppatl with
            | None -> str
            | Some ppatl -> str^" "^(str_pat ppatl)
        end

let rec str_expr_list el = 
  match el with
  | [] -> ""
  | [e] -> str_expr e
  | e::es -> (str_expr e)^" "^(str_expr_list es)

let rec pexprl_to_expr pel = 
  match pel.pexpr with
  | PSymbol strs -> Symbol strs
  | PLet (ppatl, pel1) -> Let (ppatl_to_pattern ppatl, pexprl_to_expr pel1)
  | PInt i -> Int i
  (* | PScalar i -> Scalar i *)
  | PFloat f -> Float f
  | PUnt -> Unt
  | PAray pel -> Aray (List.map (fun pe -> pexprl_to_expr pe) pel)
  | PLst pel -> Lst (List.map (fun pe -> pexprl_to_expr pe) pel)
  | POp (op, pel_list) -> Op (op, List.map (fun pel->pexprl_to_expr pel) pel_list)
  | PBool b -> Bool b
  | PTuple pels -> Tuple (List.map (fun pel->pexprl_to_expr pel) pels)
  | PRecord str_pel_list -> Record (List.map (fun (str, pel) -> str, pexprl_to_expr pel) str_pel_list)
  | PIF (pel1, pel2, opel3) -> IF (pexprl_to_expr pel1, pexprl_to_expr pel2, Options.bind pexprl_to_expr opel3)
  | PWhile (pel1, pel2) -> While (pexprl_to_expr pel1, pexprl_to_expr pel2)
  | PFor (str, pel1, pel2, pel3) -> For (str, pexprl_to_expr pel1, pexprl_to_expr pel2, pexprl_to_expr pel3)
  | PSeq pels -> Seq (List.map (fun pel -> pexprl_to_expr pel) pels)
  | PAssign (pel1, pel2) -> Assign (pexprl_to_expr pel1, pexprl_to_expr pel2)
  | PMatch (pel1, ppat_pel_list) -> Match (pexprl_to_expr pel1, List.map (fun (ppat, pel) -> ppatl_to_pattern ppat, pexprl_to_expr pel) ppat_pel_list)
  | PWith (pel1, str_pel_list) -> With (pexprl_to_expr pel1, List.map (fun (str, pel) -> str, pexprl_to_expr pel) str_pel_list)
  | PConstr (PConstr_basic str) -> Constr (str, None)
  | PConstr (PConstr_compound (str, pel1)) -> Constr (str, Some (pexprl_to_expr pel1))
and ppatl_to_pattern ppatl = 
  match ppatl.ppat with
  | PPat_Symbol str -> Pat_Symbol str
  | PPat_Int i -> Pat_Int i
  (* | PPat_Scalar i -> Pat_Scalar i *)
  | PPat_Float f -> Pat_Float f
  | PPat_Unt -> Pat_Unt
  | PPat_Aray ppatls -> Pat_Aray (List.map (fun ppatl->ppatl_to_pattern ppatl) ppatls)
  | PPat_Lst ppatls -> Pat_Lst (List.map (fun ppatl->ppatl_to_pattern ppatl) ppatls)
  | PPat_Lst_Cons (ppatl1, ppatl2) -> Pat_Lst_Cons (ppatl_to_pattern ppatl1, ppatl_to_pattern ppatl2)
  | PPat_Underline -> Pat_Underline
  | PPat_Tuple ppatls -> Pat_Tuple (List.map (fun ppatl->ppatl_to_pattern ppatl) ppatls)
  | PPat_Constr (str, opatl) -> Pat_Constr (str, Options.bind ppatl_to_pattern opatl)


let rec str_value v = 
  match v with
  | VInt i -> string_of_int i
  (* | VScalar i -> string_of_int i *)
  | VFloat f -> string_of_float f
  | VUnt -> "()"
  | VBool b -> string_of_bool b
  | VAray va -> "[|"^ (List.fold_left (fun str v1 -> str^(str_value v1)^";") "" va) ^"|]"
  | VLst va -> "["^ (List.fold_left (fun str v1 -> str^(str_value v1)^";") "" va) ^"]"
  | VTuple va -> "("^ (List.fold_left (fun str v1 -> str^(str_value v1)^",") "" va) ^")"
  | VRecord str_value_array -> "{"^ (List.fold_left (fun str (s1,v1) -> str^s1^"="^(str_value v1)^";") "" str_value_array) ^"}"
  | VConstr (str, None) -> str
  | VConstr (str, Some v1) -> str^" "^(str_value v1)
