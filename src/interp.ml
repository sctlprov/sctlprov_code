open Ast
open Expr
open Formula
open Dep

type modul = {
    imported: string list;
    (* ctx: (string*value) list; *)
    vars: (string, value) Hashtbl.t;
    functions: (string, ((pattern list) * expr)) Hashtbl.t;
}

type trans_def = 
    | Case of ((expr * expr) list)
    | No_case of expr

type model = {
    (* transition: (pattern * expr); *)
    mutable state_type: ptyp;
    transition : pattern * trans_def;
    atomic: (string, (string list)*expr) Hashtbl.t;
    fairness: formula list;
    properties: (string * formula) list;
}

type runtime = {
    moduls: (string, modul) Hashtbl.t;
    mutable model: model;
}

exception Evaluation_error of string
exception No_matched_pattern of value

type context = (string * value ref) list

let modify_ctx ctx str value = Refpairs.replace_first ctx str value
(* let add_to_ctx ctx str value = (str, value)::ctx *)

let rec value_of_str str runtime modul = 
    let m = Hashtbl.find runtime.moduls modul in
    if Hashtbl.mem m.vars str then
        Hashtbl.find m.vars str
    else begin
        let found_in_imported = ref false 
        and value = ref (VInt 0) in
        List.iter (fun mname -> 
            if not !found_in_imported then begin
                let m = Hashtbl.find runtime.moduls mname in
                if Hashtbl.mem m.vars str then begin
                    value := Hashtbl.find m.vars str;
                    found_in_imported := true
                end
            end
        ) m.imported;
        if !found_in_imported then
            !value
        else
            raise (Evaluation_error ("can not find binding of "^str))
    end

let rec value_of_str_path value strs =
    match strs with
    | [] -> value
    | str::strs' -> begin
            match value with
            | VRecord str_value_list -> 
                if Pairs.key_exists str_value_list str then
                    value_of_str_path (Pairs.get_value str_value_list str) strs'
                else
                    raise (Evaluation_error (" does not have field "^str^": "^(str_value value)))
            | _ -> raise (Evaluation_error (" should be a record with field "^str^": "^(str_value value)))
        end

let rec modified_record_value rv str_list value = 
    match str_list with
    | [] -> value
    | str::strs -> begin
            match rv with
            | VRecord str_value_list -> VRecord (Pairs.replace_first str_value_list str (modified_record_value (Pairs.get_value str_value_list str) strs value))
            | _ -> raise (Evaluation_error ((str_value rv)^" should be a record value."))
        end

let rec get_matched_pattern value pat_expr_list = 
    match value, pat_expr_list with
    | _, [] -> 
        print_endline ("can not match value with empty pattern: "^(str_value value));
        raise (No_matched_pattern value)
    | _, (Pat_Underline, expr)::pel -> [], expr
    | _, (Pat_Symbol str, expr)::pel -> [(str, ref value)], expr
    | VInt i, (Pat_Int j, expr)::pel -> if i = j then [], expr else get_matched_pattern value pel
    (* | VScalar i, (Pat_Scalar j, expr)::pel -> if i = j then [], expr else get_matched_pattern value pel  *)
    (* | VInt i, (Pat_Symbol str, expr)::pel -> [(str, VInt i)], expr *)
    | VFloat f, (Pat_Float g, expr)::pel -> if f = g then [], expr else get_matched_pattern value pel
    (* | VFloat f, (Pat_Symbol str, expr)::pel -> [(str, VFloat f)], expr *)
    | VUnt, (Pat_Unt, expr)::pel -> [], expr
    (* | VBool b, (VBool c, expr)::pel -> if b=c then [], expr else get_matched_pattern value pel *)
    | VLst [], (Pat_Lst [], expr)::pel -> [], expr
    | VAray vl, (Pat_Aray pl, expr)::pel 
    | VLst vl, (Pat_Lst pl, expr)::pel ->
        if List.length vl <> List.length pl then
            get_matched_pattern value pel
        else begin
            let ctx = ref [] in
            try
                for i = 0 to List.length vl - 1 do
                    let ctx0, _ = get_matched_pattern (List.nth vl i) [(List.nth pl i, expr)] in
                    ctx := !ctx @ ctx0    
                done;
                !ctx, expr
            with No_matched_pattern _ -> get_matched_pattern value pel    
        end
    | VLst vl, (Pat_Lst_Cons (p1, p2), expr)::pel ->
        if List.length vl = 0 then
            get_matched_pattern value pel
        else begin
            try
                let vh, vt = List.hd vl, List.tl vl in
                let ctx1, _ = get_matched_pattern vh [(p1, expr)] 
                and ctx2, _ = get_matched_pattern (VLst vt) [(p2, expr)] in
                ctx1 @ ctx2, expr
            with No_matched_pattern _ -> get_matched_pattern value pel
        end
    | VTuple vl, (Pat_Tuple pl, expr)::pel ->
        if List.length vl <> List.length pl then
            get_matched_pattern value pel
        else begin
            let ctx = ref [] in
            try
                for i = 0 to List.length vl - 1 do
                    let ctx0, _ = get_matched_pattern (List.nth vl i) [(List.nth pl i, expr)] in
                    ctx := !ctx @ ctx0    
                done;
                !ctx, expr
            with No_matched_pattern _ -> get_matched_pattern value pel    
        end
    | VConstr (str1, None), (Pat_Constr (str2, None), expr)::pel ->
        if str1 = str2 then
            [], expr
        else
            get_matched_pattern value pel
    | VConstr (str1, Some v1), (Pat_Constr (str2, Some p1), expr)::pel ->
        if str1 <> str2 then
            get_matched_pattern value pel
        else begin
            try
                let ctx, _ = get_matched_pattern v1 [(p1, expr)] in
                ctx, expr
            with No_matched_pattern _ -> get_matched_pattern value pel
        end
    | _, _::pel -> get_matched_pattern value pel

let find_function str runtime modul = 
    (* print_endline ("finding function "^str^" in modul "^modul); *)
    let m = Hashtbl.find runtime.moduls modul in
    if Hashtbl.mem m.functions str then
        Hashtbl.find m.functions str
    else begin
        let found = ref false in
        let f = ref ([], Int 0) in
        List.iter (fun mname ->
            if not !found then
                let m = Hashtbl.find runtime.moduls mname in
                if Hashtbl.mem m.functions str then
                    f := Hashtbl.find m.functions str
        ) m.imported;
        if !found then !f else raise (Evaluation_error ("function "^str^" is not defined in the scope of "^modul))
    end

let rec evaluate_seq exprs ctx runtime modul = 
  match exprs with
  | [] -> raise (Evaluation_error "error evaluating seq expr")
  | [e] -> evaluate e ctx runtime modul 
  | e :: es -> begin
      match e with
      | Let (p, e1) -> 
        let v = evaluate e1 ctx runtime modul in
        let ctx1,_ = get_matched_pattern v [(p, e1)] in
        evaluate_seq es (ctx1 @ ctx) runtime modul
      | _ -> let _ = evaluate e ctx runtime modul in evaluate_seq es ctx runtime modul
    end  
and evaluate expr ctx runtime modul = 
  match expr with
    | Int i -> VInt i
    (* | Scalar i -> VScalar i *)
    | Float f -> VFloat f
    | Unt -> VUnt
    | Bool b -> VBool b
    | Symbol str_list -> begin
        match str_list with
        | [] -> raise (Evaluation_error "can not evaluate an empty symbol")
        | [str] -> 
            if str = (String.capitalize_ascii str) then
                raise (Evaluation_error ("can not evaluate a modul name as a symbol: "^str))
            else begin
                match Refpairs.find ctx str with
                | None -> value_of_str str runtime modul 
                | Some v -> v
            end 
        | str::strs ->
            if str = (String.capitalize_ascii str) then
                value_of_str_path (value_of_str (List.hd strs) runtime str) (List.tl strs)
            else if Pairs.key_exists ctx str then
                value_of_str_path (Refpairs.get_value ctx str) strs
            else
                value_of_str_path (value_of_str str runtime modul) strs
        end
    (* | Val_binding _ | Var_binding _ -> raise (Evaluation_error "should not bind variables in the last expression") *)
    | Let _ -> raise (Evaluation_error "should not bind variables in the last expression") 
    | Aray ea -> VAray (List.map (fun e -> evaluate e ctx runtime modul) ea)
    | Lst ea -> VLst (List.map (fun e -> evaluate e ctx runtime modul) ea)
    | Op (op, el) -> begin
            match op, el with
            | "[]", [e1; e2] -> 
                let v1 = evaluate e1 ctx runtime modul 
                and v2 = evaluate e2 ctx runtime modul in begin
                    match v1,v2 with
                    | VAray va, VInt i -> List.nth va i
                    | _ -> raise (Evaluation_error ((str_value v1)^" should be an array value, and "^(str_value v2)^" should be an integer value."))
                end
            | "::", [e1; e2] ->
                let v1 = evaluate e1 ctx runtime modul
                and v2 = evaluate e2 ctx runtime modul in begin
                    match v2 with
                    | VLst vl -> VLst (v1::vl)    
                    | _ -> raise (Evaluation_error ((str_value v2)^" should be a list value."))
                end
            | "@", [e1; e2] ->
                let v1 = evaluate e1 ctx runtime modul 
                and v2 = evaluate e2 ctx runtime modul in begin
                    match v1, v2 with
                    | VLst vl1, VLst vl2 -> VLst (vl1 @ vl2)
                    | VLst vl1, _ -> raise (Evaluation_error ((str_value v2)^" should be a list value."))
                    | _ -> raise (Evaluation_error ("both "^(str_value v1)^" and "^(str_value v2)^" should be a list value."))
                end
            | "!", [e1] ->
                let v1 = evaluate e1 ctx runtime modul in begin
                    match v1 with
                    | VBool b -> VBool (not b)
                    | _ -> raise (Evaluation_error ((str_value v1)^" is not a bool value."))    
                end
            | "&&", [e1; e2] -> 
                let v1 = evaluate e1 ctx runtime modul in
                if v1 = VBool true then
                    let v2 = evaluate e2 ctx runtime modul in begin
                        match v2 with
                        | VBool b -> VBool b
                        | _ -> raise (Evaluation_error "can not evaluate to bool value.")
                    end
                else 
                    VBool false
                (* and v2 = evaluate e2 ctx runtime modul in begin
                    match v1, v2 with
                    | VBool b1, VBool b2 -> VBool (b1 && b2)
                    | _ -> raise (Evaluation_error "can not evaluate to bool value.")    
                end *)
            | "||", [e1; e2] ->
                let v1 = evaluate e1 ctx runtime modul in
                if v1 = VBool true then
                    VBool true
                else if v1 = VBool false then
                    let v2 = evaluate e2 ctx runtime modul in begin
                        match v2 with
                        | VBool b -> v2
                        | _ -> raise (Evaluation_error "can not evaluate to bool value.")
                    end
                else
                    raise (Evaluation_error "can not evaluate to bool value.")

                    (* match v1, v2 with
                    | VBool b1, VBool b2 -> VBool (b1 || b2)
                    | _ -> raise (Evaluation_error "can not evaluate to bool value.")    
                end *)
            | "-", [e1] ->
                let v1 = evaluate e1 ctx runtime modul in begin
                    match v1 with
                    | VInt i -> VInt (-i)
                    | _ -> raise (Evaluation_error ("is not a integer value: "^(str_value v1)))    
                end
            | "-.", [e1] -> 
                let v1 = evaluate e1 ctx runtime modul in begin
                    match v1 with
                    | VFloat f -> VFloat (0. -. f)
                    | _ -> raise (Evaluation_error ("is not a float value."^(str_value v1)))    
                end
            | "+", [e1; e2] ->
                let v1 = evaluate e1 ctx runtime modul 
                and v2 = evaluate e2 ctx runtime modul in begin
                    match v1, v2 with
                    | VInt i1, VInt i2 -> VInt (i1+i2)
                    | _ -> raise (Evaluation_error "can not evaluate to integer value.")    
                end
            | "+.", [e1; e2] ->
                let v1 = evaluate e1 ctx runtime modul 
                and v2 = evaluate e2 ctx runtime modul in begin
                    match v1, v2 with
                    | VFloat f1, VFloat f2 -> VFloat (f1+.f2)
                    | _ -> raise (Evaluation_error "can not evaluate to integer value.")    
                end
            | "-", [e1; e2] ->
                let v1 = evaluate e1 ctx runtime modul 
                and v2 = evaluate e2 ctx runtime modul in begin
                    match v1, v2 with
                    | VInt i1, VInt i2 -> VInt (i1-i2)
                    | _ -> raise (Evaluation_error "can not evaluate to integer value.")    
                end
            | "-.", [e1; e2] ->
                let v1 = evaluate e1 ctx runtime modul 
                and v2 = evaluate e2 ctx runtime modul in begin
                    match v1, v2 with
                    | VFloat f1, VFloat f2 -> VFloat (f1-.f2)
                    | _ -> raise (Evaluation_error "can not evaluate to float value.")    
                end
            | "*", [e1; e2] ->
                let v1 = evaluate e1 ctx runtime modul 
                and v2 = evaluate e2 ctx runtime modul in begin
                    match v1, v2 with
                    | VInt i1, VInt i2 -> VInt (i1*i2)
                    | _ -> raise (Evaluation_error "can not evaluate to integer value.")    
                end
            | "*.", [e1; e2] ->
                let v1 = evaluate e1 ctx runtime modul 
                and v2 = evaluate e2 ctx runtime modul in begin
                    match v1, v2 with
                    | VFloat i1, VFloat i2 -> VFloat (i1*.i2)
                    | _ -> raise (Evaluation_error "can not evaluate to integer value.")    
                end
            | "=", [e1; e2] ->
                let v1 = evaluate e1 ctx runtime modul 
                and v2 = evaluate e2 ctx runtime modul in
                VBool (v1 = v2)
            | "!=", [e1; e2] ->
                let v1 = evaluate e1 ctx runtime modul 
                and v2 = evaluate e2 ctx runtime modul in
                VBool (v1 <> v2)
            | "<", [e1; e2] ->
                let v1 = evaluate e1 ctx runtime modul 
                and v2 = evaluate e2 ctx runtime modul in
                VBool (v1 < v2)
            | "<=", [e1; e2] ->
                let v1 = evaluate e1 ctx runtime modul 
                and v2 = evaluate e2 ctx runtime modul in
                VBool (v1 <= v2)
            | ">", [e1; e2] ->
                let v1 = evaluate e1 ctx runtime modul 
                and v2 = evaluate e2 ctx runtime modul in
                VBool (v1 > v2)
            | ">=", [e1; e2] ->
                let v1 = evaluate e1 ctx runtime modul 
                and v2 = evaluate e2 ctx runtime modul in
                VBool (v1 >= v2)
            | str, es ->
                (try 
                    let pats, e1 = find_function str runtime modul in
                    if List.length es <> List.length pats then 
                        raise (Evaluation_error ("function "^str^" has "^(string_of_int (List.length pats))^" parameters, but is applied to "^(string_of_int (List.length es))^" arguments."))
                    else begin
                        let ctx0 = ref [] in
                        for i = 0 to List.length es - 1 do
                            let e1 = List.nth es i in
                            let ctx1, _ = get_matched_pattern (evaluate e1 ctx runtime modul) [(List.nth pats i, e1)] in
                            ctx0 := ctx1 @ !ctx0
                        done;
                        evaluate e1 (!ctx0 @ ctx) runtime modul
                    end
                with e -> print_endline ("error when evaluation function "^str); raise e)
        end
    | Tuple ea -> VTuple (List.map (fun e -> evaluate e ctx runtime modul) ea)
    | Record str_expr_array -> VRecord ((List.map (fun (str, expr) -> str, evaluate expr ctx runtime modul) str_expr_array))
    | IF (e1, e2, None) ->
        let v1 = evaluate e1 ctx runtime modul in
        if v1 = VBool true then
            evaluate e2 ctx runtime modul
        else if v1 = VBool false then
            VUnt
        else
            raise (Evaluation_error (" should be a bool value: "^(str_value v1)))
    | IF (e1, e2, Some e3) ->
        let v1 = evaluate e1 ctx runtime modul in
        if v1 = VBool true then
            evaluate e2 ctx runtime modul
        else if v1 = VBool false then
            evaluate e3 ctx runtime modul
        else
            raise (Evaluation_error (" should be a bool value: "^(str_value v1)))
    | While (e1, e2) ->
        let v1 = ref (evaluate e1 ctx runtime modul) in
        while (!v1 = VBool true) do
            ignore(evaluate e2 ctx runtime modul);
            v1 := evaluate e1 ctx runtime modul
        done;
        VUnt
    | For (str, e1, e2, e3) ->
        let v1 = evaluate e1 ctx runtime modul 
        and v2 = evaluate e2 ctx runtime modul in begin
            match v1, v2 with
            | VInt i, VInt j -> 
                let ctx0 = Refpairs.add_to_first ctx str v1 in
                if i<=j then begin
                    for counter = i to j do
                        Refpairs.replace_first ctx0 str (VInt counter);
                        ignore(evaluate e3 ctx0 runtime modul)    
                    done;
                    VUnt
                end else begin
                    for counter = i downto j do
                        Refpairs.replace_first ctx0 str (VInt counter);
                        ignore(evaluate e3 ctx0 runtime modul)
                    done;
                    VUnt
                end
            | _ -> raise (Evaluation_error "error evaluating for expression.")    
        end
    | Seq es -> evaluate_seq es ctx runtime modul
    | Assign (e1, e2) -> begin
            match e1 with
            | Symbol str_list -> begin
                    match str_list with
                    | [] -> raise (Evaluation_error "can not assign to an empty symbol.")
                    | [str] -> modify_ctx ctx str (evaluate e2 ctx runtime modul); VUnt
                    | str::strs -> modify_ctx ctx str (modified_record_value (Refpairs.get_value ctx str) strs (evaluate e2 ctx runtime modul)); VUnt
                end
            | Op ("[]", [Symbol [s]; e3]) -> begin
                    if not (Pairs.key_exists ctx s) then
                        raise (Evaluation_error (s^" is not defined."));
                    match Refpairs.get_value ctx s with
                    | VAray vl -> begin
                            match evaluate e3 ctx runtime modul with
                            | VInt i -> 
                                if i > List.length vl then
                                    raise (Evaluation_error ("index out of bounds: "^(string_of_int i)));
                                let index = ref (-1) in 
                                let new_vl = List.map (fun v -> incr index; if !index = i then evaluate e2 ctx runtime modul else v) vl in
                                modify_ctx ctx s (VAray new_vl); VUnt
                            | _ -> raise (Evaluation_error ("can not evaluate to an int value: "^(str_expr e3)))
                        end 
                    | _ -> raise (Evaluation_error (s^" is not bounded to an array"))
                end
            | _ -> raise (Evaluation_error ("error evaluating assign expr."))
        end        
    | Match (e1, pat_expr_list) -> 
        let v1 = evaluate e1 ctx runtime modul in
        let ctx0, e1 = get_matched_pattern v1 pat_expr_list in
        evaluate e1 (ctx0 @ ctx) runtime modul
    | With (e1, str_expr_list) -> 
        let v1 = evaluate e1 ctx runtime modul in begin
            match v1 with
            | VRecord str_value_list -> VRecord (List.fold_left (fun svl (str, expr) -> Pairs.replace_first svl str (evaluate expr ctx runtime modul)) str_value_list str_expr_list)
            | _ -> raise (Evaluation_error ("should be a record value: "^(str_value v1)))    
        end
    | Constr (str, None) -> VConstr (str, None)
    | Constr (str, Some e1) -> VConstr (str, Some (evaluate e1 ctx runtime modul))
            

let pstate_to_state ps runtime modul = 
    match ps with
    | PSVar str -> SVar str
    | PState pst -> State (evaluate (pexprl_to_expr pst) [] runtime modul)
    
let rec pfmll_to_fml pfmll runtime modul = 
    match pfmll.pfml with
    | PTop -> Top 
    | PBottom -> Bottom
    | PAtomic (str, pels) -> Atomic (str, List.map (fun pel -> 
            pstate_to_state pel runtime modul
        ) pels)
    | PNeg pfml1 -> Neg (pfmll_to_fml pfml1 runtime modul)
    | PAnd (pfml1, pfml2) -> And (pfmll_to_fml pfml1 runtime modul, pfmll_to_fml pfml2 runtime modul)
    | POr (pfml1, pfml2) -> Or (pfmll_to_fml pfml1 runtime modul, pfmll_to_fml pfml2 runtime modul)
    | PAX (str, pfml1, pel1) -> AX (str, pfmll_to_fml pfml1 runtime modul, pstate_to_state pel1 runtime modul)
    | PEX (str, pfml1, pel1) -> EX (str, pfmll_to_fml pfml1 runtime modul, pstate_to_state pel1 runtime modul)
    | PAF (str, pfml1, pel1) -> AF (str, pfmll_to_fml pfml1 runtime modul, pstate_to_state pel1 runtime modul)
    | PEG (str, pfml1, pel1) -> EG (str, pfmll_to_fml pfml1 runtime modul, pstate_to_state pel1 runtime modul)
    | PAR (str1, str2, pfml1, pfml2, pel1) -> AR (str1, str2, pfmll_to_fml pfml1 runtime modul, pfmll_to_fml pfml2 runtime modul, pstate_to_state pel1 runtime modul)
    | PEU (str1, str2, pfml1, pfml2, pel1) -> EU (str1, str2, pfmll_to_fml pfml1 runtime modul, pfmll_to_fml pfml2 runtime modul, pstate_to_state pel1 runtime modul)
    
	  
let rec preprocess_fml fml runtime modul =
    match fml with
    | Atomic (str, ss) -> Atomic(str, List.map (fun s ->
            match s with
            | SVar sv -> State (evaluate (Symbol [sv]) [] runtime modul)
            | _ -> s
        ) ss)
    | Neg fml1 -> Neg (preprocess_fml fml1 runtime modul)
    | And (fml1, fml2) -> And (preprocess_fml fml1 runtime modul, preprocess_fml fml2 runtime modul)
    | Or (fml1, fml2) -> Or (preprocess_fml fml1 runtime modul, preprocess_fml fml2 runtime modul)
    | AX (str, fml1, SVar sv) -> AX (str, fml1, State (evaluate (Symbol [sv]) [] runtime modul))
    | EX (str, fml1, SVar sv) -> EX (str, fml1, State (evaluate (Symbol [sv]) [] runtime modul))
    | AF (str, fml1, SVar sv) -> AF (str, fml1, State (evaluate (Symbol [sv]) [] runtime modul))
    | EG (str, fml1, SVar sv) -> EG (str, fml1, State (evaluate (Symbol [sv]) [] runtime modul))
    | AR (str1, str2, fml1, fml2, SVar sv) -> AR (str1, str2, fml1, fml2, State (evaluate (Symbol [sv]) [] runtime modul))
    | EU (str1, str2, fml1, fml2, SVar sv) -> EU (str1, str2, fml1, fml2, State (evaluate (Symbol [sv]) [] runtime modul))
    | _ -> fml
    
let pkripke_model_to_model (pkm:pkripke_model) runtime modul = 
    let trans = 
    match snd pkm.transition with
    | PCase case_nexts -> Case (List.map (fun (e1,e2) -> pexprl_to_expr e1, pexprl_to_expr e2) case_nexts)
    | PNo_case no_case_nexts -> No_case (pexprl_to_expr no_case_nexts) in
    {
        state_type = pkm.state_type;
        transition = (ppatl_to_pattern (fst pkm.transition), trans);
        atomic = (
                let atomic_tbl = Hashtbl.create 1 in
                Hashtbl.iter (fun str (args, pel) -> Hashtbl.add atomic_tbl str (args, pexprl_to_expr pel)) pkm.atomic;
                (* print_endline ("added "^(string_of_int (Hashtbl.length atomic_tbl))^" atomic definitions."); *)
                atomic_tbl
            );
        fairness = List.map (fun pfl -> pfmll_to_fml pfl runtime modul) pkm.fairness;
        properties = List.map (fun (str, pfmll) -> 
        let fml = preprocess_fml (pfmll_to_fml pfmll runtime modul) runtime modul in
        str, fml
        (* match fml with
        | Atomic (pred, ss) -> 
            str, Atomic (pred, List.map ( fun s ->
                match s with
                | State _ -> s
                | SVar sv -> begin
                        try
                            State (evaluate (Symbol [sv]) [] runtime modul)
                        with _ -> s
                    end
            ) ss)
        | _ -> str, fml *)
        ) pkm.properties;
    }

let pmoduls_to_runtime pmoduls pkripke_model start_modul =
    let dummy_kripke_model = {
        state_type = PTVar (-1);
        transition = (Pat_Symbol "", Case []);
        atomic = Hashtbl.create 0;
        fairness = [];
        properties = [];
    } in
    let runtime = {
        moduls = Hashtbl.create 1;
        model = dummy_kripke_model;
    } in
    (* let moduls = Hashtbl.create 1 in *)
    let dep_graph = Dep.dep_graph_of_pmodul start_modul pmoduls in
    let rec modify_runtime dg =
        match dg with
        | Leaf mname -> 
            let m = Hashtbl.find pmoduls mname in 
            let modul = {
                imported = m.imported;
                vars = begin
                        let tmp_vars = Hashtbl.create 1 in
                        Hashtbl.iter (fun str (_, ast) ->
                            match ast with
                            | PExpr_loc (_, pel) -> Hashtbl.add tmp_vars str (evaluate (pexprl_to_expr pel) [] runtime mname)
                            | _ -> ()
                        ) m.psymbol_tbl;
                        tmp_vars
                    end;
                functions = begin
                        let tmp_funs = Hashtbl.create 1 in
                        Hashtbl.iter (fun str (_, ast) ->
                            match ast with
                            | PFunction (_, ppatls, pel) -> Hashtbl.add tmp_funs str (List.map (fun ppatl -> ppatl_to_pattern ppatl) ppatls, pexprl_to_expr pel)
                            | _ -> ()
                        ) m.psymbol_tbl;
                        tmp_funs
                    end;
            } in
            Hashtbl.add runtime.moduls mname modul
        | Node (mname, dgs) -> 
            List.iter (fun dg -> modify_runtime dg) dgs;
            let m = Hashtbl.find pmoduls mname in 
            let modul = {
                imported = m.imported;
                vars = begin
                        let tmp_vars = Hashtbl.create 1 in
                        Hashtbl.iter (fun str (_, ast) ->
                            match ast with
                            | PExpr_loc (_, pel) -> Hashtbl.add tmp_vars str (evaluate (pexprl_to_expr pel) [] runtime mname)
                            | _ -> ()
                        ) m.psymbol_tbl;
                        tmp_vars
                    end;
                functions = begin
                        let tmp_funs = Hashtbl.create 1 in
                        Hashtbl.iter (fun str (_, ast) ->
                            match ast with
                            | PFunction (_, ppatls, pel) -> Hashtbl.add tmp_funs str (List.map (fun ppatl -> ppatl_to_pattern ppatl) ppatls, pexprl_to_expr pel)
                            | _ -> ()
                        ) m.psymbol_tbl;
                        tmp_funs
                    end;
            } in
            Hashtbl.add runtime.moduls mname modul in
        modify_runtime dep_graph;
        (* print_endline "initialized moduls in runtime"; *)
        runtime.model <- pkripke_model_to_model pkripke_model runtime start_modul;
        (* print_endline "initialized kripke model in runtime"; *)
        (* print_endline "printing state type:"; *)
        (* print_endline (Print.str_ptyp runtime.model.state_type); *)
        runtime



