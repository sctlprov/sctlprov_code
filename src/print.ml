open Ast

let rec str_ptyp pt = 
    match pt with
    | PTInt -> "int"
    | PTIntRange (min, max) -> "("^(string_of_int min)^".."^(string_of_int max)^")"
    | PTScalar strs -> "{"^(List.fold_left (fun ss s -> ss^","^s) "" strs)^"}"
    | PTFloat -> "float"
    | PTBool -> "bool"
    | PTUnt -> "unit"
    | PTAray pt1 -> "(array "^(str_ptyp pt1)^")"
    | PTLst pt1 -> "(list "^(str_ptyp pt1)^")"
    | PTTuple pt_list -> 
        let tmp_str = ref "(" in
        tmp_str := !tmp_str ^ (str_ptyp (List.hd pt_list));
        for i = 1 to List.length pt_list - 1 do
            tmp_str := !tmp_str ^ ", "^(str_ptyp (List.nth pt_list i))
        done;
        tmp_str := !tmp_str ^ ")";
        !tmp_str
    | PTRecord str_pt_list ->
        let tmp_str = ref "{" in
        List.iter (fun (str, pt1) -> tmp_str := !tmp_str^str^":"^(str_ptyp pt1)^";") str_pt_list;
        tmp_str := !tmp_str ^ "}";
        !tmp_str
    | PTArrow (pt1, pt2) -> "("^(str_ptyp pt1)^")->("^(str_ptyp pt2)^")"
    | PTConstrs str_opt_list ->
        let str_constr (str, opt) = 
            match opt with
            | None -> str
            | Some pt1 -> str^" "^(str_ptyp pt1) in
        let tmp_str = ref "" in
        tmp_str := !tmp_str ^ (str_constr (List.hd str_opt_list));
        List.iter (fun str_opt -> tmp_str := !tmp_str^" | "^(str_constr str_opt)) (List.tl str_opt_list);
        !tmp_str
    | PTUdt (str, pt_list) -> str^" "^(List.fold_left (fun s pt -> s^" "^(str_ptyp pt)) "" pt_list)
    | PTVar i -> "(Type "^(string_of_int i)^")"

let rec str_ppatl ppatl = 
    let rec str_ppat ppat = 
        match ppat with
        | PPat_Symbol str -> str
        | PPat_Int i -> string_of_int i
        | PPat_Float f -> string_of_float f
        | PPat_Unt -> "()"
        | PPat_Aray ppatl_list -> 
            if List.length ppatl_list = 0 then 
                "[||]"
            else begin
                let tmp_str = ref "[|" in
                tmp_str := !tmp_str ^ (str_ppatl (List.hd ppatl_list));
                List.iter (fun ppatl->tmp_str := !tmp_str^";"^(str_ppatl ppatl)) (List.tl ppatl_list);
                tmp_str := !tmp_str^"|]";
                !tmp_str
            end
        | PPat_Lst ppatl_list -> 
            if List.length ppatl_list = 0 then 
                "[]"
            else begin
                let tmp_str = ref "[" in
                tmp_str := !tmp_str ^ (str_ppatl (List.hd ppatl_list));
                List.iter (fun ppatl->tmp_str := !tmp_str^";"^(str_ppatl ppatl)) (List.tl ppatl_list);
                tmp_str := !tmp_str^"]";
                !tmp_str
            end
        | PPat_Lst_Cons (ppatl1, ppatl2) ->
            (str_ppatl ppatl1)^" :: (" ^(str_ppatl ppatl2)^")"
        | PPat_Underline -> "_"
        | PPat_Tuple ppatl_list ->
            begin
                let tmp_str = ref "(" in
                tmp_str := !tmp_str ^ (str_ppatl (List.hd ppatl_list));
                List.iter (fun ppatl->tmp_str := !tmp_str^";"^(str_ppatl ppatl)) (List.tl ppatl_list);
                tmp_str := !tmp_str^")";
                !tmp_str
            end
        | PPat_Constr (str, oppatl) -> begin
                match oppatl with
                | None -> str
                | Some ppatl -> str^" "^(str_ppatl ppatl)
            end
    in
    (str_ppat ppatl.ppat)^":"^(str_ptyp ppatl.ptyp)

let rec str_pexprl pel =
    let rec str_pexpr pe =
        match pe with
        | PSymbol str_list -> 
            let rec str_strs strs = 
                match strs with
                | [] -> "<empty_str>"
                | [str] -> str
                | str::strs' -> str^"."^(str_strs strs') in
            str_strs str_list
        | PLet (ppatl, pel1) ->
            "let "^(str_ppatl ppatl)^" = "^(str_pexprl pel1)
        | PInt i -> (string_of_int i)
        | PFloat f -> (string_of_float f)
        | PUnt -> "()"
        | PAray pel_list -> "[|" ^ (List.fold_left (fun s pel -> s^";"^(str_pexprl pel)) "" pel_list) ^ "|]"
        | PLst pel_list -> "[" ^ (List.fold_left (fun s pel -> s^";"^(str_pexprl pel)) "" pel_list) ^ "]"
        | POp (op, pel_list) ->begin
                match op, pel_list with
                | "[]",[pel1; pel2] -> (str_pexprl pel1)^"["^(str_pexprl pel2)^"]"
                | "::",[pel1; pel2] -> (str_pexprl pel1)^" :: "^(str_pexprl pel2)
                | "@", [pel1; pel2] -> (str_pexprl pel1)^" @ "^(str_pexprl pel2)
                | "!",[pel1] -> "(! "^(str_pexprl pel1)^")"
                | "&&",[pel1; pel2] -> "("^(str_pexprl pel1)^"&&"^(str_pexprl pel2)^")"
                | "||",[pel1; pel2] -> "("^(str_pexprl pel1)^"||"^(str_pexprl pel2)^")"
                | "-",[pel1] -> "(- "^(str_pexprl pel1)^")"
                | "-.",[pel1] -> "(-. "^(str_pexprl pel1)^")"
                | "+", [pel1; pel2] -> "("^(str_pexprl pel1)^"+"^(str_pexprl pel2)^")"
                | "+.", [pel1; pel2] -> "("^(str_pexprl pel1)^"+."^(str_pexprl pel2)^")"
                | "-",[pel1; pel2] -> "("^(str_pexprl pel1)^"-"^(str_pexprl pel2)^")"
                | "-.",[pel1; pel2] -> "("^(str_pexprl pel1)^"-."^(str_pexprl pel2)^")"
                | "*",[pel1; pel2] -> "("^(str_pexprl pel1)^"*"^(str_pexprl pel2)^")"
                | "*.",[pel1; pel2] -> "("^(str_pexprl pel1)^"*."^(str_pexprl pel2)^")"
                | "=",[pel1; pel2] -> "("^(str_pexprl pel1)^"="^(str_pexprl pel2)^")"
                | "!=",[pel1; pel2] -> "("^(str_pexprl pel1)^"!="^(str_pexprl pel2)^")"
                | "<",[pel1; pel2] -> "("^(str_pexprl pel1)^"<"^(str_pexprl pel2)^")"
                | "<=",[pel1; pel2] -> "("^(str_pexprl pel1)^"<="^(str_pexprl pel2)^")"
                | ">",[pel1; pel2] -> "("^(str_pexprl pel1)^">"^(str_pexprl pel2)^")"
                | ">=",[pel1; pel2] -> "("^(str_pexprl pel1)^">="^(str_pexprl pel2)^")"
                | str, _ -> 
                    let tmp_str = ref (str) in
                    List.iter (fun pel->tmp_str:= !tmp_str^" "^(str_pexprl pel)) pel_list;
                    !tmp_str
            end
        | PBool b -> string_of_bool b
        | PTuple pel_list ->
            let tmp_str = ref "(" in
            tmp_str := !tmp_str ^ (str_pexprl (List.hd pel_list));
            List.iter (fun pel -> tmp_str := !tmp_str^","^(str_pexprl pel)) (List.tl pel_list);
            tmp_str := !tmp_str ^ ")";
            !tmp_str
        | PRecord str_pel_list -> 
            let tmp_str = ref "{" in
            List.iter (fun (str, pel) -> tmp_str := !tmp_str^str^"="^(str_pexprl pel)^";") (str_pel_list);
            tmp_str := !tmp_str ^ "}";
            !tmp_str
        | PIF (pel1, pel2, opel3) -> begin
                match opel3 with
                | None -> "if "^(str_pexprl pel1)^" then ("^(str_pexprl pel2)^")"
                | Some pel3 -> "if "^(str_pexprl pel1)^" then ("^(str_pexprl pel2)^") else ("^(str_pexprl pel3)^")"
            end
        | PWhile (pel1, pel2) -> "while "^(str_pexprl pel1)^" do \n("^(str_pexprl pel2)^")\ndone"
        | PFor (str, pel1, pel2, pel3) -> "for "^str^" from "^(str_pexprl pel1)^" to "^(str_pexprl pel2)^" do\n("^(str_pexprl pel3)^")\ndone"
        | PSeq pel_list -> List.fold_left (fun s pel -> s^(str_pexprl pel)^";\n") "" pel_list
        | PAssign (pel1, pel2) -> (str_pexprl pel1)^" <- "^(str_pexprl pel2)
        | PMatch (pel1, ppatl_pel_list) ->
            let tmp_str = ref "match " in
            tmp_str := !tmp_str ^ (str_pexprl pel1) ^" with\n";
            List.iter (fun (ppatl, pel) -> tmp_str:= !tmp_str^"| "^(str_ppatl ppatl)^" -> "^(str_pexprl pel)^"\n") ppatl_pel_list;
            tmp_str := !tmp_str^"\n";
            !tmp_str
        | PWith (pel1, str_pel_list) ->
            let tmp_str = ref ((str_pexprl pel1)^" with {") in
            List.iter (fun (str, pel) -> tmp_str := !tmp_str^str^"="^(str_pexprl pel)^";") str_pel_list;
            tmp_str := !tmp_str^"}";
            !tmp_str
        | PConstr (PConstr_basic str) -> str
        | PConstr (PConstr_compound (str, pel1)) -> str^" "^(str_pexprl pel1)
    in
    (str_pexpr (pel.pexpr))^":"^(str_ptyp (pel.ptyp))

let str_pstate ps = 
    match ps with
    | PSVar str -> str
    | PState pel -> str_pexprl pel


let rec str_pformulal (pfml:pformula_loc) = 
    match pfml.pfml with
    | PTop -> "TRUE"
    | PBottom -> "FALSE"
    | PAtomic (str, pel_list) -> 
        let tmp_str = ref str in
        List.iter (fun pel-> tmp_str:=!tmp_str^" "^(str_pstate pel)) pel_list;
        !tmp_str
    | PNeg pfml1 -> "not ("^(str_pformulal pfml1)^")"
    | PAnd (pfml1, pfml2) -> "("^(str_pformulal pfml1)^") /\\ ("^(str_pformulal pfml2)^")"
    | POr (pfml1, pfml2) -> "("^(str_pformulal pfml1)^") \\/ ("^(str_pformulal pfml2)^")"
    | PAX (str, pfml1, pel) -> "AX ("^str^","^(str_pformulal pfml1)^","^(str_pstate pel)^")"
    | PEX (str, pfml1, pel) -> "EX ("^str^","^(str_pformulal pfml1)^","^(str_pstate pel)^")"
    | PAF (str, pfml1, pel) -> "AF ("^str^","^(str_pformulal pfml1)^","^(str_pstate pel)^")"
    | PEG (str, pfml1, pel) -> "EG ("^str^","^(str_pformulal pfml1)^","^(str_pstate pel)^")"
    | PAR (str1, str2, pfml1, pfml2, pel) -> "AR ("^str1^","^str2^","^(str_pformulal pfml1)^","^(str_pformulal pfml2)^","^(str_pstate pel)^")"
    | PEU (str1, str2, pfml1, pfml2, pel) -> "EU ("^str1^","^str2^","^(str_pformulal pfml1)^","^(str_pformulal pfml2)^","^(str_pstate pel)^")"

let str_modul modul =
    let tmp_str = ref (modul.fname^"\n") in
    List.iter (fun mn -> tmp_str:=!tmp_str^"import "^mn^"\n") modul.imported;
    Hashtbl.iter (fun str symbol ->
        match symbol with
        | (UDT, PTyp ptyp) -> tmp_str:=!tmp_str^"datatype "^str^"="^(str_ptyp ptyp)^"\n\n"
        | (Val, PExpr_loc (ptyp, pel)) ->tmp_str:=!tmp_str^"Val "^str^":"^(str_ptyp ptyp)^"="^(str_pexprl pel)^"\n\n"
        (* | (Var, PExpr_loc (ptyp, pel)) ->tmp_str:=!tmp_str^"Var "^str^":"^(str_ptyp ptyp)^"="^(str_pexprl pel)^"\n\n" *)
        | (Function, PFunction (ptyp, ppatl_list, pel)) ->
            tmp_str:=!tmp_str^"Function "^str;
            List.iter (fun ppatl->tmp_str:=!tmp_str^" "^(str_ppatl ppatl)) ppatl_list;
            tmp_str:=!tmp_str^" :"^(str_ptyp ptyp)^"=\n";
            tmp_str:=!tmp_str^(str_pexprl pel)^"\n\n"
        | _ -> tmp_str:=!tmp_str^"****illed formed declaration: "^str^"****\n"
    ) modul.psymbol_tbl;
    begin
        match modul.pkripke_model with
        | None -> ()
        | Some kripke -> 
            (* tmp_str:= !tmp_str^"transition "^(str_ppatl (fst(kripke.transition)))^"=\n"^(str_pexprl (snd (kripke.transition)))^"\n\n"; *)
            let (p, nexts) = kripke.transition in
            tmp_str := !tmp_str ^ "transition "^(str_ppatl p)^" = \n";
            begin
                match nexts with
                | PCase case_nexts ->    
                    List.iter (fun (e1, e2) -> 
                        tmp_str := !tmp_str ^ (str_pexprl e1)^" : "^(str_pexprl e2)^";\n"
                    ) case_nexts
                | PNo_case no_case_nexts ->
                    tmp_str := !tmp_str ^ (str_pexprl no_case_nexts)
            end;
            if List.length kripke.fairness <> 0 then begin
                tmp_str := !tmp_str^"fairness ";
                List.iter (fun f -> tmp_str := !tmp_str ^ (str_pformulal f)) kripke.fairness
            end;
            List.iter (fun (str, pfml) ->tmp_str:=!tmp_str^"property "^str^"="^(str_pformulal pfml)^"\n") kripke.properties
    end;
    !tmp_str
