open Ast
open Printf

exception Unify_error of ptyp * ptyp
exception Invalid_typepath of string
exception Invalid_pexpr_loc of pexpr_loc * string
exception Undefined_modul of string
exception Undefined_idenfier of string 


type ptyp_eqs = (ptyp * ptyp) list


type env = (ptyp * ptyp) list


let rec expand_udt pt modul moduls =
  match pt with
  | PTAray pt1 -> PTAray (expand_udt pt1 modul moduls)
  | PTLst pt1 -> PTLst (expand_udt pt1 modul moduls)
  | PTTuple pt_list -> PTTuple (List.map (fun pt->expand_udt pt modul moduls) pt_list)
  | PTRecord str_pt_list -> PTRecord (List.map (fun (str, pt) -> (str, expand_udt pt modul moduls)) str_pt_list)
  | PTArrow (pt1, pt2) -> PTArrow (expand_udt pt1 modul moduls, expand_udt pt2 modul moduls)
  | PTConstrs str_opt_list -> 
    PTConstrs (List.map (fun (str, opt) ->
        match opt with
        | None -> (str, None)
        | Some pt -> (str, Some (expand_udt pt modul moduls))
      ) str_opt_list) 
  | PTUdt (str, pt_list) -> 
    let pt1 = List.map (fun pt -> expand_udt pt modul moduls) pt_list in
    let strs = String.split_on_char '.' (String.trim str) in begin
      match strs with
      | [s] -> 
        if Hashtbl.mem moduls modul then begin
          let m = Hashtbl.find moduls modul in
          let tmp_pt = ref pt in
          let found = ref false in
          if Hashtbl.mem m.psymbol_tbl s then begin
            match (Hashtbl.find m.psymbol_tbl s) with
            | (UDT, PTyp pt) -> 
              tmp_pt := pt;
              found := true;
              let index = ref 0 in
              List.iter (fun pt2 -> decr index; tmp_pt := replace_ptvar !tmp_pt !index pt2) pt1
            | _ -> ()
          end else
            List.iter (fun mname ->
              if not !found then begin
                let mi = Hashtbl.find moduls mname in
                match (Hashtbl.find mi.psymbol_tbl s) with
                | (UDT, PTyp pt) ->
                  tmp_pt := pt;
                  found := true;
                  let index = ref 0 in
                  List.iter (fun pt2 -> decr index; tmp_pt := replace_ptvar !tmp_pt !index pt2) pt1
                | _ -> ()
              end
            ) m.imported;
          if not !found then begin
            raise (Invalid_typepath (s^" was not defined."))
          end else
            !tmp_pt
        end else begin
          raise (Undefined_modul modul)
        end
      | [s1;s2] -> expand_udt (PTUdt (s2, pt1)) s1 moduls
      | _ -> raise (Invalid_typepath str)
    end
  | _ -> pt


(*Using the unification algorithm in http://www.cmi.ac.in/~madhavan/courses/pl2005/lecturenotes/lecture-notes/node113.html*)
let mgu env modul moduls = 
  let rec normal_form env =
    match env with
    | [] -> []
    | (PTVar v1, PTVar v2)::env1 -> if v1=v2 then normal_form env1 else (PTVar v1, PTVar v2)::(normal_form env1)
    | (pt, PTVar v)::env1 -> (PTVar v, pt)::(normal_form env1)
    | (PTVar v, pt)::env1 -> (PTVar v, pt)::(normal_form env1)
    | (PTAray pt1, PTAray pt2)::env1 | (PTLst pt1, PTLst pt2)::env1 -> normal_form ((pt1, pt2)::env1)
    | (PTTuple pts1, PTTuple pts2)::env1 -> normal_form ((Lists.zip_to_pairs pts1 pts2)@env1)
    | (PTRecord str_pts1, PTRecord str_pts2)::env1 -> 
      begin
        let rec seconds str_pts1 str_pts2 = 
          match str_pts1, str_pts2 with
          | [],[] -> []
          | (str1, pt1)::str_pts3, (str2, pt2)::str_pts4 -> 
            if str1<>str2 then 
              raise (Unify_error (PTRecord str_pts1, PTRecord str_pts2))
            else 
              (pt1, pt2)::(seconds str_pts3 str_pts4) 
          | _ -> raise (Unify_error (PTRecord str_pts1, PTRecord str_pts2)) in
        (normal_form ((seconds str_pts1 str_pts2)@env1))
      end
    | (PTArrow (pt1, pt2), PTArrow (pt3, pt4))::env1 -> normal_form ([(pt1, pt3);(pt2, pt4)]@env1)
    | (PTConstrs str_opts1, PTConstrs str_opts2)::env1 ->  
      begin
        let rec seconds str_opts1 str_opts2 = 
          match str_opts1, str_opts2 with
          | [],[] -> []
          | (str1, None)::str_opts3, (str2, None)::str_opts4 ->
            if str1 <> str2 then 
              raise (Unify_error (PTConstrs str_opts1, PTConstrs str_opts2))
            else 
              seconds str_opts3 str_opts4
          | (str1, Some pt1)::str_opts3, (str2, Some pt2)::str_opts4 -> 
            if str1<>str2 then 
              raise (Unify_error (PTConstrs str_opts1, PTConstrs str_opts2))
            else 
              (pt1, pt2)::(seconds str_opts3 str_opts4) 
          | _ -> raise (Unify_error (PTConstrs str_opts1, PTConstrs str_opts2)) in
        (normal_form ((seconds str_opts1 str_opts2)@env1))
      end
    (* | (PTUdt (str1, pts1), PTUdt (str2, pts2)) :: env1 ->
      if str1 <> str2 then
        raise (Unify_error (PTUdt (str1, pts1), PTUdt (str2, pts2)))
      else 
        normal_form ((Lists.zip_to_pairs pts1 pts2)@env1) *)
    | (PTUdt (str, pts), pt)::env1 ->
      let pt1 = expand_udt (PTUdt (str, pts)) modul moduls in
      normal_form ((pt1, pt)::env1)
    | (pt, PTUdt (str, pts))::env1 ->
      let pt1 = expand_udt (PTUdt (str, pts)) modul moduls in
      normal_form ((pt,pt1)::env1)
    | (PTIntRange _, PTInt) :: env1 | (PTInt, PTIntRange _) :: env1 -> normal_form env1
    | (pt1, pt2)::env1 -> 
      if pt1=pt2 then 
        normal_form (env1) 
      else begin
        print_endline ("type error: "^(Print.str_ptyp pt1)^" -- "^(Print.str_ptyp pt2));
        raise (Unify_error (pt1, pt2))
      end in
  let rec replace_env ptv pt env nth = 
    match ptv, pt, env with
    | _, _, [] -> []
    | PTVar v, pt, ((pt1, pt2)::env1) -> 
      if nth=0 then 
        (pt1, pt2):: replace_env ptv pt env1 (-1)
      else
        (replace_ptvar pt1 v pt, replace_ptvar pt2 v pt)::(replace_env ptv pt env1 (nth-1))
    | pt, PTVar v, (pt1, pt2)::env1 ->
      if nth=0 then 
        (pt1, pt2):: replace_env ptv pt env1 (-1)
      else
        (replace_ptvar pt1 v pt, replace_ptvar pt2 v pt)::(replace_env ptv pt env1 (nth-1))
    | _ -> env in
  let tmp_env = ref env in
  let changed = ref true in
  while !changed do
    let new_tmp_env = ref (normal_form (!tmp_env)) in
    for i = 0 to List.length !new_tmp_env - 1 do
      let ptv,pt = List.nth !new_tmp_env i in
      new_tmp_env := replace_env ptv pt !new_tmp_env i
    done;
    if !tmp_env <> !new_tmp_env then begin
      (* print_endline "changed"; *)
      changed := true;
      tmp_env := !new_tmp_env
    end else 
      changed := false
  done;
  !tmp_env


(*new merge env*)
let rec merge_env env1 env2 modul moduls = 
  let new_env = mgu (env1 @ env2) modul moduls in
  (* print_endline "printing a mgu:";
  List.iter (fun (pt1, pt2) -> print_string "("; print_string (Print.str_ptyp pt1); print_string ","; print_string (Print.str_ptyp pt2); print_endline ")") new_env; *)
  new_env


let ptyp_of_env env var = 
  let rec ptyp_of_var ptyp_list var = 
    match ptyp_list with
    | [] -> PTVar var
    | (PTVar v)::pts -> ptyp_of_var (pts@(Pairs.find_all env (PTVar v))) v
    | pt :: pts -> pt in
  ptyp_of_var (Pairs.find_all env (PTVar var)) var

let rec apply_env_to_ptyp env ptyp = 
  match ptyp with
  | PTInt | PTFloat | PTBool | PTUnt | PTUdt _ | PTIntRange _ | PTScalar _ -> ptyp
  | PTAray pt -> PTAray (apply_env_to_ptyp env pt)
  | PTLst pt -> PTLst (apply_env_to_ptyp env pt)
  | PTTuple pts -> PTTuple (List.map (fun a -> apply_env_to_ptyp env a) pts)
  | PTRecord str_ptyps -> PTRecord (List.map (fun (a,b) -> a, apply_env_to_ptyp env b) str_ptyps)
  | PTConstrs str_optyps -> 
    PTConstrs (List.map (fun (a, ob) -> 
        match ob with
        | None -> a, None
        | Some b -> a, Some (apply_env_to_ptyp env b)
      ) str_optyps)
  | PTVar vi -> 
        (* if vi = 18 then print_endline "calculating 18"; *)
       (* if vi = 21 then begin
        List.iter (fun (pt1, pt2)->print_endline ((Print.str_ptyp pt1)^","^(Print.str_ptyp pt2))) env;
        print_endline ("type of ptvar 21 is: "^(Print.str_ptyp (ptyp_of_env env (vi))))
      end;  *)
      begin
        match Pairs.find env ptyp with
        | None -> ptyp
        | Some pt -> pt
      end
      (* let pt = (ptyp_of_env env (vi)) in
      if pt = ptyp then pt else apply_env_to_ptyp env pt *)
  | PTArrow (pt1, pt2) -> PTArrow (apply_env_to_ptyp env pt1, apply_env_to_ptyp env pt2)

let rec unify ptyp_list modul moduls = 
  match ptyp_list with
  | [] -> []
  | [ptyp] -> []
  | ptyp1 :: ptyp2 :: ptyps -> begin
      match ptyp1, ptyp2 with
      | PTInt, PTInt | PTIntRange _, PTInt | PTInt, PTIntRange _ | PTFloat, PTFloat | PTBool, PTBool | PTUnt, PTUnt -> unify (ptyp2:: ptyps) modul moduls
      | PTScalar strs1, PTScalar strs2  -> if strs1 = strs2 then unify (ptyp2:: ptyps) modul moduls else raise (Unify_error (ptyp1, ptyp2))
      | PTVar vi1, PTVar vi2 -> 
        if vi1 = vi2 then 
          unify (ptyp2::ptyps) modul moduls
        else if vi1 < vi2 then
          let env = [(PTVar vi2, PTVar vi1)] in
          merge_env env (unify (List.map (fun a -> apply_env_to_ptyp env a) (ptyp2::ptyps)) modul moduls) modul moduls
        else 
          let env = [(PTVar vi1, PTVar vi2)] in
          merge_env env (unify (List.map (fun a -> apply_env_to_ptyp env a) (ptyp2::ptyps)) modul moduls) modul moduls
      | pt, PTVar vi | PTVar vi, pt -> 
        let env = [(PTVar vi, pt)] in
        merge_env env (unify (List.map (fun a -> apply_env_to_ptyp env a) (ptyp2::ptyps)) modul moduls) modul moduls
      | PTAray pt1, PTAray pt2 | PTLst pt1, PTLst pt2 -> 
        let env = unify [pt1;pt2] modul moduls in
        merge_env env (unify (List.map (fun a -> apply_env_to_ptyp env a) (ptyp2::ptyps)) modul moduls) modul moduls
      | PTTuple pts1, PTTuple pts2 -> 
        if List.length pts1 <> List.length pts2 then begin
          print_endline ("length of "^(Print.str_ptyp ptyp1)^" is not equal to "^(Print.str_ptyp ptyp2));
          raise (Unify_error (ptyp1, ptyp2))
        end else
          let env = List.fold_left (fun e (a1,a2) -> merge_env (unify [a1;a2] modul moduls) e modul moduls) [] (List.combine pts1 pts2) in
          merge_env env (unify (List.map (fun a -> apply_env_to_ptyp env a) (ptyp2::ptyps)) modul moduls) modul moduls
      | PTRecord str_pt_list1, PTRecord str_pt_list2 ->
        if List.length str_pt_list1 <> List.length str_pt_list2 then
          raise (Unify_error (ptyp1, ptyp2))
        else 
          let rec find_ptyp str_pt_list str =
            match str_pt_list with
            | [] -> PTVar 0
            | (s,pt)::str_pt_list' -> if s = str then pt else find_ptyp str_pt_list' str in
          let env = List.fold_left (fun e (str, pt) ->
              let pt2 = find_ptyp str_pt_list2 str in
              if pt2 = PTVar 0 then 
                raise (Unify_error (ptyp1, ptyp2))
              else
                merge_env e (unify [pt;pt2] modul moduls) modul moduls
            ) [] str_pt_list1 in
          merge_env env (unify (List.map (fun a -> apply_env_to_ptyp env a) (ptyp2::ptyps)) modul moduls) modul moduls
      | PTConstrs str_opt_list1, PTConstrs str_opt_list2 -> 
        if List.length str_opt_list1 <> List.length str_opt_list2 then
          raise (Unify_error (ptyp1, ptyp2))
        else 
          let rec find_ptyp str_pt_list str =
            match str_pt_list with
            | [] -> Some (PTVar 0)
            | (s,pt)::str_pt_list' -> if s = str then pt else find_ptyp str_pt_list' str in
          let env = List.fold_left (fun e (str, opt) ->
              let opt2 = find_ptyp str_opt_list2 str in
              match opt, opt2 with
              | None, None -> e
              | None, Some _ | Some _, None -> raise (Unify_error (ptyp1, ptyp2))
              | Some PTVar 0, _ | _, Some PTVar 0 -> raise (Unify_error (ptyp1, ptyp2))
              | Some pt1, Some pt2 -> e @ (unify [pt1; pt2] modul moduls)
            ) [] str_opt_list1 in
          merge_env env (unify (List.map (fun a -> apply_env_to_ptyp env a) (ptyp2::ptyps)) modul moduls) modul moduls
      | PTUdt (str, ptyp_list), _ -> 
        (*let strs = String.split_on_char '.' (String.trim str) in*)
        (* let ptyp = ptyp_from_typepath str modul moduls in
           let index = ref (0) in
           let ptyp_concrete = List.fold_left (fun pt pt1 -> descr index; replace_ptvar pt index pt1) ptyp ptyp_list in *)
        let ptyp_concrete = expand_udt ptyp1 modul moduls in
        unify (ptyp_concrete::ptyp2::ptyps) modul moduls
      | _, PTUdt (str, ptyp_list) ->
        (*let strs = String.split_on_char '.' (String.trim str) in*)
        (* let ptyp = ptyp_from_typepath str modul moduls in
           let index = ref (0) in
           let ptyp_concrete = List.fold_left (fun pt pt1 -> descr index; replace_ptvar pt index pt1) ptyp ptyp_list in *)
        let ptyp_concrete = expand_udt ptyp2 modul moduls in
        unify (ptyp1::ptyp_concrete::ptyps) modul moduls
      | PTArrow (pt1, pt2), PTArrow (pt3, pt4) ->
        let env1 = unify [pt1; pt3] modul moduls in
        let env2 = unify [pt2; pt4] modul moduls in
        merge_env (merge_env env1 env2 modul moduls) (unify (ptyp2::ptyps) modul moduls) modul moduls
      | _ ->
          print_endline ("error unifying types: "^(Print.str_ptyp ptyp1)^", "^(Print.str_ptyp ptyp2));  
          raise (Unify_error (ptyp1,ptyp2))
    end


type type_context = (string * ptyp) list

let rec find_ptyp str_ptyps str1 = 
  match str_ptyps with
  | [] -> PTVar 0
  | (str, ptyp) :: str_ptyps' -> if str1 = str then ptyp else find_ptyp str_ptyps' str1

let rec type_of_var str tctx = 
  match tctx with
  | [] -> PTVar 0
  | (s, pt) :: tctx' -> 
    if s=str then pt else type_of_var str tctx'
(* let pt = find_ptyp str_ptyps str in
   if pt = PTVar 0 then
    type_of_var str tctx'
   else 
    pt *)
let add_to_tctx str pt tctx = (str, pt) :: tctx

let rec type_of_str str modul moduls =
  try
    let pt = ref (PTVar 0) in
    let m = Hashtbl.find moduls modul in
    if Hashtbl.mem m.psymbol_tbl str then begin
      match (Hashtbl.find m.psymbol_tbl str) with
      | (Val, PExpr_loc (ptyp, pel)) -> pt := ptyp
      (* | (Var, PExpr_loc (ptyp, pel)) -> pt := ptyp *)
      | (Function, PFunction (ptyp, _, _)) -> pt := ptyp
      | _ -> ()
    end else begin
      List.iter (fun mname ->
          if Hashtbl.mem moduls mname then
            let m1 = Hashtbl.find moduls mname in
            if Hashtbl.mem m1.psymbol_tbl str then begin
              match (Hashtbl.find m1.psymbol_tbl str) with
              | (Val, PExpr_loc (ptyp, pel)) -> pt := ptyp
              (* | (Var, PExpr_loc (ptyp, pel)) -> pt := ptyp *)
              | (Function, PFunction (ptyp, _, _)) -> pt := ptyp
              | _ -> ()
            end
            else
              raise (Undefined_modul mname)
        ) m.imported
    end;
    if !pt = PTVar 0 then
      raise (Undefined_idenfier (str^" is not defined."))
    else 
      !pt
  with Not_found -> raise (Undefined_modul modul)


let rec check_ppat_type ppatl modul moduls =
  match ppatl.ppat with
  | PPat_Symbol str -> ([], add_to_tctx str ppatl.pptyp [])
  | PPat_Int _ -> let env1 = unify [PTInt; ppatl.pptyp] modul moduls in (env1, [])
  | PPat_Float _ -> let env1 = unify [PTFloat; ppatl.pptyp] modul moduls in (env1, [])
  | PPat_Unt -> let env1 = unify [PTUnt; ppatl.pptyp] modul moduls in (env1, [])
  | PPat_Aray ppatls -> 
    let env0 = ref [] 
    and tctx0 = ref [] in
    List.iter (fun ppatl -> 
        let env,tctx = check_ppat_type ppatl modul moduls in
        env0 := merge_env env !env0 modul moduls;
        tctx0 := tctx @ !tctx0
      ) ppatls;
    begin
      match ppatls with
      | [] -> (!env0, !tctx0)
      | p::pl -> let env1 = unify [ppatl.pptyp; PTAray (p.pptyp)] modul moduls in (merge_env env1 !env0 modul moduls, !tctx0)
    end
  | PPat_Lst ppatls -> 
    let env0 = ref [] 
    and tctx0 = ref [] in
    List.iter (fun ppatl -> 
        let env,tctx = check_ppat_type ppatl modul moduls in
        env0 := merge_env env !env0 modul moduls;
        tctx0 := tctx @ !tctx0
      ) ppatls;
    begin
      match ppatls with
      | [] -> (!env0, !tctx0)
      | p::pl -> let env1 = unify [ppatl.pptyp; PTLst (p.pptyp)] modul moduls in (merge_env env1 !env0 modul moduls, !tctx0)
    end
  | PPat_Lst_Cons (ppatl1, ppatl2) ->
    let env1, tctx1 = check_ppat_type ppatl1 modul moduls in
    let env2, tctx2 = check_ppat_type ppatl2 modul moduls in
    let env3 = unify [ppatl.pptyp; PTLst (ppatl1.pptyp); ppatl2.pptyp] modul moduls in
    (merge_env (merge_env env3 env2 modul moduls) env1 modul moduls, tctx1 @ tctx2)
  | PPat_Underline -> ([], [])
  | PPat_Tuple ppatls ->
    let env0 = ref [] 
    and tctx0 = ref [] in
    List.iter (fun ppatl -> 
        let env,tctx = check_ppat_type ppatl modul moduls in
        env0 := merge_env env !env0 modul moduls;
        tctx0 := tctx @ !tctx0
      ) ppatls;
    let env1 = unify [ppatl.pptyp; PTTuple (List.map (fun p->p.pptyp) ppatls)] modul moduls in 
    (merge_env env1 !env0 modul moduls, !tctx0)
  | PPat_Constr (str, oppatl) -> begin
      match oppatl with
      | None -> ([], [])
      | Some ppatl1 ->
        let env1, tctx1 = check_ppat_type ppatl1 modul moduls in
        (env1, tctx1)
    end


let rec ptyp_of_pexpr_path ptyp_expected str_list modul moduls =
  match str_list with
  | [] -> ptyp_expected
  | str::strs -> 
    if str = (String.capitalize_ascii str) then
      ptyp_of_pexpr_path ptyp_expected strs modul moduls
    else begin
      if ptyp_expected = PTVar 0 then
        ptyp_of_pexpr_path (type_of_str str modul moduls) strs modul moduls 
      else begin
        match ptyp_expected with
        | PTRecord str_ptyp_list -> begin
            match Pairs.find str_ptyp_list str with
            | None -> PTVar 0
            | Some ptyp -> ptyp_of_pexpr_path ptyp strs modul moduls
          end  
        | PTUdt _ -> 
          let pt = expand_udt ptyp_expected modul moduls in begin
            print_endline ("expanding udt "^(Print.str_ptyp ptyp_expected)^": "^(Print.str_ptyp pt));
            match pt with
            | PTRecord str_ptyp_list -> begin
                match Pairs.find str_ptyp_list str with
                | None -> print_endline ("can not find binding of "^str^" in record type "^(Print.str_ptyp pt));PTVar 0
                | Some ptyp -> ptyp_of_pexpr_path ptyp strs modul moduls
              end  
            | _ -> PTVar 0
          end
        | _ -> 
          (* print_endline ("ptyp_expected: "^(Print.str_ptyp ptyp_expected));  *)
          PTVar 0
      end
    end


let rec find_record_ptyp keys modul moduls =
  let m = Hashtbl.find moduls modul in
  let rptyp = ref None in
  let found = ref false in
  Hashtbl.iter (fun str (kind, ast) -> 
    match kind,ast with
    | UDT, PTyp (PTRecord str_pts) -> 
      let include_keys = List.fold_left (fun b str -> 
        if not b then false else Pairs.key_exists str_pts str
      ) true keys in
      if include_keys then begin
        rptyp := Some (PTRecord str_pts);
        found := true
      end
    | _ -> ()
  ) m.psymbol_tbl;
  if !found then
      !rptyp
  else begin
      let imported = m.imported in
      for i = 0 to List.length imported - 1 do
        if !found then () 
        else begin
          match (find_record_ptyp keys (List.nth imported i) moduls) with
          | None -> ()
          | Some pt ->
            found := true;
            rptyp := Some pt
        end
      done;
      !rptyp
  end

let rec check_pel_type pel env tctx modul moduls = 
  match pel.pexpr with
  | PSymbol str_list -> begin
      match str_list with
      | [] -> raise (Invalid_pexpr_loc (pel, "not a valid expression."))
      | [str] -> 
        if str = (String.capitalize_ascii str) then
          raise (Invalid_pexpr_loc (pel, str^" is a module name, not an expression identifier."))
        else begin
          try
            if Pairs.key_exists tctx str then
              let pt = Pairs.get_value tctx str in
              let env1 = unify [pt; pel.eptyp] modul moduls in
              (merge_env env1 env modul moduls, tctx)
            else begin
              let found = ref false in
              let tmp_env_tctx = ref ([], []) in
              let m = Hashtbl.find moduls modul in begin
                try 
                  match Hashtbl.find m.psymbol_tbl str with
                  | (Val, PExpr_loc (pt, pel1)) ->
                  (* | (Var, PExpr_loc (pt, pel1)) -> *)
                    found := true;
                    let env1 = unify [pt;pel.eptyp; pel1.eptyp] modul moduls in 
                    tmp_env_tctx := (merge_env env1 env modul moduls, tctx)
                  | _ -> raise (Undefined_idenfier ("not defined as a value: "^modul^"."^str))
                with Not_found -> raise (Undefined_idenfier (modul^"."^str))
              end;
              List.iter (fun mname ->
                let mi = Hashtbl.find moduls mname in
                try
                  match Hashtbl.find mi.psymbol_tbl str with
                  | (Val, PExpr_loc (pt, pel1)) ->
                  (* | (Var, PExpr_loc (pt, pel1)) -> *)
                    found := true;
                    let env1 = unify [pt;pel.eptyp; pel1.eptyp] modul moduls in 
                    tmp_env_tctx := (merge_env env1 env modul moduls, tctx)
                  | _ -> raise (Undefined_idenfier ("not defined as a value: "^mname^"."^str))
                with Not_found -> raise (Undefined_idenfier (mname^"."^str))
              ) m.imported;
              if not !found then
                raise (Undefined_idenfier (modul^"."^str))
              else
                !tmp_env_tctx
            end
          with Not_found -> raise (Undefined_modul modul)
        end
      | str::strs -> 
        if str = (String.capitalize_ascii str) then
          let pt = ptyp_of_pexpr_path (PTVar 0) strs str moduls in
          if pt = PTVar 0 then 
            raise (Invalid_pexpr_loc (pel, "can not be typed"))
          else 
            let env1 = unify [pt; pel.eptyp] modul moduls in 
            (merge_env env1 env modul moduls, tctx)
        else 
          let pt = type_of_var str tctx in
          if pt <> PTVar 0 then
            let pt1 = ptyp_of_pexpr_path pt strs modul moduls in
            if pt1 = PTVar 0 then
              (* raise (Invalid_pexpr_loc (pel, "can not be typed")) *)
              (env, tctx)
            else 
              let env1 = unify [pt1; pel.eptyp] modul moduls in
              (merge_env env1 env modul moduls, tctx)
          else
            let pt1 = ptyp_of_pexpr_path (PTVar 0) str_list modul moduls in
            if pt1 = PTVar 0 then
              (* raise (Invalid_pexpr_loc (pel, "can not be typed")) *)
              (env, tctx)
            else 
              let env1 = unify [pt1; pel.eptyp] modul moduls in
              (merge_env env1 env modul moduls, tctx)
          
    end
  | PLet (p, pel1) ->
    let env0, tctx0 = check_pel_type pel1 env tctx modul moduls in
    let env1, tctx1 = check_ppat_type p modul moduls in
    let env2 = unify [p.pptyp; pel1.eptyp] modul moduls in
    (merge_env (merge_env env0 env1 modul moduls) env2 modul moduls, tctx1 @ tctx)
  | PInt i -> env, tctx
    (* begin try
      let env1 = unify [pel.ptyp; PTInt] modul moduls in (merge_env env1 env modul moduls, tctx)
    with Unify_error _ -> 
      print_endline "unifying error";
      exit 1
    end *)
  | PFloat f -> let env1 = unify [pel.eptyp; PTFloat] modul moduls in (merge_env env1 env modul moduls, tctx)
  | PUnt -> let env1 = unify [pel.eptyp; PTUnt] modul moduls in (merge_env env1 env modul moduls, tctx)
  | PAray pel_aray -> 
    let env1 = unify (List.map (fun (pel:pexpr_loc) -> pel.eptyp) (pel_aray)) modul moduls in
    let new_env = merge_env env1 env modul moduls in
    (* List.iter (fun (pel:pexpr_loc) -> pel.ptyp <- apply_env_to_ptyp new_env pel.ptyp) pel_aray; *)
    let env2 = unify [pel.eptyp; PTAray ((List.hd pel_aray).eptyp)] modul moduls in 
    (merge_env env2 new_env modul moduls, tctx)
  | PLst pel_list ->
    if List.length pel_list = 0 then
        (env, tctx)
    else
        let env1 = unify (List.map (fun (pel:pexpr_loc) -> pel.eptyp) pel_list) modul moduls in
        let new_env = merge_env env1 env modul moduls in
        (* List.iter (fun (pel:pexpr_loc) -> pel.ptyp <- apply_env_to_ptyp new_env pel.ptyp) pel_list; *)
        let env2 = unify [pel.eptyp; PTLst ((List.hd pel_list).eptyp)] modul moduls in 
        (merge_env env2 new_env modul moduls, tctx)
  | POp (op, pel_list) -> begin
      match op, pel_list with
      | "[]", [pel1; pel2] -> 
        let env1, _ = check_pel_type pel1 env tctx modul moduls  in
        (* let env2 = merge_env env1 env in *)
        let env3, _ = check_pel_type pel2 env1 tctx modul moduls in
        let env4 = unify [pel.eptyp; PTAray (pel2.eptyp)] modul moduls in
        (merge_env env4 env3 modul moduls, tctx)
      | "::", [pel1; pel2] -> 
        let env1,_ = check_pel_type pel1 env tctx modul moduls in
        let env2,_ = check_pel_type pel2 env1 tctx modul moduls in
        let env3 = unify [pel.eptyp; pel2.eptyp; PTLst (pel1.eptyp)] modul moduls in
        (merge_env env3 env2 modul moduls, tctx)
      | "@", [pel1; pel2] ->
        let env1,_ = check_pel_type pel1 env tctx modul moduls in
        let env2,_ = check_pel_type pel2 env1 tctx modul moduls in
        let env3 = unify [pel.eptyp; pel2.eptyp; pel1.eptyp] modul moduls in
        (merge_env env3 env2 modul moduls, tctx)
      | "!", [pel1] ->
        let env1, _ = check_pel_type pel1 env tctx modul moduls in
        let env2 = unify [PTBool; pel1.eptyp; pel.eptyp] modul moduls in
        (merge_env env2 env1 modul moduls, tctx)
      | "&&", [pel1; pel2] ->
        let env1, _ = check_pel_type pel1 env tctx modul moduls in
        let env2, _ = check_pel_type pel2 env1 tctx modul moduls in
        let env3 = unify [PTBool; pel1.eptyp; pel2.eptyp; pel.eptyp] modul moduls in
        (merge_env env3 env2 modul moduls, tctx)
      | "||", [pel1; pel2] ->
        let env1, _ = check_pel_type pel1 env tctx modul moduls in
        let env2, _ = check_pel_type pel2 env1 tctx modul moduls in
        let env3 = unify [PTBool; pel1.eptyp; pel2.eptyp; pel.eptyp] modul moduls in
        (merge_env env3 env2 modul moduls, tctx)
      | "-", [pel1] ->
        let env1, _ = check_pel_type pel1 env tctx modul moduls in
        let env2 = unify [PTInt; pel1.eptyp; pel.eptyp] modul moduls in
        (merge_env env2 env1 modul moduls, tctx)
      | "-.", [pel1] ->
        let env1, _ = check_pel_type pel1 env tctx modul moduls in
        let env2 = unify [PTFloat; pel1.eptyp; pel.eptyp] modul moduls in
        (merge_env env2 env1 modul moduls, tctx)
      | "+", [pel1; pel2] ->
        let env1, _ = check_pel_type pel1 env tctx modul moduls in
        let env2, _ = check_pel_type pel2 env1 tctx modul moduls in
        let env3 = unify [PTInt; pel1.eptyp; pel2.eptyp; pel.eptyp] modul moduls in
        (merge_env env3 env2 modul moduls, tctx)
      | "+.", [pel1; pel2] ->
        let env1, _ = check_pel_type pel1 env tctx modul moduls in
        let env2, _ = check_pel_type pel2 env1 tctx modul moduls in
        let env3 = unify [PTFloat; pel1.eptyp; pel2.eptyp; pel.eptyp] modul moduls in
        (merge_env env3 env2 modul moduls, tctx)
      | "-", [pel1; pel2] ->
        let env1, _ = check_pel_type pel1 env tctx modul moduls in
        let env2, _ = check_pel_type pel2 env1 tctx modul moduls in
        let env3 = unify [PTInt; pel1.eptyp; pel2.eptyp; pel.eptyp] modul moduls in
        (merge_env env3 env2 modul moduls, tctx)
      | "-.", [pel1; pel2] ->
        let env1, _ = check_pel_type pel1 env tctx modul moduls in
        let env2, _ = check_pel_type pel2 env1 tctx modul moduls in
        let env3 = unify [PTFloat; pel1.eptyp; pel2.eptyp; pel.eptyp] modul moduls in
        (merge_env env3 env2 modul moduls, tctx)
      | "*", [pel1; pel2] ->
        let env1, _ = check_pel_type pel1 env tctx modul moduls in
        let env2, _ = check_pel_type pel2 env1 tctx modul moduls in
        let env3 = unify [PTInt; pel1.eptyp; pel2.eptyp; pel.eptyp] modul moduls in
        (merge_env env3 env2 modul moduls, tctx)
      | "*.", [pel1; pel2] ->
        let env1, _ = check_pel_type pel1 env tctx modul moduls in
        let env2, _ = check_pel_type pel2 env1 tctx modul moduls in
        let env3 = unify [PTFloat; pel1.eptyp; pel2.eptyp; pel.eptyp] modul moduls in
        (merge_env env3 env2 modul moduls, tctx)
      | "=", [pel1; pel2] ->
        let env1, _ = check_pel_type pel1 env tctx modul moduls in
        let env2, _ = check_pel_type pel2 env1 tctx modul moduls in
        let env3 = unify [pel1.eptyp; pel2.eptyp] modul moduls in
        let env4 = unify [PTBool; pel.eptyp] modul moduls in
        (merge_env (merge_env env3 env4 modul moduls) env2 modul moduls, tctx)
      | "!=", [pel1; pel2] ->
        let env1, _ = check_pel_type pel1 env tctx modul moduls in
        let env2, _ = check_pel_type pel2 env1 tctx modul moduls in
        let env3 = unify [pel1.eptyp; pel2.eptyp] modul moduls in
        let env4 = unify [PTBool; pel.eptyp] modul moduls in
        (merge_env (merge_env env3 env4 modul moduls) env2 modul moduls, tctx)
      | "<", [pel1; pel2] ->
        let env1, _ = check_pel_type pel1 env tctx modul moduls in
        let env2, _ = check_pel_type pel2 env1 tctx modul moduls in
        let env3 = unify [pel1.eptyp; pel2.eptyp] modul moduls in
        let env4 = unify [PTBool; pel.eptyp] modul moduls in
        (merge_env (merge_env env3 env4 modul moduls) env2 modul moduls, tctx)
      | ">", [pel1; pel2] ->
        let env1, _ = check_pel_type pel1 env tctx modul moduls in
        let env2, _ = check_pel_type pel2 env1 tctx modul moduls in
        let env3 = unify [pel1.eptyp; pel2.eptyp] modul moduls in
        let env4 = unify [PTBool; pel.eptyp] modul moduls in
        (merge_env (merge_env env3 env4 modul moduls) env2 modul moduls, tctx)
      | "<=", [pel1; pel2] ->
        let env1, _ = check_pel_type pel1 env tctx modul moduls in
        let env2, _ = check_pel_type pel2 env1 tctx modul moduls in
        let env3 = unify [pel1.eptyp; pel2.eptyp] modul moduls in
        let env4 = unify [PTBool; pel.eptyp] modul moduls in
        (merge_env (merge_env env3 env4 modul moduls) env2 modul moduls, tctx)
      | ">=", [pel1; pel2] ->
        let env1, _ = check_pel_type pel1 env tctx modul moduls in
        let env2, _ = check_pel_type pel2 env1 tctx modul moduls in
        let env3 = unify [pel1.eptyp; pel2.eptyp] modul moduls in
        let env4 = unify [PTBool; pel.eptyp] modul moduls in
        (merge_env (merge_env env3 env4 modul moduls) env2 modul moduls, tctx)
      | str, _ ->(***reimplement this part***)
        (* print_endline ("checking type of function "^str); *)
        let ptf = type_of_str str modul moduls in
        let env0 = ref env in
        List.iter (fun pel ->
            let env, _ = check_pel_type pel !env0 tctx modul moduls in
            env0 := env
          ) pel_list;
        let pt1 = ref pel.eptyp in
        let rec construct_apply ptyps = 
          match ptyps with
          | [] -> raise (Invalid_pexpr_loc (pel, "not enough argument(s)."))
          | [pt] -> pt1 := pt; pt
          | pt::pts -> PTArrow (pt, construct_apply pts) in
        let env1 = unify [pel.eptyp; !pt1] modul moduls in
        let env2 = unify [ptf; construct_apply ((List.map (fun (pel:pexpr_loc)->pel.eptyp) pel_list)@[!pt1])] modul moduls in
        (merge_env (merge_env env1 env2 modul moduls) !env0 modul moduls, tctx)
    end
  | PBool b -> let env1 = unify [pel.eptyp; PTBool] modul moduls in (merge_env env1 env modul moduls, tctx)
  | PTuple pel_list -> 
    let env0 = ref env in
    List.iter (fun pel ->
        let env, _ = check_pel_type pel !env0 tctx modul moduls in
        env0 := env
      ) pel_list;
    let env1 = unify [pel.eptyp; PTTuple (List.map (fun (pel:pexpr_loc) -> pel.eptyp) pel_list)] modul moduls in
    (merge_env env1 !env0 modul moduls, tctx)
  | PRecord str_pels ->
    let env0 = ref env in
    List.iter (fun (str, pel) ->
        let env, _ = check_pel_type pel !env0 tctx modul moduls in
        env0 := env
      ) str_pels;
    let env1 = unify [pel.eptyp; PTRecord (List.map (fun (str, (pel:pexpr_loc)) ->
        (str, pel.eptyp)
      ) str_pels)] modul moduls in
    (merge_env env1 !env0 modul moduls, tctx)
  | PIF (pel1, pel2, opel3) -> begin
      match opel3 with
      | None ->
        let env1,_ = check_pel_type pel1 env tctx modul moduls in
        let env2,_ = check_pel_type pel2 env1 tctx modul moduls in
        let env3 = unify [PTBool; pel1.eptyp] modul moduls in
        let env4 = unify [PTUnt; pel.eptyp; pel2.eptyp] modul moduls in
        (merge_env (merge_env env3 env4 modul moduls) env2 modul moduls, tctx)
      | Some pel3 ->
        let env1, _ = check_pel_type pel1 env tctx modul moduls in
        let env2, _ = check_pel_type pel2 env1 tctx modul moduls in
        let env3, _ = check_pel_type pel3 env2 tctx modul moduls in
        let env4 = unify [PTBool; pel1.eptyp] modul moduls in
        let env5 = unify [pel.eptyp; pel2.eptyp; pel3.eptyp] modul moduls in
        (merge_env (merge_env env4 env5 modul moduls) env3 modul moduls, tctx)
    end
  | PWhile (pel1, pel2) ->
    let env1, _ = check_pel_type pel1 env tctx modul moduls in
    let env2, _ = check_pel_type pel2 env1 tctx modul moduls in
    let env3 = unify [PTBool; pel1.eptyp] modul moduls in
    let env4 = unify [PTUnt; pel.eptyp; pel2.eptyp] modul moduls in
    (merge_env (merge_env env3 env4 modul moduls) env2 modul moduls, tctx)
  | PFor (str, pel1, pel2, pel3) ->
    let env1, _ = check_pel_type pel1 env tctx modul moduls in
    let env2, _ = check_pel_type pel2 env1 tctx modul moduls in
    let env3, _ = check_pel_type pel3 env2 (add_to_tctx str pel1.eptyp tctx) modul moduls in
    let env4 = unify [PTInt; pel1.eptyp; pel2.eptyp] modul moduls in
    let env5 = unify [pel3.eptyp; pel.eptyp] modul moduls in
    (merge_env (merge_env env5 env4 modul moduls) env3 modul moduls, tctx)
  | PSeq pels ->
    if List.length pels = 0 then begin
      print_endline "PSeq expression can not contain 0 single expression";
      exit 1
    end;
    let env0 = ref env
    and tctx0 = ref tctx in
    List.iter (fun pel -> 
        let env, tctx = check_pel_type pel !env0 !tctx0 modul moduls in
        env0 := env;
        tctx0 := tctx
      ) pels;
    let env1 = unify [pel.eptyp; (List.hd (List.rev pels)).eptyp] modul moduls in
    (merge_env env1 !env0 modul moduls, !tctx0)
  | PAssign (pel1, pel2) ->
    let env1, _ = check_pel_type pel1 env tctx modul moduls in
    let env2, _ = check_pel_type pel2 env1 tctx modul moduls in
    let env3 = unify [pel1.eptyp; pel2.eptyp] modul moduls in
    let env4 = unify [PTUnt; pel.eptyp] modul moduls in
    (merge_env (merge_env env3 env4 modul moduls) env2 modul moduls, tctx)
  | PMatch (pel1, ppatl_pel_list) ->
    let env1, _ = check_pel_type pel1 env tctx modul moduls in
    let env0 = ref env1 in
    List.iter (fun (ppatl1, pel2) ->
        let env2, tctx2 = check_ppat_type ppatl1 modul moduls in
        env0 := merge_env env2 !env0 modul moduls;
        let env3, _ = check_pel_type pel2 !env0 (tctx2@tctx) modul moduls in
        let env4 = unify [pel1.eptyp; ppatl1.pptyp] modul moduls in
        let env5 = unify [pel.eptyp; pel2.eptyp] modul moduls in
        env0 := merge_env (merge_env env4 env5 modul moduls) env3 modul moduls
      ) ppatl_pel_list;
    (!env0, tctx)
  | PWith (pel1, str_pel_list) ->
    let env1, _ = check_pel_type pel1 env tctx modul moduls in
    let env0 = ref env1 in
    List.iter (fun (str, pel2) ->
        let env,_ = check_pel_type pel2 !env0 tctx modul moduls in
        env0 := env
      ) str_pel_list;
    let keys = Pairs.keys str_pel_list in begin
      match (find_record_ptyp keys modul moduls) with
      | Some (PTRecord rpt) -> 
        (* print_endline ("find a suitable record type: "^(Print.str_ptyp (PTRecord rpt))); *)
        let tmp_env = ref [] in
        List.iter (fun k ->
          let pt = Pairs.get_value rpt k in
          let pel = Pairs.get_value str_pel_list k in
          tmp_env := (pt, pel.eptyp)::!tmp_env
        ) keys;
        env0 := !tmp_env @ !env0
      | _ -> 
      print_endline "cannot find a suitable record with keys: ";
      List.iter (fun str -> print_string (str^" ")) keys;
      print_endline "";
      exit 1
    end;
    (!env0, tctx)
  | PConstr _ -> (env, tctx)


let rec check_pformulal_type pfml tctx modul moduls =
  match pfml.pfml with
  | PAtomic (str, pel_list) -> 
    let env0 = ref [] in
    List.iter (fun ps ->
      match ps with
      | PSVar _ -> ()
      | PState pel -> 
        let env, _ = check_pel_type pel !env0 tctx modul moduls in
        env0 := env
    ) pel_list;
    !env0
  | PNeg pfml1 -> check_pformulal_type pfml1 tctx modul moduls
  | PAnd (pfml1, pfml2) -> merge_env (check_pformulal_type pfml1 tctx modul moduls) (check_pformulal_type pfml2 tctx modul moduls) modul moduls
  | POr (pfml1, pfml2) -> merge_env (check_pformulal_type pfml1 tctx modul moduls) (check_pformulal_type pfml2 tctx modul moduls) modul moduls
  | PAX (x, pfml1, PState pel) -> 
    let env,_ = (check_pel_type pel [] tctx modul moduls) in
    let tctx1 = (x, pel.eptyp)::tctx in
    merge_env (check_pformulal_type pfml1 tctx1 modul moduls) env modul moduls
  | PEX (x, pfml1, PState pel) -> 
    let env,_ = (check_pel_type pel [] tctx modul moduls) in
    let tctx1 = (x, pel.eptyp)::tctx in
    merge_env (check_pformulal_type pfml1 tctx1 modul moduls) env modul moduls
  | PAF (x, pfml1, PState pel) -> 
    let env,_ = (check_pel_type pel [] tctx modul moduls) in
    let tctx1 = (x, pel.eptyp)::tctx in
    merge_env (check_pformulal_type pfml1 tctx1 modul moduls) env modul moduls
  | PEG (x, pfml1, PState pel) -> 
    let env,_ = (check_pel_type pel [] tctx modul moduls) in
    let tctx1 = (x, pel.eptyp)::tctx in
    merge_env (check_pformulal_type pfml1 tctx1 modul moduls) env modul moduls
  | PAR (x,y, pfml1, pfml2, PState pel) -> 
    let env,_ = check_pel_type pel [] tctx modul moduls in
    let tctx1 = (x, pel.eptyp)::tctx 
    and tctx2 = (y, pel.eptyp)::tctx in
    merge_env (merge_env (check_pformulal_type pfml1 tctx1 modul moduls) (check_pformulal_type pfml2 tctx2 modul moduls) modul moduls) env modul moduls
  | PEU (x,y, pfml1, pfml2, PState pel) -> 
    let env,_ = check_pel_type pel [] tctx modul moduls in
    let tctx1 = (x, pel.eptyp)::tctx 
    and tctx2 = (y, pel.eptyp)::tctx in
    merge_env (merge_env (check_pformulal_type pfml1 tctx1 modul moduls) (check_pformulal_type pfml2 tctx2 modul moduls) modul moduls) env modul moduls
  | _ -> []


let rec apply_env_to_ppatl env ppatl = 
  ppatl.pptyp <- apply_env_to_ptyp env ppatl.pptyp;
  match ppatl.ppat with
  | PPat_Aray ppatl1 -> List.iter (fun ppatl -> apply_env_to_ppatl env ppatl) ppatl1
  | PPat_Lst ppatl1 -> List.iter (fun ppatl -> apply_env_to_ppatl env ppatl) ppatl1
  | PPat_Lst_Cons (ppatl1, ppatl2) -> apply_env_to_ppatl env ppatl1; apply_env_to_ppatl env ppatl2
  | PPat_Tuple ppatl_list -> List.iter (fun ppatl -> apply_env_to_ppatl env ppatl) ppatl_list
  | PPat_Constr (str, oppatl) -> begin
      match oppatl with
      | None -> ()
      | Some ppatl1 -> apply_env_to_ppatl env ppatl1
    end
  | _ -> ()

let rec apply_env_to_pel env (pel:pexpr_loc) = 
  pel.eptyp <- apply_env_to_ptyp env pel.eptyp;
  match pel.pexpr with
  | PLet (ppatl, pel1) ->
    apply_env_to_ppatl env ppatl;
    apply_env_to_pel env pel1
  | PAray (pel_list) -> List.iter (fun pel->apply_env_to_pel env pel) pel_list
  | PLst (pel_list) -> List.iter (fun pel->apply_env_to_pel env pel) pel_list
  | POp (op, pel_list) -> List.iter (fun pel->apply_env_to_pel env pel) pel_list
  | PTuple pel_list -> List.iter (fun pel->apply_env_to_pel env pel) pel_list
  | PRecord str_pel_list -> List.iter (fun (str,pel) -> apply_env_to_pel env pel) str_pel_list
  | PIF (pel1, pel2, opel3) -> begin
      match opel3 with
      | None -> apply_env_to_pel env pel1; apply_env_to_pel env pel2
      | Some pel3 -> apply_env_to_pel env pel1; apply_env_to_pel env pel2; apply_env_to_pel env pel3
    end
  | PWhile (pel1, pel2) -> apply_env_to_pel env pel1; apply_env_to_pel env pel2
  | PFor (str, pel1, pel2, pel3) -> apply_env_to_pel env pel1; apply_env_to_pel env pel2; apply_env_to_pel env pel3
  | PSeq pel_list -> List.iter (fun pel->apply_env_to_pel env pel) pel_list
  | PAssign (pel1, pel2) -> apply_env_to_pel env pel1; apply_env_to_pel env pel2
  | PMatch (pel1, ppatl_pel_list) -> 
    apply_env_to_pel env pel1; 
    List.iter (fun (ppatl, pel) -> apply_env_to_pel env pel; apply_env_to_ppatl env ppatl) ppatl_pel_list
  | PWith (pel1, str_pel_list) ->
    apply_env_to_pel env pel1; 
    List.iter (fun (str, pel) -> apply_env_to_pel env pel) str_pel_list
  | PConstr (PConstr_compound (str, pel1)) -> apply_env_to_pel env pel1
  | _ -> ()

let rec apply_env_to_pformulal env pfml =
  match pfml.pfml with
  | PAtomic (str, pel_list) -> 
      List.iter (fun ps->
        match ps with
        | PSVar _ -> ()
        | PState pel -> apply_env_to_pel env pel
      ) pel_list
  | PNeg pfml1 -> apply_env_to_pformulal env pfml1
  | PAnd (pfml1, pfml2) -> apply_env_to_pformulal env pfml1; apply_env_to_pformulal env pfml2
  | POr (pfml1, pfml2) -> apply_env_to_pformulal env pfml1; apply_env_to_pformulal env pfml2
  | PAX (_, pfml1, PState pel) -> apply_env_to_pformulal env pfml1; apply_env_to_pel env pel
  | PEX (_, pfml1, PState pel) -> apply_env_to_pformulal env pfml1; apply_env_to_pel env pel
  | PAF (_, pfml1, PState pel) -> apply_env_to_pformulal env pfml1; apply_env_to_pel env pel
  | PEG (_, pfml1, PState pel) -> apply_env_to_pformulal env pfml1; apply_env_to_pel env pel
  | PAR (_,_, pfml1, pfml2, PState pel) -> apply_env_to_pformulal env pfml1; apply_env_to_pformulal env pfml2; apply_env_to_pel env pel
  | PEU (_,_, pfml1, pfml2, PState pel) -> apply_env_to_pformulal env pfml1; apply_env_to_pformulal env pfml2; apply_env_to_pel env pel
  | _ -> ()

let check_modul modul moduls = 
  if Hashtbl.mem moduls modul then begin
    let m = Hashtbl.find moduls modul in
    Hashtbl.iter (fun str kind_ast -> 
      match kind_ast with
      | (Val, PExpr_loc (ptyp, pel)) -> 
        let env,_ = check_pel_type pel [] [] modul moduls in
        let env1 = merge_env (unify [ptyp; pel.eptyp] modul moduls) env modul moduls in
        let ptyp1 = apply_env_to_ptyp env1 ptyp in
        apply_env_to_pel env1 pel;
        Hashtbl.replace m.psymbol_tbl str (Val, PExpr_loc (ptyp1, pel))
      | (Function, PFunction (ptyp, ppatl_list, pel)) -> 
        (* print_endline ("type checking function "^str); *)
        let rec build_arrow ptyp_list ptyp1 = 
          match ptyp_list with
          | [] -> ptyp1
          | pt::pts -> PTArrow (pt, build_arrow pts ptyp1) in
        let env0 = ref []
        and tctx0 = ref [] in
        List.iter (fun ppatl->
          let env,tctx = check_ppat_type ppatl modul moduls in
          env0:=merge_env env !env0 modul moduls;
          tctx0:=tctx@(!tctx0)
        ) ppatl_list;
        let env1, tctx1 = check_pel_type pel !env0 !tctx0 modul moduls in
        let env2 = merge_env (unify [ptyp; build_arrow (List.map (fun ppatl->ppatl.pptyp) ppatl_list) pel.eptyp] modul moduls) env1 modul moduls in
        List.iter (fun ppatl->apply_env_to_ppatl env2 ppatl) ppatl_list;
        apply_env_to_pel env2 pel;
        Hashtbl.replace m.psymbol_tbl str (Function, PFunction (apply_env_to_ptyp env2 ptyp, ppatl_list, pel))
        (* print_endline ("type check function "^str^" complete.") *)
      | _ -> ()
    ) m.psymbol_tbl;
     match m.pkripke_model with
    | None -> ()
    | Some kripke -> 
        (* print_endline ("type checking kripke model..."); *)
        let env1, tctx1 = check_ppat_type (fst kripke.transition) modul moduls in
        let nexts = snd kripke.transition in begin
          match nexts with
          | PCase case_nexts ->  
            let tmp_env = ref env1 in
            List.iter (fun (e1, e2) -> 
              let env1, _ = check_pel_type e1 !tmp_env tctx1 modul moduls in
              let env2, _ = check_pel_type e2 env1 tctx1 modul moduls in
              tmp_env := env2
            ) case_nexts;
            apply_env_to_ppatl !tmp_env (fst kripke.transition);
            List.iter (fun (e1, e2) ->
              apply_env_to_pel !tmp_env e1;
              apply_env_to_pel !tmp_env e2
            ) case_nexts;
          | PNo_case no_case_nexts ->
            let tmp_env,_ = check_pel_type no_case_nexts env1 tctx1 modul moduls in
            apply_env_to_ppatl tmp_env (fst kripke.transition);
            apply_env_to_pel tmp_env no_case_nexts
        end;
        List.iter (fun (str, pfml) -> 
          let env = check_pformulal_type pfml [] modul moduls in
          apply_env_to_pformulal env pfml
        ) kripke.properties;
        (* print_endline ("type check kripke model complete.") *)
        (* let init = m.psymbol_tbl.find "init" *)
        if kripke.state_type = PTVar (-1) then begin
          let pt = pfml_pstate_type (snd (List.hd kripke.properties)) in
          if pt <> PTVar (-1) then
            kripke.state_type <- pt
          else begin
            if Hashtbl.mem m.psymbol_tbl "init" then
              kripke.state_type <- type_of_str "init" modul moduls
            else if Hashtbl.mem m.psymbol_tbl "ini" then
              kripke.state_type <- type_of_str "ini" modul moduls
            else
              ()
          end
        end
        
        (* printf "kripke.state_type: %s\n" (Print.str_ptyp kripke.state_type) *)
  end else 
    raise (Undefined_modul modul)
