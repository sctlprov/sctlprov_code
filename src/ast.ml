open Lexing
open Printf

type location = {
    loc_start: position;
    loc_end: position;
}
type attribute = Mutable | Unmutable
type ptyp = PTInt | PTFloat | PTBool | PTUnt 
          | PTAray of ptyp
          | PTLst of ptyp
          | PTTuple of (ptyp) list
          | PTRecord of (string * (ptyp)) list
          | PTArrow of ptyp * ptyp
          | PTConstrs of (string * (ptyp option)) list
          | PTUdt of string * (ptyp list)
          | PTIntRange of int * int
          | PTScalar of string list
          | PTVar of int
and ptyp_loc = {
    ptyp: ptyp;
    loc: location;
}

let domain_size ptyp = 
    match ptyp with
    | PTIntRange (i, j) -> j-i+1
    | PTScalar strs -> List.length strs
    | PTBool -> 2
    | PTUnt -> 1
    | _ -> 0

let rec ptvar_occurs ptv pt = 
    match ptv, pt with
    | _, PTInt | _, PTFloat | _, PTBool | _, PTUnt -> false
    | PTVar v1, PTVar v2 -> if v1 = v2 then true else false
    | PTVar _, PTAray pt' -> ptvar_occurs ptv pt'
    | PTVar _, PTLst pt' -> ptvar_occurs ptv pt'
    | PTVar _, PTTuple pts -> List.fold_left (fun b pt -> if b then b else ptvar_occurs ptv pt) false pts
    | PTVar _, PTRecord str_pts -> List.fold_left (fun b (str, pt) -> if b then b else ptvar_occurs ptv pt) false str_pts
    | PTVar _, PTArrow (pt1, pt2) -> (ptvar_occurs ptv pt1) && (ptvar_occurs ptv pt2)
    | PTVar _, PTConstrs str_opts -> 
        List.fold_left (fun b (str, opt) -> 
        match opt with
        | None -> false
        | Some pt1 -> if b then b else ptvar_occurs ptv pt1
        ) false str_opts
    | PTVar _, PTUdt (str, pts) -> List.fold_left (fun b pt -> if b then b else ptvar_occurs ptv pt) false pts
    | _ -> false

let rec replace_ptvar ptyp i pt = 
    match ptyp with
    | PTInt | PTFloat | PTBool | PTUnt | PTIntRange _ | PTScalar _ -> ptyp
    | PTVar j -> if i = j then pt else ptyp
    | PTAray pt1 -> PTAray (replace_ptvar pt1 i pt)
    | PTLst pt1 -> PTLst (replace_ptvar pt1 i pt)
    | PTTuple pts -> PTTuple (List.map (fun a -> replace_ptvar a i pt) pts)
    | PTRecord str_pts -> PTRecord (List.map (fun (str, pt1) -> (str, replace_ptvar pt1 i pt)) str_pts)
    | PTConstrs str_opts -> 
        PTConstrs (List.map (fun (str, opt) -> 
            match opt with 
            | None -> str, None 
            | Some pt1 -> str, Some (replace_ptvar pt1 i pt)) str_opts)
    | PTUdt (str, pts) -> PTUdt (str, List.map (fun pt1 -> replace_ptvar pt1 i pt) pts)
    | PTArrow (pt1, pt2) -> PTArrow (replace_ptvar pt1 i pt, replace_ptvar pt2 i pt)

let rec replace_udt_with_ptvar ptyp str i = 
    match ptyp with
    | PTUdt (s, pts) -> if str=s then PTVar i else PTUdt (s, List.map (fun pt -> replace_udt_with_ptvar pt str i) pts)
    | PTAray pt1 -> PTAray (replace_udt_with_ptvar pt1 str i)
    | PTLst pt1 -> PTLst (replace_udt_with_ptvar pt1 str i)
    | PTTuple (pts) -> PTTuple (List.map (fun pt -> replace_udt_with_ptvar pt str i) pts)
    | PTRecord str_pts -> PTRecord (List.map (fun (str, pt) -> (str, replace_udt_with_ptvar pt str i)) str_pts)
    | PTConstrs str_opts ->
        PTConstrs (List.map (fun (str, opt) ->
            match opt with
            | None -> (str, None)
            | Some pt -> (str, Some (replace_udt_with_ptvar pt str i))
        ) str_opts)
    | PTArrow (pt1, pt2) -> PTArrow (replace_udt_with_ptvar pt1 str i, replace_udt_with_ptvar pt2 str i)
    | _ -> ptyp
 

type pexpr_loc = {
    mutable pexpr: pexpr;
    mutable ptyp: ptyp;
    loc: location;
}
and pexpr = 
      PSymbol of string list
    | PLet of ppattern_loc * pexpr_loc
    | PInt of int
    (* | PScalar of int *)
    | PFloat of float
    | PUnt
    | PAray of (pexpr_loc list)
    | PLst of (pexpr_loc list)
    | POp of string * (pexpr_loc list)
    | PBool of bool
    | PTuple of (pexpr_loc list)
    | PRecord of ((string * pexpr_loc) list)
    | PIF of pexpr_loc * pexpr_loc * (pexpr_loc option)
    | PWhile of pexpr_loc * pexpr_loc
    | PFor of string * pexpr_loc * pexpr_loc * pexpr_loc
    | PSeq of pexpr_loc list
    | PAssign of pexpr_loc * pexpr_loc
    | PMatch of pexpr_loc * ((ppattern_loc * pexpr_loc) list)
    | PWith of pexpr_loc * ((string * pexpr_loc) list)
    | PConstr of pconstr
and ppattern_loc = {
    ppat: ppattern;
    mutable ptyp: ptyp;
    loc: location;
}
and ppattern =
      PPat_Symbol of string
    | PPat_Int of int
    (* | PPat_Scalar of int *)
    | PPat_Float of float
    | PPat_Unt
    | PPat_Aray of (ppattern_loc list)
    | PPat_Lst of (ppattern_loc list)
    | PPat_Lst_Cons of ppattern_loc * ppattern_loc
    | PPat_Underline
    | PPat_Tuple of (ppattern_loc list)
    | PPat_Constr of (string * (ppattern_loc option))
and pconstr = 
    | PConstr_basic of string
    | PConstr_compound of string * pexpr_loc
and pstate = 
    | PSVar of string
    | PState of pexpr_loc
and pformula = 
    | PTop
    | PBottom
    | PAtomic of string * (pstate list)
    | PNeg of pformula_loc
    | PAnd of pformula_loc * pformula_loc
    | POr of pformula_loc * pformula_loc
    | PAX of string * pformula_loc * pstate 
    | PEX of string * pformula_loc * pstate
    | PAF of string * pformula_loc * pstate
    | PEG of string * pformula_loc * pstate
    | PAR of string * string * pformula_loc * pformula_loc * pstate
    | PEU of string * string * pformula_loc * pformula_loc * pstate
and pformula_loc = {
    pfml: pformula;
    loc: location;
}

let rec pel_add_prefix str pel = 
    match pel.pexpr with
    | PSymbol strs -> {pexpr = PSymbol (str::strs); ptyp = pel.ptyp; loc = pel.loc}
    | PInt _ | PFloat _ | PUnt | PBool _ -> pel
    | PLet (ppatl, pel1) -> {pexpr = PLet (ppatl, pel_add_prefix str pel1); ptyp = pel.ptyp; loc = pel.loc}
    | PAray pels -> {pexpr = PAray (List.map (fun pel -> pel_add_prefix str pel) pels); ptyp = pel.ptyp; loc = pel.loc}
    | PLst pels -> {pexpr = PLst (List.map (fun pel -> pel_add_prefix str pel) pels); ptyp = pel.ptyp; loc = pel.loc}
    | POp (op, pels) -> {pexpr = POp (op, List.map (fun pel -> pel_add_prefix str pel) pels); ptyp = pel.ptyp; loc = pel.loc}
    | PTuple pels -> {pexpr = PTuple (List.map (fun pel -> pel_add_prefix str pel) pels); ptyp = pel.ptyp; loc = pel.loc}
    | PRecord str_pels -> {pexpr = PRecord (List.map (fun (s,pel) -> (s, pel_add_prefix str pel)) str_pels); ptyp = pel.ptyp; loc = pel.loc}
    | PIF (pel1, pel2, None) -> {pexpr = PIF (pel_add_prefix str pel1, pel_add_prefix str pel2, None); ptyp = pel.ptyp; loc = pel.loc}
    | PIF (pel1, pel2, Some pel3) -> {pexpr = PIF (pel_add_prefix str pel1, pel_add_prefix str pel2, Some (pel_add_prefix str pel3)); ptyp = pel.ptyp; loc = pel.loc}
    | PWhile (pel1, pel2) -> {pexpr = PWhile (pel_add_prefix str pel1, pel_add_prefix str pel2); ptyp = pel.ptyp; loc = pel.loc}
    | PFor (s, pel1, pel2, pel3) -> {pexpr = PFor (s, pel_add_prefix str pel1, pel_add_prefix str pel2, pel_add_prefix str pel3); ptyp = pel.ptyp; loc = pel.loc}
    | PSeq pels -> {pexpr = PSeq (List.map (fun pel -> pel_add_prefix str pel) pels); ptyp = pel.ptyp; loc = pel.loc}
    | PAssign (pel1, pel2) -> {pexpr = PAssign (pel_add_prefix str pel1, pel_add_prefix str pel2); ptyp = pel.ptyp; loc = pel.loc}
    | PMatch (pel1, ppat_pels) -> {pexpr = PMatch (pel_add_prefix str pel1, List.map (fun (ppatl, pel) -> ppatl, pel_add_prefix str pel) ppat_pels); ptyp = pel.ptyp; loc = pel.loc}
    | PWith (pel1, str_pels) -> {pexpr = PWith (pel_add_prefix str pel1, List.map (fun (s,pel) -> s, pel_add_prefix str pel) str_pels); ptyp = pel.ptyp; loc = pel.loc}
    | PConstr (PConstr_basic _) -> pel
    | PConstr (PConstr_compound (s, pel1)) -> {pexpr = PConstr (PConstr_compound (s, pel_add_prefix str pel1)); ptyp = pel.ptyp; loc = pel.loc}

let rec pel_add_prefix_func strs pel = 
    match pel.pexpr with
    | PSymbol _ (*-> {pexpr = PSymbol (str::strs); ptyp = pel.ptyp; loc = pel.loc}*)
    | PInt _ | PFloat _ | PUnt | PBool _ -> pel
    | PLet (ppatl, pel1) -> {pexpr = PLet (ppatl, pel_add_prefix_func strs pel1); ptyp = pel.ptyp; loc = pel.loc}
    | PAray pels -> {pexpr = PAray (List.map (fun pel -> pel_add_prefix_func strs pel) pels); ptyp = pel.ptyp; loc = pel.loc}
    | PLst pels -> {pexpr = PLst (List.map (fun pel -> pel_add_prefix_func strs pel) pels); ptyp = pel.ptyp; loc = pel.loc}
    | POp (op, pels) -> 
        if (List.exists (fun s -> s=op) strs) && (List.length pels = 1) then
            pel_add_prefix op (List.hd pels)
        else 
            {pexpr = POp (op, List.map (fun pel -> pel_add_prefix_func strs pel) pels); ptyp = pel.ptyp; loc = pel.loc}

    | PTuple pels -> {pexpr = PTuple (List.map (fun pel -> pel_add_prefix_func strs pel) pels); ptyp = pel.ptyp; loc = pel.loc}
    | PRecord str_pels -> {pexpr = PRecord (List.map (fun (s,pel) -> (s, pel_add_prefix_func strs pel)) str_pels); ptyp = pel.ptyp; loc = pel.loc}
    | PIF (pel1, pel2, None) -> {pexpr = PIF (pel_add_prefix_func strs pel1, pel_add_prefix_func strs pel2, None); ptyp = pel.ptyp; loc = pel.loc}
    | PIF (pel1, pel2, Some pel3) -> {pexpr = PIF (pel_add_prefix_func strs pel1, pel_add_prefix_func strs pel2, Some (pel_add_prefix_func strs pel3)); ptyp = pel.ptyp; loc = pel.loc}
    | PWhile (pel1, pel2) -> {pexpr = PWhile (pel_add_prefix_func strs pel1, pel_add_prefix_func strs pel2); ptyp = pel.ptyp; loc = pel.loc}
    | PFor (s, pel1, pel2, pel3) -> {pexpr = PFor (s, pel_add_prefix_func strs pel1, pel_add_prefix_func strs pel2, pel_add_prefix_func strs pel3); ptyp = pel.ptyp; loc = pel.loc}
    | PSeq pels -> {pexpr = PSeq (List.map (fun pel -> pel_add_prefix_func strs pel) pels); ptyp = pel.ptyp; loc = pel.loc}
    | PAssign (pel1, pel2) -> {pexpr = PAssign (pel_add_prefix_func strs pel1, pel_add_prefix_func strs pel2); ptyp = pel.ptyp; loc = pel.loc}
    | PMatch (pel1, ppat_pels) -> {pexpr = PMatch (pel_add_prefix_func strs pel1, List.map (fun (ppatl, pel) -> ppatl, pel_add_prefix_func strs pel) ppat_pels); ptyp = pel.ptyp; loc = pel.loc}
    | PWith (pel1, str_pels) -> {pexpr = PWith (pel_add_prefix_func strs pel1, List.map (fun (s,pel) -> s, pel_add_prefix_func strs pel) str_pels); ptyp = pel.ptyp; loc = pel.loc}
    | PConstr (PConstr_basic _) -> pel
    | PConstr (PConstr_compound (s, pel1)) -> {pexpr = PConstr (PConstr_compound (s, pel_add_prefix_func strs pel1)); ptyp = pel.ptyp; loc = pel.loc}


let rec pfml_pstate_type pfmll = 
    match pfmll.pfml with
    | PTop | PBottom -> PTVar (-1)
    | PAtomic (_, psts) -> 
        if List.length psts = 0 then 
            PTVar (-1)
        else begin
            let pst = List.hd psts in
            match pst with
            | PSVar _ -> PTVar (-1)
            | PState pel -> pel.ptyp
        end
    | PNeg pfml1 -> pfml_pstate_type pfml1
    | PAnd (pfml1, pfml2) | POr (pfml1, pfml2) -> 
        let pt = pfml_pstate_type pfml1 in
        if pt <> PTVar (-1) then
            pt
        else 
            pfml_pstate_type pfml2
    | PAX (_, _, pst) | PEX (_, _, pst) | PAF (_, _, pst) | PEG (_, _, pst) | PAR (_,_,_,_,pst) | PEU (_,_,_,_,pst) -> begin
            match pst with
            | PSVar _ -> PTVar (-1)
            | PState pel -> pel.ptyp
        end


exception Type_mismatch of pexpr_loc * ptyp * ptyp (*type_mismatch (type_has, type_expected)*)
type ast = 
    | PExpr_loc of ptyp * pexpr_loc
    | PTyp of ptyp
    | PFunction of ptyp * (ppattern_loc list) * pexpr_loc

type psymbol_kind = UDT | Val | Function
type psymbol_tbl = (string, (psymbol_kind * ast)) Hashtbl.t
type ptrans_def = 
    | PCase of (pexpr_loc * pexpr_loc) list
    | PNo_case of pexpr_loc
type pkripke_model = {
    mutable state_type: ptyp;
    transition : ppattern_loc * ptrans_def;
    fairness: pformula_loc list;
    atomic: (string, (string list) * pexpr_loc) Hashtbl.t;
    properties: (string * pformula_loc) list;
}
type pmodul = {
    fname: string;
    imported: string list;
    psymbol_tbl: psymbol_tbl;
    pkripke_model: pkripke_model option;
}

let mk_pexpr_loc pexpr ptyp loc_start loc_end = {
    pexpr = pexpr;
    ptyp = ptyp;
    loc = {
        loc_start = loc_start;
        loc_end = loc_end;
    };
}
let mk_ppat_loc ppat ptyp loc_start loc_end = {
    ppat = ppat;
    ptyp = ptyp;
    loc = {
        loc_start = loc_start;
        loc_end = loc_end;
    };
}
let mk_pformula_loc pfml loc_start loc_end = {
    pfml = pfml;
    loc = {
        loc_start = loc_start;
        loc_end = loc_end;
    };
}


