open OUnit2
open Sys
open Ast
open Typechecker
open Dep
open Interp
open Printf
open Lexing
open Oterm 
open Oformula
open Omodul
open Oprover_output
open Oprover
open Oparser 

let test_dir = "./test/"

let answers_cp = 
  [
    [false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false];
    [true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true];
    [true; false; false; false; false; false; false; false; false; false; false; false; false; false; true; false; false; false; false; false; false; false; false; false; false; false; true; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false];
    [true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true];
    [true; true; true; true; true; true; true; true; false; false; false; true; true; true; true; true; true; true; false; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; false; true; true; true; false; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; false; true; true; true; true; true];
    [true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true];
    [true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true];
    [true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true];
    [true; true; true; true; true; true; true; true; false; false; false; true; true; false; true; true; true; true; false; false; true; true; true; true; true; true; true; true; true; true; true; false; true; true; true; true; true; true; false; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true] ;
    [true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true];
    [false; false; false; true; false; false; false; false; false; false; false; true; false; false; false; false; false; false; true; false; false; true; true; false; false; false; false; true; false; false; false; true; false; true; false; true; false; true; false; false; false; false; false; false; false; true; false; false; false; false; false; false; true; false; false; false; false; false; false; true] ;
    [true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true] ;
    [false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false] ;
    [false; false; false; false; false; false; true; false; false; false; false; false; false; false; false; false; true; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; true; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false] ;
    [true; false; false; false; true; false; true; true; false; false; false; false; false; false; true; false; false; false; false; false; false; false; false; false; false; false; true; false; false; false; false; false; false; true; false; false; false; false; false; false; false; true; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false] ;
    [true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true] ;
    [true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; false; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; false; true; true; true; false; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; false; true; true; true; true; true] ;
    [true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true] ;
    [true; false; false; false; false; false; true; false; false; false; true; false; false; false; false; false; true; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; true; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false] ;
    [true; true; true; true; false; true; true; false; false; false; true; false; true; false; false; true; true; false; false; true; false; true; false; true; true; true; false; false; false; false; false; false; false; false; false; true; true; false; false; false; false; false; false; true; true; false; false; false; false; false; false; false; true; false; false; false; false; false; true; false] ;
    [false; false; false; false; false; false; true; false; false; false; false; false; false; false; false; false; true; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; true; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false] ;
    [false; false; false; false; false; false; true; false; false; false; false; false; false; false; false; false; true; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; true; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false] ;
    [false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false] ;
    [false; true; true; true; false; true; false; true; true; true; false; true; true; true; false; true; true; true; true; true; false; true; false; true; true; true; false; true; false; false; true; false; false; false; false; true; true; true; true; false; false; false; false; true; true; false; false; false; false; false; false; true; true; true; false; false; false; false; true; false] 
  ]
let answers_csp = 
  [
    [true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; false; true; true; false; true; false; true; true; true; false; false; true; true; false; true; true; true; true; false; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true];
    [true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true];
    [false; false; true; true; false; false; false; false; true; true; false; false; false; false; true; false; true; false; false; false; false; false; false; true; false; false; true; false; false; false; false; false; false; false; false; true; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; true; false; false; false; false];
    [true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true];
    [false; true; true; true; true; true; true; true; true; true; false; true; true; true; true; true; true; true; false; true; false; true; true; true; true; true; true; true; false; false; true; true; true; false; true; true; true; true; false; true; false; true; true; false; true; true; true; true; true; false; true; true; true; false; false; true; true; true; false; true];
    [true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true];
    [true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true];
    [true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true];
    [false; true; true; true; true; true; true; false; true; true; true; true; true; true; true; true; true; true; false; true; true; true; true; true; true; true; true; true; false; true; true; true; true; false; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; false; true; true; true; true; true; true; true; true; true; true];
    [true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true];
    [false; true; true; false; true; true; true; true; false; true; true; true; true; true; true; true; true; false; true; false; true; true; true; true; true; false; false; true; true; true; true; true; false; true; true; true; true; false; true; true; true; false; false; true; true; true; true; false; true; false; true; true; true; true; true; true; true; true; true; true];
    [true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true];
    [false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false];
    [false; false; false; false; false; false; true; false; false; false; false; false; false; false; false; false; true; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; true; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; true; false; false; false];
    [false; false; true; true; false; false; false; false; true; true; false; false; false; false; true; false; true; false; false; false; false; false; false; true; false; false; true; false; false; false; false; false; false; false; false; true; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; true; false; false; false; false];
    [true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true];
    [true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; false; true; false; true; true; true; true; true; true; true; false; false; true; true; true; false; true; true; true; true; false; true; false; true; true; false; true; true; true; true; true; false; true; true; true; false; false; true; true; true; false; true];
    [true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true];
    [true; false; false; false; false; false; true; false; false; false; true; false; false; false; false; false; true; false; false; false; false; false; false; false; false; false; false; false; false; false; true; false; false; false; false; false; true; false; false; false; false; false; false; false; false; false; false; false; false; false; true; false; false; false; false; false; true; false; false; false];
    [true; false; false; true; false; false; true; false; false; false; true; false; true; false; false; true; true; false; false; false; false; true; false; false; false; true; true; false; false; false; true; false; true; false; false; false; true; false; false; false; false; false; true; false; false; true; true; false; false; false; true; false; false; false; false; false; true; false; false; false];
    [false; false; false; false; false; false; true; false; false; false; false; false; false; false; false; false; true; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; true; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; true; false; false; false];
    [false; false; false; false; false; false; true; false; false; false; false; false; false; false; false; false; true; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; true; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; true; false; false; false];
    [false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false];
    [true; false; false; true; false; false; true; false; true; false; true; false; true; true; false; true; false; false; false; false; false; false; false; false; false; true; true; false; false; false; true; false; false; false; false; false; false; false; false; false; false; false; true; false; false; true; true; true; false; false; false; false; false; false; false; false; true; false; false; false]
  ]

(* filename has the format: *n1n2 *)
let cp_index mname = 
  let n1 = String.sub mname 2 2
  and n2 = String.sub mname 4 2 in
  if n1 = "02" then
    (int_of_string n2) - 1
  else if n1 = "04" then
    20 + (int_of_string n2) - 1
  else
    40 + (int_of_string n2) - 1

let csp_index mname = 
  let n1 = String.sub mname 2 2
  and n2 = String.sub mname 4 2 in
  if n1 = "03" then
    (int_of_string n2) - 1
  else if n1 = "04" then
    20 + (int_of_string n2) - 1
  else
    40 + (int_of_string n2) - 1

let input_paras pl = 
  let rec get_para_from_stdin i paras = 
    match paras with
    | (v, vt) :: paras' -> 
      (match vt with
      | Int_type (i1, i2) -> (Const (int_of_string Sys.argv.(i)))
      | Bool_type -> (Const (let b = Sys.argv.(i) in (if b="true" then 1 else (if b="false" then (0) else (-1)))))
      | _ -> print_endline ("invalid input for parameter: "^v^"."); exit 1) :: (get_para_from_stdin (i+1) paras')
    | [] -> [] in
  get_para_from_stdin 2 pl

let opt_prove file = 
  let (modl_tbl, modl) = Oparser.input Olexer.token (Lexing.from_channel (open_in file)) in
  let modl_tbl1 = Hashtbl.create (Hashtbl.length modl_tbl) 
  and modl1 = modul021 modl in	
  Hashtbl.iter (fun a b -> Hashtbl.add modl_tbl1 a (modul021 b)) modl_tbl;
  let modl2 = modul122 modl1 (input_paras modl1.parameter_list) modl_tbl1 in
  let modl3 = modul223 modl2 in
  let modl4 = modul324 modl3 in
  let modl5 = modul425 modl4 in
  Oprover.prove_modelb modl5

let plain_prove file =
  let get_mname fname = 
    (
        let lfname = List.hd (List.rev (String.split_on_char '/' (String.trim fname))) in
        let mname = List.hd (String.split_on_char '.' lfname) in
        String.capitalize_ascii mname
    ) in
  let pmoduls = Hashtbl.create 1 in
  let opkripke = ref None in
  let start_pmodul = ref "" in
  List.iter (fun fname -> 
      let mname = get_mname fname in
      let cha = open_in fname in
      let lbuf = Lexing.from_channel (cha) in
      try
          let imported, psymbol_tbl, pkripke_model = Parser.program Lexer.token lbuf in 
          begin
              match pkripke_model with
              | None -> ()
              | Some pk -> opkripke := Some pk; start_pmodul := mname
          end;
          let modul = {
              fname = fname;
              imported = imported;
              psymbol_tbl = psymbol_tbl;
              pkripke_model = pkripke_model;
          } in
          Hashtbl.add pmoduls mname modul
      with e -> 
          let sp = lbuf.lex_start_p in
          let ep = lbuf.lex_curr_p in
          printf "syntax error from line %d, column %d to line %d, column %d\n" 
              sp.pos_lnum (sp.pos_cnum - sp.pos_bol)
              ep.pos_lnum (ep.pos_cnum - ep.pos_bol)
  ) [file];
  match !opkripke with
  | None -> print_endline "no kripke model was built, exit."; exit 1
  | Some pkripke -> 
      let dg = dep_graph_of_pmodul !start_pmodul pmoduls in 
      let rec typecheck dg moduls = 
      match dg with
      | Leaf mname -> 
          (try
              Typechecker.check_modul mname moduls
          with Invalid_pexpr_loc (pel, msg) ->
              print_endline ("Error: "^msg);
              print_endline (Print.str_pexprl pel);
              exit 1)
      | Node (mname, dgs) -> 
          List.iter (fun dg -> typecheck dg moduls) dgs; 
          (try
              Typechecker.check_modul mname moduls
          with Invalid_pexpr_loc (pel, msg) ->
              print_endline ("Error: "^msg);
              print_endline (Print.str_pexprl pel);
              exit 1) in
      typecheck dg pmoduls;
      let runtime = pmoduls_to_runtime pmoduls pkripke !start_pmodul in
      Prover.prove_modelb runtime !start_pmodul

let test_cp opt i test_ctx = 
  let ans = List.nth answers_cp (i-1) in
  let cp_dir = ref "" in
  if i<10 then
    cp_dir := test_dir ^ "random/p1/p0" ^ (string_of_int i) ^ "/"
  else
    cp_dir := test_dir ^ "random/p1/p" ^ (string_of_int i) ^ "/";
  let files = Sys.readdir !cp_dir in
  Array.iter (fun f ->
    let mnames = (String.split_on_char '.' f) in
    if List.length mnames = 2 && (List.nth mnames 1 = "model") then
      let file = !cp_dir ^ f in
      let result = if opt then opt_prove file else plain_prove file in
      let correct = (List.nth ans (cp_index (List.nth mnames 0))) in
      if result = correct then 
        (* print_endline "Pass" *)()
      else begin
        print_endline ("Fail: "^f^" should be "^(string_of_bool correct)^" but got "^(string_of_bool result));
        exit 1
      end;
      assert_equal result correct 
  ) files

let test_csp opt i test_ctx = 
  let ans = List.nth answers_csp (i-1) in
  let csp_dir = ref "" in
  if i<10 then
    csp_dir := test_dir ^ "random/p2/p0" ^ (string_of_int i) ^ "/"
  else
    csp_dir := test_dir ^ "random/p2/p" ^ (string_of_int i) ^ "/";
  let files = Sys.readdir !csp_dir in
  Array.iter (fun f ->
    let mnames = (String.split_on_char '.' f) in
    if List.length mnames = 2 && (List.nth mnames 1 = "model") then
      let file = !csp_dir ^ f in
      let result = if opt then opt_prove file else plain_prove file in
      let correct = (List.nth ans (csp_index (List.nth mnames 0))) in
      if result = correct then 
        (* print_endline "Pass" *) ()
      else begin
        print_endline ("Fail: "^f^" should be "^(string_of_bool correct)^" but got "^(string_of_bool result));
        exit 1
      end;
      assert_equal result correct
  ) files

let random_suit opt = 
  "Random Programs" >:::
  (* (List.init 3 (fun i -> "Test CP "^(string_of_int (i+1)) >:: test_cp opt (i+1))) *)
    ((List.init 24 (fun i -> "Test CP "^(string_of_int (i+1)) >:: test_cp opt (i+1))) @
     (List.init 24 (fun i -> "Test CSP "^(string_of_int (i+1)) >:: test_csp opt (i+1))))

let _ = 
  run_test_tt_main (random_suit true)

