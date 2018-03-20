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


let choose_to_prove bdd output_file visualize_addr input_file = 
	try
		let (modl_tbl, modl) = Oparser.input Olexer.token (Lexing.from_channel (open_in input_file)) in
		let modl_tbl1 = Hashtbl.create (Hashtbl.length modl_tbl) 
		and modl1 = modul021 modl in	
		Hashtbl.iter (fun a b -> Hashtbl.add modl_tbl1 a (modul021 b)) modl_tbl;
		let modl2 = modul122 modl1 (input_paras modl1.parameter_list) modl_tbl1 in
		let modl3 = modul223 modl2 in
		let modl4 = modul324 modl3 in
		let modl5 = modul425 modl4 in
		match (bdd, output_file, visualize_addr) with
		| (true, None, None) -> Oprover_bdd.prove_model modl5
		| (false, None, None) -> 
			print_endline ("verifying on the model " ^ modl5.name ^"...");
			Oprover.prove_model modl5
		| (_, Some filename, _) -> 
			let out = open_out filename in
			Oprover_output.Seq_Prover.prove_model modl5 out filename;
			close_out out
		| (_, None, _) ->
			if visualize_addr <> None then begin
				printf "prove with visualization\n";
				flush stdout;
				Oprover_visualization.prove_model modl5 (Options.value visualize_addr)
			end else begin
				printf "input arguments not valid\n";
				flush stdout
			end
    with e -> raise e
    (* print_endline ("parse error at line: "^(string_of_int (!(Olexer.line_num)))) *)
	

let parse_and_prove fnames ip = 
    let get_mname fname = 
        (* List.iter (fun str -> print_endline (":"^str^" ")) (String.split_on_char '.' (String.trim fname)); *)
        (
            let lfname = List.hd (List.rev (String.split_on_char '/' (String.trim fname))) in
            let mname = List.hd (String.split_on_char '.' lfname
        ) in
        (* print_endline ("mname: "^(String.capitalize_ascii mname)); *)
        String.capitalize_ascii mname) in
    let pmoduls = Hashtbl.create 1 in
    let opkripke = ref None in
    let start_pmodul = ref "" in
    List.iter (fun fname -> 
        let mname = get_mname fname in
        (* print_endline ("proving modul "^mname^" in "^fname); *)
        let cha = open_in fname in
        let lbuf = Lexing.from_channel (cha) in
        try
            let imported, psymbol_tbl, pkripke_model = Parser.program Lexer.token lbuf in 
            (* print_endline ("*****************parse module "^mname^" finished*****************"); *)
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
            (* let origin_out = open_out (mname^".origin") in
            output_string origin_out (Print.str_modul modul);
            flush origin_out; *)
            Hashtbl.add pmoduls mname modul
        with e -> raise e
            (* let ep = lbuf.lex_curr_p in
            (* printf "syntax error at line %d, column %d\n" ep.pos_lnum (ep.pos_cnum - ep.pos_bol) *) *)
    ) fnames;
    match !opkripke with
    | None -> print_endline "no kripke model was built, exit."; exit 1
    | Some pkripke -> 
        let dg = dep_graph_of_pmodul !start_pmodul pmoduls in 
        let rec typecheck dg moduls = 
            match dg with
            | Leaf mname -> 
                (try
                    Typechecker.check_modul mname moduls(*;
                    let out = open_out (mname^".typed") in
                    output_string out (Print.str_modul (Hashtbl.find moduls mname));
                    flush out*)
                with Invalid_pexpr_loc (pel, msg) ->
                    print_endline ("Error: "^msg);
                    print_endline (Print.str_pexprl pel);
                    exit 1)
            | Node (mname, dgs) -> 
                List.iter (fun dg -> typecheck dg moduls) dgs; 
                (try
                    Typechecker.check_modul mname moduls(*;
                    let out = open_out (mname^".typed") in
                    output_string out (Print.str_modul (Hashtbl.find moduls mname));
                    flush out*)
                with Invalid_pexpr_loc (pel, msg) ->
                    print_endline ("Error: "^msg);
                    print_endline (Print.str_pexprl pel);
                    exit 1) in
        typecheck dg pmoduls;
        let runtime = pmoduls_to_runtime pmoduls pkripke !start_pmodul in
        match ip with
        | "" -> Prover.prove_model runtime !start_pmodul
        | str -> Prover_visualization.prove_model runtime !start_pmodul str

let _ = 
    let files = ref [] in
    let vis_addr = ref "" in
    Arg.parse [
        "-visualize_addr ip", Arg.String (fun s -> vis_addr := s; Flags.visualize_addr := Some s), "\tIP address of the VMDV server";
        "-bdd", Arg.Unit (fun () -> Flags.using_bdd := true), "\tUsing BDD to store visited states";
        "-optmize", Arg.Bool (fun b -> Flags.optmization := b), "\tApplying optimization";
        "-bcg", Arg.String (fun s -> Flags.bcg_property := s), "\tDetecting livelocks or deadlocks for BCG files"
    ] (fun s -> files := !files @ [s]) "Usage: sctl [-optimize <true/false>] [-bcg <deadlock/livelock>] [-visualize_addr <ip>] files";
    let filename = List.hd !files in
    if List.nth (String.split_on_char '.' filename) 1 = "bcg" then begin
        let lstate = Bcg_interface.read_bcg filename in
        match !Flags.bcg_property with
        | "livelock" -> Prover_bcg.prove_model (Ks_bcg.create_model lstate) [(!Flags.bcg_property, Formula_bcg.EU (Formula_bcg.SVar "z", Formula_bcg.SVar "w", Formula_bcg.Top, Formula_bcg.EG (Formula_bcg.SVar "x", Formula_bcg.Atomic ("has_tau", [Formula_bcg.SVar "x"]), Formula_bcg.SVar "w"), Formula_bcg.SVar "ini"))] false false
        | _ -> Prover_bcg.prove_model (Ks_bcg.create_model lstate) [(!Flags.bcg_property, Formula_bcg.EU (Formula_bcg.SVar "x", Formula_bcg.SVar "y", Formula_bcg.Top, (Formula_bcg.Atomic ("is_deadlock", [Formula_bcg.SVar "y"])), Formula_bcg.SVar "ini"))] false false
    end else if (!Flags.optmization) then begin
        try
            (* print_endline "using opt version"; *)
            choose_to_prove !Flags.using_bdd !Flags.output_file !Flags.visualize_addr (List.hd !files)
        with _ ->
            (* print_endline "not using opt version"; *)
            parse_and_prove !files !vis_addr
    end

    