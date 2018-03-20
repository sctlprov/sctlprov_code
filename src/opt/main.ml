open Printf
open Term 
open Formula
open Modul
open Prover_output
open Prover
open Parser

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
		let (modl_tbl, modl) = Parser.input Lexer.token (Lexing.from_channel (open_in input_file)) in
		let modl_tbl1 = Hashtbl.create (Hashtbl.length modl_tbl) 
		and modl1 = modul021 modl in	
		Hashtbl.iter (fun a b -> Hashtbl.add modl_tbl1 a (modul021 b)) modl_tbl;
		let modl2 = modul122 modl1 (input_paras modl1.parameter_list) modl_tbl1 in
		let modl3 = modul223 modl2 in
		let modl4 = modul324 modl3 in
		let modl5 = modul425 modl4 in
		match (bdd, output_file, visualize_addr) with
		| (true, None, "") -> Prover_bdd.prove_model modl5
		| (false, None, "") -> 
			print_endline ("verifying on the model " ^ modl5.name ^"...");
			Prover.prove_model modl5
		| (_, Some filename, _) -> 
			let out = open_out filename in
			Prover_output.Seq_Prover.prove_model modl5 out filename;
			close_out out
		| (_, None, _) ->
			if visualize_addr <> "" then begin
				printf "prove with visualization\n";
				flush stdout;
				Prover_visualization.prove_model modl5 visualize_addr
			end else begin
				printf "input arguments not valid\n";
				flush stdout
			end
			
	with Parsing.Parse_error -> print_endline ("parse error at line: "^(string_of_int (!(Lexer.line_num))))
	

let main () = 
	let use_bdd = ref false 
	and output_file = ref None 
	and visualize_addr = ref "" in
	Arg.parse
		[
			"-bdd", Arg.Unit (fun () -> use_bdd := true), " Whether using BDDs to store state sets";
			"-output", Arg.String (fun s -> output_file := Some s), " The output file";
			"-visualize_addr", Arg.String (fun s -> visualize_addr := s), " IP address of the vmdv server";
		]
		(fun s -> choose_to_prove !use_bdd !output_file !visualize_addr s)
		"Usage: sctl [-bdd] [-output <filename>] <filename>"

let _ = 
	Printexc.print main ()
