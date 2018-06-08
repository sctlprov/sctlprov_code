
(* let input_paras pl = 
	let rec get_para_from_stdin i paras = 
		match paras with
		| (v, vt) :: paras' -> 
			(match vt with
			| Int_type (i1, i2) -> (Const (int_of_string Sys.argv.(i)))
			| Bool_type -> (Const (let b = Sys.argv.(i) in (if b="true" then 1 else (if b="false" then (0) else (-1)))))
			| _ -> print_endline ("invalid input for parameter: "^v^"."); exit 1) :: (get_para_from_stdin (i+1) paras')
		| [] -> [] in
	get_para_from_stdin 2 pl *)


let _ = 
    let files = ref [] in
    let bcg_property = ref "deadlock" in
    Arg.parse [
        "-bcg", Arg.String (fun s -> bcg_property := s), "\tDetecting livelocks or deadlocks for BCG files"
    ] (fun s -> files := !files @ [s]) "Usage: sctl [-bcg <deadlock/livelock>] files";
    let filename = List.hd !files in
    if List.nth (String.split_on_char '.' filename) 1 = "bcg" then begin
        let lstate = Bcg_interface.read_bcg filename in
        match !bcg_property with
        | "livelock" -> Prover_bcg.prove_model (Ks_bcg.create_model lstate) [(!bcg_property, Formula_bcg.EU (Formula_bcg.SVar "z", Formula_bcg.SVar "w", Formula_bcg.Top, Formula_bcg.EG (Formula_bcg.SVar "x", Formula_bcg.Atomic ("has_tau", [Formula_bcg.SVar "x"]), Formula_bcg.SVar "w"), Formula_bcg.SVar "ini"))] false false
        | _ -> Prover_bcg.prove_model (Ks_bcg.create_model lstate) [(!bcg_property, Formula_bcg.EU (Formula_bcg.SVar "x", Formula_bcg.SVar "y", Formula_bcg.Top, (Formula_bcg.Atomic ("is_deadlock", [Formula_bcg.SVar "y"])), Formula_bcg.SVar "ini"))] false false
    end else begin
        print_endline ("This executable can only handle \".bcg\" files, for \".model\" files, please try \"make opt\" or \"make all\"")
    end

    