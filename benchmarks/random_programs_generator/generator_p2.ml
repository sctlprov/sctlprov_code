(* for smv input files *)
type smv_spec = 
	  Andi of int * int
	| Ori of int * int
	| Or of smv_spec * smv_spec
	| And of smv_spec * smv_spec
	| Not of smv_spec 
	| AG of smv_spec
	| AF of smv_spec
	| EF of smv_spec
	| EG of smv_spec
	| AU of smv_spec * smv_spec
	| EU of smv_spec * smv_spec
	| AX of smv_spec
	| EX of smv_spec

let rec str_spec spec = 
	match spec with
	| Andi (i, j) -> let str = ("v"^(string_of_int i)^"=TRUE") in if i = j then str else (str ^"&"^ (str_spec (Andi (i+1, j))))
	| Ori (i, j) -> let str = ("v"^(string_of_int i)^"=TRUE") in if i = j then str else (str ^"|"^ (str_spec (Ori (i+1, j))))
	| Or (s1, s2) -> "("^(str_spec s1) ^")|("^(str_spec s2)^")"
	| And (s1, s2) -> "("^(str_spec s1) ^")&("^(str_spec s2)^")"
	| Not s -> "!("^(str_spec s)^")"
	| AG s -> "AG("^(str_spec s)^")"
	| AF s -> "AF("^(str_spec s)^")"
	| EF s -> "EF("^(str_spec s)^")"
	| EG s -> "EG("^(str_spec s)^")"
	| AU (s1, s2) -> "A[("^(str_spec s1)^")U("^(str_spec s2)^")]"
	| EU (s1, s2) -> "E[("^(str_spec s1)^")U("^(str_spec s2)^")]"
	| AX s -> "AX("^(str_spec s)^")"
	| EX s -> "EX("^(str_spec s)^")"

let rec str_verds_spec spec = 
	match spec with
	| Andi (i, j) -> let str = ("v"^(string_of_int i)^"=1") in if i = j then str else (str ^"&"^ (str_verds_spec (Andi (i+1, j))))
	| Ori (i, j) -> let str = ("v"^(string_of_int i)^"=1") in if i = j then str else (str ^"|"^ (str_verds_spec (Ori (i+1, j))))
	| Or (s1, s2) -> "("^(str_verds_spec s1) ^")|("^(str_verds_spec s2)^")"
	| And (s1, s2) -> "("^(str_verds_spec s1) ^")&("^(str_verds_spec s2)^")"
	| Not s -> "!("^(str_verds_spec s)^")"
	| AG s -> "AG("^(str_verds_spec s)^")"
	| AF s -> "AF("^(str_verds_spec s)^")"
	| EF s -> "EF("^(str_verds_spec s)^")"
	| EG s -> "EG("^(str_verds_spec s)^")"
	| AU (s1, s2) -> "A(("^(str_verds_spec s1)^")U("^(str_verds_spec s2)^"))"
	| EU (s1, s2) -> "E(("^(str_verds_spec s1)^")U("^(str_verds_spec s2)^"))"
	| AX s -> "AX("^(str_verds_spec s)^")"
	| EX s -> "EX("^(str_verds_spec s)^")"


let make_smv_spec ith var_number = 
	match ith with
	| 1 -> AG (Ori (1, var_number/2))
	| 2 -> AF (Ori (1, var_number/2))
	| 3 -> AG (Or (Not (Ori (1, 1)), AF (And (Ori(2,2), Ori(3,var_number/2)))))
	| 4 -> AG (Or (Not (Ori (1, 1)), EF (And (Ori(2,2), Ori(3,var_number/2)))))
	| 5 -> EG (Or (Not (Ori (1, 1)), AF (And (Ori(2,2), Ori(3,var_number/2)))))
	| 6 -> EG (Or (Not (Ori (1, 1)), EF (And (Ori(2,2), Ori(3,var_number/2)))))
	| 7 -> AU (Ori (1,1), AU (Ori(2,2), Ori(3,var_number/2)))
	| 8 -> AU (Ori (1,1), EU (Ori(2,2), Ori(3,var_number/2)))
	| 9 -> AU (Ori (1,1), Not (EU (Not (Ori(2,2)), Not (Ori(3,var_number/2)))))
	| 10 -> AU (Ori (1,1), Not (AU (Not (Ori(2,2)), Not (Ori(3,var_number/2)))))
	| 11 -> Not (EU (Not (AX (Ori (1,1))), Not (AX (AU (Ori (2,2), Ori (3, var_number/2))))))
	| 12 -> Not (EU (Not (EX (Ori (1,1))), Not (EX (EU (Ori (2,2), Ori (3, var_number/2))))))
	| 13 -> AG (Andi (1, var_number/2))
	| 14 -> AF (Andi (1, var_number/2))
	| 15 -> AG (Or (Not (Ori (1, 1)), AF (Or (Andi(2,2), Andi(3,var_number/2)))))
	| 16 -> AG (Or (Not (Ori (1, 1)), EF (Or (Andi(2,2), Andi(3,var_number/2)))))
	| 17 -> EG (Or (Not (Ori (1, 1)), AF (Or (Andi(2,2), Andi(3,var_number/2)))))
	| 18 -> EG (Or (Not (Ori (1, 1)), EF (Or (Andi(2,2), Andi(3,var_number/2)))))
	| 19 -> AU (Ori (1,1), AU (Ori(2,2), Andi(3,var_number/2)))
	| 20 -> AU (Ori (1,1), EU (Ori(2,2), Andi(3,var_number/2)))
	| 21 -> AU (Ori (1,1), Not (EU (Not (Ori(2,2)), Not (Andi(3,var_number/2)))))
	| 22 -> AU (Ori (1,1), Not (AU (Not (Ori(2,2)), Not (Andi(3,var_number/2)))))
	| 23 -> Not (EU (Not (AX (Ori (1,1))), Not (AX (AU (Ori (2,2), Andi (3, var_number/2))))))
	| 24 -> Not (EU (Not (EX (Ori (1,1))), Not (EX (EU (Ori (2,2), Andi (3, var_number/2))))))
	| _ -> print_endline ("not a valid number: "^(string_of_int ith)); exit 1

type smv_model = 
{
	main_init: (string, bool) Hashtbl.t;
	proc_args: int;
	proc1_next: ((string*string) list) list;
	proc2_next: ((string*string) list) list;
}

let models = Hashtbl.create 20

let spec_tbl = Hashtbl.create 24

let rec make_sctl_atomic is_and i j = 
	if i = j then "s(v"^(string_of_int i)^")" else 
	"s(v"^(string_of_int i)^")"^(if is_and then " && " else " || ")^(make_sctl_atomic is_and (i+1) j)


 let generate_sctl_fmls var_number = 
 	Hashtbl.add spec_tbl 1 ("\tAtomic\n\t{\n\t\tokay(s) := "^(make_sctl_atomic false 1 (var_number/2))^";\n\t}\n\n\tSpec\n\t{\n\t\tspec := not EU(x, y, TRUE, not okay(y), ini);\n\t}");
 	Hashtbl.add spec_tbl 2 ("\tAtomic\n\t{\n\t\tokay(s) := "^(make_sctl_atomic false 1 (var_number/2))^";\n\t}\n\n\tSpec\n\t{\n\t\tspec := AF(x, okay(x), ini);\n\t}");
 	Hashtbl.add spec_tbl 3 ("\tAtomic\n\t{\n\t\tatom1(s) := "^(make_sctl_atomic false 1 1)^";\n\t\tatom2(s) := "^(make_sctl_atomic false 2 2)^";\n\t\tatom3(s) := "^(make_sctl_atomic false 3 (var_number/2))^";\n\t}\n\n\tSpec\n\t{\n\t\tspec := not EU(x, y, TRUE, (atom1(y) /\\ not AF(z, atom2(z) /\\ atom3(z), y)), ini);\n\t}");
 	Hashtbl.add spec_tbl 4 ("\tAtomic\n\t{\n\t\tatom1(s) := "^(make_sctl_atomic false 1 1)^";\n\t\tatom2(s) := "^(make_sctl_atomic false 2 2)^";\n\t\tatom3(s) := "^(make_sctl_atomic false 3 (var_number/2))^";\n\t}\n\n\tSpec\n\t{\n\t\tspec := not EU(x, y, TRUE, (atom1(y) /\\ not EU(z, v, TRUE, atom2(v) /\\ atom3(v), y)), ini);\n\t}");
 	Hashtbl.add spec_tbl 5 ("\tAtomic\n\t{\n\t\tatom1(s) := "^(make_sctl_atomic false 1 1)^";\n\t\tatom2(s) := "^(make_sctl_atomic false 2 2)^";\n\t\tatom3(s) := "^(make_sctl_atomic false 3 (var_number/2))^";\n\t}\n\n\tSpec\n\t{\n\t\tspec := EG(x, (not atom1(x)) \\/ (AF(y, atom2(y) /\\ atom3(y), x)), ini);\n\t}");
 	Hashtbl.add spec_tbl 6 ("\tAtomic\n\t{\n\t\tatom1(s) := "^(make_sctl_atomic false 1 1)^";\n\t\tatom2(s) := "^(make_sctl_atomic false 2 2)^";\n\t\tatom3(s) := "^(make_sctl_atomic false 3 (var_number/2))^";\n\t}\n\n\tSpec\n\t{\n\t\tspec := EG(x, (not atom1(x)) \\/ (EU(y, z, TRUE, atom2(z) /\\ atom3(z), x)), ini);\n\t}");
 	Hashtbl.add spec_tbl 7 ("\tAtomic\n\t{\n\t\tatom1(s) := "^(make_sctl_atomic false 1 1)^";\n\t\tatom2(s) := "^(make_sctl_atomic false 2 2)^";\n\t\tatom3(s) := "^(make_sctl_atomic false 3 (var_number/2))^";\n\t}\n\n\tSpec\n\t{\n\t\tspec := not EU(x, y, EU(z, v, not atom3(z), (not atom2(v)) /\\ (not atom3(v)), x) \\/ EG(v, not atom3(v), x), (not atom1(y)) /\\ (EU(z, v, not atom3(z), (not atom2(v)) /\\ (not atom3(v)), y) \\/ EG(v, not atom3(v), y)), ini) /\\ not EG(y, EU(z, v, not atom3(z), (not atom2(v)) /\\ (not atom3(v)), y) \\/ EG(v, not atom3(v), y), ini);\n\t}");
 	Hashtbl.add spec_tbl 8 ("\tAtomic\n\t{\n\t\tatom1(s) := "^(make_sctl_atomic false 1 1)^";\n\t\tatom2(s) := "^(make_sctl_atomic false 2 2)^";\n\t\tatom3(s) := "^(make_sctl_atomic false 3 (var_number/2))^";\n\t}\n\n\tSpec\n\t{\n\t\tspec := not EU(x, y, not EU(z, v, atom2(z), atom3(v), x), (not atom1(y)) /\\ (not EU(z, v, atom2(z), atom3(v), y)), ini) /\\ not EG(y, not EU(z, v, atom2(z), atom3(v), y), ini);\n\t}");
 	Hashtbl.add spec_tbl 9 ("\tAtomic\n\t{\n\t\tatom1(s) := "^(make_sctl_atomic false 1 1)^";\n\t\tatom2(s) := "^(make_sctl_atomic false 2 2)^";\n\t\tatom3(s) := "^(make_sctl_atomic false 3 (var_number/2))^";\n\t}\n\n\tSpec\n\t{\n\t\tspec := (not EU(x, y, EU(z, v, not atom2(z), not atom3(v), x), (not atom1(y)) /\\ EU(z, v, not atom2(z), not atom3(v), y), ini)) /\\ not EG(y, EU(z, v, not atom2(z), not atom3(v), y), ini);\n\t}");
 	Hashtbl.add spec_tbl 10 ("\tAtomic\n\t{\n\t\tatom1(s) := "^(make_sctl_atomic false 1 1)^";\n\t\tatom2(s) := "^(make_sctl_atomic false 2 2)^";\n\t\tatom3(s) := "^(make_sctl_atomic false 3 (var_number/2))^";\n\t}\n\n\tSpec\n\t{\n\t\tspec := (not EU(x, y, (not EU(z, v, atom3(z), atom2(v) /\\ atom3(v), x)) /\\ (not EG(v, atom3(v), x)), (not atom1(y)) /\\ (not EU(z, v, atom3(z), atom2(v) /\\ atom3(v), y)) /\\ (not EG(v, atom3(v), y)), ini)) /\\ not EG(y, (not EU(z, v, atom3(z), atom2(v) /\\ atom3(v), y)) /\\ (not EG(v, atom3(v), y)), ini);\n\t}");
 	Hashtbl.add spec_tbl 11 ("\tAtomic\n\t{\n\t\tatom1(s) := "^(make_sctl_atomic false 1 1)^";\n\t\tatom2(s) := "^(make_sctl_atomic false 2 2)^";\n\t\tatom3(s) := "^(make_sctl_atomic false 3 (var_number/2))^";\n\t}\n\n\tSpec\n\t{\n\t\tspec := not EU(x, y, not AX(z, atom1(z), x), not AX(v, (not EU(w, u, not atom3(w), (not atom2(u)) /\\ (not atom3(u)), v)) /\\ (not EG(u, not atom3(u), v)), y), ini);\n\t}");
 	Hashtbl.add spec_tbl 12 ("\tAtomic\n\t{\n\t\tatom1(s) := "^(make_sctl_atomic false 1 1)^";\n\t\tatom2(s) := "^(make_sctl_atomic false 2 2)^";\n\t\tatom3(s) := "^(make_sctl_atomic false 3 (var_number/2))^";\n\t}\n\n\tSpec\n\t{\n\t\tspec := not EU(x, y, not EX(z, atom1(z), x), not EX(v, EU(w, u, atom2(w), atom3(u), v), y), ini);\n\t}");
 	Hashtbl.add spec_tbl 13 ("\tAtomic\n\t{\n\t\tokay(s) := "^(make_sctl_atomic true 1 (var_number/2))^";\n\t}\n\n\tSpec\n\t{\n\t\tspec := not EU(x, y, TRUE, not okay(y), ini);\n\t}");
 	Hashtbl.add spec_tbl 14 ("\tAtomic\n\t{\n\t\tokay(s) := "^(make_sctl_atomic true 1 (var_number/2))^";\n\t}\n\n\tSpec\n\t{\n\t\tspec := AF(x, okay(x), ini);\n\t}");
 	Hashtbl.add spec_tbl 15 ("\tAtomic\n\t{\n\t\tatom1(s) := "^(make_sctl_atomic true 1 1)^";\n\t\tatom2(s) := "^(make_sctl_atomic true 2 2)^";\n\t\tatom3(s) := "^(make_sctl_atomic true 3 (var_number/2))^";\n\t}\n\n\tSpec\n\t{\n\t\tspec := not EU(x, y, TRUE, (atom1(y) /\\ not AF(z, atom2(z) /\\ atom3(z), y)), ini);\n\t}");
 	Hashtbl.add spec_tbl 16 ("\tAtomic\n\t{\n\t\tatom1(s) := "^(make_sctl_atomic true 1 1)^";\n\t\tatom2(s) := "^(make_sctl_atomic true 2 2)^";\n\t\tatom3(s) := "^(make_sctl_atomic true 3 (var_number/2))^";\n\t}\n\n\tSpec\n\t{\n\t\tspec := not EU(x, y, TRUE, (atom1(y) /\\ not EU(z, v, TRUE, atom2(v) /\\ atom3(v), y)), ini);\n\t}");
 	Hashtbl.add spec_tbl 17 ("\tAtomic\n\t{\n\t\tatom1(s) := "^(make_sctl_atomic true 1 1)^";\n\t\tatom2(s) := "^(make_sctl_atomic true 2 2)^";\n\t\tatom3(s) := "^(make_sctl_atomic true 3 (var_number/2))^";\n\t}\n\n\tSpec\n\t{\n\t\tspec := EG(x, (not atom1(x)) \\/ (AF(y, atom2(y) /\\ atom3(y), x)), ini);\n\t}");
 	Hashtbl.add spec_tbl 18 ("\tAtomic\n\t{\n\t\tatom1(s) := "^(make_sctl_atomic true 1 1)^";\n\t\tatom2(s) := "^(make_sctl_atomic true 2 2)^";\n\t\tatom3(s) := "^(make_sctl_atomic true 3 (var_number/2))^";\n\t}\n\n\tSpec\n\t{\n\t\tspec := EG(x, (not atom1(x)) \\/ (EU(y, z, TRUE, atom2(z) /\\ atom3(z), x)), ini);\n\t}");
 	Hashtbl.add spec_tbl 19 ("\tAtomic\n\t{\n\t\tatom1(s) := "^(make_sctl_atomic true 1 1)^";\n\t\tatom2(s) := "^(make_sctl_atomic true 2 2)^";\n\t\tatom3(s) := "^(make_sctl_atomic true 3 (var_number/2))^";\n\t}\n\n\tSpec\n\t{\n\t\tspec := not EU(x, y, EU(z, v, not atom3(z), (not atom2(v)) /\\ (not atom3(v)), x) \\/ EG(v, not atom3(v), x), (not atom1(y)) /\\ (EU(z, v, not atom3(z), (not atom2(v)) /\\ (not atom3(v)), y) \\/ EG(v, not atom3(v), y)), ini) /\\ not EG(y, EU(z, v, not atom3(z), (not atom2(v)) /\\ (not atom3(v)), y) \\/ EG(v, not atom3(v), y), ini);\n\t}");
 	Hashtbl.add spec_tbl 20 ("\tAtomic\n\t{\n\t\tatom1(s) := "^(make_sctl_atomic true 1 1)^";\n\t\tatom2(s) := "^(make_sctl_atomic true 2 2)^";\n\t\tatom3(s) := "^(make_sctl_atomic true 3 (var_number/2))^";\n\t}\n\n\tSpec\n\t{\n\t\tspec := not EU(x, y, not EU(z, v, atom2(z), atom3(v), x), (not atom1(y)) /\\ (not EU(z, v, atom2(z), atom3(v), y)), ini) /\\ not EG(y, not EU(z, v, atom2(z), atom3(v), y), ini);\n\t}");
 	Hashtbl.add spec_tbl 21 ("\tAtomic\n\t{\n\t\tatom1(s) := "^(make_sctl_atomic true 1 1)^";\n\t\tatom2(s) := "^(make_sctl_atomic true 2 2)^";\n\t\tatom3(s) := "^(make_sctl_atomic true 3 (var_number/2))^";\n\t}\n\n\tSpec\n\t{\n\t\tspec := (not EU(x, y, EU(z, v, not atom2(z), not atom3(v), x), (not atom1(y)) /\\ EU(z, v, not atom2(z), not atom3(v), y), ini)) /\\ not EG(y, EU(z, v, not atom2(z), not atom3(v), y), ini);\n\t}");
 	Hashtbl.add spec_tbl 22 ("\tAtomic\n\t{\n\t\tatom1(s) := "^(make_sctl_atomic true 1 1)^";\n\t\tatom2(s) := "^(make_sctl_atomic true 2 2)^";\n\t\tatom3(s) := "^(make_sctl_atomic true 3 (var_number/2))^";\n\t}\n\n\tSpec\n\t{\n\t\tspec := (not EU(x, y, (not EU(z, v, atom3(z), atom2(v) /\\ atom3(v), x)) /\\ (not EG(v, atom3(v), x)), (not atom1(y)) /\\ (not EU(z, v, atom3(z), atom2(v) /\\ atom3(v), y)) /\\ (not EG(v, atom3(v), y)), ini)) /\\ not EG(y, (not EU(z, v, atom3(z), atom2(v) /\\ atom3(v), y)) /\\ (not EG(v, atom3(v), y)), ini);\n\t}");
 	Hashtbl.add spec_tbl 23 ("\tAtomic\n\t{\n\t\tatom1(s) := "^(make_sctl_atomic true 1 1)^";\n\t\tatom2(s) := "^(make_sctl_atomic true 2 2)^";\n\t\tatom3(s) := "^(make_sctl_atomic true 3 (var_number/2))^";\n\t}\n\n\tSpec\n\t{\n\t\tspec := not EU(x, y, not AX(z, atom1(z), x), not AX(v, (not EU(w, u, not atom3(w), (not atom2(u)) /\\ (not atom3(u)), v)) /\\ (not EG(u, not atom3(u), v)), y), ini);\n\t}");
 	Hashtbl.add spec_tbl 24 ("\tAtomic\n\t{\n\t\tatom1(s) := "^(make_sctl_atomic true 1 1)^";\n\t\tatom2(s) := "^(make_sctl_atomic true 2 2)^";\n\t\tatom3(s) := "^(make_sctl_atomic true 3 (var_number/2))^";\n\t}\n\n\tSpec\n\t{\n\t\tspec := not EU(x, y, not EX(z, atom1(z), x), not EX(v, EU(w, u, atom2(w), atom3(u), v), y), ini);\n\t}")




let rec generate_models var_number = 
	for i=1 to 20 do
		Hashtbl.add models i (make_smv_model var_number)
	done

and make_smv_model var_number = 
(* Random.init 1000; *)
{
	main_init = (let ht = Hashtbl.create var_number in 
				for i = 1 to (var_number/2) do
					Hashtbl.add ht ("v"^(string_of_int i)) (Random.bool ())
				done; 
				ht);
	proc_args = var_number / 2;
	proc1_next = 
		(
			let tmp_list_list = ref [] in
			for i = 1 to var_number/2 do
				let tmp_list = ref [] in
				for j = 1 to 4 do
					let v1 = ref ("v"^(string_of_int (Random.int (var_number*3/4) + 1)))
					and v2 = ref ("v"^(string_of_int (Random.int (var_number*3/4) + 1))) in
					while List.mem_assoc !v1 !tmp_list do
						v1 := "v"^(string_of_int (Random.int (var_number*3/4) + 1))
					done;
					tmp_list := (!v1, !v2) :: !tmp_list;
				done;
				tmp_list_list := !tmp_list :: !tmp_list_list
			done; !tmp_list_list
		);
	proc2_next = 
		(
			let tmp_list_list = ref [] in
			for i = 1 to var_number/2 do
				let tmp_list = ref [] in
				for j = 1 to 4 do
					let r1 = let rb = Random.bool () in if rb then Random.int (var_number/2) + 1 else (Random.int (var_number/4) + (var_number*3/4) + 1)
					and r2 = let rb = Random.bool () in if rb then Random.int (var_number/2) + 1 else (Random.int (var_number/4) + (var_number*3/4) + 1) in
					let v1 = ref ("v"^(string_of_int (r1)))
					and v2 = ref ("v"^(string_of_int (r2))) in
					while List.mem_assoc !v1 !tmp_list do
						let r1 = let rb = Random.bool () in if rb then Random.int (var_number/2) + 1 else (Random.int (var_number/4) + (var_number*3/4) + 1) in
						v1 := "v"^(string_of_int (r1))
					done;
					tmp_list := (!v1, !v2) :: !tmp_list;
				done;
				tmp_list_list := !tmp_list :: !tmp_list_list
			done; !tmp_list_list
		);
}

let rec get_smv_next v tmp_list_list var_number = 
	let tmp_str = ref ("TRUE:"^v^";") in
	for i = var_number/2 - 1 downto 0 do
		let tmp_list = List.nth tmp_list_list i in
		try
			let b = List.assoc v tmp_list in
			tmp_str := ("cp=c"^(string_of_int i)^":!"^b^";\n") ^ !tmp_str
		with
		| Not_found -> ()
	done; !tmp_str

let print_smv_model var_number = 
	(* Random.init 100; *)
	for j = 1 to 20 do
		let model = Hashtbl.find models j in
		for i = 1 to 24 do
			let file_name = (if i<10 then "0"^(string_of_int i) else string_of_int i)^
							(let m = var_number/4 in if (m<10) then "0"^(string_of_int m) else string_of_int m)^
							(if j<10 then "0"^(string_of_int j) else string_of_int j)^
							".smv" in
			let out = open_out file_name in

			output_string out "MODULE main\nVAR\n";
			for tmp = 1 to (var_number/2) do
				output_string out ("v"^(string_of_int tmp)^":boolean;\n")
			done;
			output_string out "cp:{";
			for tmpi = 0 to var_number/2 - 2 do 
				output_string out ("c"^(string_of_int tmpi)^",")
			done;
			output_string out ("c"^(string_of_int (var_number/2 - 1))^"};\n");
			for tmp = var_number/2 + 1 to (var_number/4)*3 do
				output_string out ("v"^(string_of_int tmp)^":boolean;\n")
			done;
			output_string out "p1: process p1t(";
			for tmp = 1 to var_number/2-1 do
				output_string out ("v"^(string_of_int tmp)^",");
			done;
			output_string out ("v"^(string_of_int (var_number/2))^");\n");
(* 			output_string out "p2: process p2t(";
			for tmp = 1 to var_number/2 - 1 do
				output_string out ("v"^(string_of_int tmp)^",");
			done;
			output_string out ("v"^(string_of_int (var_number/2))^");\n"); *)
			(* output_string out "\b);\n"; *)
			output_string out "ASSIGN\n";
			Hashtbl.iter (fun a b -> output_string out ("init("^a^"):="^(String.uppercase (string_of_bool b))^";\n")) model.main_init;
			output_string out "init(cp):=c0;\n";
			for tmp = var_number/2+1 to (var_number/4)*3 do
				output_string out ("init(v"^(string_of_int tmp)^"):=FALSE;\n")
			done;
			(* Hashtbl.iter (fun a b -> output_string out ("next("^a^"):=!v"^(string_of_int b)^";\n")) model.main_next; *)
			(* Hashtbl.iter (fun a b -> output_string out ("next("^a^"):=!v"^(string_of_int b)^";\n")) model.proc0_next; *)
			output_string out "next(cp):=case\n";
			for tmpi = 0 to var_number/2 - 1 do
				output_string out ("cp=c"^(string_of_int tmpi)^":c"^(string_of_int ((tmpi+1) mod (var_number/2)))^";\n")
			done;
			output_string out "esac;\n";

			for tmpi = 1 to var_number/4*3 do
				output_string out ("next(v"^(string_of_int tmpi)^"):=case\n"^(get_smv_next ("v"^(string_of_int tmpi)) model.proc1_next var_number)^"\nesac;\n")
			done; 
			output_string out ("SPEC "^(str_spec (make_smv_spec i var_number)) ^"\n");
			output_string out "MODULE p1t(";
			for tmp = 1 to var_number/2-1 do
				output_string out ("v"^(string_of_int tmp)^",");
			done;
			output_string out ("v"^(string_of_int (var_number/2))^")\nVAR\n");
			output_string out "cp:{";
			for tmpi = 0 to var_number/2 - 2 do 
				output_string out ("c"^(string_of_int tmpi)^",")
			done;
			output_string out ("c"^(string_of_int (var_number/2 - 1))^"};\n");
			for tmp = (var_number/4)*3 + 1 to (var_number) do
				output_string out ("v"^(string_of_int tmp)^":boolean;\n")
			done;
			output_string out "ASSIGN\n";
			output_string out "init(cp):=c0;\n";
			for tmp = (var_number/4)*3 + 1 to (var_number) do
				output_string out ("init(v"^(string_of_int tmp)^"):=FALSE;\n")
			done;
			(* Hashtbl.iter (fun a b -> output_string out ("next("^a^"):=!v"^(string_of_int b)^";\n")) model.proc1_next; *)
			output_string out "next(cp):=case\n";
			for tmpi = 0 to var_number/2 - 1 do
				output_string out ("cp=c"^(string_of_int tmpi)^":c"^(string_of_int ((tmpi+1) mod (var_number/2)))^";\n")
			done;
			output_string out "esac;\n";

			for tmpi = 1 to var_number/2 do
				output_string out ("next(v"^(string_of_int tmpi)^"):=case\n"^(get_smv_next ("v"^(string_of_int tmpi)) model.proc2_next var_number)^"\nesac;\n")
			done;	
			for tmpi = var_number*3/4 + 1 to var_number do
				output_string out ("next(v"^(string_of_int tmpi)^"):=case\n"^(get_smv_next ("v"^(string_of_int tmpi)) model.proc2_next var_number)^"\nesac;\n")
			done;
(* 			output_string out "MODULE p2t(";
			for tmp = 1 to var_number/2-1 do
				output_string out ("v"^(string_of_int tmp)^",");
			done;
			output_string out ("v"^(string_of_int (var_number/2))^")\nVAR\n");
			(* output_string out "\b);\nVAR\n"; *)
			for tmp = (var_number/6)*5 + 1 to (var_number) do
				output_string out ("v"^(string_of_int tmp)^":boolean;\n")
			done;
			output_string out "ASSIGN\n";
			for tmp = (var_number/6)*5 + 1 to (var_number) do
				output_string out ("init(v"^(string_of_int tmp)^"):=FALSE;\n")
			done;
			Hashtbl.iter (fun a b -> output_string out ("next("^a^"):=!v"^(string_of_int b)^";\n")) model.proc2_next; *)
			flush out;
			close_out out
		done 
	done

let print_verds_model var_number = 
	(* Random.init 100; *)
	for j = 1 to 20 do
		let model = Hashtbl.find models j in
		for i = 1 to 24 do
			let file_name = (if i<10 then "0"^(string_of_int i) else string_of_int i)^
							(let m = var_number/4 in if (m<10) then "0"^(string_of_int m) else string_of_int m)^
							(if j<10 then "0"^(string_of_int j) else string_of_int j)^
							".vvm" in
			let out = open_out file_name in

			output_string out "VVM\nVAR\n";
			for tmp = 1 to var_number/2 do
				output_string out ("v"^(string_of_int tmp)^":(0..1);\n")
			done;
			output_string out "INIT\n";
			Hashtbl.iter (fun a b -> output_string out (a^"="^(string_of_int (if b then 1 else 0))^";\n")) model.main_init;
			output_string out "PROC\n";
			for tmp = 0 to 1 do
				output_string out ("p"^(string_of_int tmp)^":p"^(string_of_int tmp)^"t(");
				for tmpi = 1 to var_number/2-1 do
					output_string out ("v"^(string_of_int tmpi)^",")
				done;
				output_string out ("v"^(string_of_int (var_number/2))^");\n")
			done;
			output_string out ("SPEC\n"^(str_verds_spec (make_smv_spec i var_number))^";\n");
			for tmp = 0 to 1 do
				output_string out ("MODULE p"^(string_of_int tmp)^"t(");
				for tmpi = 1 to var_number/2-1 do
					output_string out ("v"^(string_of_int tmpi)^",")
				done;
				output_string out ("v"^(string_of_int (var_number/2))^")\nVAR\n");

				output_string out "cp:{";
				for tmpi = 0 to var_number/2 - 2 do 
					output_string out ("c"^(string_of_int tmpi)^",")
				done;
				output_string out ("c"^(string_of_int (var_number/2 - 1))^"};\n");

				for tmpi = tmp*var_number/4 + var_number/2+1 to tmp*var_number/4 + (var_number/4)*3 do
					output_string out ("v"^(string_of_int tmpi)^":(0..1);\n")
				done;
				output_string out "INIT\n";
				output_string out "cp=c0;\n";
				for tmpi = tmp*var_number/4 + var_number/2 + 1 to tmp*var_number/4 + (var_number/4)*3 do
					output_string out ("v"^(string_of_int tmpi)^"=0;\n")
				done;
				output_string out "TRANS\n";
				let proc_next = if tmp = 0 then model.proc1_next else model.proc2_next in
				for tmpi = 0 to var_number/2 - 1 do
					let tmp_list = List.nth proc_next tmpi in
					output_string out ("cp=c"^(string_of_int tmpi)^": (");
					List.iter (fun (a, b) -> output_string out (a^",")) tmp_list;
					output_string out "cp):=(";
					List.iter (fun (a, b) -> output_string out ("1-"^b^",")) tmp_list;
					output_string out ("c"^(string_of_int ((tmpi+1) mod (var_number/2)))^");\n");
				done
			done;

			flush out;
			close_out out
		done 
	done

let print_sctl_model var_number = 
	(* Random.init 100; *)
	for j = 1 to 20 do
		let model = Hashtbl.find models j in
		for i = 1 to 24 do
			let file_name = (if i<10 then "0"^(string_of_int i) else string_of_int i)^
							(let m = var_number/4 in if (m<10) then "0"^(string_of_int m) else string_of_int m)^
							(if j<10 then "0"^(string_of_int j) else string_of_int j) in
			let out = open_out (file_name^".model") in

			output_string out ("Model m"^file_name^"()\n{\n");

			output_string out ("\tVar\n\t{\n");
			for tmp = 1 to var_number do
				output_string out ("\t\tv"^(string_of_int tmp)^": Bool;\n")
			done;
			output_string out "\t\tcp0:{";
			for tmpi = 0 to var_number/2 - 2 do 
				output_string out ("#c"^(string_of_int tmpi)^",")
			done;
			output_string out ("#c"^(string_of_int (var_number/2 - 1))^"};\n");

			output_string out "\t\tcp1:{";
			for tmpi = 0 to var_number/2 - 2 do 
				output_string out ("#c"^(string_of_int tmpi)^",")
			done;
			output_string out ("#c"^(string_of_int (var_number/2 - 1))^"};\n");
			output_string out "\t}\n\n";

			output_string out "\tInit\n\t{\n";
			for tmp = 1 to var_number/2 do
				output_string out ("\t\tv"^(string_of_int tmp)^" := "^(string_of_bool (Hashtbl.find model.main_init ("v"^(string_of_int tmp))))^";\n")
			done;
			for tmp = var_number/2+1 to var_number do
				output_string out ("\t\tv"^(string_of_int tmp)^" := false;\n")
			done;
			output_string out "\t\tcp0 := #c0;\n\t\tcp1 := #c0;\n";
			output_string out "\t}\n\n";

			output_string out "\tTransition\n\t{\n";
			for tmpi = 0 to 1 do
				let proc_next = if tmpi = 0 then model.proc1_next else model.proc2_next in
				for tmpj = 0 to var_number/2 - 1 do
					output_string out ("\t\tcp"^(string_of_int tmpi)^" = #c"^(string_of_int tmpj)^" : {");
					List.iter (fun (a, b) -> output_string out (a^" := !"^b^"; ")) (List.nth proc_next tmpj);
					output_string out ("cp"^(string_of_int tmpi)^" := #c"^ (string_of_int ((tmpj+1) mod (var_number/2)))^";};\n")
				done

			done;
			output_string out "\t}\n\n";

			output_string out (Hashtbl.find spec_tbl i);

			output_string out "\n}";

			flush out;
			close_out out
		done 
	done

let _ = 
	let var_number = int_of_string Sys.argv.(1) in
	Random.init 100;
	generate_models var_number;
	generate_sctl_fmls var_number;
	print_smv_model var_number;
	print_verds_model var_number;
	print_sctl_model var_number