let generate_var p out = 
	output_string out "\tVar\n\t{\n";
	for i = 0 to p do
		if i < 10 
		then
			output_string out ("\t\ts0"^(string_of_int i)^": {#noncritical, #trying, #critical};\n") 
		else 
			output_string out ("\t\ts"^(string_of_int i)^": {#noncritical, #trying, #critical};\n")
	done;
	output_string out ("\t\tturn: (0 .. "^(string_of_int p)^");\n");
	output_string out ("\t\tpc: (0 .. "^(string_of_int (p+1))^");\n");
	output_string out "\t}\n\n"

let generate_init p out = 
	output_string out "\tInit\n\t{\n";
	for i = 0 to p do
		if i < 10 
		then
			output_string out ("\t\ts0"^(string_of_int i)^" := #noncritical;\n") 
		else 
			output_string out ("\t\ts"^(string_of_int i)^" := #noncritical;\n")
	done;
	output_string out ("\t\tturn := 0;\n");
	output_string out ("\t\tpc := "^(string_of_int (p+1))^";\n");
	output_string out "\t}\n\n"

let generate_transition p out = 
	output_string out "\tTransition\n\t{\n";
	for i = 0 to p do
		for j = i to i do
			output_string out ("\t\t(s"^(if i < 10 then ("0"^(string_of_int i)) else string_of_int i)^" = #noncritical && turn = "^(string_of_int i)^") : {s"^(if i < 10 then ("0"^(string_of_int i)) else string_of_int i)^" := #noncritical; turn := "^(string_of_int ((i+1) mod (p+1)))^"; pc := "^(string_of_int j)^";};\n")
		done;
		for j = i to i do
			output_string out ("\t\t(s"^(if i < 10 then ("0"^(string_of_int i)) else string_of_int i)^" = #noncritical && turn != "^(string_of_int i)^") : {s"^(if i < 10 then ("0"^(string_of_int i)) else string_of_int i)^" := #noncritical; pc := "^(string_of_int j)^";};\n")
		done;
		for j = i to i do
			output_string out ("\t\t(s"^(if i < 10 then ("0"^(string_of_int i)) else string_of_int i)^" = #noncritical && turn = "^(string_of_int i)^") : {s"^(if i < 10 then ("0"^(string_of_int i)) else string_of_int i)^" := #trying; turn := "^(string_of_int ((i+1) mod (p+1)))^"; pc := "^(string_of_int j)^";};\n")
		done;
		for j = i to i do
			output_string out ("\t\t(s"^(if i < 10 then ("0"^(string_of_int i)) else string_of_int i)^" = #noncritical && turn != "^(string_of_int i)^") : {s"^(if i < 10 then ("0"^(string_of_int i)) else string_of_int i)^" := #trying; pc := "^(string_of_int j)^";};\n")			
		done;
		for j = i to i do
			output_string out ("\t\t(s"^(if i < 10 then ("0"^(string_of_int i)) else string_of_int i)^" = #trying && s" ^(let i1 = (i+1) mod (p+1) in if i1 < 10 then ("0"^(string_of_int i1)) else string_of_int i1)^" = #noncritical) : {s"^(if i < 10 then ("0"^(string_of_int i)) else string_of_int i)^" := #critical; pc := "^(string_of_int j)^";};\n")			
		done;
		for j = i to i do
			output_string out ("\t\t(s"^(if i < 10 then ("0"^(string_of_int i)) else string_of_int i)^" = #trying && s" ^(let i1 = (i+1) mod (p+1) in if i1 < 10 then ("0"^(string_of_int i1)) else string_of_int i1)^" = #trying && turn = "^(string_of_int i)^") : {s"^(if i < 10 then ("0"^(string_of_int i)) else string_of_int i)^" := #critical; pc := "^(string_of_int j)^";};\n")			
		done;
		for j = i to i do
			output_string out ("\t\ts"^(if i < 10 then ("0"^(string_of_int i)) else string_of_int i)^" = #critical : {s"^(if i < 10 then ("0"^(string_of_int i)) else string_of_int i)^" := #critical; pc := "^(string_of_int j)^";};\n" )
		done;
		for j = i to i do
			output_string out ("\t\ts"^(if i < 10 then ("0"^(string_of_int i)) else string_of_int i)^" = #critical : {s"^(if i < 10 then ("0"^(string_of_int i)) else string_of_int i)^" := #noncritical; pc := "^(string_of_int j)^";};\n" )
		done;
		for j = i to i do
			(*s00 = #trying && s01 != #noncritical && (s01 != #trying || turn != 0) : {pc := 0;};*)
			output_string out ("\t\ts"^(if i < 10 then ("0"^(string_of_int i)) else string_of_int i)^" = #trying && s"^(let i1 = (i+1) mod (p+1) in if i1 < 10 then ("0"^(string_of_int i1)) else string_of_int i1)^" != #noncritical && (s"^(let i1 = (i+1) mod (p+1) in if i1 < 10 then ("0"^(string_of_int i1)) else string_of_int i1)^" != #trying || turn != "^(string_of_int i)^") : {pc := "^(string_of_int j)^";};\n")	
		done
	done;
	output_string out "\t}\n\n"

let generate_fairness p out = 
	output_string out "\tFairness\n\t{\n\t\t";
	for i = 0 to p+1 do
		output_string out ("fair"^(string_of_int i)^"(s); ");
	done;
(*
	for i = 0 to p do
		output_string out ("pc = "^(string_of_int i)^"; ")
	done;
	output_string out "s00 != #critical;\n";
*)
	output_string out "\n\t}\n\n"

let generate_atomic p i out = 
	output_string out "\tAtomic\n\t{\n";
	begin
		match i with
		| 1 -> output_string out "\t\tatom1(s) := s(s00 = #critical);\n\t\tatom2(s) := s(s01 = #critical);\n"
		| 2 -> output_string out "\t\tatom1(s) := s(s00 = #trying);\n\t\tatom2(s) := s(s00 = #critical);\n"
		| 3 -> output_string out "\t\tatom1(s) := s(s01 = #trying);\n\t\tatom2(s) := s(s01 = #critical);\n"
		| 4 -> output_string out "\t\tatom1(s) := s(s00 = #critical);\n\t\tatom2(s) := s(s01 = #critical);\n"
		| 5 -> output_string out "\t\tatom1(s) := s(s01 = #critical);\n\t\tatom2(s) := s(s00 = #critical);\n"
		| _ -> output_string out "\t\tError specs;\n"
	end;
	for i = 0 to p do
		output_string out ("\t\tfair"^(string_of_int i)^"(s) := "^"s(pc = "^(string_of_int i)^");\n")
	done;
	output_string out ("\t\tfair"^(string_of_int (p+1))^"(s) := s(s00 != #critical);\n");
	output_string out "\t}\n\n"

let generate_spec p i out = 
	output_string out "\tSpec\n\t{\n";
	begin
		match i with
		| 1 -> output_string out "\t\tmutual := EU(x, y, TRUE, atom1(y) /\\ atom2(y), ini);\n"
		| 2 -> output_string out "\t\tmutual := AR(x, y, FALSE, (not atom1(y)) \\/ AF(z, atom2(z), y), ini);\n"
		| 3 -> output_string out "\t\tmutual := AR(x, y, FALSE, (not atom1(y)) \\/ AF(z, atom2(z), y), ini);\n"
		| 4 -> output_string out "\t\tmutual := AR (x, y, FALSE, (not atom1(y)) \\/ (AR (z, w, (not atom1(z)) /\\ AR(v, p, atom2(v), (not atom1(p)) \\/ atom2(p), z) /\\ AF(p, atom2(p), z), atom1(w) \\/ ((not atom1(w)) /\\ AR(v, p, atom2(v), (not atom1(p)) \\/ atom2(p), w) /\\ AF(p, atom2(p), w)), y) /\\ AF(w, (not atom1(w)) /\\ AR(v, p, atom2(v), (not atom1(p)) \\/ atom2(p), w) /\\ AF(p, atom2(p), w), y)), ini);\n"
		| 5 -> output_string out "\t\tmutual := AR (x, y, FALSE, (not atom1(y)) \\/ (AR (z, w, (not atom1(z)) /\\ AR(v, p, atom2(v), (not atom1(p)) \\/ atom2(p), z) /\\ AF(p, atom2(p), z), atom1(w) \\/ ((not atom1(w)) /\\ AR(v, p, atom2(v), (not atom1(p)) \\/ atom2(p), w) /\\ AF(p, atom2(p), w)), y) /\\ AF(w, (not atom1(w)) /\\ AR(v, p, atom2(v), (not atom1(p)) \\/ atom2(p), w) /\\ AF(p, atom2(p), w), y)), ini);\n"
		| _ -> output_string out "\t\tError spec;\n"
	end;
	output_string out "\t}\n\n"

let _ = 
	let para = Sys.argv.(1) in
	let p = int_of_string para in
	for i = 1 to 5 do
		(*let output_file = "mutex_a"^para^(string_of_int i) in*)
		let output_file = "mutex_a"^(if p<10 && p>0 then "0"^(string_of_int p) else (string_of_int p))^(string_of_int i) in
		let out = open_out (output_file^".model") in
		output_string out ("Model "^output_file^"()\n{\n");
		generate_var p out;
		generate_init p out;
		generate_transition p out;
		generate_atomic p i out;
		generate_fairness p out;
		generate_spec p i out;
		output_string out "}";
		flush out;
		close_out out
	done
