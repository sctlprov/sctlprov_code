let generate_var p out = 
	output_string out "\tVar\n\t{\n";
	for i = 1 to 5 do
		output_string out ("\t\tr"^(string_of_int i)^" : Bool["^(string_of_int p)^"];\n")
(*
		if i < 10 
		then
			output_string out ("\t\ts0"^(string_of_int i)^": {#noncritical, #trying, #critical};\n") 
		else 
			output_string out ("\t\ts"^(string_of_int i)^": {#noncritical, #trying, #critical};\n")*)
	done;
	output_string out ("\t\toutput : Bool["^(string_of_int p)^"];\n");
	output_string out ("\t\tpc: (0 .. "^(string_of_int (p))^");\n");
	output_string out "\t}\n\n"

let generate_init p out = 
	let p_fs = ref "false" in
	for i = 1 to p-1 do
		p_fs := "false, "^(!p_fs)
	done;
	output_string out "\tInit\n\t{\n";
	for i = 1 to 5 do
		output_string out ("\t\tr"^(string_of_int i)^" := {"^(!p_fs)^"};\n")
		(*if i < 10 
		then
			output_string out ("\t\ts0"^(string_of_int i)^" := #noncritical;\n") 
		else 
			output_string out ("\t\ts"^(string_of_int i)^" := #noncritical;\n")*)
	done;
	output_string out ("\t\toutput := {"^(!p_fs)^"};\n");
	output_string out ("\t\tpc := "^(string_of_int (p))^";\n");
	output_string out "\t}\n\n"

let generate_transition p out = 
	output_string out "\tTransition\n\t{\n";
	for i = 0 to p-1 do
		let str_i = string_of_int i in
		let str_mod_i = string_of_int ((i+p-1) mod p) in
		output_string out ("\t\ttrue : {r1["^str_i^"] := !(output["^str_mod_i^"]); r2["^str_i^"] := !(r1["^str_i^"]); r3["^str_i^"] := !(r2["^str_i^"]); r4["^str_i^"] := !(r3["^str_i^"]); r5["^str_i^"] := !(r4["^str_i^"]); output["^str_i^"] := !(r5["^str_i^"]); pc := "^str_i^";};\n")
	done;
	output_string out "\t}\n\n"

let generate_fairness p out = 
	output_string out "\tFairness\n\t{\n\t\t";
	for i = 0 to p-1 do
		output_string out ("fair"^(string_of_int i)^"(s); ")
	done;
	output_string out "\n";
	output_string out "\t}\n\n"

let generate_atomic p i out = 
	output_string out "\tAtomic\n\t{\n";
	output_string out "\t\tatom(s) := s(output[0] = true);\n";
	for i = 0 to p-1 do
		output_string out ("\t\tfair"^(string_of_int i)^"(s) := "^"s(pc = "^(string_of_int i)^");\n")
	done;
	output_string out "\t}\n\n"

let generate_spec p i out = 
	output_string out "\tSpec\n\t{\n";
	begin
		match i with
		| 1 -> output_string out "\t\tring := AR (x, y, FALSE, AF (z, atom(z), y), ini) /\\ AR (x, y, FALSE, AF (z, not atom(z), y), ini);\n"
		| 2 -> output_string out "\t\tring := AR (x, y, FALSE, EU (w, z, TRUE, atom(z), y), ini) /\\ AR (x, y, FALSE, EU (w, z, TRUE, not atom(z), y), ini);\n"
		| 3 -> output_string out "\t\tring := EG (y, AF (z, atom(z), y), ini) /\\ EG (y, AF (z, not atom(z), y), ini);\n"
		| 4 -> output_string out "\t\tring := EG (y, EU (w, z, TRUE, atom(z), y), ini) /\\ EG (y, EU (w, z, TRUE, not atom(z), y), ini);\n"
		(*| 5 -> output_string out "\t\tmutual := AR (x, y, FALSE, (not atom1(y)) \\/ (AR (z, w, (not atom1(z)) /\\ AR(v, p, atom2(v), (not atom1(p)) \\/ atom2(p), z) /\\ AF(p, atom2(p), z), atom1(w) \\/ ((not atom1(w)) /\\ AR(v, p, atom2(v), (not atom1(p)) \\/ atom2(p), w) /\\ AF(p, atom2(p), w)), y) /\\ AF(w, (not atom1(w)) /\\ AR(v, p, atom2(v), (not atom1(p)) \\/ atom2(p), w) /\\ AF(p, atom2(p), w), y)), ini);\n"*)
		| _ -> output_string out "\t\tError spec;\n"
	end;
	output_string out "\t}\n\n"

let _ = 
	let para = Sys.argv.(1) in
	let p = int_of_string para in
	for i = 1 to 4 do
		let output_file = "ring_a"^(if p<10 && p>0 then "0"^(string_of_int p) else (string_of_int p))^(string_of_int i) in
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
