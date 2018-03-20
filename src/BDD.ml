open Cudd

let man = ref (Man.make_v ~numVars:(0) ())
let number_of_vars = ref 0
let leaf_true = ref (Bdd.dtrue !man)
let leaf_false = ref (Bdd.dfalse !man)

let init nv = 
	number_of_vars := nv;
	man := Man.make_v ~numVars:nv ();
	leaf_true := Bdd.dtrue !man;
	leaf_false := Bdd.dfalse !man

let bdd_from_int_array ia = 
	let bdd = ref !leaf_true in
	for i = 0 to (Array.length ia - 1) do
		if (ia.(i) = 1) then bdd := Bdd.dand !bdd (Bdd.ithvar !man i) else bdd := Bdd.dand !bdd (Bdd.dnot (Bdd.ithvar !man i))
	done;
	!bdd

let int_array_satisfy ia bdd = 
	let bdd2 = bdd in
	let bdd3 = ref bdd2 in
	while Bdd.is_cst !bdd3 = false do
		if ia.(Bdd.topvar !bdd3) = 1 then bdd3 := Bdd.dthen !bdd3 else bdd3 := Bdd.delse !bdd3	
	done;
	if !bdd3 = !leaf_true then true else false


let add_int_array ia bdd = 
	let bdd1 = bdd_from_int_array ia in
	let bdd2 = Bdd.dor bdd bdd1 in
	bdd2

let rec bdd_union bdd1 bdd2 = 
	Bdd.dor bdd1 bdd2
