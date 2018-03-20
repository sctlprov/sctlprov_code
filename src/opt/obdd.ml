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
		(*let bdd1 = bdd_from_int_array ia in*)
		let bdd2 = bdd in
		(*let bdd2 = Bdd.dor bdd bdd1 in*)
		(*if (Bdd.eq bdd bdd2) = leaf_true then true else false*)

		(*let bdd3 = ref bdd2 in
		for i = 0 to (Array.length ia - 1) do
			let (ct, cf) = Bdd.cofactors i !bdd3 in
			if ia.(i) = 1 then bdd3 := ct else bdd3 := cf
		done;
		if !bdd3 = leaf_true then true else false*)
		let bdd3 = ref bdd2 in
		while Bdd.is_cst !bdd3 = false do
			if ia.(Bdd.topvar !bdd3) = 1 then bdd3 := Bdd.dthen !bdd3 else bdd3 := Bdd.delse !bdd3	
		done;
		if !bdd3 = !leaf_true then true else false


	let add_int_array ia bdd = 
		let bdd1 = bdd_from_int_array ia in
		let bdd2 = Bdd.dor bdd bdd1 in
		(*print_endline ("support size: "^(string_of_int (Bdd.supportsize bdd2))); *)
		bdd2

	let rec bdd_union bdd1 bdd2 = 
		Bdd.dor bdd1 bdd2

(*****
type bdd =
	| Leaf of bool
	| Node of int * bdd * bdd

exception Invalid_value of int * string
exception BDD_wrong_size
exception Add_to_array_error

let bdd_from_bool_array_i (ba: bool array) i0 = 
	let rec build_from_i ba i b = 
		if i<i0 then b else 
			if (ba.(i)) then build_from_i ba (i-1) (Node (i, b, Leaf false)) else build_from_i ba (i-1) (Node (i, Leaf false, b)) in build_from_i ba (Array.length ba - 1) (Leaf true)

let bdd_from_bool_array (ba: bool array) = bdd_from_bool_array_i ba 0
	
let bdd_from_int_array_i (ia : int array) i0 = 
	let rec build_from_i ba i b = 
	if i<i0 then b else 
		if (ba.(i) = 1) then build_from_i ba (i-1) (Node (i, b, Leaf false)) else 
			if (ba.(i) = (0)) then build_from_i ba (i-1) (Node (i, Leaf false, b)) else ((Array.iter (fun a -> print_string ((string_of_int a)^" ")) ba);raise (Invalid_value (ba.(i), "bdd_from_int_array"))) in build_from_i ia (Array.length ia - 1) (Leaf true)


let bdd_from_int_array (ia: int array) = bdd_from_int_array_i ia 0


let int_array_satisfy (ia: int array) (b: bdd) = 
	let rec satisfy_upto_i ia i b = 
	match b with
	| Leaf bol -> bol
	| Node (i1, b1, b2) -> if (i1>i) then (satisfy_upto_i ia i1 b) else 
							(if (i=i1) then (satisfy_upto_i ia (i+1) (if (ia.(i) = 1) then b1 else b2)) else raise BDD_wrong_size) in satisfy_upto_i ia 0 b

let bool_array_satisfy (ba: bool array) (b: bdd) = 
	let rec satisfy_upto_i ba i b = 
	match b with
	| Leaf bol -> bol
	| Node (i1, b1, b2) -> if (i1>i) then (satisfy_upto_i ba i1 b) else 
							(if (i=i1) then (satisfy_upto_i ba (i+1) (if (ba.(i)) then b1 else b2)) else raise BDD_wrong_size) in satisfy_upto_i ba 0 b


let add_int_array (ia: int array) b = 
	let rec add_from_i ia i b = 
	match b with
	| Leaf true -> b
	| Leaf false -> bdd_from_int_array_i ia i
	| Node (i1, b1, b2) -> let ia1 = (ia.(i)=1) in if (i<i1) then (if ia1 then Node (i, add_from_i ia (i+1) b, b) else Node(i, b, add_from_i ia (i+1) b)) else (if ia1 then Node(i,add_from_i ia (i+1) b1,b2) else Node(i,b1,add_from_i ia (i+1) b2)) in add_from_i ia 0 b

let add_bool_array (ba: bool array) b = 
	let rec add_from_i ia i b = 
	match b with
	| Leaf true -> b
	| Leaf false -> bdd_from_bool_array_i ia i
	| Node (i1, b1, b2) -> let ia1 = (ia.(i)) in if (i<i1) then (if ia1 then Node (i, add_from_i ia (i+1) b, b) else Node(i, b, add_from_i ia (i+1) b)) else (if ia1 then Node (i, add_from_i ia (i+1) b1, b2) else Node(i, b1, add_from_i ia (i+1) b2)) in add_from_i ba 0 b

let rec bdd_union b1 b2 = 
	match (b1, b2) with
	| (Leaf true, _) -> b1
	| (Leaf false, _) -> b2
	| (_, Leaf true) -> b2
	| (_, Leaf false) -> b1
	| (Node (i, b3, b4), Node (j, b5, b6)) -> if (i=j) then Node (i, bdd_union b3 b5, bdd_union b4 b6) else (if (i>j) then bdd_union (Node(j+1, b1, b1)) b2 else bdd_union b1 (Node(i+1, b2, b2)))


let is_empty b = 
	match b with
	| Leaf false -> true
	| _ -> false


let rec bdd_to_string b = 
	match b with
	| Leaf bol -> string_of_bool bol
	| Node (i, b1, b2) -> "Node "^(string_of_int i)^": \n\tt-->("^(bdd_to_string b1)^")\n\tf-->("^(bdd_to_string b2)^")"
*****)
