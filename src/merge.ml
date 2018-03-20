open Expr
open Ast
open Formula
open Interp
open Printf
open Cudd

module State_key = struct
	type t = value
	let compare = Pervasives.compare
end;;
module State_set = Set.Make(State_key)

(***normal to binary***)
let ia_bin_size = ref 0
let var_bin_size_ary = ref (Array.make 0 0)
let var_base_val_ary = ref (Array.make 0 0)
let flag = ref false
(*module BDD = Bdd.BDD (struct let nv = 24 end)*)

let rec get_bin_attr modl = 
  match modl.state_type with
  | PTRecord str_ptyps -> 
    let domain_size_list = List.map (fun (_,pt) -> domain_size pt) str_ptyps in
    let is_finite = not (List.exists (fun d -> d=0) domain_size_list) in
    (* flag := is_finite; *)
    if is_finite then
      flag := true;
      let var_list_size = List.length domain_size_list in
      let bin_size = ref 0 
      and bin_size_ary =  (Array.make var_list_size 0)
      and var_base_ary =  (Array.make var_list_size 0) 
      and index = ref 0 in
      List.iter (fun (a) -> 
        (match a with
        | (s, PTIntRange (i1, i2)) -> let bs = (int_size (i2-i1+1)) in bin_size := !bin_size + bs; bin_size_ary.(!index) <- bs; var_base_ary.(!index) <- i1
        | (s, PTScalar ss) -> let bs = int_size (List.length ss) in bin_size := !bin_size + bs; bin_size_ary.(!index) <- bs
        | (s, _) -> bin_size := !bin_size + 1; bin_size_ary.(!index) <- 1
        ); incr index
        ) str_ptyps; 
      ia_bin_size := !bin_size; 
      var_bin_size_ary := bin_size_ary; 
      var_base_val_ary := var_base_ary
  | _ -> flag := false

	(* let var_list_size = (List.length modl.var_list) in
	let bin_size = ref 0 
	and bin_size_ary =  (Array.make var_list_size 0)
	and var_base_ary =  (Array.make var_list_size 0) 
	and index = ref 0 in
	List.iter (fun a -> 
		(match a with
		| (s, Int_type (i1, i2)) -> let bs = (int_size (i2-i1+1)) in bin_size := !bin_size + bs; bin_size_ary.(!index) <- bs; var_base_ary.(!index) <- i1
		| (s, Scalar_type ss) -> let bs = int_size (List.length ss) in bin_size := !bin_size + bs; bin_size_ary.(!index) <- bs
		| (s, _) -> bin_size := !bin_size + 1; bin_size_ary.(!index) <- 1
		); incr index
		) modl.var_list; (ia_bin_size := !bin_size; var_bin_size_ary := bin_size_ary; var_base_val_ary := var_base_ary; flag := true) *)
	
and int_size i = 
	let tmp = ref 2
	and index = ref 1 in
	while (i) >= !tmp do
		incr index;
		tmp := 2 * !tmp
	done; !index
	
and int_to_binary i =
	let tmp_list = ref [] 
	and tmp_i = ref i in
	if i = 0 then [0] else
	begin
		while !tmp_i > 0 do
			tmp_list := (!tmp_i mod 2) :: !tmp_list;
			tmp_i := !tmp_i / 2
		done; !tmp_list
	end

and value_to_il value = 
  match value with
  | VRecord str_vals -> 
    List.map (fun (s,value) -> 
      match value with
      | VInt i -> i
      | VBool b -> if b then 1 else 0
      | VUnt -> 0
      | _ -> (-1) 
    ) str_vals
  | _ -> []

let rec ia_to_bin ia = 
  try
    if !flag = true then
      (* let ia = Array.of_list il in *)
      begin
        let tmp_ary = Array.make !ia_bin_size 0 
        and index = ref 0 in
        for i=0 to (Array.length ia) - 1 do
          if (!var_bin_size_ary.(i) < 2) then (tmp_ary.(!index) <- ia.(i); incr index) else 
          begin
            let bin_lst = int_to_binary (ia.(i) - !var_base_val_ary.(i)) in
            let tmp_index = ref (!index + !var_bin_size_ary.(i) - 1) in
            List.iter (fun a -> tmp_ary.(!tmp_index) <- a; decr tmp_index) (List.rev bin_lst);
            index := !index + !var_bin_size_ary.(i)
          end
        done; tmp_ary
      end
    else
      Array.make !ia_bin_size 0 
  with _ -> print_endline "exception encountered in ia_to_bin."; exit (-1)
(*****)

let true_merge = Hashtbl.create 10
let false_merge = Hashtbl.create 10
let true_mergeb : (string, (Man.v) Bdd.t) Hashtbl.t = Hashtbl.create 10
let false_mergeb : (string, (Man.v) Bdd.t) Hashtbl.t = Hashtbl.create 10

let is_in_true_merge s levl = 
  begin
    try
      State_set.mem s (Hashtbl.find true_merge levl)
    with Not_found -> print_endline ("level not found in finding true merge: "^levl); exit 1
  end
let is_in_true_mergeb s levl = 
  let il = value_to_il s in
  BDD.int_array_satisfy (ia_to_bin (Array.of_list il)) (Hashtbl.find true_mergeb levl) 
  
let is_in_false_merge s levl = 
  begin
    State_set.mem s (Hashtbl.find false_merge levl)
  end
let is_in_false_mergeb s levl = 
  (* if !Flags.using_bdd && !flag then begin *)
  let il = value_to_il s in
  BDD.int_array_satisfy (ia_to_bin (Array.of_list il)) (Hashtbl.find false_mergeb levl) 
  (* end else begin
    State_set.mem s (Hashtbl.find false_merge levl)
  end *)
let add_to_true_merge s levl = 
  begin
    try
      let bss = Hashtbl.find true_merge levl in
      Hashtbl.replace true_merge levl (State_set.add s bss)
    with Not_found -> print_endline ("level not found in finding true merge: "^levl); exit 1
  end
let add_to_true_mergeb s levl = 
  (* if !Flags.using_bdd && !flag then begin *)
  let il = value_to_il s in
    (* BDD.int_array_satisfy (ia_to_bin (Array.of_list il)) (Hashtbl.find true_mergeb levl)  *)
  Hashtbl.replace true_mergeb levl (BDD.add_int_array (ia_to_bin (Array.of_list il)) (Hashtbl.find true_mergeb levl))
  (* end else begin
    try
      let bss = Hashtbl.find true_merge levl in
      Hashtbl.replace true_merge levl (State_set.add s bss)
    with Not_found -> print_endline ("level not found in finding true merge: "^levl); exit 1
  end *)
let add_to_false_merge s levl = 
  begin
    try
      let bss = Hashtbl.find false_merge levl in
      Hashtbl.replace false_merge levl (State_set.add s bss)
    with Not_found -> print_endline ("level not found in finding false merge: "^levl); exit 1
  end
let add_to_false_mergeb s levl = 
  (* if !Flags.using_bdd && !flag then begin *)
  let il = value_to_il s in
    (* BDD.int_array_satisfy (ia_to_bin (Array.of_list il)) (Hashtbl.find true_mergeb levl)  *)
  Hashtbl.replace false_mergeb levl (BDD.add_int_array (ia_to_bin (Array.of_list il)) (Hashtbl.find false_mergeb levl))
  (* end else begin
    try
      let bss = Hashtbl.find false_merge levl in
      Hashtbl.replace false_merge levl (State_set.add s bss)
    with Not_found -> print_endline ("level not found in finding false merge: "^levl); exit 1
  end *)
let clear_true_merge levl = 
  begin
    Hashtbl.replace true_merge levl (State_set.empty)
  end
let clear_true_mergeb levl = 
  (* if !Flags.using_bdd && !flag then begin *)
    (* let il = value_to_il s in *)
    (* BDD.int_array_satisfy (ia_to_bin (Array.of_list il)) (Hashtbl.find true_mergeb levl)  *)
  Hashtbl.replace true_mergeb levl (!BDD.leaf_false)
  (* end else begin
    Hashtbl.replace true_merge levl (State_set.empty)
  end *)
let clear_false_merge levl = 
  begin
    Hashtbl.replace false_merge levl (State_set.empty)
  end
let clear_false_mergeb levl = 
  (* if !Flags.using_bdd && !flag then begin *)
    (* let il = value_to_il s in *)
    (* BDD.int_array_satisfy (ia_to_bin (Array.of_list il)) (Hashtbl.find true_mergeb levl)  *)
  Hashtbl.replace false_mergeb levl (!BDD.leaf_false)
  (* end else begin
    Hashtbl.replace false_merge levl (State_set.empty)
  end *)
(* let merges = Hashtbl.create 10 *)
let pre_process_merges sub_fml_tbl = 
  (* Hashtbl.iter (fun a b -> Hashtbl.add merges a (State_set.empty)) sub_fml_tbl; *)
  Hashtbl.iter (fun a b -> Hashtbl.add true_merge a (State_set.empty)) sub_fml_tbl;
  Hashtbl.iter (fun a b -> Hashtbl.add false_merge a (State_set.empty)) sub_fml_tbl;
  Hashtbl.iter (fun a b -> Hashtbl.add true_mergeb a (!BDD.leaf_false)) sub_fml_tbl;
  Hashtbl.iter (fun a b -> Hashtbl.add false_mergeb a (!BDD.leaf_false)) sub_fml_tbl

(* let in_global_merge s level = 
  State_set.mem s (Hashtbl.find merges level)

let add_to_global_merge ss level = 
  let sts = Hashtbl.find merges level in
  Hashtbl.replace merges level (State_set.fold (fun elem b -> State_set.add elem b) ss sts)
    
let clear_global_merge level = 
  Hashtbl.replace merges level (State_set.empty)
let get_global_merge level = 
  Hashtbl.find merges level *)


  