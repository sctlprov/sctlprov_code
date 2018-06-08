open Printf

type kstate = {
  state: int;
  label: int;
}

let sd = {state = -1; label = -2;}

let tau = ref (-1)

exception No_next of kstate

let compare_state s1 s2 = Pervasives.compare s1 s2

module State_label_key = 
struct
	type t = kstate
	let compare = Pervasives.compare
end;;

module State_label_set = Set.Make(State_label_key)

module State_key = 
struct
  type t = int
  let compare = Pervasives.compare
end;;

module State_set = Set.Make(State_key)

let state si li = {state = si; label = li;}
	
let str_kstate s = "("^(string_of_int s.state)^","^(string_of_int s.label)^")"


type t = {
	init: kstate;
	trans: (kstate, State_set.t) Hashtbl.t;
}

let create_model s = {init = state s (-2); trans = Hashtbl.create 1;} 


let add_trans ks s1 s2 = 
	try
		Hashtbl.replace ks.trans s1 (State_set.add s2 (Hashtbl.find ks.trans s1))
	with Not_found ->
		Hashtbl.add ks.trans s1 (State_set.singleton s2)

let next ks s ignore_label = 
  if s = sd then
  State_label_set.singleton sd 
  else begin 
  let nexts = ref State_label_set.empty in
  let lts_trans = Bcg_interface.trans s.state in
  (* print_string (str_kstate s);
  print_string "->"; *)
  if lts_trans = [] then
    nexts := State_label_set.add sd !nexts;
  List.iter (fun (ln, lv, ns) -> 
    if lv then begin
      (* print_string ((str_kstate {state = ns; label = ln;})^","); *)
      nexts := State_label_set.add {state = ns; label = ln;} !nexts
    end else begin
      (* tau := ln; *)
      (* print_string ((str_kstate {state = ns; label = -1;})^","); *)
      nexts := State_label_set.add {state = ns; label = -1;} !nexts
    end
  ) lts_trans;
  (* print_endline ""; *)
  !nexts
  end


let has_tau s = s.label = !tau
let is_deadlock s = s = sd
(**)