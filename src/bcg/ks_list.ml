open Printf

type kstate = {
	sfrom: int;
	label: int;
	sto: int;
}

exception No_next of kstate

let compare_state s1 s2 = Pervasives.compare s1 s2

module Key = 
struct
	type t = kstate
	let compare = Pervasives.compare
end;;

module State_set = Set.Make(Key)

let state si = {sfrom = si; label = -1; sto = si;}

let str_kstate s = sprintf "{%d, %d, %d}" s.sfrom s.label s.sto 

type t = {
	init: kstate;
	trans: (kstate, kstate list) Hashtbl.t;
}

let create_model s = {init = s; trans = Hashtbl.create 1;} 

(* let trans = (kstate, kstate list) Hashtbl.t; *)

let add_trans ks s1 s2 = 
	try
		Hashtbl.replace ks.trans s1 (s2 :: (Hashtbl.find ks.trans s1))
	with Not_found ->
    Hashtbl.add ks.trans s1 [s2]
    
let next ks s = 
	if Hashtbl.mem ks.trans s then begin
		let nexts = Hashtbl.find ks.trans s in
		Hashtbl.remove ks.trans s;
		nexts
	end else begin
		let lts_trans = Bcg_interface.trans s.sfrom in
		List.iter (fun (ln, ls, lv, ns) -> 
			if lv then begin
				let label_state = {sfrom = s.sfrom; label = ln; sto = ns;} 
				and next_state = {sfrom = ns; label = -1; sto = ns;} in
				add_trans ks s label_state;
				add_trans ks label_state next_state
			end else begin
				let next_state = {sfrom = ns; label = -1; sto = ns;} in
				add_trans ks s next_state
			end
			) lts_trans;
		try 
			let nexts = Hashtbl.find ks.trans s in
			Hashtbl.remove ks.trans s;
			nexts
		with Not_found -> 
			[]
	end

let is_state s = s.label = -1
let is_label s = not (is_state s)
