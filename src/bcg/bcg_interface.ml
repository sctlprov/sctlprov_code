(* open Printf *)

type state = int
(* type nb_states = int
type nb_edges = int
type nb_labels = int *)

external read_bcg : string -> state = "read_bcg"
external trans: state -> ((int * bool * int) list) = "trans"
external close_bcg : unit -> unit = "close_bcg"

(* let read_lts filename = 
  let init = read_bcg filename in
  let lts = Lts.new_lts init in
  let next = trans  *)
(* 
let _ = 
  print_endline "parsing file";
  let filename = Sys.argv.(1) in
  (* print_int (bcg_nb_states()); *)
  print_endline "";
  let ini = read_bcg filename in
  printf "the initial state: %d" ini;
  (* printf "%s: \n\tinitial state: %d\n\tnb_states: %d\n\tnb_edges: %d\n\tnb_labels: %d\n" filename ini ns ne nl; *)
  close_bcg ();
  print_endline "bcg file is closed." *)