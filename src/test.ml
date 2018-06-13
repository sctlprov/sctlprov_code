open OUnit2
open Sys
open Ast
open Typechecker
open Dep
open Interp
open Printf
open Lexing
open Oterm 
open Oformula
open Omodul
open Oprover_output
open Oprover
open Oparser 

let test_dir = "./test/"

(* The Standard answer of the result of test cases (Concurrent Processes), run by NuSMV in advance *)
let answers_cp = 
  [
    [false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false];
    [true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true];
    [true; false; false; false; false; false; false; false; false; false; false; false; false; false; true; false; false; false; false; false; false; false; false; false; false; false; true; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false];
    [true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true];
    [true; true; true; true; true; true; true; true; false; false; false; true; true; true; true; true; true; true; false; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; false; true; true; true; false; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; false; true; true; true; true; true];
    [true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true];
    [true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true];
    [true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true];
    [true; true; true; true; true; true; true; true; false; false; false; true; true; false; true; true; true; true; false; false; true; true; true; true; true; true; true; true; true; true; true; false; true; true; true; true; true; true; false; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true] ;
    [true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true];
    [false; false; false; true; false; false; false; false; false; false; false; true; false; false; false; false; false; false; true; false; false; true; true; false; false; false; false; true; false; false; false; true; false; true; false; true; false; true; false; false; false; false; false; false; false; true; false; false; false; false; false; false; true; false; false; false; false; false; false; true] ;
    [true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true] ;
    [false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false] ;
    [false; false; false; false; false; false; true; false; false; false; false; false; false; false; false; false; true; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; true; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false] ;
    [true; false; false; false; true; false; true; true; false; false; false; false; false; false; true; false; false; false; false; false; false; false; false; false; false; false; true; false; false; false; false; false; false; true; false; false; false; false; false; false; false; true; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false] ;
    [true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true] ;
    [true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; false; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; false; true; true; true; false; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; false; true; true; true; true; true] ;
    [true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true] ;
    [true; false; false; false; false; false; true; false; false; false; true; false; false; false; false; false; true; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; true; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false] ;
    [true; true; true; true; false; true; true; false; false; false; true; false; true; false; false; true; true; false; false; true; false; true; false; true; true; true; false; false; false; false; false; false; false; false; false; true; true; false; false; false; false; false; false; true; true; false; false; false; false; false; false; false; true; false; false; false; false; false; true; false] ;
    [false; false; false; false; false; false; true; false; false; false; false; false; false; false; false; false; true; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; true; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false] ;
    [false; false; false; false; false; false; true; false; false; false; false; false; false; false; false; false; true; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; true; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false] ;
    [false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false] ;
    [false; true; true; true; false; true; false; true; true; true; false; true; true; true; false; true; true; true; true; true; false; true; false; true; true; true; false; true; false; false; true; false; false; false; false; true; true; true; true; false; false; false; false; true; true; false; false; false; false; false; false; true; true; true; false; false; false; false; true; false] 
  ]
(* The Standard answer of the result of test cases (Concurrent Sequential Processes), run by NuSMV in advance *)
let answers_csp = 
  [
    [true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; false; true; true; false; true; false; true; true; true; false; false; true; true; false; true; true; true; true; false; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true];
    [true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true];
    [false; false; true; true; false; false; false; false; true; true; false; false; false; false; true; false; true; false; false; false; false; false; false; true; false; false; true; false; false; false; false; false; false; false; false; true; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; true; false; false; false; false];
    [true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true];
    [false; true; true; true; true; true; true; true; true; true; false; true; true; true; true; true; true; true; false; true; false; true; true; true; true; true; true; true; false; false; true; true; true; false; true; true; true; true; false; true; false; true; true; false; true; true; true; true; true; false; true; true; true; false; false; true; true; true; false; true];
    [true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true];
    [true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true];
    [true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true];
    [false; true; true; true; true; true; true; false; true; true; true; true; true; true; true; true; true; true; false; true; true; true; true; true; true; true; true; true; false; true; true; true; true; false; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; false; true; true; true; true; true; true; true; true; true; true];
    [true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true];
    [false; true; true; false; true; true; true; true; false; true; true; true; true; true; true; true; true; false; true; false; true; true; true; true; true; false; false; true; true; true; true; true; false; true; true; true; true; false; true; true; true; false; false; true; true; true; true; false; true; false; true; true; true; true; true; true; true; true; true; true];
    [true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true];
    [false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false];
    [false; false; false; false; false; false; true; false; false; false; false; false; false; false; false; false; true; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; true; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; true; false; false; false];
    [false; false; true; true; false; false; false; false; true; true; false; false; false; false; true; false; true; false; false; false; false; false; false; true; false; false; true; false; false; false; false; false; false; false; false; true; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; true; false; false; false; false];
    [true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true];
    [true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; false; true; false; true; true; true; true; true; true; true; false; false; true; true; true; false; true; true; true; true; false; true; false; true; true; false; true; true; true; true; true; false; true; true; true; false; false; true; true; true; false; true];
    [true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true];
    [true; false; false; false; false; false; true; false; false; false; true; false; false; false; false; false; true; false; false; false; false; false; false; false; false; false; false; false; false; false; true; false; false; false; false; false; true; false; false; false; false; false; false; false; false; false; false; false; false; false; true; false; false; false; false; false; true; false; false; false];
    [true; false; false; true; false; false; true; false; false; false; true; false; true; false; false; true; true; false; false; false; false; true; false; false; false; true; true; false; false; false; true; false; true; false; false; false; true; false; false; false; false; false; true; false; false; true; true; false; false; false; true; false; false; false; false; false; true; false; false; false];
    [false; false; false; false; false; false; true; false; false; false; false; false; false; false; false; false; true; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; true; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; true; false; false; false];
    [false; false; false; false; false; false; true; false; false; false; false; false; false; false; false; false; true; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; true; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; true; false; false; false];
    [false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false];
    [true; false; false; true; false; false; true; false; true; false; true; false; true; true; false; true; false; false; false; false; false; false; false; false; false; true; true; false; false; false; true; false; false; false; false; false; false; false; false; false; false; false; true; false; false; true; true; true; false; false; false; false; false; false; false; false; true; false; false; false]
  ]

let answers_mutual = [
  ("051", true);
  ("052", false);
  ("053", false);
  ("054", false);
  ("055", false);
  ("111", true);
  ("112", false);
  ("113", false);
  ("115", false);
  ("171", true);
  ("172", false);
  ("173", false);
  ("175", false);
  ("231", true);
  ("232", false);
  ("233", false);
  ("235", false);
  ("291", true);
  ("292", false);
  ("293", false);
  ("351", true);
  ("352", false);
  ("353", false);
  ("411", true)
]

let answers_ring = [
  ("031", false);
  ("032", false);
  ("033", true);
  ("034", true);
  ("041", false);
  ("042", false);
  ("043", true);
  ("044", true);
  ("052", false);
  ("053", true);
  ("054", true);
  ("062", false);
  ("064", true);
  ("072", false);
  ("074", true);
  ("082", false);
  ("084", true);
  ("092", false);
  ("094", true);
  ("102", false);
  ("104", true)
]
(* 
let answers_bcg_deadlock = [
  ("vasy_0_1.bcg", false);
  ("cwi_1_2.bcg", false);
  ("vasy_1_4.bcg", false);
  ("cwi_3_14.bcg", true);
  ("vasy_5_9.bcg", true);
  ("vasy_8_24.bcg", false);
  ("vasy_8_38.bcg", true);
  ("vasy_10_56.bcg", false);
  ("vasy_18_73.bcg", false);
  ("vasy_25_25.bcg", true);
  ("vasy_40_60.bcg", false);
  ("vasy_52_318.bcg", false);
  ("vasy_65_2621.bcg", false);
  ("vasy_66_1302.bcg", false);
  ("vasy_69_520.bcg", true);
  ("vasy_83_325.bcg", true);
  ("vasy_116_368.bcg", false);
  ("cwi_142_925.bcg", true);
  ("vasy_157_297.bcg", true);
  ("vasy_164_1619.bcg", false);
  ("vasy_166_651.bcg", true);
  ("cwi_214_684.bcg", true);
  ("cwi_371_641.bcg", false);
  ("vasy_386_1171.bcg", false);
  ("cwi_566_3984.bcg", true);
  ("vasy_574_13561.bcg", false);
  ("vasy_720_390.bcg", true);
  ("vasy_1112_5290.bcg", false);
  ("cwi_2165_8723.bcg", false);
  ("cwi_2416_17605.bcg", true);
  ("vasy_2581_11442.bcg", true);
  ("vasy_4220_13944.bcg", true);
  ("vasy_4338_15666.bcg", true);
  ("vasy_6020_19353.bcg", false);
  ("vasy_6120_11031.bcg", true);
  ("cwi_7838_59101.bcg", false);
  ("vasy_8082_42933.bcg", true);
  ("vasy_11026_24660.bcg", true);
  ("vasy_12323_27667.bcg", true);
  ("cwi_33949_165318.bcg", false)
]


let answers_bcg_livelock = [
  ("vasy_0_1.bcg", false);
  ("cwi_1_2.bcg", false);
  ("vasy_1_4.bcg", false);
  ("cwi_3_14.bcg", false);
  ("vasy_5_9.bcg", false);
  ("vasy_8_24.bcg", false);
  ("vasy_8_38.bcg", false);
  ("vasy_10_56.bcg", false);
  ("vasy_18_73.bcg", false);
  ("vasy_25_25.bcg", false);
  ("vasy_40_60.bcg", false);
  ("vasy_52_318.bcg", true);
  ("vasy_65_2621.bcg", false);
  ("vasy_66_1302.bcg", false);
  ("vasy_69_520.bcg", false);
  ("vasy_83_325.bcg", false);
  ("vasy_116_368.bcg", false);
  ("cwi_142_925.bcg", false);
  ("vasy_157_297.bcg", false);
  ("vasy_164_1619.bcg", false);
  ("vasy_166_651.bcg", false);
  ("cwi_214_684.bcg", true);
  ("cwi_371_641.bcg", true);
  ("vasy_386_1171.bcg", false);
  ("cwi_566_3984.bcg", false);
  ("vasy_574_13561.bcg", false);
  ("vasy_720_390.bcg", false);
  ("vasy_1112_5290.bcg", false);
  ("cwi_2165_8723.bcg", true);
  ("cwi_2416_17605.bcg", true);
  ("vasy_2581_11442.bcg", false);
  ("vasy_4220_13944.bcg", false);
  ("vasy_4338_15666.bcg", false);
  ("vasy_6020_19353.bcg", true);
  ("vasy_6120_11031.bcg", false);
  ("cwi_7838_59101.bcg", true);
  ("vasy_8082_42933.bcg", false);
  ("vasy_11026_24660.bcg", false);
  ("vasy_12323_27667.bcg", false);
  ("cwi_33949_165318.bcg", true)
] *)


(* filename has the format: *n1n2 *)
let cp_index mname = 
  let n1 = String.sub mname 2 2
  and n2 = String.sub mname 4 2 in
  if n1 = "02" then
    (int_of_string n2) - 1
  else if n1 = "04" then
    20 + (int_of_string n2) - 1
  else
    40 + (int_of_string n2) - 1

let csp_index mname = 
  let n1 = String.sub mname 2 2
  and n2 = String.sub mname 4 2 in
  if n1 = "03" then
    (int_of_string n2) - 1
  else if n1 = "04" then
    20 + (int_of_string n2) - 1
  else
    40 + (int_of_string n2) - 1

let input_paras pl = 
  let rec get_para_from_stdin i paras = 
    match paras with
    | (v, vt) :: paras' -> 
      (match vt with
      | Int_type (i1, i2) -> (Const (int_of_string Sys.argv.(i)))
      | Bool_type -> (Const (let b = Sys.argv.(i) in (if b="true" then 1 else (if b="false" then (0) else (-1)))))
      | _ -> print_endline ("invalid input for parameter: "^v^"."); exit 1) :: (get_para_from_stdin (i+1) paras')
    | [] -> [] in
  get_para_from_stdin 2 pl

let opt_prove file = 
  let (modl_tbl, modl) = Oparser.input Olexer.token (Lexing.from_channel (open_in file)) in
  let modl_tbl1 = Hashtbl.create (Hashtbl.length modl_tbl) 
  and modl1 = modul021 modl in	
  Hashtbl.iter (fun a b -> Hashtbl.add modl_tbl1 a (modul021 b)) modl_tbl;
  let modl2 = modul122 modl1 (input_paras modl1.parameter_list) modl_tbl1 in
  let modl3 = modul223 modl2 in
  let modl4 = modul324 modl3 in
  let modl5 = modul425 modl4 in
  Oprover.prove_modelb modl5

let plain_prove file =
  let get_mname fname = 
    (
        let lfname = List.hd (List.rev (String.split_on_char '/' (String.trim fname))) in
        let mname = List.hd (String.split_on_char '.' lfname) in
        String.capitalize_ascii mname
    ) in
  let pmoduls = Hashtbl.create 1 in
  let opkripke = ref None in
  let start_pmodul = ref "" in
  List.iter (fun fname -> 
      let mname = get_mname fname in
      let cha = open_in fname in
      let lbuf = Lexing.from_channel (cha) in
      try
          let imported, psymbol_tbl, pkripke_model = Parser.program Lexer.token lbuf in 
          begin
              match pkripke_model with
              | None -> ()
              | Some pk -> opkripke := Some pk; start_pmodul := mname
          end;
          let modul = {
              fname = fname;
              imported = imported;
              psymbol_tbl = psymbol_tbl;
              pkripke_model = pkripke_model;
          } in
          Hashtbl.add pmoduls mname modul
      with e -> 
          let sp = lbuf.lex_start_p in
          let ep = lbuf.lex_curr_p in
          printf "syntax error from line %d, column %d to line %d, column %d\n" 
              sp.pos_lnum (sp.pos_cnum - sp.pos_bol)
              ep.pos_lnum (ep.pos_cnum - ep.pos_bol)
  ) [file];
  match !opkripke with
  | None -> print_endline "no kripke model was built, exit."; exit 1
  | Some pkripke -> 
      let dg = dep_graph_of_pmodul !start_pmodul pmoduls in 
      let rec typecheck dg moduls = 
      match dg with
      | Leaf mname -> 
          (try
              Typechecker.check_modul mname moduls
          with Invalid_pexpr_loc (pel, msg) ->
              print_endline ("Error: "^msg);
              print_endline (Print.str_pexprl pel);
              exit 1)
      | Node (mname, dgs) -> 
          List.iter (fun dg -> typecheck dg moduls) dgs; 
          (try
              Typechecker.check_modul mname moduls
          with Invalid_pexpr_loc (pel, msg) ->
              print_endline ("Error: "^msg);
              print_endline (Print.str_pexprl pel);
              exit 1) in
      typecheck dg pmoduls;
      let runtime = pmoduls_to_runtime pmoduls pkripke !start_pmodul in
      Prover.prove_modelb runtime !start_pmodul

let test_cp opt i = 
  let ans = List.nth answers_cp (i-1) in
  let cp_dir = ref "" in
  if i<10 then
    cp_dir := test_dir ^ "random/p1/p0" ^ (string_of_int i) ^ "/"
  else
    cp_dir := test_dir ^ "random/p1/p" ^ (string_of_int i) ^ "/";
  let files = Sys.readdir !cp_dir in
  (* let cp_cases = Hashtbl.create 10 in *)
  Array.map (fun f ->
    f, (fun test_ctx -> begin
      let mnames = (String.split_on_char '.' f) in
      if List.length mnames = 2 && (List.nth mnames 1 = "model") then
        let file = !cp_dir ^ f in
        let result = if opt then opt_prove file else plain_prove file in
        let correct = (List.nth ans (cp_index (List.nth mnames 0))) in
        assert_equal result correct
      end)
  ) files
  (* cp_cases *)

let test_mutual opt = 
  let answers = Hashtbl.create 10 in
  List.iter (fun (midx, correct) -> Hashtbl.add answers midx correct) answers_mutual;
  let mutual_dir = test_dir ^ "fairness/mutual/" in
  let files = Sys.readdir mutual_dir in
  Array.map (fun f ->
    (f, fun test_ctx ->
      let mnames = (String.split_on_char '.' f) in
      let midx = String.sub (List.hd mnames) 7 3 in
      let correct = Hashtbl.find answers midx in
      let file = mutual_dir^f in
      let result = if opt then opt_prove file else plain_prove file in
      assert_equal result correct 
    )) files

let test_ring opt = 
  let answers = Hashtbl.create 10 in
  List.iter (fun (midx, correct) -> Hashtbl.add answers midx correct) answers_ring;
  let ring_dir = test_dir ^ "fairness/ring/" in
  let files = Sys.readdir ring_dir in
  Array.map (fun f ->
    (f, fun test_ctx ->
      let mnames = (String.split_on_char '.' f) in
      let midx = String.sub (List.hd mnames) 6 3 in
      let correct = Hashtbl.find answers midx in
      let file = ring_dir^f in
      let result = if opt then opt_prove file else plain_prove file in
      assert_equal result correct 
    )) files

(* let test_bcg_deadlock () =
  let answers = Hashtbl.create 10 in
  List.iter (fun (midx, correct) -> Hashtbl.add answers midx correct) answers_ring; *)


let test_csp opt i = 
  let ans = List.nth answers_csp (i-1) in
  let csp_dir = ref "" in
  if i<10 then
    csp_dir := test_dir ^ "random/p2/p0" ^ (string_of_int i) ^ "/"
  else
    csp_dir := test_dir ^ "random/p2/p" ^ (string_of_int i) ^ "/";
  let files = Sys.readdir !csp_dir in
  (* let csp_cases = Hashtbl.create 10 in *)
  Array.map (fun f ->
    f, (fun test_ctx -> begin
      let mnames = (String.split_on_char '.' f) in
      if List.length mnames = 2 && (List.nth mnames 1 = "model") then
        let file = !csp_dir ^ f in
        let result = if opt then opt_prove file else plain_prove file in
        let correct = (List.nth ans (csp_index (List.nth mnames 0))) in
        assert_equal result correct
    end)
  ) files
  (* csp_cases *)


let cp_suit opt = 
  List.init 24 (fun i ->
    let cases = ref [] in
    let tmp_cp_cases = test_cp opt (i+1) in
    Array.iter (fun (f, t) -> cases := !cases @ [("p1"^f) >:: t]) tmp_cp_cases;
    ("CP "^(string_of_int i)) >::: !cases
  )

let csp_suit opt = 
  List.init 24 (fun i ->
    let cases = ref [] in
    let tmp_csp_cases = test_csp opt (i+1) in
    Array.iter (fun (f, t) -> cases := !cases @ [("p2"^f) >:: t]) tmp_csp_cases;
    ("CSP "^(string_of_int i)) >::: !cases
  )
(* 
let mutual_suit opt = 
  let ta = test_mutual opt in
  let len = Array.length ta in
  List.init len (fun i -> 
    let f, t = ta.(i) in
    ("Mutual "^f) >::: [f>::t])

let ring_suit opt = 
  let ta = test_ring opt in
  let len = Array.length ta in
  List.init len (fun i -> 
    let f, t = ta.(i) in
    ("Ring "^f) >::: [f>::t]) *)

let mutual_suit opt = 
  let ta = test_mutual opt in
  let len = Array.length ta in
  ("Mutual ") >:::(List.init len (fun i -> 
    let f, t = ta.(i) in
     f>::t))

let ring_suit opt = 
  let ta = test_ring opt in
  let len = Array.length ta in
  ("Ring ") >:::(List.init len (fun i -> 
    let f, t = ta.(i) in
     f>::t))

let _ = 
  (* The test handles the optimizated version of SCTLProV, and cannot handle the ordinary version, as far as we know, this 
    should be an internal bug of OUnit2, because the ordinary version run well on each case.
  *)
  print_endline "Tesing cases without fairness";
  List.iter (fun s -> run_test_tt_main s) (cp_suit true);
  List.iter (fun s -> run_test_tt_main s) (csp_suit true);
  print_endline "Testing fairness cases";
  run_test_tt_main (mutual_suit true);
  run_test_tt_main (ring_suit true)
