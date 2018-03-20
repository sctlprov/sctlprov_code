#load "unix.cma";;

open Printf
open Unix


(*
/usr/bin/time -v -a -o ~/results/sctl_orig_output_2_0112 timeout 10m ~/sctl_with_modules8_array_symbolic_partial/sctl.opt ~/cpcsp/p2/p"$p"/sctl/"$filename"
*)
let run () = 
  (* let result_out = open_out "result.txt" in *)
  (* ignore(Sys.command "bash"); *)
  let mode = ref "timememory" in
  let current_dir = Sys.getcwd () in
  let tm = localtime (time ()) in
  let result_file = (Sys.getcwd ())^"/result_"^
                    (string_of_int (tm.tm_year+1900))^"-"^
                    (string_of_int tm.tm_mon)^"-"^
                    (string_of_int tm.tm_mday)^"-"^
                    (string_of_int tm.tm_hour)^"-"^
                    (string_of_int tm.tm_min)^"-"^
                    (string_of_int tm.tm_sec) in
  (* print_endline result_file; *)
  let exec = ref "" in
  let timeout = ref "" in
  let dir = ref "" in
  let extra = ref "" in
  let surfix = ref "" in
  let command = ref " timeout " in
  let extra_last = ref false in
  (* if !mode = "time" then
    command := "time -a -o "^result_file^" timeout "
  else 
    command := ("/usr/bin/time -v -a -o "^result_file^" timeout "); *)
  Arg.parse
    [
      "-exec", Arg.String (fun s -> exec := s), "\tThe executable and argument(s)";
      "-timeout", Arg.String (fun s -> timeout := s), "\tSet timeout";
      "-dir", Arg.String (fun s -> dir := s), "\tTarget directory of the test cases";
      "-surfix", Arg.String (fun s -> surfix := s), "\tSurfix of the test cases";
      "-extra", Arg.String (fun s -> extra := s), "\tExtra argument(s)";
      "-extra-last", Arg.Unit (fun () -> extra_last := true), "\tPut extra argument(s) at last"
    ]
    (fun s -> printf "Unknown argument: %s\n" s; exit 1)
    "Usage: ocaml run.ml -exec <command> -timeout <timeout> -dir <targetdir> -surfix <surfix> -extra <filename> [-extra-last]";
  let extra_arguments = 
    try
      input_line (open_in !extra)
    with _ -> "" in 
  let files = Sys.readdir !dir in
  (* if !mode = "time" then
    ignore (Sys.command ("script -a "^result_file)); *)
  Array.sort (Pervasives.compare) files;
  Array.iter ( fun file ->
      if (List.nth (String.split_on_char '.' file) 1) = !surfix then begin
        let exec_path_items = String.split_on_char '/' !exec in
        let exec_dir = ref "/" in
        for i = 0 to List.length exec_path_items - 2 do
          let tmp_item = List.nth exec_path_items i in
          if  tmp_item <> "" then
            exec_dir := !exec_dir ^ tmp_item ^ "/"
        done;
        Sys.chdir !exec_dir;
        let exec_name = "./"^ (List.nth exec_path_items (List.length exec_path_items - 1)) in
        let dir_items = String.split_on_char '/' !dir in
        let new_dir = ref "/" in
        List.iter (fun item -> if item <> "" then new_dir := !new_dir ^ item ^ "/") dir_items;
        let new_command = ref "" in
        if !mode = "time" then begin
          new_command := "time "^ !command ^ !timeout ^ " " ^ exec_name ^ " " ^ extra_arguments ^ " " ^ !new_dir ^ file
        end else begin 
          if !extra_last then
            new_command := "/usr/bin/time -v -a -o "^result_file ^" "^ !command ^ !timeout ^ " " ^ exec_name ^ " " ^ !new_dir ^ file ^ " " ^ extra_arguments
          else
            new_command := "/usr/bin/time -v -a -o "^result_file ^" "^ !command ^ !timeout ^ " " ^ exec_name ^ " " ^ extra_arguments ^ " " ^ !new_dir ^ file
        end;
        (* print_endline ("command: "^ !new_command); *)
        ignore(Sys.command !new_command);
        Sys.chdir current_dir
      end
    ) files