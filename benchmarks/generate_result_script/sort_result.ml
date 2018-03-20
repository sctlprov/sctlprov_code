let _ =
  let filename = Sys.argv.(1) in
  let fin = open_in filename in
  let index = [
    "vasy_0_1";
    "cwi_1_2";
    "vasy_1_4";
    "cwi_3_14";
    "vasy_5_9"; 
    "vasy_8_24"; 
    "vasy_8_38"; 
    "vasy_10_56"; 
    "vasy_18_73";
    "vasy_25_25"; 
    "vasy_40_60";
    "vasy_52_318";
    "vasy_65_2621";
    "vasy_66_1302";
    "vasy_69_520";
    "vasy_83_325"; 
    "vasy_116_368"; 
    "cwi_142_925"; 
    "vasy_157_297"; 
    "vasy_164_1619"; 
    "vasy_166_651"; 
    "cwi_214_684";
    "cwi_371_641";
    "vasy_386_1171"; 
    "cwi_566_3984";
    "vasy_574_13561"; 
    "vasy_720_390";
    "vasy_1112_5290"; 
    "cwi_2165_8723";
    "cwi_2416_17605"; 
    "vasy_2581_11442"; 
    "vasy_4220_13944";
    "vasy_4338_15666";
    "vasy_6020_19353";
    "vasy_6120_11031";
    "cwi_7838_59101";
    "vasy_8082_42933"; 
    "vasy_11026_24660"; 
    "vasy_12323_27667";
    "cwi_33949_165318"
  ] in
  let sorted = ref [] in 
  let str_tbl = Hashtbl.create 1 in
  begin try
    while true do
      let line = input_line fin in
      let strs = String.split_on_char '.' line in
      Hashtbl.add str_tbl (List.hd strs) line
    done
  with _ -> ()
  end;
  let fout = open_out (filename^"_sorted") in
  for i = 0 to List.length index - 1 do
    output_string fout ((Hashtbl.find str_tbl ((List.nth index i)))^"\n")
  done
