exception Zip_error of int * int

let rec zip_to_pairs list1 list2 = 
    match list1, list2 with
    | [], [] -> []
    | h1::tl1, h2::tl2 -> (h1,h2)::(zip_to_pairs tl1 tl2)
    | _ -> raise (Zip_error (List.length list1, List.length list2))

let rec zip_to_refpairs list1 list2 = 
    match list1, list2 with
    | [], [] -> []
    | h1::tl1, h2::tl2 -> (h1,ref h2)::(zip_to_refpairs tl1 tl2)
    | _ -> raise (Zip_error (List.length list1, List.length list2))
