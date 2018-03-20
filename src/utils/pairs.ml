exception Key_not_found

let rec keys pairs =
    match pairs with
    | [] -> []
    | (k,_)::pairs' -> k :: (keys pairs')

let rec key_exists pairs key = 
    match pairs with
    | [] -> false
    | (k,_)::pairs' -> if k = key then true else key_exists pairs' key

let rec get_value pairs key = 
    match pairs with
    | [] -> raise Key_not_found
    | (k,v)::pairs' -> if k = key then v else get_value pairs' key

let rec find pairs key = 
    match pairs with
    | [] -> None
    | (k,v) :: pairs' -> if k=key then Some v else find pairs' key

let rec find_all pairs key = 
    match pairs with
    | [] -> []
    | (k,v) :: pairs' -> if k=key then v::(find_all pairs' key) else find_all pairs' key

let rec remove_first pairs key =
    match pairs with
    | [] -> []
    | (k,v)::pairs' -> if k=key then pairs' else (k,v)::(remove_first pairs' key)

let rec remove_all pairs key = 
    match pairs with
    | [] -> []
    | (k,v) :: pairs' -> if k=key then remove_all pairs' key else (k,v)::(remove_all pairs' key)

let rec replace_first pairs key value = 
    match pairs with
    | [] -> [] 
    | (k,v)::pairs' -> if k=key then (k,value)::pairs' else (k,v)::(replace_first pairs' key value)

let rec replace_all pairs key value = 
    match pairs with
    | [] -> []
    | (k,v)::pairs' -> if k=key then (k,value)::(replace_all pairs' key value) else (k,v)::(replace_all pairs' key value)