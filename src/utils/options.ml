exception No_value

let bind f op =
  match op with
  | None -> None
  | Some a -> Some (f a) 

let rec pipe fs op = 
  match fs with
  | [] -> op
  | f::fs' -> pipe fs' (bind f op)

let choose_action op action1 action2 = 
  match op with
  | None -> action1 ()
  | Some a -> action2 a

let value op = 
  match op with
  | None -> raise No_value
  | Some v -> v