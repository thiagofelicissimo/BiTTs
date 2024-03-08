

let split_at (n : int) (l : 'a list) : 'a list * 'a list =
  let rec aux n l acc =
    if n = 0 then (List.rev acc, l)
    else match l with
      | x :: l -> aux (n - 1) l (x :: acc)
      | [] -> assert false (* pre-condition |l| >= n not satisfied *)
  in aux n l []
