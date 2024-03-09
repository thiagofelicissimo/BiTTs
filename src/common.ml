
let colored n s =
  "\027[3" ^ string_of_int n ^ "m" ^ s ^ "\027[m"

let yellow = colored 3
let command = colored 6
let green = colored 2
let red = colored 1

let darkblue = colored 4

let syntax_error () = Format.printf "%s: " (red "Syntax error")

let split_at (n : int) (l : 'a list) : 'a list * 'a list =
  let rec aux n l acc =
    if n = 0 then (List.rev acc, l)
    else match l with
      | x :: l -> aux (n - 1) l (x :: acc)
      | [] -> assert false (* pre-condition |l| >= n not satisfied *)
  in aux n l []
