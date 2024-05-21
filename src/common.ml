
exception TODO

let colored n s =
  "\027[3" ^ string_of_int n ^ "m" ^ s ^ "\027[m"

let yellow = colored 3
let command = colored 6
let green = colored 2
let red = colored 1

let darkblue = colored 4

let syntax_error () = Format.printf "%s: " (red "Syntax error")