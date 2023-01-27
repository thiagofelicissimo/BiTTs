open Format



type stat =
  | Defined
  | Constant

type head =
  | Symb of string
  | Ix of int

type term =
  {head : head;
   spine : spine}

and spine = arg list

and arg =
  {body : term;
   binds : int}

type rew_rule =
  {lhs_spine : spine;
   rhs : term
  }

module RewTbl = Map.Make(String)
type rew_map = (rew_rule list) RewTbl.t

type ty =
  | Star
  | Ty of term

type mode = Pos | Neg | Ersd

type rule =
  {ctx : ctx;
   ty : ty}
and ctx = (rule * mode) list

type sign = string -> ty


let pp_head fmt hd =
  match hd with
  | Symb(str) -> fprintf fmt "%s" str
  | Ix(n) -> fprintf fmt "i%s" (string_of_int n)

let rec pp_term fmt t =
  if t.spine = []
  then pp_head fmt t.head
  else fprintf fmt "%a(%a)" pp_head t.head pp_spine t.spine

and pp_spine fmt sp =
  match sp with
  | [] -> fprintf fmt ""
  | [{binds = n; body = t}] ->
    if n = 0
    then fprintf fmt "%a" pp_term t
    else fprintf fmt "%s.%a" (string_of_int n) pp_term t
  | {binds = n; body = t} :: sp ->
    if n = 0
    then fprintf fmt "%a, %a" pp_spine sp pp_term t
    else fprintf fmt "%a, %s.%a" pp_spine sp (string_of_int n) pp_term t
