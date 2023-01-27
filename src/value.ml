module T = Term
open Format


type vhead =
  | Symb of string
  | Var of string

type value =
  {head : vhead;
   spine : env}

and env = enventry list

and enventry =
  | Value of value
  | Clo of closure

and closure =
  {binds : int;
   body : T.term;
   env : env
  }


let rec pp_head fmt hd =
  match hd with
  | Symb(str) -> fprintf fmt "%s" str
  | Var(str) -> fprintf fmt "%s" str

and pp_value fmt t =
  if t.spine = []
  then pp_head fmt t.head
  else fprintf fmt "%a(%a)" pp_head t.head pp_spine t.spine

and pp_spine fmt sp =
  match sp with
  | [] -> fprintf fmt ""
  | [Value(v)] -> fprintf fmt "%a" pp_value v
  | Value(v) :: sp -> fprintf fmt "%a, %a" pp_spine sp pp_value v
  | [Clo({binds = n; body = t; env = e})] ->
    fprintf fmt "<%a|%s.%a>" pp_spine e (string_of_int n) T.pp_term t
  | Clo({binds = n; body = t; env = e}) :: sp ->
    fprintf fmt "%a, <%a|%s.%a>" pp_spine sp pp_spine e (string_of_int n) T.pp_term t





(*
type aty =
  | Star
  | Aty of term

type mode = Pos | Neg | Ersd

type ty =
  {ctx : ctx;
   codom : ty}
and ctx = (ty * mode) list

type signature = string -> ty
*)
