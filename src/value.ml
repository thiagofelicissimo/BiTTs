module T = Term
open Format

type vhead =
  | Symb of string
  | Lvl of int

type value =
  {
    head : vhead;
    env : env
  }

and env = enve list

and enve =
  | Val of value
  | Clo of closure

and closure =
  {
    binds : int;
    body : T.term;
    env : env
  }

type vty =
  {
    vty_cst : string;
    vty_env : env
  }

type vctx = (value * vty) list

(* PRETTY PRINTING *)

let pp_vhead fmt hd =
  match hd with
  | Symb(str) -> fprintf fmt "%s" str
  | Lvl(n) -> fprintf fmt "l%s" (string_of_int n)

let rec pp_value fmt t =
  if t.env = []
  then pp_vhead fmt t.head
  else fprintf fmt "%a(%a)" pp_vhead t.head pp_env t.env

(* we print from right to left because env are snoc lists *)
and pp_env fmt env =
  match env with
  | [] -> fprintf fmt ""
  | [Val(v)] -> fprintf fmt "%a" pp_value v
  | Val(v) :: env -> fprintf fmt "%a, %a" pp_env env pp_value v
  | [Clo({binds = n; body = t; env = env'})] ->
    fprintf fmt "<%a|%s.%a>" pp_env env' (string_of_int n) T.pp_term t
  | Clo({binds = n; body = t; env = env'}) :: env ->
    fprintf fmt "%a, <%a|%s.%a>" pp_env env pp_env env' (string_of_int n) T.pp_term t

let pp_vty fmt vty =
  if vty.vty_env = []
  then fprintf fmt "%s" vty.vty_cst
  else fprintf fmt "%s(%a)" vty.vty_cst pp_env vty.vty_env

let rec pp_vctx fmt vctx =
  match vctx with
  | [] -> fprintf fmt ""
  | [(_, vty)] -> pp_vty fmt vty
  | (_, vty) :: vctx -> fprintf fmt "%a, %a" pp_vctx vctx pp_vty vty
