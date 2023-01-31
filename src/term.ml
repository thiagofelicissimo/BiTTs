open Format

type head =
  | Symb of string
  | Ix of int

type term =
  {
    head : head;
    spine : spine
  }

and spine = arg list

and arg =
  {
    body : term;
    binds : int
  }

type rew_rule =
  {
    lhs_spine : spine;
    rhs : term
  }

module RewTbl = Map.Make(String)
type rew_map = (rew_rule list) RewTbl.t
let rew_map : rew_map ref = ref RewTbl.empty

type ty =
  | Star
  | Term of term

type ctx = ty list

type mode = Pos | Neg | Ersd

type prem =
  {
    ctx : ctx;
    mode : mode;
    boundary : ty
  }

type rule =
  {
    prems : prem list;
    mode : mode;
    ty : ty
  }

module SignTbl = Map.Make(String)
type sign = rule SignTbl.t
let sign : sign ref = ref SignTbl.empty

(* PRETTY PRINTING *)

let pp_head fmt hd =
  match hd with
  | Symb(str) -> fprintf fmt "%s" str
  | Ix(n) -> fprintf fmt "i%s" (string_of_int n)

let rec pp_term fmt t =
  if t.spine = []
  then pp_head fmt t.head
  else fprintf fmt "%a(%a)" pp_head t.head pp_spine t.spine

(* we print from right to left because spines are snoc lists *)
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

let pp_ty fmt ty =
  match ty with
  | Star -> fprintf fmt "*"
  | Term(tm) -> pp_term fmt tm

let rec pp_ctx fmt ctx =
  match ctx with
  | [] -> fprintf fmt ""
  | [ty] -> pp_ty fmt ty
  | ty :: ctx -> fprintf fmt "%a, %a" pp_ctx ctx pp_ty ty


let pp_prem fmt (prem : prem) =
  match prem.mode with
  | Ersd -> fprintf fmt "{(%a) -> %a}" pp_ctx prem.ctx pp_ty prem.boundary
  | Pos -> fprintf fmt "((%a) -> %a)+" pp_ctx prem.ctx pp_ty prem.boundary
  | Neg -> fprintf fmt "((%a) -> %a)-" pp_ctx prem.ctx pp_ty prem.boundary

let rec pp_prems fmt prems =
  match prems with
  | [] -> fprintf fmt ""
  | prem :: prems -> fprintf fmt "%a %a" pp_prems prems pp_prem prem
