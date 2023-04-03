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
  {
    ty_cst : string;
    ty_spine : spine
  }

type ctx = ty list (* only types of order 0 *)

type mode = Pos | Neg | Ersd

type prem =
  {
    ctx : ctx;
    mode : mode;
    boundary : ty
  }

type tm_symb = {
  prems : prem list;
  mode : mode;
  ty : ty
}

type ty_symb = {
  prems : prem list
}

type symb =
  | Tm_symb of tm_symb
  | Ty_symb of ty_symb

module SignTbl = Map.Make(String)
type sign = symb SignTbl.t
let sign : sign ref = ref SignTbl.empty

(* PRETTY PRINTING WITH NAMES *)

let ppn_head depth fmt hd =
  match hd with
  | Symb(str) -> fprintf fmt "%s" str
  | Ix(n) -> fprintf fmt "x%s" (string_of_int (depth - n - 1))

let rec ppn_binders depth fmt size =
  if size = 0 then assert false
  else if size = 1 then fprintf fmt "x%s" (string_of_int depth)
  else fprintf fmt "%a x_%s" (ppn_binders (depth + 1)) (size - 1) (string_of_int depth)

let rec ppn_term depth fmt t =
  if t.spine = []
  then ppn_head depth fmt t.head
  else fprintf fmt "%a(%a)" (ppn_head depth) t.head (ppn_spine depth) t.spine

(* we print from right to left because spines are snoc lists *)
and ppn_spine depth fmt sp =
  match sp with
  | [] -> fprintf fmt ""
  | [{binds = n; body = t}] ->
    if n = 0
    then fprintf fmt "%a" (ppn_term depth) t
    else fprintf fmt "%a. %a" (ppn_binders depth) n (ppn_term (depth + n)) t
  | {binds = n; body = t} :: sp ->
    if n = 0
    then fprintf fmt "%a, %a" (ppn_spine depth) sp (ppn_term depth) t
    else fprintf fmt "%a, %a. %a" (ppn_spine depth) sp (ppn_binders depth) n (ppn_term (depth + n)) t

let ppn_ty depth fmt ty =
  if ty.ty_spine = []
  then fprintf fmt "%s" ty.ty_cst
  else fprintf fmt "%s(%a)" ty.ty_cst (ppn_spine depth) ty.ty_spine


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
  if ty.ty_spine = []
  then fprintf fmt "%s" ty.ty_cst
  else fprintf fmt "%s(%a)" ty.ty_cst pp_spine ty.ty_spine

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
