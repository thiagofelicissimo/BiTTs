open Format

(* syntax of terms, using de bruijn indices *)

type tm =
  | Var of int (* index *)
  | Meta of int * subst
  | Const of string * msubst
  | Dest of string * tm * msubst
  | Def of string (* top-level def *)
  | Ascr of tm * tm (* t :: ty *)

and subst = tm list

(* we also store the number of variables bound in the argument *)
and msubst = (int * tm) list

type ctx = tm list

type mctx = (ctx * tm) list

(* patterns *)
type p_tm =
  | Meta
  | Const of string * p_msubst
and p_msubst = (int * p_tm) list

(* schematic rules *)
type schem_rule =
  | Sort of mctx
  | Const of int * mctx * msubst * p_tm
            (* num_ixs, args_mctx, inst_msubst, p_sort *)
  | Dest of p_tm * mctx * tm
            (* p_sort, args_mctx, sort *)

(* schematic rules table *)

module RuleTbl = Map.Make(String)
type schem_rules = schem_rule RuleTbl.t
let schem_rules : schem_rules ref = ref RuleTbl.empty

type rew_rule = p_msubst * tm


(* rewrite rules table *)

module RewTbl = Map.Make(String)
type rew_rules = (rew_rule list) RewTbl.t
let rew_rules : rew_rules ref = ref RewTbl.empty

(* pretty printing functions *)

let separator fmt () =
  fprintf fmt ", "


let rec pp_term fmt t =
  match t with
  | Var(n) -> fprintf fmt "%d" n
  | Meta(n, subst) -> fprintf fmt "%d{%a}" n pp_subst subst
  | Dest(name, t, []) -> fprintf fmt "%s(%a)" name pp_term t
  | Dest(name, t, msubst) -> fprintf fmt "%s(%a; %a)" name pp_term t pp_msubst msubst
  | Const(name, []) -> fprintf fmt "%s" name
  | Const(name, msubst) -> fprintf fmt "%s(%a)" name pp_msubst msubst
  | Def(name) -> fprintf fmt "%s" name
  | Ascr(t, ty) -> fprintf fmt "[%a] %a" pp_term ty pp_term t

and pp_subst fmt subst =
  pp_print_list ~pp_sep:separator pp_term fmt (List.rev subst)

and pp_msubst fmt msubst =
let pp_arg fmt (n, t) =
  if n = 0 then pp_term fmt t
  else fprintf fmt "%d. %a" n pp_term t in
pp_print_list ~pp_sep:separator pp_arg fmt (List.rev msubst)

let pp_ctx fmt ctx =
let pp_ctx_entry fmt ty = fprintf fmt "%a" pp_term ty in
pp_print_list ~pp_sep:separator pp_ctx_entry fmt (List.rev ctx)

let pp_mctx fmt mctx =
let pp_mctx_entry fmt (ctx, ty) =
  if ctx = [] then fprintf fmt "%a" pp_term ty
  else fprintf fmt "{%a} : %a" pp_ctx ctx pp_term ty in
pp_print_list ~pp_sep:separator pp_mctx_entry fmt (List.rev mctx)

let rec pp_p_term fmt t =
  match t with
  | Meta -> fprintf fmt "?"
  | Const(name, []) -> fprintf fmt "%s" name
  | Const(name, msubst) -> fprintf fmt "%s(%a)" name pp_p_msubst msubst

and pp_p_msubst fmt msubst =
  let pp_arg fmt (n, t) =
    if n = 0 then pp_p_term fmt t
    else fprintf fmt "%d. %a" n pp_p_term t in
  pp_print_list ~pp_sep:separator pp_arg fmt (List.rev msubst)
