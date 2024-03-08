module T = Term
open Format

(* syntax of values, using de bruijn levels and closures *)

type v_tm =
  | Var of int (* level *)
  | Meta of int (* index *) * v_subst
  | Const of string * v_msubst
  | Dest of string * v_msubst

and v_subst = v_tm list

(* an argument is either fully evaluated or a closure *)
and v_arg =
  | Value of v_tm
  | Closure of int * T.tm * v_msubst * v_subst
and v_msubst = v_arg list

type v_ctx = v_tm list


(* top-level definitions table *)

module DefTbl = Map.Make(String)

type def = {rhs : v_tm; ty : v_tm}
type defs = def DefTbl.t
let defs : defs ref = ref DefTbl.empty


(* pretty printing functions *)

let rec pp_vterm fmt t =
  match t with
  | Var(n) -> fprintf fmt "%d" n
  | Meta(n, subst) -> fprintf fmt "%d{%a}" n pp_vsubst subst
  | Dest(name, []) -> fprintf fmt "%s()" name
  | Dest(name, msubst) -> fprintf fmt "%s(%a)" name pp_vmsubst msubst
  | Const(name, []) -> fprintf fmt "%s" name
  | Const(name, msubst) -> fprintf fmt "%s(%a)" name pp_vmsubst msubst

and pp_vsubst fmt subst =
  pp_print_list ~pp_sep:T.separator pp_vterm fmt (List.rev subst)

and pp_vmsubst fmt msubst =
  let pp_arg fmt arg =
    match arg with
    | Value(t) -> pp_vterm fmt t
    | Closure(n', t, v_msubst, v_subst) ->
      fprintf fmt "<%d. %a | %a | %a>" n' T.pp_term t pp_vmsubst v_msubst pp_vsubst v_subst in
  pp_print_list ~pp_sep:T.separator pp_arg fmt (List.rev msubst)
