module T = Term
open Format

(* syntax of values, using de bruijn levels and closures *)

type v_tm =
  | Var of int (* level *)
  | Meta of int (* level *) * v_subst
  | Sym of string * v_msubst

and v_subst = v_tm list

(* an argument is either fully evaluated or a closure *)
and v_arg =
  | Value of v_tm
  | Closure of int (* num of binders *) * T.tm * int (* meta offset *) * v_msubst * v_subst
and v_msubst = v_arg list

type v_ctx = v_tm list


(* pretty printing functions *)

let rec pp_vterm fmt t =
  match t with
  | Var(n) -> fprintf fmt "%d" n
  | Meta(n, subst) -> fprintf fmt "%d{%a}" n pp_vsubst subst
  | Sym(name, []) -> fprintf fmt "%s" name
  | Sym(name, msubst) -> fprintf fmt "%s(%a)" name pp_vmsubst msubst

and pp_vsubst fmt subst =
  pp_print_list ~pp_sep:T.separator pp_vterm fmt (List.rev subst)

and pp_vmsubst fmt msubst =
  let pp_arg fmt arg =
    match arg with
    | Value(t) -> pp_vterm fmt t
    | Closure(n', t, m, v_msubst, v_subst) ->
      fprintf fmt "<%d. %a | offset: %d | %a | %a>" n' T.pp_term t m pp_vmsubst v_msubst pp_vsubst v_subst in
  pp_print_list ~pp_sep:T.separator pp_arg fmt (List.rev msubst)
