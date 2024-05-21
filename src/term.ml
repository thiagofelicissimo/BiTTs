open Format

(* syntax of terms, using de bruijn indices *)

type tm =
  | Var of int (* index *)
  | Meta of int * subst
  | Sym of string * msubst
  | Def of string * msubst (* top-level def *)
  | Let of tm * tm
  | Ascr of tm * tm (* t :: ty *)

and subst = tm list

(* we also store the number of variables bound in the argument *)
and msubst = (int * tm) list

type ctx = tm list

type mctx = (ctx * tm) list

(* patterns *)
type p_tm =
  | Meta
  | Sym of string * p_msubst
and p_msubst = (int * p_tm) list

(* schematic rules *)
type schem_rule =
  | Sort of mctx
  | Const of mctx * subst * subst * p_tm
            (* mctx2, subst1, subst2, p_sort *)
  | Dest of p_tm * mctx * tm
            (* p_sort, mctx2, sort *)

(* schematic rules table *)

module RuleTbl = Map.Make(String)
type schem_rules = schem_rule RuleTbl.t
let schem_rules : schem_rules ref = ref RuleTbl.empty


type rew_rule = (* rewcount *) int * p_msubst * tm


(* rewrite rules table *)

module RewTbl = Map.Make(String)
type rew_rules = (rew_rule list) RewTbl.t
let rew_rules : rew_rules ref = ref RewTbl.empty


(* top-level definitions table *)

module DefTbl = Map.Make(String)

type def = {mctx : mctx; ty : tm; tm : tm}
type defs = def DefTbl.t
let defs : defs ref = ref DefTbl.empty


(* --- functions for patterns --- *)

(* checks if two patterns unify, raises Do_not_unify if no *)

exception Do_not_unify

let rec check_unify_tm t t' =
  match t, t' with
  | Meta, _ -> ()
  | _, Meta -> ()
  | Sym(name, msubst), Sym(name', msubst') ->
    if name <> name' then raise Do_not_unify;
    check_unify_msubst msubst msubst'

and check_unify_msubst msubst msubst' =
  if List.length msubst <> List.length msubst' then raise Do_not_unify;
  List.iter2 (fun (n,t) (n',t') ->
    if n <> n' then raise Do_not_unify;
    check_unify_tm t t') msubst msubst'

(* check if pattern t overlaps with t', raises Overlap it yes *)

exception Overlap
let rec check_overlap t t' =
  match t with
  | Meta -> ()
  | Sym(_, msubst) -> begin
    try check_unify_tm t t'; raise Overlap with Do_not_unify -> ();
    List.iter (fun (_, t) -> check_overlap t t') msubst end

(* check if pattern e is rigid, raises Not_rigid it not *)

exception Not_rigid of int
let check_rigid t =
  let checkr name rews =
    List.iter
      (fun (rew_id, p_msubst, rhs) ->
        try check_overlap t (Sym(name, p_msubst))
        with Overlap -> raise (Not_rigid(rew_id)))
      rews in
  RewTbl.iter checkr !rew_rules


(* check if lhs t breaks the rigidity of some schematic rule pattern,
   raises Breaks_ridigity it yes *)

exception Breaks_ridigity of string
let check_not_break_rig t =
  let checkr name rule =
    match rule with
    | Const(_, _, _, t') | Dest(t', _, _) ->
      begin
        try check_overlap t' t
        with Overlap -> raise (Breaks_ridigity(name)) end
    | _ -> () in
  RuleTbl.iter checkr !schem_rules


(* check it lhs t creates some critical pair with the rewrite rules,
   raises Critical_pair if yes *)

exception Critical_pair of int
let check_critical_pair t =
  let checkcr name rews =
    List.iter
      (fun (rew_id, p_msubst, rhs) ->
        try
          check_overlap t (Sym(name, p_msubst));
          check_overlap (Sym(name, p_msubst)) t
        with Overlap -> raise (Critical_pair(rew_id)))
      rews in
  RewTbl.iter checkcr !rew_rules

(* checks if pattern is destructor-free, raises Not_dest_free if not *)

exception Not_dest_free
let rec check_dest_free t =
  match t with
  | Meta -> ()
  | Sym(name, msubst) ->
    begin match RuleTbl.find name !schem_rules with
    | Dest(_) -> raise Not_dest_free
    | _ -> List.iter (fun (_, t) -> check_dest_free t) msubst end


(* --- pretty printing functions --- *)

let separator fmt () =
  fprintf fmt ", "


let rec pp_term fmt t =
  match t with
  | Var(n) -> fprintf fmt "%d" n
  | Meta(n, subst) -> fprintf fmt "%d{%a}" n pp_subst subst
  | Sym(name, []) -> fprintf fmt "%s" name
  | Sym(name, msubst) -> fprintf fmt "%s(%a)" name pp_msubst msubst
  | Def(name, []) -> fprintf fmt "%s" name
  | Def(name, msubst) -> fprintf fmt "%s(%a)" name pp_msubst msubst
  | Ascr(t, ty) -> fprintf fmt "[%a] %a" pp_term ty pp_term t
  | Let(t, u) -> fprintf fmt "let %a in %a" pp_term t pp_term u

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
  fprintf fmt "{%a} : %a" pp_ctx ctx pp_term ty in
pp_print_list ~pp_sep:separator pp_mctx_entry fmt (List.rev mctx)

let rec pp_p_term fmt t =
  match t with
  | Meta -> fprintf fmt "?"
  | Sym(name, []) -> fprintf fmt "%s" name
  | Sym(name, msubst) -> fprintf fmt "%s(%a)" name pp_p_msubst msubst

and pp_p_msubst fmt msubst =
  let pp_arg fmt (n, t) =
    if n = 0 then pp_p_term fmt t
    else fprintf fmt "%d. %a" n pp_p_term t in
  pp_print_list ~pp_sep:separator pp_arg fmt (List.rev msubst)
