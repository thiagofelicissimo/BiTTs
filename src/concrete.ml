open Format
module T = Term
module V = Value
module Ty = Typing

(* concrete syntax *)
type tm =
  | NotApplied of string (* either a variable or a meta/const with no args *)
  | Meta of string * subst (* invariant: subst <> [] *)
  | Symb of string * msubst
  | Let of string * tm * tm
  | Ascr of tm * tm

and subst = tm list
and msubst = (string list * tm) list

type ctx = (string * tm) list

type mctx = (string * ctx * tm) list

type imctx = (string * tm * tm) list

type entry =
  | Let of string * mctx * tm * tm
  | Sort of string * mctx
  | Cons of string * mctx * mctx * subst   * subst   * ctx option * tm
    (*      c       (Xi_1) (Xi_2) (\vec{t} = \vec{u} : Delta)) :    T *)
  | Dest of string * mctx * string * tm * mctx  * tm
    (*      d       (Xi_1) [x :      T]  (Xi_2) : U *)
  | Rew of tm * tm
  | Eval of tm
  | Eq of tm * tm


(* calculates the corresponding indice of a variable name in the given scope *)
let get_db name scope =
  let rec get_db' scope name k =
    match scope with
    | [] -> None
    | x :: scope when x = name -> Some k
    | _ :: scope -> get_db' scope name (k + 1) in
  get_db' scope name 0

exception Name_not_in_scope of string
exception Dest_not_applied
exception Dest_binds_first_arg

(* scoping functions *)

let rec scope_tm (t : tm) (mscope : string list) (scope : string list) : T.tm =
  (* in the following, we consider that the variable scope shadows the
     metavariable scope, which shadows the signature *)
  match t with
  | Let(name, t, u) ->
    T.Let(scope_tm t mscope scope, scope_tm u mscope (name :: scope))
  | Ascr(t, ty) ->
    let t' = scope_tm t mscope scope in
    let ty' = scope_tm ty mscope scope in
    T.Ascr(t', ty')
  | NotApplied(name) ->
    begin match get_db name scope, get_db name mscope with
    | None, Some i -> T.Meta(i, [])
    | Some i, _ -> T.Var(i)
    | None, None ->
      begin match T.RuleTbl.find_opt name !T.schem_rules with
      | Some _ -> T.Sym(name, [])
      | None ->
        if (T.DefTbl.find_opt name !T.defs) <> None
        then T.Def(name, [])
        else raise (Name_not_in_scope name) end end
  | Meta(name, subst) ->
    begin match get_db name mscope with
    | None -> raise (Name_not_in_scope name)
    | Some i -> T.Meta(i, scope_subst subst mscope scope) end
  | Symb(name, msubst) ->
    begin match T.RuleTbl.find_opt name !T.schem_rules with
    | Some(_) -> T.Sym(name, scope_msubst msubst mscope scope)
    | None ->
      if (T.DefTbl.find_opt name !T.defs) <> None
        then T.Def(name, scope_msubst msubst mscope scope)
        else raise (Name_not_in_scope name)
  end

and scope_subst (subst : subst) (mscope : string list) (scope : string list) : T.subst =
  List.map (fun x -> scope_tm x mscope scope) subst

and scope_msubst (msubst : msubst) (mscope : string list) (scope : string list) : T.msubst =
  List.map (fun (names, x) -> List.length names, scope_tm x mscope (names @ scope)) msubst


let rec scope_ctx (ctx : ctx) (mscope : string list) : T.ctx * string list =
  match ctx with
  | [] -> [], []
  | (name, ty) :: ctx' ->
    let scoped_ctx', scope' = scope_ctx ctx' mscope in
    scope_tm ty mscope scope' :: scoped_ctx', name :: scope'

let rec scope_mctx (mctx : mctx) (mscope : string list) : T.mctx * string list =
  match mctx with
  | [] -> [], mscope
  | (name, ctx, ty) :: mctx' ->
    let scoped_mctx', mscope' = scope_mctx mctx' mscope in
    let scoped_ctx, scope = scope_ctx ctx mscope' in
    (scoped_ctx, scope_tm ty mscope' scope) :: scoped_mctx', name :: mscope'


exception Not_a_patt

let subst_to_scope (subst : subst) : string list =
  List.map (fun t -> match t with | NotApplied(name) -> name |_ -> raise Not_a_patt) subst

(* pattern scoping *)

let rec scope_p_tm (t : tm) : T.p_tm * string list =
  match t with
  | NotApplied(name) ->
    begin match T.RuleTbl.find_opt name !T.schem_rules with
    | Some _ -> T.Sym(name, []), []
    | None -> Meta, [name] end
  | Symb(name, msubst) ->
    let msubst_p, mscope = scope_p_msubst msubst in
    T.Sym(name, msubst_p), mscope
  | _ -> raise Not_a_patt

and scope_p_msubst (msubst : msubst) : T.p_msubst * string list =
  match msubst with
  | [] -> [], []
  | ([], t) :: msubst' ->
    let t_p, mscope1 = scope_p_tm t in
    let msubst'_p, mscope2 = scope_p_msubst msubst' in
    (0, t_p) :: msubst'_p, mscope1 @ mscope2
  | (names, Meta(name, subst)) :: msubst' when subst_to_scope subst = names ->
    let msubst'_p, mscope = scope_p_msubst msubst' in
    (List.length names, Meta) :: msubst'_p, name :: mscope
  | (names, _) :: _ ->
    (* matching inside binders not allowed, as this would require
       entering a closure, matching it, and then reading back the result.
       therefore, any binder must be immediately followed by a meta.
       example: lambda(x. X{x}) OK, lambda(x. succ(X{x})) not OK *)
    raise Not_a_patt


let mctx_of_imctx (imctx : imctx) : mctx =
  List.map (fun (id, tm, ty) -> (id, [], ty)) imctx

let msubst_of_imctx (imctx : imctx) : msubst =
  List.map (fun (id, tm, ty) -> ([], tm)) imctx


(* PRETTY PRINTING *)

let rec pp_scope fmt scope =
  match scope with
  | [s] -> fprintf fmt "%s" s
  | s :: scope' -> fprintf fmt "%a %s" pp_scope scope' s
  | [] -> ()


let rec pp_term fmt t =
  match t with
  | NotApplied(name) -> fprintf fmt "%s" name
  | Let(name, t, u) ->
    fprintf fmt "let %s := %a in %a" name pp_term t pp_term u
  | Meta(name, subst) -> fprintf fmt "%s{%a}" name pp_subst subst
  | Symb(name, msubst) -> fprintf fmt "%s(%a)" name pp_msubst msubst
  | Ascr(t, ty) -> fprintf fmt "[%a] %a" pp_term ty pp_term t

and pp_subst fmt subst =
  pp_print_list ~pp_sep:T.separator pp_term fmt (List.rev subst)

and pp_msubst fmt msubst =
  let pp_arg fmt (scope, t) =
    if scope = [] then pp_term fmt t
    else fprintf fmt "%a. %a" pp_scope scope pp_term t in
  pp_print_list ~pp_sep:T.separator pp_arg fmt (List.rev msubst)

let pp_ctx fmt ctx =
  let pp_ctx_entry fmt (name, ty) = fprintf fmt "%s : %a" name pp_term ty in
  pp_print_list ~pp_sep:T.separator pp_ctx_entry fmt (List.rev ctx)

let pp_mctx fmt mctx =
  let pp_mctx_entry fmt (name, ctx, ty) =
    if ctx = [] then fprintf fmt "%s : %a" name pp_term ty
    else fprintf fmt "%s{%a} : %a" name pp_ctx ctx pp_term ty in
  pp_print_list ~pp_sep:T.separator pp_mctx_entry fmt (List.rev mctx)


let pp_imctx fmt imctx =
  let pp_imctx_entry fmt (name, tm, ty) =
    fprintf fmt "%a / %s : %a" pp_term tm name pp_term ty in
  pp_print_list ~pp_sep:T.separator pp_imctx_entry fmt (List.rev imctx)


let pp_entry fmt entry =
  match entry with
  | Sort(name, mctx) -> fprintf fmt "sort %s (%a)@." name pp_mctx mctx
  | Cons(name, mctx1, mctx2, [], [], None, ty)
  | Cons(name, mctx1, mctx2, [], [], Some [], ty) ->
    fprintf fmt "constructor %s (%a) (%a) : %a@."
      name pp_mctx mctx1 pp_mctx mctx2 pp_term ty
  | Cons(name, mctx1, mctx2, subst1, subst2, None, ty) ->
    fprintf fmt "constructor %s (%a) (%a) (%a = %a) : %a@."
      name pp_mctx mctx1 pp_mctx mctx2 pp_subst subst1 pp_subst subst2 pp_term ty
  | Cons(name, mctx1, mctx2, subst1, subst2, Some(ctx), ty) ->
    fprintf fmt "constructor %s (%a) (%a) (%a = %a : (%a)) : %a@."
      name pp_mctx mctx1 pp_mctx mctx2
      pp_subst subst1 pp_subst subst2 pp_ctx ctx pp_term ty
  | Dest(name, mctx1, name_arg, ty_arg, mctx2, ty) ->
    fprintf fmt "destructor %s (%a) [%s : %a] (%a) : %a@."
    name pp_mctx mctx1 name_arg pp_term ty_arg pp_mctx mctx2 pp_term ty
  | Rew(lhs, rhs) ->
    fprintf fmt "equation %a --> %a@." pp_term lhs pp_term rhs
  | Let(name, mctx, ty, t) ->
    fprintf fmt "let %s (%a) : %a := %a@." name pp_mctx mctx pp_term ty pp_term t
  | Eval(t) -> fprintf fmt "eval %a@." pp_term t
  | Eq(t, u) -> fprintf fmt "check %a = %a@." pp_term t pp_term u
