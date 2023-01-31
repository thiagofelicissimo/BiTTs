open Format
module T = Term
module Ty = Typing

type term = { head : string; spine : spine }

and spine = arg list

and arg = { body : term; scope : string list }

type ty =
  | Star
  | Term of term

type ctx = (string * ty) list

type mode =
  | Pos
  | Neg
  | Ersd

type prem = mode * string * ctx * ty

type entry =
  | Let of string * ty option * term
  | Rule of string * mode * prem list * ty
  | Rew of term * term
  | Type of term
  | Eval of term

(*
type rule =
  {
    name : string;
    prems : prem list;
    mode : mode;
    ty : ty
  }

type rew_rule =
  {
    lhs : term;
    rhs : term
  }
*)

(* SCOPING *)

let get_db scope name =
  let rec get_db' scope name k =
    match scope with
    | [] -> None
    | x :: scope when x = name -> Some k
    | _ :: scope -> get_db' scope name (k + 1) in
  get_db' scope name 0

exception Todo

let rec scope_tm scope (tm : term) : T.term =
  match get_db scope tm.head with
  | None -> {head = T.Symb(tm.head); spine = scope_sp scope tm.spine}
  | Some n -> {head = T.Ix(n); spine = scope_sp scope tm.spine}

and scope_sp scope (sp : spine) : T.spine = List.map (scope_arg scope) sp

and scope_arg scope (arg : arg) : T.arg =
  {body = scope_tm (arg.scope @ scope) arg.body; binds = List.length arg.scope}

let scope_ty scope (ty : ty) : T.ty =
  match ty with
  | Star -> T.Star
  | Term(tm) -> T.Term(scope_tm scope tm)

let scope_of_ctx (ctx : ctx) : string list = List.map fst ctx

let rec scope_ctx scope (ctx : ctx) : T.ctx =
  match ctx with
  | [] -> []
  | (name, ty) :: ctx ->
    let ctx' = scope_ctx scope ctx in
    let ty' = scope_ty (scope_of_ctx ctx @ scope) ty in
    ty' :: ctx'

let scope_of_prems (prems : prem list) : string list = List.map (fun (_, name, _, _) -> name) prems

let mode_to_mode mode : T.mode =
  match mode with
  | Pos -> T.Pos
  | Neg -> T.Neg
  | Ersd -> T.Ersd

let rec scope_prems scope (prems : prem list) : T.prem list =
  match prems with
  | [] -> []
  | (mode, name, ctx , ty) :: prems ->
    let scope' = scope_of_prems prems in
    let ctx' = scope_ctx (scope' @ scope) ctx in
    let ty' = scope_ty (scope_of_ctx ctx @ scope' @ scope) ty in
    let prems' = scope_prems scope prems in
    {T.mode = mode_to_mode mode; T.boundary = ty'; T.ctx = ctx'} :: prems'

let scope_rule mode prems ty : T.rule =
  {
    T.prems = scope_prems [] prems;
    T.mode = mode_to_mode mode;
    T.ty = scope_ty (scope_of_prems prems) ty
  }


(* scopes spine x1 .. xk *)
let scope_patt_spine scope (e : spine) : T.spine =
  List.map begin fun {body = body; scope = scope'} ->
    match get_db scope body.head with
    | Some n when scope' = [] && body.spine = [] ->
      {T.body = {T.head = T.Ix(n); T.spine = []}; T.binds = 0}
    | _ -> failwith "not a valid lhs" end e

let rec scope_lhs scope k (tm : term) : T.term * string list =
  if tm.head.[0] = '$'
  then {T.head = T.Ix(List.length scope + k); T.spine = scope_patt_spine scope tm.spine}, [tm.head]
  else
    let sp, rew_metavars = scope_lhs_spine scope k tm.spine in
    {T.head = T.Symb(tm.head); T.spine = sp}, rew_metavars

and scope_lhs_spine (scope : string list) (k : int) (e : spine) : T.spine * string list =
  match e with
  | [] -> [], []
  | arg :: e ->
    let tm, rew_metavars = scope_lhs (arg.scope @ scope) k arg.body in
    let e, rew_metavars' = scope_lhs_spine scope (k + List.length rew_metavars) e in
    {T.body = tm; T.binds = List.length arg.scope} :: e, rew_metavars @ rew_metavars'

let scope_rew lhs rhs =
  let lhs, rew_metavars = scope_lhs [] 0 lhs in
  let head_symb = match lhs.head with | Symb(str) -> str | _ -> failwith "not a valid lhs" in
  let rhs = scope_tm rew_metavars rhs in
  head_symb, {T.lhs_spine =  lhs.spine; T.rhs = rhs}

(*
let run scope entries =
  match entries with
  | [] -> ()
  | Rule(name, mode, prems, ty) :: entries ->
    let rule = scope_rule scope (name, mode, prems, ty) in
    Ty.sign := T.SignTbl.add name rule !Ty.sign
  | _ -> raise Todo*)




(* PRETTY PRINTING *)

let rec pp_binds fmt l =
  match l with
  | [s] -> fprintf fmt "%s" s
  | s :: l -> fprintf fmt "%a %s"pp_binds l s
  | [] -> assert false

let rec pp_term fmt term =
  if term.spine = [] then fprintf fmt "%s" term.head
  else fprintf fmt "%s(%a)" term.head pp_spine term.spine

and pp_spine fmt e =
  match e with
  | [arg] -> pp_arg fmt arg
  | arg :: e -> fprintf fmt "%a, %a" pp_spine e pp_arg arg
  | [] -> assert false

and pp_arg fmt arg =
  if arg.scope = [] then pp_term fmt arg.body
  else fprintf fmt "%a. %a" pp_binds arg.scope pp_term arg.body

let pp_ty fmt ty =
  match ty with
  | Star -> fprintf fmt "*"
  | Term(tm) -> pp_term fmt tm

let pp_pol fmt pol =
  match pol with
  | Pos -> fprintf fmt "+"
  | Neg -> fprintf fmt "-"
  | _ -> assert false

let rec pp_ctx fmt ctx =
  match ctx with
  | [(name, ty)] -> fprintf fmt "%s : %a" name pp_ty ty
  | (name, ty) :: ctx -> fprintf fmt "%a, %s : %a" pp_ctx ctx name pp_ty ty
  | _ -> ()

let pp_prem fmt (mode, name, ctx, ty) =
  match mode with
  | Pos | Neg -> fprintf fmt "(%s : (%a) %a)%a" name pp_ctx ctx pp_ty ty pp_pol mode
  | Ersd -> fprintf fmt "{%s : (%a) %a}" name pp_ctx ctx pp_ty ty

let rec pp_prems fmt (prems : prem list) =
  match prems with
  | [prem] -> fprintf fmt "%a" pp_prem prem
  | prem :: prems -> fprintf fmt "%a %a" pp_prems prems pp_prem prem
  | _ -> assert false

let pp_entry fmt entry =
  match entry with
  | Let(name, None, tm) -> fprintf fmt "let %s := %a@." name pp_term tm
  | Let(name, Some ty, tm) -> fprintf fmt "let %s : %a := %a@." name pp_ty ty pp_term tm
  | Rew(lhs, rhs) -> fprintf fmt "rew %a -> %a@." pp_term lhs pp_term rhs
  | Rule(name, mode, [], ty) ->
    fprintf fmt "rule%a %s : %a@." pp_pol mode name pp_ty ty
  | Rule(name, mode, prems, ty) ->
    fprintf fmt "rule%a %s %a : %a@." pp_pol mode name pp_prems prems pp_ty ty
  | Type(tm) -> fprintf fmt "type %a@."pp_term tm
  | Eval(tm) -> fprintf fmt "eval %a@."pp_term tm

let pp_prog fmt prog = List.iter (fun x -> pp_entry fmt x) prog
