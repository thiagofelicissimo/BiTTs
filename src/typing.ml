open Term

exception Todo

let equal (ty : ty) (ty' : ty) : unit = raise Todo

(* let subst_tm (t : term) (theta : spine) : term = raise Todo *)

let subst_ty (t : ty) (theta : spine) : ty = raise Todo

let subst_ctx (sp : spine) (ctx : ctx) : ctx = raise Todo

let lookup (sign : sign) (ctx : ctx) (hd : head) : mode * rule = raise Todo

let whnf tm = raise Todo

let match_spine (sp : spine) (sp' : spine) (depth : int) : spine = raise Todo

exception NoMatch

let match_tm (t : term) (u : term) (depth : int) : spine =
  match t.head, u.head with
  | Ix(_), _ -> [{body = u; binds = depth}]
  | _, Ix(_) -> raise NoMatch
  | Symb(str), Symb(str') when str = str' -> match_spine t.spine u.spine depth
  | Symb(str), Symb(str') when str <> str' -> raise NoMatch



let match_ty (ty : ty) (ty' : ty) : spine =
  match ty, ty' with
  | Ty t, Ty u -> match_tm t (whnf u) 0
  | Star, Star -> []
  | _ -> assert false

let rec infer (sign : sign) (ctx : ctx) (tm : term) : ty =
  let mode, {ctx = delta; ty = ty} = lookup sign ctx tm.head in
  match mode with
  | Pos ->
    let theta = type_spine sign ctx delta tm.spine in
    subst_ty ty theta
  | Neg -> assert false
  | Ersd -> assert false

and check (sign : sign) (ctx : ctx) (tm : term) (ty : ty) : unit =
  let mode, {ctx = delta; ty = ty_sig} = lookup sign ctx tm.head in
  match mode with
  | Pos ->
    let ty' = infer sign ctx tm in equal ty ty'
  | Neg ->
    let theta = match_ty ty ty_sig in
    raise Todo
  | Ersd -> assert false

and type_spine (sign : sign) (gamma : ctx) (delta : ctx) (sp : spine) : spine =
  match delta, sp with
  | [], [] -> []
  | (rule, Pos) :: delta, arg :: sp ->
    let sp' = type_spine sign gamma delta sp in
    let ty' = infer sign (gamma @ (subst_ctx sp' rule.ctx)) arg.body in
    let sp'' = match_ty ty' rule.ty in
    arg :: sp'' @ sp'
  | (rule, Neg) :: delta, arg :: sp ->
    let sp' = type_spine sign gamma delta sp in
    check sign (gamma @ (subst_ctx sp rule.ctx)) arg.body (subst_ty rule.ty sp);
    arg :: sp
  | _ -> assert false
