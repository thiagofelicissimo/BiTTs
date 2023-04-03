open Format
open Term
open Value

exception Todo

exception MatchUnderLambda
exception LenghtMismatch
exception LenghtMismatch2
exception HeadMismatch

exception NoMatch
exception Problem
exception Matched of env * term
exception NotEqual

module MatchTbl = Map.Make(Int)
type match_tbl = enve MatchTbl.t

let empty_match_tbl = MatchTbl.empty

let match_tbl_to_env match_tbl =
  List.rev @@ MatchTbl.fold (fun _ enve env -> enve :: env) match_tbl []

(* this function supposes that we only deal with 0-order variables *)
let rec gen_fresh (depth : int) (n : int) : env =
  let rec aux depth n acc =
    if n = 0 then acc
    else
      let new_var = {head = Lvl(depth); env = []} in
      aux (depth + 1) (n - 1) ((Val(new_var) : enve) :: acc) in
  aux depth n []


(* EVAL *)

let rec eval_tm (env : env) (t : term) : value =
  (*printf "%a |- %a@." pp_env env T.pp_term t;*)
  let env_sp = eval_sp env t.spine in
  match t.head with
  | Ix(n) ->
    begin match List.nth env n with
      | Val(v) -> v (* then env_sp should be [], but it is invariant *)
      | Clo(clo) when List.length env_sp = clo.binds -> eval_tm (env_sp @ clo.env) clo.body
      | Clo(_) -> raise LenghtMismatch end

  | Symb(str) -> begin try
    List.iter
        begin fun rew_rule ->
          try
            let match_tbl = match_sp empty_match_tbl rew_rule.lhs_spine env_sp in
            let new_env = match_tbl_to_env match_tbl in
            raise @@ Matched(new_env, rew_rule.rhs)
          with
          | Matched(new_env, rhs) -> raise @@ Matched(new_env, rhs)
          | _ -> () end
        (RewTbl.find str !rew_map);
    raise NoMatch
    with
    | Matched(new_env, rhs) -> eval_tm new_env rhs
    | Not_found | NoMatch -> {head = Symb(str); env = env_sp} end

and eval_sp (env : env) (sp : spine) : env = List.map (eval_arg env) sp

and eval_arg (env : env) (arg : arg) : enve =
  if arg.binds = 0
  then
    Val(eval_tm env arg.body)
  else
    Clo({
        binds = arg.binds;
        body = arg.body;
        env = env
      })

(* MATCH *)

and match_sp (match_tbl : match_tbl) (sp : spine) (envsp : env) : match_tbl =
  match sp, envsp with
  | [], [] -> match_tbl
  | arg :: sp, e :: envsp ->
    let match_tbl = match_arg match_tbl arg e in
    match_sp match_tbl sp envsp
  | _ -> raise LenghtMismatch2

and match_arg (match_tbl : match_tbl) (arg : arg) (e : enve) : match_tbl =
  match arg, e with
  | {binds = 0; body = t}, Val(v) -> match_val match_tbl t v
  | {binds = k; body = body}, Clo({binds = n}) when n = k ->
    begin match body.head with
      (* we suppose the lhs is of the right form, so don't need to check
       * that body.spine = x1 .. xk *)
      | Ix(n) ->
        begin match MatchTbl.find_opt (n-k) match_tbl with
          | None -> MatchTbl.add (n-k) e match_tbl
          | Some e' -> equal_enve e e' 0; match_tbl end
      | _ -> assert false end (* matching inside binder not supported *)
  | _ -> assert false

and match_val (match_tbl : match_tbl) (t : term) (v : value) : match_tbl =
  match t.head, v.head with
  | Ix(n), _ ->
    begin match MatchTbl.find_opt n match_tbl with
      | None -> MatchTbl.add n (Val(v) : enve) match_tbl
      | Some v' -> equal_enve (Val(v) : enve) v' 0; match_tbl end
  | Symb(c), Symb(d) when c = d -> match_sp match_tbl t.spine v.env
  | _ -> raise HeadMismatch

(* EQUAL *)

and equal_val (v : value) (v' : value) (depth : int) : unit =
  match v.head, v'.head with
  | Symb(str1), Symb(str2) when str1 = str2 ->
    equal_env v.env v'.env depth
  | Lvl(n), Lvl(m) when n = m ->
    equal_env v.env v'.env depth
  | _ -> raise NotEqual

and equal_env (env : env) (env' : env) (depth : int) : unit =
  match env, env' with
  | [], [] -> ()
  | e :: env, e' :: env' ->
    equal_enve e e' depth;
    equal_env env env' depth
  | _ -> raise NotEqual

and equal_enve (e : enve) (e' : enve) (depth : int) : unit =
  match e, e' with
  | Val(v), Val(v') ->
    equal_val v v' depth
  | Clo({binds = n1;body = t1;env = env1}), Clo({binds = n2; body = t2;env = env2}) ->
    (* we suppose we only compare well-typed terms, hence n1 is supposed equal to n2 *)
    let env' = gen_fresh depth n1 in
    equal_val
      (eval_tm (env' @ env1) t1)
      (eval_tm (env' @ env2) t2)
      (depth + n1)
  | _ -> raise NotEqual


(* READ_BACK *)

let rec read_back_tm (depth : int) (v : value) : term =
  match v.head with
  | Symb(str) -> {head = Symb(str); spine = read_back_sp depth v.env}
  | Lvl(lvl) -> {head = Ix(depth - (lvl + 1)); spine = read_back_sp depth v.env}

and read_back_sp (depth : int) (env : env) : spine =
  List.map (read_back_arg depth) env

and read_back_arg (depth : int) (enve : enve) : arg =
  match enve with
  | Val(v) -> {body = read_back_tm depth v; binds = 0}
  | Clo({body = body; binds = k; env = env}) ->
    let env' = gen_fresh depth k in
    let v = eval_tm (env' @ env) body in
    {body = read_back_tm (k + depth) v; binds = k}

(* CLOSE *)

(* reads back env and then puts each term inside arg of size binds *)
let close_env (depth : int) (binds : int) (env : env) : spine =
  List.map
    begin fun enve ->
      let arg = read_back_arg depth enve in
      assert (arg.binds = 0);
      {body = arg.body; binds = binds} end
    env


(* types and contexts *)

let eval_ty (env : env) (ty : ty) : vty =
  {vty_cst = ty.ty_cst; vty_env = eval_sp env ty.ty_spine}

let match_ty (ty : ty) (vty : vty) : env =
  if ty.ty_cst <> vty.vty_cst then raise NoMatch
  else match_tbl_to_env @@ match_sp empty_match_tbl ty.ty_spine vty.vty_env

let equal_vty (vty : vty) (vty' : vty) (depth : int) : unit =
  if vty.vty_cst <> vty'.vty_cst then raise NotEqual
  else equal_env vty.vty_env vty'.vty_env depth

let read_back_ty (depth : int) (vty : vty) : ty =
  {ty_cst = vty.vty_cst; ty_spine = read_back_sp depth vty.vty_env}


let env_of_vctx (vctx : vctx) : env = List.map (fun x -> (Val(fst x) : enve)) vctx

(* evaluates gamma in env, producing a value context with lvls starting at lvl=depth *)
let rec eval_ctx (depth : int) (env : env) (gamma : ctx) : vctx =
  match gamma with
  | [] -> []
  | ty :: gamma ->
    let gamma = eval_ctx depth env gamma in
    let vty = eval_ty (env_of_vctx gamma @ env) ty in
    let nvar = {head = Lvl(List.length gamma + depth); env = []} in
    (nvar, vty) :: gamma
