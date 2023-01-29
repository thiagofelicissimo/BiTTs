open Format
open Term
open Value

exception Todo

let rew_map : rew_map ref = ref RewTbl.empty

exception MatchUnderLambda
exception LenghtMismatch
exception HeadMismatch

exception NoMatch
exception Problem
exception Matched of env * term

(* EVAL *)

let rec eval_tm (env : env) (t : term) : value =
  (* printf "%a |- %a@." V.pp_spine env T.pp_term t; *)
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
            let new_env = match_sp rew_rule.lhs_spine env_sp in
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

and match_sp (sp : spine) (envsp : env) : env =
  match sp, envsp with
  | [], [] -> []
  | arg :: sp, e :: envsp -> (match_arg arg e) @ match_sp sp envsp
  | _ -> raise LenghtMismatch

and match_arg (arg : arg) (e : enve) : env =
  match arg, e with
  | {binds = 0; body = t}, Val(v) -> match_val t v
  | {binds = k; body = body}, Clo({binds = n}) when n = k ->
    begin match body.head with
      | Ix(_) -> [e] (* we suppose it is of the right form, so don't need to check *)
      | _ -> assert false end (* matching inside binder not supported *)
  | _ -> assert false

and match_val (t : term) (v : value) : env =
  match t.head, v.head with
  | Ix(_), _ -> [Val(v)]
  | Symb(c), Symb(d) when c = d -> match_sp t.spine v.env
  | _ -> raise HeadMismatch

(* this function supposes that we only deal with 0-order variables *)
let rec ext_env (env : env) (depth : int) (k : int) : env =
  if k = 0 then env
  else
    let newvar = Lvl(depth) in
    let new_entry : enve = Val({head = newvar; env = []}) in
    ext_env (new_entry :: env) (depth + 1) (k - 1)



(* EQUAL *)

(* this function supposes that we only deal with 0-order variables *)
let rec gen_fresh (depth : int) (n : int) : env =
  let rec aux depth n acc =
    if n = 0 then acc
    else
      let new_var = {head = Lvl(depth); env = []} in
      aux (depth + 1) (n - 1) ((Val(new_var) : enve) :: acc) in
  aux depth n []

exception NotEqual
let rec equal_val (v : value) (v' : value) (depth : int) : unit =
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
  match ty with
  | Term(t) -> Val(eval_tm env t)
  | Star -> Star

let match_ty (ty : ty) (vty : vty) : env =
  match ty, vty with
  | Star, Star -> []
  | Term(t), Val(v) -> match_val t v
  | _ -> raise NoMatch

let equal_vty (vty : vty) (vty' : vty) (depth : int) : unit =
  match vty, vty' with
  | Val(v), Val(v') -> equal_val v v' depth
  | Star, Star -> ()
  | _ -> raise NotEqual

let read_back_ty (depth : int) (vty : vty) : ty =
  match vty with
  | Star -> Star
  | Val(v) -> Term(read_back_tm depth v)


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
