module T = Term
module V = Value

exception Todo

let app (t : T.term) (u : T.term) : T.term =
  {T.head = T.Symb("app"); T.spine = [{T.binds = 0; T.body = u}; {T.binds = 0; T.body = t}]}

let abs (t : T.term) : T.term =
  {T.head = T.Symb("abs"); T.spine = [{T.binds = 1; T.body = t}]}

let vabs (env : V.env) (t : T.term) : V.enventry =
  Value ({V.head = V.Symb("abs"); V.spine = [Clo({V.binds = 1; V.body = t; V.env = env})]})

let vcst (str : string) : V.enventry = Value ({V.head = V.Symb (str); V.spine = []})

let var (n : int) : T.term =
  {T.head = T.Ix(n); T.spine = []}

let zero : T.term =
  {T.head = T.Symb("zero"); T.spine = []}

let succ (t : T.term) : T.term =
  {T.head = T.Symb("succ"); T.spine = [{T.binds = 0; T.body = t}]}

let plus (t : T.term) (u : T.term) : T.term =
  {T.head = T.Symb("plus"); T.spine = [{T.binds = 0; T.body = t}; {T.binds = 0; T.body = u}]}

let rew_map : T.rew_map ref = ref T.RewTbl.empty

let beta_rule : T.rew_rule =
  let x = {T.head = T.Ix(0); T.spine = []} in
  let fx = {T.head = T.Ix(2); T.spine = [{T.binds = 0; T.body = x}]} in
  let abs = {T.head = T.Symb("abs"); T.spine = [{T.binds = 1; T.body = fx}]} in
  let y = {T.head = T.Ix(0); T.spine = []} in
  let fy = {T.head = T.Ix(1);
            T.spine = [{T.binds = 0; T.body = {T.head = T.Ix(0); T.spine = []}}]} in
  {lhs_spine = [{T.binds = 0; T.body = y}; {T.binds = 0; T.body = abs}];
   rhs = fy
  }
let _ =
  rew_map := T.RewTbl.add "app" [beta_rule] !rew_map

let plus_zero_rule : T.rew_rule =
  {lhs_spine = [{T.binds = 0; T.body = zero};
                {T.binds = 0; T.body = var 0}];
   rhs = var 0}
let plus_succ_rule : T.rew_rule =
  {lhs_spine = [{T.binds = 0; T.body = succ (var 1)};
                {T.binds = 0; T.body = var 0}];
   rhs = succ (plus (var 1) (var 0))
  }
let _ =
  rew_map := T.RewTbl.add "plus" [plus_zero_rule; plus_succ_rule] !rew_map

exception MatchUnderLambda
exception LenghtMismatch
exception HeadMismatch

exception Matched of V.env * T.term

let rec eval (env : V.env) (t : T.term) : V.value =
  let spv = eval_sp env t.spine in
  match t.head with
  | Ix(n) ->
    begin match List.nth env n with
      | Value(v) -> v
      | Clo(clo) ->
        if List.length spv = clo.binds
        then eval (spv @ clo.env) clo.body
        else raise LenghtMismatch end
  | Symb(str) -> begin try
    List.iter
        begin fun {T.lhs_spine = sp; T.rhs =  t} ->
          try
            let new_env = match_sp sp spv in
            raise @@ Matched(new_env, t)
          with
          | Matched(new_env, t) -> raise @@ Matched(new_env, t)
          | _ -> () end
        (T.RewTbl.find str !rew_map);
    {V.head = Symb(str); V.spine = spv}
    with
    | Matched(new_env, t) -> eval new_env t
    | Not_found -> {V.head = Symb(str); V.spine = spv} end

and eval_sp (env : V.env) (sp : T.spine) : V.env =
  match sp with
  | [] -> []
  | arg :: sp ->
    if arg.binds = 0
    then Value(eval env arg.body) :: eval_sp env sp
    else Clo({V.binds = arg.binds; V.body = arg.body; V.env = env}) :: eval_sp env sp

and match_sp (sp : T.spine) (vsp : V.env) : V.env =
  match sp, vsp with
  | [], [] -> []
  | arg :: sp, e :: vsp -> (match_arg arg e) @ match_sp sp vsp
  | _ -> raise LenghtMismatch

and match_arg (arg : T.arg) (e : V.enventry) : V.env =
  match e with
  | Value(v) ->
    if arg.binds <> 0
    then raise LenghtMismatch
    else let t = arg.body in
      begin match t.head, v.head with
      | Ix(_), _ -> [e]
      | Symb(c), Symb(d) when c = d -> match_sp t.spine v.spine
      | _ -> raise HeadMismatch end
  | Clo(clo) ->
    if clo.binds <> arg.binds
    then raise LenghtMismatch
    else begin match arg.body.head with
      | Ix(_) -> [e] (* we suppose it is of the right form, so don't need to check *)
      | Symb(_) -> assert false end

let rec ext_env (env : V.env) (depth : int) (k : int) : V.env =
  if k = 0 then env
  else
    let str = V.Var(string_of_int depth) in
    let new_entry = V.Value({V.head = str; V.spine = []}) in
    ext_env (new_entry :: env) (depth + 1) (k - 1)

exception NotEqual

let rec equal_vl (t : V.value) (u : V.value) (depth : int) : unit =
  match t.head, u.head with
  | V.Symb(str1), V.Symb(str2) | V.Var(str1), V.Var(str2) ->
    if str1 <> str2
    then raise NotEqual
    else equal_sp t.spine u.spine depth
  | _ -> raise NotEqual

and equal_sp (sp : V.env) (sp' : V.env) (depth : int) : unit =
  match sp, sp' with
  | [], [] -> ()
  | e :: sp, e' :: sp' ->
    equal_enventry e e' depth;
    equal_sp sp sp' depth
  | _ -> raise NotEqual

and equal_enventry (e : V.enventry) (e' : V.enventry) (depth : int) : unit =
  match e, e' with
  | Value(t), Value(u) -> equal_vl t u depth
  | Clo({binds = n1;body = t1;env = env1}), Clo({binds = n2; body = t2;env = env2}) ->
    (* we suppose we only compare well-typed terms, hence n1 is supposed equal to n2 *)
    equal_vl
      (eval (ext_env env1 depth n1) t1)
      (eval (ext_env env2 depth n2) t2)
      (depth + n1)
  | _ -> raise NotEqual


(* TESTS *)

(* terms to test *)

let e = [vabs [vcst "a"] (app (var 0) (var 1))]
let t = app (var 0) (abs (var 0))

let v =
  app
    (app
       (abs (abs (app
                 (var 1)
                 (var 0))))
       (abs (var 0)))
    (abs (var 0))


let t2 = abs (plus zero (var 0)) (* \x. 0 + x *)
let u2 = abs (var 0) (* (\y.y) *)
let r2 = equal_vl (eval [] t2) (eval [] u2) 0

let t3 = abs (app (abs (var 0)) (var 0)) (* (\f x. f x) (\y.y) *)
let u3 = abs (var 0) (* (\y.y) *)
let r3 = equal_vl (eval [] t3) (eval [] u3) 0
