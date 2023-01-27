module T = Term
module V = Value

exception Todo
let rew (symb : string) : (T.spine * T.term) list =
  if symb <> "app"
  then []
  else
    let x = {T.head = T.Ix(0); T.spine = []} in
    let fx = {T.head = T.Ix(2); T.spine = [{T.binds = 0; T.body = x}]} in
    let abs = {T.head = T.Symb("abs"); T.spine = [{T.binds = 1; T.body = fx}]} in
    let y = {T.head = T.Ix(0); T.spine = []} in

    let fy = {T.head = T.Ix(1);
              T.spine = [{T.binds = 0; T.body = {T.head = T.Ix(0); T.spine = []}}]} in
    [([{T.binds = 0; T.body = y}; {T.binds = 0; T.body = abs}], fy)]

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
  | Symb(str) ->
    try
      List.iter
        begin fun (sp, t) ->
          try
            let new_env = match_sp sp spv in
            raise @@ Matched(new_env, t)
          with
          | Matched(new_env, t) -> raise @@ Matched(new_env, t)
          | _ -> () end
        (rew str);
      {V.head = Symb(str); V.spine = spv}
    with Matched(new_env, t) -> eval new_env t

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
      | Symb(_) -> raise MatchUnderLambda end



(* TESTS *)


let app (t : T.term) (u : T.term) : T.term =
  {T.head = T.Symb("app"); T.spine = [{T.binds = 0; T.body = u}; {T.binds = 0; T.body = t}]}

let abs (t : T.term) : T.term =
  {T.head = T.Symb("abs"); T.spine = [{T.binds = 1; T.body = t}]}

let vabs (env : V.env) (t : T.term) : V.enventry =
  Value ({V.head = V.Symb("abs"); V.spine = [Clo({V.binds = 1; V.body = t; V.env = env})]})

let vcst (str : string) : V.enventry = Value ({V.head = V.Symb (str); V.spine = []})

let var (n : int) : T.term =
  {T.head = T.Ix(n); T.spine = []}




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
