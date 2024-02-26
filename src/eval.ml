open Term
open Value

exception Matched of v_msubst * tm
exception Match_failure

(* MATCHING : we match a tm/msubst value against a tm/msubst pattern,
   which yields a msubst value *)

let rec match_tm (p_tm : p_tm) (v_tm : v_tm) : v_msubst =
  match p_tm, v_tm with
  | Meta, _ -> [Value(v_tm)]
  | Const(c, p_msubst), Const(c', msubst) when c = c' -> match_msubst p_msubst msubst
  | Dest(d, p_msubst), Dest(d', t, msubst) when d = d' ->
    match_msubst p_msubst ([Value(t)] @ msubst)
  | _ -> raise Match_failure

and match_msubst (p_msubst : p_msubst) (v_msubst : v_msubst) : v_msubst =
  match p_msubst, v_msubst with
  | [], [] -> []
  | (0, p_t) :: p_msubst, Value(v) :: v_msubst ->
    (match_tm p_t v) @ (match_msubst p_msubst v_msubst)
  | (n, Meta) :: p_msubst, Closure(n', t', v_msubst', v_subst') :: v_msubst when n = n' ->
    Closure(n', t', v_msubst', v_subst') :: (match_msubst p_msubst v_msubst)
  | (n, _) :: _, _ ->
    (* matching inside binders not supported *)
    raise Match_failure
  | _ -> raise Match_failure


(* EVAL : we evaluate a tm/subst/msubst to a tm/subst/msubst value, under
   the environment given by a subst value (mapping occuring vars to values)
   and a msubst value (mapping occuring metas to values or closures) *)

let rec eval_tm (t : tm) (v_msubst : v_msubst) (v_subst : v_subst) : v_tm =
  match t with
  | Var(n) -> List.nth v_subst n
  | Ascr(t, ty) -> eval_tm t v_msubst v_subst
  | Meta(n, subst) ->
    begin match List.nth v_msubst n with
    | Value(v) -> v
    | Closure(n, t', v_msubst', v_subst') ->
      eval_tm t' v_msubst' ((eval_subst subst v_msubst v_subst) @ v_subst')
    end
  | Def(d) -> (DefTbl.find d !defs).rhs
  | Dest(d, u, msubst') ->
    begin
      let v_u = eval_tm u v_msubst v_subst in
      let v_msubst' = eval_msubst msubst' v_msubst v_subst in
      let args =  v_msubst' @ [Value(v_u)] in
      let try_match (p_msubst, r) =
        try
          let result = match_msubst p_msubst args in
          raise (Matched(result,r))
        with Match_failure -> () in
      try
        List.iter try_match (try RewTbl.find d !rew_rules with _ -> []);
        Dest(d, v_u, v_msubst')
      with Matched(result, r) -> eval_tm r result []
    end
(*| Const(c, msubst) -> Const(c, eval_msubst msubst v_msubst v_subst)*)
  | Const(c, msubst') ->
    let args = eval_msubst msubst' v_msubst v_subst in
    let try_match (p_msubst, r) =
      try
        let result = match_msubst p_msubst args in
        raise (Matched(result,r))
      with Match_failure -> () in
    try
      List.iter try_match (try RewTbl.find c !rew_rules with _ -> []);
      Const(c, args)
    with Matched(result, r) -> eval_tm r result []


and eval_subst (subst : subst) (v_msubst : v_msubst) (v_subst : v_subst) : v_subst =
    List.map (fun t -> eval_tm t v_msubst v_subst) subst

and eval_msubst (msubst : msubst) (v_msubst : v_msubst) (v_subst : v_subst) : v_msubst =
    List.map (fun (n, t) ->
      if n = 0
      then Value(eval_tm t v_msubst v_subst)
      else Closure(n, t, v_msubst, v_subst)) msubst

let rec eval_ctx (ctx : ctx) (v_msubst : v_msubst) (depth : int) : v_ctx * v_subst * int =
  match ctx with
  | [] -> ([], [], depth)
  | ty :: ctx ->
    let v_ctx, v_subst, depth = eval_ctx ctx v_msubst depth in
    let v_ty = eval_tm ty v_msubst v_subst in
    (v_ty :: v_ctx, Var(depth) :: v_subst, depth + 1)


(* EQUALITY CHECK : we check for equality while recursively entering closures
   and checking their corresponding values for equality *)

exception Equality_check_error

let rec gen_fresh n depth =
  if n = 0 then []
  else Var(depth + n - 1) :: gen_fresh (n-1) depth

let rec equal_tm (v_t : v_tm) (v_t' : v_tm) (depth : int) : unit =
  match v_t, v_t' with
  | Var(n), Var(m) when n = m -> ()
  | Const(c, v_msubst), Const(c', v_msubst') when c = c' ->
    equal_msubst v_msubst v_msubst' depth
  | Dest(d, v_t, v_msubst), Dest(d', v_t', v_msubst') when d = d' ->
    equal_tm v_t v_t' depth;
    equal_msubst v_msubst v_msubst' depth
  | _ -> raise Equality_check_error

and equal_msubst (v_msubst : v_msubst) (v_msubst' : v_msubst) (depth : int) : unit =
  if (List.length v_msubst) <> (List.length v_msubst') then raise Equality_check_error;
  List.iter2
    begin fun x y -> match x, y with
    | Value(v_t), Value(v_t') -> equal_tm v_t v_t' depth
    | Closure(n, t, v_msubst, v_subst), Closure(n', t', v_msubst', v_subst') when n = n' ->
      let fresh = gen_fresh n depth in
      let v_t = eval_tm t v_msubst (fresh @ v_subst) in
      let v_t' = eval_tm t' v_msubst' (fresh @ v_subst') in
      equal_tm v_t v_t' (depth + n)
    | _ -> raise Equality_check_error end
    v_msubst v_msubst'



(* READ_BACK : reads back a value into its corresponding (deep) normal form
   in the syntax of regular terms/msubsts *)

let rec read_back_tm (depth : int) (t : v_tm) : tm =
  match t with
  | Var(i) -> Var(depth - (i + 1))
  | Dest(name, t, msubst) -> Dest(name, read_back_tm depth t, read_back_msubst depth msubst)
  | Const(name, msubst) -> Const(name, read_back_msubst depth msubst)

and read_back_msubst (depth : int) (msubst : v_msubst) : msubst =
  match msubst with
  | [] -> []
  | Value(v) :: msubst' -> (0, read_back_tm depth v) :: read_back_msubst depth msubst'
  | Closure(n, t, v_msubst', v_subst') :: msubst' ->
    let v_t = eval_tm t v_msubst' (gen_fresh n depth @ v_subst') in
    (n, read_back_tm (depth + n) v_t) :: read_back_msubst depth msubst'
