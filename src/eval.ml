open Term
open Value

exception Matched of v_msubst * tm
exception Match_failure

(* MATCHING : we match a tm/msubst value against a tm/msubst pattern,
   which yields a msubst value *)

let rec match_tm (p_tm : p_tm) (v_tm : v_tm) : v_msubst =
  match p_tm, v_tm with
  | Meta, _ -> [Value(v_tm)]
  | Sym(c, p_msubst), Sym(c', msubst) when c = c' -> match_msubst p_msubst msubst
  | _ -> raise Match_failure

and match_msubst (p_msubst : p_msubst) (v_msubst : v_msubst) : v_msubst =
  match p_msubst, v_msubst with
  | [], [] -> []
  | (0, p_t) :: p_msubst, Value(v) :: v_msubst ->
    (match_tm p_t v) @ (match_msubst p_msubst v_msubst)
  | (n, Meta) :: p_msubst, Closure(n', t', meta_offset', v_msubst', v_subst') :: v_msubst when n = n' ->
    Closure(n', t', meta_offset', v_msubst', v_subst') :: (match_msubst p_msubst v_msubst)
  | (n, _) :: _, _ ->
    (* matching inside binders not supported *)
    raise Match_failure
  | _ -> raise Match_failure


(* EVAL : we evaluate from the regular syntax to the syntax of values, under
   the environment given by a subst value (mapping occuring vars to values)
   and a msubst value (mapping occuring metas to values or closures) *)

let rec eval_tm (t : tm) (meta_offset : int) (v_msubst : v_msubst) (v_subst : v_subst) : v_tm =
  match t with
  | Var(n) -> List.nth v_subst n
  | Ascr(t, _) -> eval_tm t meta_offset v_msubst v_subst
  | Let(t, u) ->
    let v_t = eval_tm t meta_offset v_msubst v_subst in
    eval_tm u meta_offset v_msubst (v_t :: v_subst)
  | Meta(n, subst) ->
    begin match List.nth_opt v_msubst n with
    | Some Value(v) -> v
    | Some Closure(n, t', meta_offset', v_msubst', v_subst') ->
      eval_tm t' meta_offset' v_msubst' ((eval_subst subst meta_offset v_msubst v_subst) @ v_subst')
    | None ->
       Meta(n + meta_offset, eval_subst subst meta_offset v_msubst v_subst)
    end
  | Def(d, msubst) ->
    let body = (DefTbl.find d !defs).tm in
    let v_msubst' = eval_msubst msubst meta_offset v_msubst v_subst in
    eval_tm body 0 v_msubst' []
  | Sym(d, msubst') ->
    begin
      let v_msubst' = eval_msubst msubst' meta_offset v_msubst v_subst in
      let args =  v_msubst' in
      let try_match (_, p_msubst, r) =
        try
          let result = match_msubst p_msubst args in
          raise (Matched(result,r))
        with Match_failure -> () in
      try
        List.iter try_match (try RewTbl.find d !rew_rules with _ -> []);
        Sym(d, v_msubst')
      with Matched(result, r) -> eval_tm r meta_offset result []
    end


and eval_subst (subst : subst) (meta_offset : int)  (v_msubst : v_msubst) (v_subst : v_subst) : v_subst =
    List.map (fun t -> eval_tm t meta_offset v_msubst v_subst) subst

and eval_msubst (msubst : msubst) (meta_offset : int)  (v_msubst : v_msubst) (v_subst : v_subst) : v_msubst =
    List.map (fun (n, t) ->
      if n = 0
      then Value(eval_tm t meta_offset v_msubst v_subst)
      else Closure(n, t, meta_offset, v_msubst, v_subst)) msubst

let rec eval_ctx (ctx : ctx) (meta_offset : int)  (v_msubst : v_msubst) (depth : int) : v_ctx * v_subst * int =
  match ctx with
  | [] -> ([], [], depth)
  | ty :: ctx ->
    let v_ctx, v_subst, depth = eval_ctx ctx meta_offset v_msubst depth in
    let v_ty = eval_tm ty meta_offset v_msubst v_subst in
    (v_ty :: v_ctx, Var(depth) :: v_subst, depth + 1)


(* EQUALITY CHECK : we check for equality while recursively entering closures
   and checking their corresponding values for equality *)

exception Equality_check_error

let rec gen_fresh n depth =
  if n = 0 then []
  else Var(depth + n - 1) :: gen_fresh (n-1) depth

let rec equal_tm (v_t : v_tm) (v_t' : v_tm) (depth : int) : unit =
  (* Format.printf "checking if %a is equal to %a@." pp_term (read_back_tm depth v_t) pp_term (read_back_tm depth v_t'); *)
  match v_t, v_t' with
  | Var(n), Var(m) when n = m -> ()
  | Sym(c, v_msubst), Sym(c', v_msubst') when c = c' ->
    equal_msubst v_msubst v_msubst' depth
  | Meta(n, v_subst), Meta(n', v_subst') when n = n' ->
    equal_subst v_subst v_subst' depth
  | _ ->
    raise Equality_check_error

and equal_subst (v_subst : v_subst) (v_subst' : v_subst) (depth : int) : unit =
  if (List.length v_subst) <> (List.length v_subst') then raise Equality_check_error;
  List.iter2 (fun x y -> equal_tm x y depth) v_subst v_subst'

and equal_msubst (v_msubst : v_msubst) (v_msubst' : v_msubst) (depth : int) : unit =
  if (List.length v_msubst) <> (List.length v_msubst') then raise Equality_check_error;
  List.iter2
    begin fun x y -> match x, y with
    | Value(v_t), Value(v_t') -> equal_tm v_t v_t' depth
    | Closure(n, t, meta_offset, v_msubst, v_subst), Closure(n', t', meta_offset', v_msubst', v_subst') when n = n' ->
      let fresh = gen_fresh n depth in
      let v_t = eval_tm t meta_offset v_msubst (fresh @ v_subst) in
      let v_t' = eval_tm t' meta_offset' v_msubst' (fresh @ v_subst') in
      equal_tm v_t v_t' (depth + n)
    | _ -> raise Equality_check_error end
    v_msubst v_msubst'



(* READ_BACK : reads back a value into its corresponding (deep) normal form
   in the regular syntax *)

and read_back_tm (depth : int) (t : v_tm) : tm =
  match t with
  | Var(i) -> Var(depth - (i + 1))
  | Sym(name, msubst) -> Sym(name, read_back_msubst depth msubst)
  | Meta(n, subst) -> Meta(n, read_back_subst depth subst)

and read_back_subst  (depth : int) (subst : v_subst) : subst =
  List.map (read_back_tm depth) subst

and read_back_msubst (depth : int) (msubst : v_msubst) : msubst =
  match msubst with
  | [] -> []
  | Value(v) :: msubst' -> (0, read_back_tm depth v) :: read_back_msubst depth msubst'
  | Closure(n, t, meta_offset', v_msubst', v_subst') :: msubst' ->
    let v_t = eval_tm t meta_offset' v_msubst' (gen_fresh n depth @ v_subst') in
    (n, read_back_tm (depth + n) v_t) :: read_back_msubst depth msubst'

let rec read_back_ctx (depth : int) (ctx : v_ctx) : ctx =
  match ctx with
  | [] -> []
  | (ty :: ctx) ->
    read_back_tm (depth + List.length ctx) ty :: read_back_ctx depth ctx