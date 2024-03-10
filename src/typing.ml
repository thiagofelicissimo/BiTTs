open Term
open Value
open Eval
open Common

exception Not_inferable
exception Not_a_sort
exception Metas_not_supported
exception Length_mismatch

(* helper functions to get a schematic rule *)
let get_drule (x : schem_rule) =
  match x with
  | Dest(p_sort, args_mctx, sort) -> (p_sort, args_mctx, sort)
  | _ -> assert false

let get_crule (x : schem_rule) =
  match x with
  | Const(num_ixs, mctx, msubst, p_sort) -> (num_ixs, mctx, msubst, p_sort)
  | _ -> assert false

let get_srule (x : schem_rule) =
  match x with
  | Sort(mctx) -> mctx
  | _ -> assert false


(* --------- beginning of the typechecking algorithm --------- *)

(* following other implementations of bidirectional typing, we tightly
   itegrate it with the NbE algorithm by asking for all inputs (other
   than the subject) to be already in the syntax of values. *)

let typing_mgs = false

let rec infer (mctx : mctx) (v_ctx : v_ctx) (v_subst : v_subst) (t : tm) =
  if typing_mgs
    then Format.printf "inferring %a@.  with mctx = %a@.   with ctx = %a@.   with v_subst = %a@."
          pp_term t pp_mctx mctx pp_ctx (read_back_ctx 0 v_ctx) pp_vsubst v_subst;
  match t with
  | Let(t, u) ->
    let t_ty = infer mctx v_ctx v_subst t in
    let t_v = eval_tm t 0 [] v_subst in
    infer mctx (t_ty :: v_ctx) (t_v :: v_subst) u

  | Ascr(t, ty) ->
    check_sort mctx v_ctx v_subst ty;
    let v_ty = eval_tm ty 0 [] v_subst in
    check mctx v_ctx v_subst t v_ty;
    v_ty
  | Var(n) -> List.nth v_ctx n
  | Dest(d, msubst) ->

    let u, msubst = (* we extract the principal arg *)
      let msubst_rev = List.rev msubst in
      let n, u = List.hd msubst_rev in
      if n <> 0 then assert false;
      let msubst = List.rev (List.tl msubst_rev) in
      u, msubst in

    let p_sort, args_mctx, sort = get_drule (RuleTbl.find d !schem_rules) in
    let sort_u = infer mctx v_ctx v_subst u in
    let pars_ixs = match_tm p_sort sort_u in
    let v_u = eval_tm u 0 [] v_subst in
    let v_msubst =
      check_msubst mctx v_ctx v_subst (Value(v_u) :: pars_ixs) msubst args_mctx in
    eval_tm sort 0 v_msubst []
  | Def(d, msubst) ->
    let v_msubst =
      check_msubst mctx v_ctx v_subst [] msubst (DefTbl.find d !defs).mctx in
    eval_tm (DefTbl.find d !defs).ty 0 v_msubst []
  | Meta(n, subst) ->
    if typing_mgs then Format.printf  "the metacontext is:@.%a @. but we are trying to access %d@." pp_mctx mctx n;
    let ctx, ty = List.nth mctx n in
    let v_subst' = check_subst mctx (n + 1) v_ctx v_subst subst ctx in
    eval_tm ty (n + 1) [] v_subst'
  | Const(_) -> raise Not_inferable

and check_subst (mctx : mctx) (meta_offset : int) (v_ctx : v_ctx) (v_subst : v_subst) (subst : subst) (ctx : ctx) =
  if typing_mgs then Format.printf "checking subst %a@.  with v_subst = %a@." pp_subst subst pp_vsubst v_subst;
  match subst, ctx with
  | [], [] -> []
  | (t :: subst), (ty :: ctx) ->
    let v_subst' = check_subst mctx meta_offset v_ctx v_subst subst ctx in
    let v_ty = eval_tm ty meta_offset [] v_subst' in
    check mctx v_ctx v_subst t v_ty;
    (eval_tm t 0 [] v_subst) :: v_subst'
  | _ -> assert false

and check (mctx : mctx) (v_ctx : v_ctx) (v_subst : v_subst) (t : tm) (sort : v_tm) =
  if typing_mgs then Format.printf "checking %a@.  against sort %a@.  with v_subst= %a@."
    pp_term t pp_term (read_back_tm (List.length v_subst) sort)  pp_vsubst v_subst;
  match t with
  | Var(_) | Dest(_) | Def(_) | Ascr(_) | Meta(_) ->
    let sort' = infer mctx v_ctx v_subst t in
    if typing_mgs then Format.printf "inferred %a@." pp_term (read_back_tm (List.length v_subst) sort');
    equal_tm sort sort' (List.length v_subst)
  | Const(c, msubst) ->
      let num_ixs, args_mctx, inst_msubst, p_sort =
        get_crule (RuleTbl.find c !schem_rules) in
      let ixs, pars = split_at num_ixs @@ match_tm p_sort sort in
      let v_msubst = check_msubst mctx v_ctx v_subst pars msubst args_mctx in
      let expected_ixs = eval_msubst inst_msubst 0 v_msubst [] in
      equal_msubst ixs expected_ixs (List.length v_subst)
  | Let(t, u) ->
    let t_ty = infer mctx v_ctx v_subst t in
    let t_v = eval_tm t 0 [] v_subst in
    check mctx (t_ty :: v_ctx) (t_v :: v_subst) u sort

and check_msubst (mctx : mctx) (v_ctx : v_ctx) (v_subst : v_subst) (v_msubst : v_msubst) (msubst : msubst) (mctx' : mctx) : v_msubst =
  if typing_mgs then Format.printf "checking msubst %a under mctx %a@.  wiht v_subst= %a@."
    pp_msubst msubst pp_mctx mctx pp_vsubst v_subst;
  match msubst, mctx' with
  | [], [] -> v_msubst
  | (n, t) :: msubst', (ctx', sort) :: mctx' when List.length ctx' = n ->
    let v_msubst = check_msubst mctx v_ctx v_subst v_msubst msubst' mctx' in
    let depth = List.length v_subst in
    let v_ctx', v_subst', _ = eval_ctx ctx' 0 v_msubst depth in
    let v_sort = eval_tm sort 0 v_msubst v_subst' in
    check mctx (v_ctx' @ v_ctx) (v_subst' @ v_subst) t v_sort;
    let t' =
      if ctx' = [] then Value(eval_tm t 0 [] v_subst)
      else Closure(List.length ctx', t, 0, [], v_subst) in
    if typing_mgs then Format.printf "now t was %a and t' is %a, and v_subst was %a@."
      pp_term t pp_vmsubst [t'] pp_vsubst v_subst;
    t' :: v_msubst
  | _ -> raise Length_mismatch

and check_sort (mctx : mctx) (v_ctx : v_ctx) (v_subst : v_subst) (t : tm) =
  if typing_mgs then Format.printf "checking sort %a under mctx %a@.  with v_subst = %a@."
    pp_term t pp_mctx mctx pp_vsubst v_subst;
  match t with
  | Const(c, msubst) ->
    let mctx' = get_srule (RuleTbl.find c !schem_rules) in
    ignore @@ check_msubst mctx v_ctx v_subst [] msubst mctx'
  | Let(t, sort) ->
    let t_ty = infer mctx v_ctx v_subst t in
    let t_v = eval_tm t 0 [] v_subst in
    check_sort mctx (t_ty :: v_ctx) (t_v :: v_subst) sort
  | _ -> raise Not_a_sort


let rec check_ctx (mctx : mctx) (ctx : ctx) =
  if typing_mgs then Format.printf "checking ctx %a under metactx %a @." pp_ctx ctx pp_mctx mctx;
  match ctx with
  | [] -> [],[]
  | (ty :: ctx) ->
    let v_ctx, v_subst = check_ctx mctx ctx in
    check_sort mctx v_ctx v_subst ty;
    let v_ty = eval_tm ty 0 [] v_subst in
    (v_ty :: v_ctx), (Var(List.length ctx) :: v_subst)

let rec check_mctx (mctx : mctx) =
  if typing_mgs then Format.printf "checking mctx %a@." pp_mctx mctx;
  match mctx with
  | [] -> ()
  | (ctx, ty) :: mctx ->
    check_mctx mctx;
    let v_ctx, v_subst = check_ctx mctx ctx in
    check_sort mctx v_ctx v_subst ty