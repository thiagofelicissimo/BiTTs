open Term
open Value
open Eval

exception Not_inferable
exception Not_a_sort 
exception Metas_not_supported
exception Length_mismatch

let get_drule (x : schem_rule) = 
  match x with
  | Dest(mctx, p_ty, mctx', ty) -> (mctx, p_ty, mctx', ty)
  | _ -> assert false

let get_crule (x : schem_rule) = 
  match x with
  | Const(mctx, mctx', msubst1, msubst2, p_ty) -> (mctx, mctx', msubst1, msubst2, p_ty)
  | _ -> assert false

let get_srule (x : schem_rule) = 
  match x with
  | Sort(mctx) -> mctx
  | _ -> assert false

let rec infer (v_ctx : v_ctx) (v_subst : v_subst) (t : tm) =     
  match t with 
  | Var(n) -> List.nth v_ctx n
  | Dest(d, u, msubst) -> 
    let _, p_ty, mctx, ty = get_drule (RuleTbl.find d !schem_rules) in 
    let ty_u = infer v_ctx v_subst u in 
    let v_msubst = Value(eval_tm u [] v_subst) :: (match_tm p_ty ty_u) in 
    let result = check_msubst v_ctx v_subst v_msubst msubst mctx in     
    eval_tm ty result []
  | Def(d) -> (DefTbl.find d !defs).ty
  | Meta(_) -> raise Metas_not_supported
  | Const(_) -> raise Not_inferable

and check (v_ctx : v_ctx) (v_subst : v_subst) (t : tm) (ty : v_tm) =   
  match t with 
  | Var(_) | Dest(_) | Def(_) -> 
    let ty' = infer v_ctx v_subst t in equal_tm ty ty' (List.length v_subst)
  | Const(c, msubst) -> 
    let _, mctx, msubst1, msubst2, p_ty = get_crule (RuleTbl.find c !schem_rules) in 
    let v_msubst = match_tm p_ty ty in 
    let v_msubst' = check_msubst v_ctx v_subst v_msubst msubst mctx in 
    equal_msubst 
      (eval_msubst msubst1 v_msubst' [])
      (eval_msubst msubst2 v_msubst' [])
      (List.length v_subst)
  | Meta(_) -> raise Metas_not_supported

  
and check_msubst (v_ctx : v_ctx) (v_subst : v_subst) (v_msubst : v_msubst) (msubst : msubst) (mctx : mctx) : v_msubst = 
  match msubst, mctx with 
  | [], [] -> v_msubst
  | (n, t) :: msubst', (ctx', ty) :: mctx' when List.length ctx' = n -> 
    let v_msubst = check_msubst v_ctx v_subst v_msubst msubst' mctx' in 
    let depth = List.length v_subst in    
    let v_ctx', v_subst', _ = eval_ctx ctx' v_msubst depth in
    let v_ty = eval_tm ty v_msubst v_subst' in
    check (v_ctx' @ v_ctx) (v_subst' @ v_subst) t v_ty;    
    let t' = if ctx' = [] then Value(eval_tm t [] v_subst) else Closure(List.length ctx', t, [], v_subst) in
    t' :: v_msubst
  | _ -> raise Length_mismatch

let check_sort (v_ctx : v_ctx) (v_subst : v_subst) (t : tm) = 
  match t with 
  | Const(c, msubst) -> 
    let mctx = get_srule (RuleTbl.find c !schem_rules) in 
    ignore @@ check_msubst v_ctx v_subst [] msubst mctx
  | _ -> raise Not_a_sort
