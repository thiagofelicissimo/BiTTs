open Term
open Value
open Eval

exception Not_inferable
exception Not_a_sort 
exception Metas_not_supported
exception Length_mismatch

let split_at (n : int) (l : 'a list) : 'a list * 'a list =
  let rec aux n l acc = 
    if n = 0 then (List.rev acc, l)
    else match l with 
      | x :: l -> aux (n - 1) l (x :: acc)
      | [] -> assert false (* pre-condition |l| >= n not satisfied *)
  in aux n l []
  
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

let rec infer (v_ctx : v_ctx) (v_subst : v_subst) (t : tm) =     
  match t with 
  | Var(n) -> List.nth v_ctx n
  | Dest(d, u, msubst) -> 
    let p_sort, args_mctx, sort = get_drule (RuleTbl.find d !schem_rules) in 
    let sort_u = infer v_ctx v_subst u in 
    let pars_ixs = match_tm p_sort sort_u in 
    let v_u = eval_tm u [] v_subst in
    let v_msubst = 
      check_msubst v_ctx v_subst (Value(v_u) :: pars_ixs) msubst args_mctx in     
    eval_tm sort v_msubst []
  | Def(d) -> (DefTbl.find d !defs).ty
  | Meta(_) -> 
    (* we only typecheck terms without metas *)
    raise Metas_not_supported 
  | Const(_) -> raise Not_inferable

and check (v_ctx : v_ctx) (v_subst : v_subst) (t : tm) (sort : v_tm) =   
  match t with 
  | Var(_) | Dest(_) | Def(_) -> 
    let sort' = infer v_ctx v_subst t in equal_tm sort sort' (List.length v_subst)
  | Const(c, msubst) -> 
      let num_ixs, args_mctx, inst_msubst, p_sort = 
        get_crule (RuleTbl.find c !schem_rules) in      
      let ixs, pars = split_at num_ixs @@ match_tm p_sort sort in 
      let v_msubst = check_msubst v_ctx v_subst pars msubst args_mctx in 
      let expected_ixs = eval_msubst inst_msubst v_msubst [] in 
      equal_msubst ixs expected_ixs (List.length v_subst)        
  | Meta(_) -> raise Metas_not_supported

and check_msubst (v_ctx : v_ctx) (v_subst : v_subst) (v_msubst : v_msubst) (msubst : msubst) (mctx : mctx) : v_msubst = 
  match msubst, mctx with 
  | [], [] -> v_msubst
  | (n, t) :: msubst', (ctx', sort) :: mctx' when List.length ctx' = n -> 
    let v_msubst = check_msubst v_ctx v_subst v_msubst msubst' mctx' in 
    let depth = List.length v_subst in    
    let v_ctx', v_subst', _ = eval_ctx ctx' v_msubst depth in
    let v_sort = eval_tm sort v_msubst v_subst' in
    check (v_ctx' @ v_ctx) (v_subst' @ v_subst) t v_sort;    
    let t' = if ctx' = [] then Value(eval_tm t [] v_subst) else Closure(List.length ctx', t, [], v_subst) in
    t' :: v_msubst
  | _ -> raise Length_mismatch

let check_sort (v_ctx : v_ctx) (v_subst : v_subst) (t : tm) = 
  match t with 
  | Const(c, msubst) -> 
    let mctx = get_srule (RuleTbl.find c !schem_rules) in 
    ignore @@ check_msubst v_ctx v_subst [] msubst mctx
  | _ -> raise Not_a_sort
