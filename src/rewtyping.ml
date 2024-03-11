module C = Concrete
module T = Term
module V = Value
module Ty = Typing
module E = Eval
open Common



(* to type the rules, we need to store |Xi_p|, which is needed
   to parse Theta_c and Theta_d.

   we also store the underlying scope of the lhs of each rule,
   in order to check that it is equal to |Theta_c|.|Theta_d|.

   we also store Xi_d in the concrete syntax, because if Theta_c
   and Theta_d are not given, then we take Xi_c and Xi_d as the
   candidates. in this case we, we need to have Xi_d in scope
   |Xi_p|.|Xi_c|, but in the schematic rules table we only have
   Xi_d in scope |Xi_p|.|Xi_i|.|x:T|. we could implement function
   to try to unshitf from |Xi_p|.|Xi_i|.|x:T| to |Xi_p| and then
   to shift to |Xi_p|.|Xi_c|. howeover, we instead prefer to just
   parse Xi_d again, but in the scope |Xi_p|.|Xi_c|. if some
   shadowing is occuring than can maybe cause problems in some
   cases, but I think that in general it should be fine *)

module StrTbl = Map.Make(String)

type cons_info =
  {xi_p_scope   : string list;  (* |Xi_p| *)
   xi_c_scope   : string list;  (* |Xi_c| *)
   xi_p         : T.mctx;       (* Xi_p *)
   xi_c         : T.mctx;       (* Xi_c *)
   xi_i         : T.mctx;       (* Xi_i *)
   sort         : T.tm;         (* sort of c *)
   inst_msubst  : T.msubst;     (* vv_i *)
  }

type dest_info =
   {xi_pi      : T.mctx;       (* Xi_pi *)
    xi_d_conc  : C.mctx;       (* Xi_d in concrete syntax *)
    xi_d       : T.mctx;       (* Xi_d *)
    sort_parg  : T.tm;         (* sort of parg *)
    sort       : T.tm;         (* sort of d *)
   }

let cons_info : (cons_info StrTbl.t) ref = ref StrTbl.empty

let dest_info : (dest_info StrTbl.t) ref = ref StrTbl.empty


exception TODO
exception Problem

let rewrite_rule_checker mctx dest_name lhs_scope (lhs_msubst : T.msubst) rhs =

  let cons_name, tt_c, tt_d =
    match List.rev lhs_msubst with
    | (0, T.Const(cons_name, tt_c)) :: tt_d -> (cons_name, tt_c, List.rev tt_d)
    | _ -> assert false in

  let cons_info = StrTbl.find cons_name !cons_info in
  let dest_info = StrTbl.find dest_name !dest_info in

  (* 1- we check that Xi_p.Xi_i of c equals Xi_pi of d *)
  let xi_p_xi_i = cons_info.xi_i @ cons_info.xi_p in
  let xi_pi = dest_info.xi_pi in
  if xi_p_xi_i <> xi_pi then begin
    Format.printf "%s: the parameters and indices of c and d do not match:@.%a != %a@."
      (red "ERROR") T.pp_mctx xi_p_xi_i T.pp_mctx xi_pi; raise Problem end;

  (* 2- we check that the sort of the parg of d equals the sort of c *)
  if cons_info.sort <> dest_info.sort_parg then begin
    Format.printf "%s: the sort of c and the sort of the principal arg of d do not match:@.%a != %a@."
      (red "ERROR") T.pp_term cons_info.sort T.pp_term dest_info.sort_parg; raise Problem end;

  let theta_c_theta_d, theta_c_theta_d_scope = begin
    match mctx with
    | None ->
      (* Format.printf "%s " (yellow "metacontext omitted, trying to infer it"); *)
      let xi_d, xi_pcd_mscope = C.scope_mctx dest_info.xi_d_conc (cons_info.xi_c_scope @ cons_info.xi_p_scope) in
      let xi_d_mscope, _ = split_at (List.length xi_d) xi_pcd_mscope in
      (xi_d @ cons_info.xi_c, xi_d_mscope @ cons_info.xi_c_scope)
    | Some(mctx) ->
      let theta_cd, theta_cd_xi_p_scope =
        try C.scope_mctx mctx cons_info.xi_p_scope
        with e -> (Format.printf "%s: could not scope the following mctx in scope %a@.%a@."
        (red "ERROR") C.pp_scope cons_info.xi_p_scope C.pp_mctx mctx; raise e) in
      let theta_cd_scope, _ = split_at (List.length theta_cd) theta_cd_xi_p_scope in
      (theta_cd, theta_cd_scope)
  end in

  if lhs_scope <> theta_c_theta_d_scope then begin
    Format.printf "%s: the scopes of the rule and of Theta_c.Theta_d are not the same:@.%a != %a@." (red "ERROR") C.pp_scope lhs_scope C.pp_scope theta_c_theta_d_scope;  assert false end;

  let xi_p_theta_c_theta_d = theta_c_theta_d @ cons_info.xi_p in
  begin try Ty.check_mctx xi_p_theta_c_theta_d
  with | e -> (Format.printf "%s: the rule metacontext is ill-typed:@.%a@."
                (red "ERROR") T.pp_mctx xi_p_theta_c_theta_d; raise e) end;


  (* 4 - we check that the tt_c of the rule is typed by Xi_c to the
    right of id : Xi_p *)
  let id_xi_p = T.gen_id_msubst cons_info.xi_p in
  let id_xi_p' = E.eval_msubst id_xi_p (List.length theta_c_theta_d) [] [] in
  let v_id_xi_p_tt_c =
    try Ty.check_msubst xi_p_theta_c_theta_d [] [] id_xi_p' tt_c cons_info.xi_c
    with | e -> (Format.printf "%s: the lhs is ill-typed" (red "ERROR"); raise e) in

  (* 5 - we check that tt_d of the rule is typed by Xi_d to the right of
    id, vv_i[id, tt_c], c(tt_c) : Xi_p.Xi_i.(x : T) *)
  let v_ixs = E.eval_msubst cons_info.inst_msubst 0 v_id_xi_p_tt_c [] in
  let v_ctt_c = E.eval_tm (Const(cons_name, tt_c)) 0 [] [] in

  let v_id_ixs_ctt_c = [V.Value(v_ctt_c)] @ v_ixs @ id_xi_p' in

  let full_msusbt =
    try Ty.check_msubst xi_p_theta_c_theta_d [] [] v_id_ixs_ctt_c tt_d dest_info.xi_d
    with | e -> (Format.printf "%s: the lhs is ill-typed" (red "ERROR"); raise e) in

  (* 6 - we check that the rhs is typed by U[id, vv_i[id, tt_c], c(tt_c), tt_d]
    where U is the sort of d *)

  let sort_v = E.eval_tm dest_info.sort 0 full_msusbt [] in

  try Ty.check xi_p_theta_c_theta_d [] [] rhs sort_v
  with | e -> (Format.printf "%s: the rhs is ill-typed" (red "ERROR"); raise e)
