
module C = Concrete
module T = Term
module V = Value
module Ty = Typing
module E = Eval
open Common

exception Overlap_detected

exception TODO

let rewrite_rule_checker rule = raise TODO

let handle_entry entry =
  match entry with
  | C.Sort(name, mctx) ->
    (* scoping *)
    let mctx, _ = C.scope_mctx mctx [] in
    (* typechecking *)
    Ty.check_mctx mctx;
    (* adding to the theory *)
    T.schem_rules := T.RuleTbl.add name (T.Sort mctx) !T.schem_rules;

    Format.printf "[%s %s] %s@." (darkblue "sort") name (green "OK")

  | C.Cons(name, mctx_pars, mctx_args, imctx, ty) ->
    (* scoping *)
    let mctx_pars', mscope_pars = C.scope_mctx mctx_pars [] in
    let mctx_args', mscope_pars_args = C.scope_mctx mctx_args mscope_pars in
    let inst_msubst = C.scope_msubst (C.msubst_of_imctx imctx) mscope_pars_args [] in
    let mctx_ixs', mscope_pars_ixs = C.scope_mctx (C.mctx_of_imctx imctx) mscope_pars in
    let ty_p, ty_scope = C.scope_p_tm ty in
    assert (mscope_pars_ixs = ty_scope);
    let ty' = C.scope_tm ty mscope_pars_ixs [] in

    (* typechecking *)
    Ty.check_mctx (mctx_ixs' @ mctx_pars');
    Ty.check_mctx (mctx_args' @ mctx_pars');
    let id_pars = E.eval_msubst (T.gen_id_msubst mctx_pars') 0 [] [] in
    ignore @@ Ty.check_msubst (mctx_args' @ mctx_pars') [] [] id_pars inst_msubst mctx_ixs';
    Ty.check_sort (mctx_ixs' @ mctx_pars') [] [] ty';

    (* adding to the theory *)
    T.schem_rules :=
      T.RuleTbl.add name (T.Const(List.length inst_msubst, mctx_args', inst_msubst, ty_p)) !T.schem_rules;

    Format.printf "[%s %s] %s@." (darkblue "constructor") name (green "OK")
  | C.Dest(name, mctx_pars_ixs, name_arg, ty_arg, mctx_args, ty) ->

    (* scoping *)
    let full_concrete_mctx = mctx_args @ [(name_arg, [], ty_arg)] @ mctx_pars_ixs in
    let full_mctx, full_mscope = C.scope_mctx full_concrete_mctx [] in
    let ty' = C.scope_tm ty full_mscope [] in

    (* typechecking*)
    Ty.check_mctx full_mctx;
    Ty.check_sort full_mctx [] [] ty';

    (* scoping of princip arg as a pattern *)
    let ty_arg_p, ty_arg_mscope = C.scope_p_tm ty_arg in

    (* we verify that it has the expected scope *)
    let _, pars_ixs_mscope = split_at (1 + List.length mctx_args) full_mscope in
    assert (ty_arg_mscope = pars_ixs_mscope);

    (* adding to the theory *)
    let mctx_args', _ = split_at (List.length mctx_args) full_mctx in
    T.schem_rules := T.RuleTbl.add name (T.Dest(ty_arg_p, mctx_args', ty')) !T.schem_rules;

    Format.printf "[%s %s] %s@." (darkblue "destructor") name (green "OK")

  | C.Rew(mctx, lhs, rhs) ->

    if mctx <> None then assert false;
    let name, msubst = match lhs with
      | Symb(name, msubst) ->
        (* we verify that name is a destructor *)
        (match T.RuleTbl.find name !T.schem_rules with
        | Dest(_) -> () | _ -> assert false);
        if msubst = [] then assert false;
        name, msubst
      | _ -> assert false in

    let p_msubst, mscope = C.scope_p_msubst msubst in
    let rhs' = C.scope_tm rhs mscope [] in
    let rews = try T.RewTbl.find name !T.rew_rules with _ -> [] in

    (* checks that rule does not overlap any other one *)
    List.iter (fun (p_msubst', _) ->
      try
        T.check_unify_msubst p_msubst p_msubst';
        raise Overlap_detected
      with T.Do_not_unify -> ()
      ) rews;

    T.rew_rules := T.RewTbl.add name ((p_msubst, rhs') :: rews) !T.rew_rules;

    Format.printf "[%s] %s@." (darkblue "equation") (yellow "type-checker for rewrite rules not yet implemented")

  | Eval(tm) ->
    let tm = C.scope_tm tm [] [] in
    let vtm = E.eval_tm tm 0 [] [] in
    let tm' = E.read_back_tm 0 vtm in
    Format.printf "[%s %a] %a@." (command "evaluate") T.pp_term tm T.pp_term tm'

  | Let(name, mctx, ty, tm) ->

    (* scoping *)
    let mctx', mscope = C.scope_mctx mctx [] in
    let ty' = C.scope_tm ty mscope [] in
    let tm' = C.scope_tm tm mscope [] in

    (* typing *)
    Ty.check_mctx mctx';
    Ty.check_sort mctx' [] [] ty';
    let v_ty = E.eval_tm ty' 0 [] [] in
    Ty.check mctx' [] [] tm' v_ty;

    (* adding to the scope of top-level defs *)
    T.defs := T.DefTbl.add name {T.tm = tm'; mctx = mctx'; ty = ty'} !T.defs;

    Format.printf "[%s %s] %s@." (command "let") name (green "OK")

  | Eq(t, u) ->
    let t' = C.scope_tm t [] [] in
    let u' = C.scope_tm u [] [] in
    E.equal_tm (E.eval_tm t' 0 [] []) (E.eval_tm u' 0 [] []) 0;
    Format.printf "[%s %a = %a] %s@." (command "assert") T.pp_term t' T.pp_term u' (green "OK")
