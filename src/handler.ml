
module C = Concrete
module T = Term
module V = Value
module Ty = Typing
module E = Eval
open Common

let rew_count = ref 0

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

  | C.Cons(name, mctx1, mctx2, subst1, subst2, ctx, sort) ->
    (* scoping *)
    let mctx1', mscope1 = C.scope_mctx mctx1 [] in
    let mctx2', mscope12 = C.scope_mctx mctx2 mscope1 in
    let sort_p, sort_scope = C.scope_p_tm sort in
    assert (mscope1 = sort_scope);
    let sort' = C.scope_tm sort mscope1 [] in

    let subst1' = C.scope_subst subst1 mscope12 [] in
    let subst2' = C.scope_subst subst2 mscope12 [] in
    let ctx' = Option.map (fun x -> fst (C.scope_ctx x mscope12 )) ctx in

    (* checking that sort_p is rigid and destructor-free *)
    T.check_dest_free sort_p;
    T.check_rigid sort_p;

    (* typechecking *)
    let mctx12' = mctx2' @ mctx1' in
    Ty.check_mctx mctx12';
    Ty.check_sort mctx1' [] [] sort';
    begin match ctx' with
      | Some ctx ->
        let _, _ = Ty.check_ctx mctx12' ctx in
        ignore @@ Ty.check_subst mctx12' 0 [] [] subst1' ctx;
        ignore @@ Ty.check_subst mctx12' 0 [] [] subst2' ctx;
        Format.printf "[%s %s] %s@." (darkblue "constructor") name (green "OK");

      | None ->
        Format.printf "[%s %s] %s@." (darkblue "constructor") name
          (yellow "WARNING: equational premises context omitted, skipping their typing")
    end;

    (* adding to the theory *)
    T.schem_rules :=
      T.RuleTbl.add name (T.Const(mctx2', subst1', subst2', sort_p)) !T.schem_rules

  | C.Dest(name, mctx1, name_parg, sort_parg, mctx2, sort) ->

    (* scoping *)
    let mctx1', mscope1 = C.scope_mctx mctx1 [] in
    let sort_parg' = C.scope_tm sort_parg mscope1 [] in
    let mctx2', mscope12 = C.scope_mctx mctx2 (name_parg :: mscope1) in
    let sort' = C.scope_tm sort mscope12 [] in

    let full_mctx = mctx2' @ [([], sort_parg')] @ mctx1' in

    (* typechecking*)
    Ty.check_mctx full_mctx;
    Ty.check_sort full_mctx [] [] sort';

    (* scoping of princip arg as a pattern *)
    let sort_parg_p, sort_parg_mscope = C.scope_p_tm sort_parg in

    (* we verify that it has the expected scope *)
    assert (sort_parg_mscope = mscope1);

    (* checking that sort_parg_p is rigid and destructor-free *)
    T.check_dest_free sort_parg_p;
    T.check_rigid sort_parg_p;

    (* adding to the theory *)
    T.schem_rules := T.RuleTbl.add name (T.Dest(sort_parg_p, mctx2', sort')) !T.schem_rules;

    Format.printf "[%s %s] %s@." (darkblue "destructor") name (green "OK");

    | C.Rew(lhs, rhs) ->

    rew_count := 1 + !rew_count;
    Format.printf "[%s %d] " (darkblue "equation") !rew_count;

    let name, msubst = match lhs with
      | Symb(name, msubst) -> name, msubst
      | _ -> assert false in

    let p_msubst, mscope = C.scope_p_msubst msubst in
    let rhs' = C.scope_tm rhs mscope [] in
    let rews = try T.RewTbl.find name !T.rew_rules with _ -> [] in

    begin
      try
        T.check_not_break_rig (T.Sym(name, p_msubst));
        T.check_critical_pair (T.Sym(name, p_msubst));
        Format.printf "%s@." (green "OK")
    with
      | T.Breaks_ridigity(rule_name) ->
        Format.printf "%s: lhs breaks rigidity of pattern in rule %s@." (red "ERROR") rule_name;
        raise (T.Breaks_ridigity(rule_name))
      | T.Critical_pair(n) ->
        Format.printf "%s: critical pair detected with rule %d@." (yellow "WARNING") n
    end;

    T.rew_rules := T.RewTbl.add name ((!rew_count, p_msubst, rhs') :: rews) !T.rew_rules
(*
    begin
      try
        T.check_critical_pair (T.Sym(name, p_msubst));
        Format.printf "%s@." (green "OK")
      with T.Critical_pair(n) ->
        Format.printf "%s: critical pair detected with rule %d@." (yellow "WARNING") n
    end;*)



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
