open Term
open Value
open Eval


let sign : sign ref = ref SignTbl.empty

let remove_erased (prems : prem list) : prem list * int =
  let rec removed_erased' (prems : prem list) k =
    match prems with
    | {mode = Ersd} :: prems -> removed_erased' prems (k + 1)
    | _ -> prems, k in
  removed_erased' prems 0

let rec dummy_env (size : int) : env =
  if size = 0 then [] else
    Val({head = Symb("DUMMY"); env = []}) :: dummy_env (size - 1)


let lookup_ty (gamma : vctx) (n : int) : vty =
  snd (List.nth gamma n)

exception NotInferable

let rec infer (gamma : vctx) (tm : term) : vty =
  Format.printf "%a |- %a => ?@." pp_vctx gamma pp_term tm;
  match tm.head with
  | Ix(n) -> lookup_ty gamma n
  | Symb(str) ->
    let rule = SignTbl.find str !sign in
    begin match rule.mode with
      | Pos ->
        let env = type_spine gamma [] rule.prems tm.spine in
        eval_ty env rule.ty
      | Neg -> raise NotInferable
      | Ersd -> assert false (* signatures should not contain erased rules *) end

and check (gamma : vctx) (tm : term) (vty : vty) : unit =
  Format.printf "%a |- %a <= %a@." pp_vctx gamma pp_term tm pp_vty vty;
  match tm.head with
  | Ix(_) ->
    let vty' = infer gamma tm in equal_vty vty vty' (List.length gamma)
  | Symb(str) ->
    let rule = SignTbl.find str !sign in
    begin match rule.mode with
      | Pos ->
        let vty' = infer gamma tm in equal_vty vty vty' (List.length gamma)
      | Ersd -> assert false
      | Neg ->
        let prevals = match_ty rule.ty vty in
        let prems = Common.remove_last_elems (List.length prevals) rule.prems in
        ignore @@ type_spine gamma prevals prems tm.spine end

and type_spine (gamma : vctx) (prevals : env) (prems : prem list) (e : spine) : env =
  Format.printf "%a | %a |- %a ; %a ~~> ?@."
    pp_vctx gamma pp_prems prems pp_env prevals pp_spine e;
  match prems, e with
  | [], [] -> prevals

  | {ctx = delta; mode = Pos; boundary = ty} :: prems, arg :: e ->
    let prems, k = remove_erased prems in (* removes the {X1 : T1} .. {Xk : Tk} *)
    (* Format.printf "k = %s@." (string_of_int k); *)
    let rho_e = type_spine gamma prevals prems e in

    let rho_e_bot = dummy_env k @ rho_e in

    let delta' = eval_ctx (List.length gamma) rho_e_bot delta in
    let vty = infer (delta' @ gamma) arg.body in

    let gamma_env = env_of_vctx gamma in

    let nu = match_ty ty vty in

    (* because we need a value in gamma, if delta <> [] we need to read it back and
     * then evaluate it once more, this time only in gamma *)
    let nu' =
      if delta = [] then nu
      else nu |> close_env (List.length gamma + k) k |> eval_sp gamma_env in

    let enve = eval_arg gamma_env arg in

    enve :: nu' @ rho_e

  | {ctx = delta; mode = Neg; boundary = ty} :: prems, arg :: e ->
    let rho_e = type_spine gamma prevals prems e in
    let delta' = eval_ctx (List.length gamma) rho_e delta in
    let rho_e' = env_of_vctx delta' @ rho_e in
    let vty = eval_ty rho_e' ty in
    check (delta' @ gamma) arg.body vty;
    let enve = eval_arg (env_of_vctx gamma) arg in
    enve :: rho_e

  | _ -> assert false



(* TESTS *)
let _ =
  let prems = [
    {
      ctx = [Term (var 1)];
      mode = Neg;
      boundary = Term(meta_app 1 [var 0])
    };
    {
      ctx = [Term (var 0)];
      mode = Ersd;
      boundary = Term(cst "Type")
    };
    {
      ctx = [];
      mode = Ersd;
      boundary = Term(cst "Type")
    }
  ] in
  let mode = Neg in
  let ty = Term(pi (var 2) (meta_app 2 [var 0])) in
  sign := SignTbl.add "abs" {prems = prems; mode = mode; ty = ty} !sign

let _ =
  let prems = [
    {
      ctx = [];
      mode = Neg;
      boundary = Term(cst "nat")
    };
    {
      ctx = [];
      mode = Neg;
      boundary = Term(cst "nat")
    }
  ] in
  let mode = Pos in
  let ty = Term(cst "nat") in
  sign := SignTbl.add "plus" {prems = prems; mode = mode; ty = ty} !sign

let _ =
  check [] (abs (var 0)) (eval_ty [] @@ T.Term(pi (cst "a") (cst "a"))); (* \x.x <= a -> a *)
  check [] (abs (abs (plus (var 0) (var 1))))
    (eval_ty [] @@ Term(pi (cst "nat") (pi (cst "nat") (cst "nat")))); (* \x y. y + x *)

  Format.printf "%a@." pp_vty
    @@ infer [({head = Lvl(0); env = []}, eval_ty [] @@ Term(cst "nat"))] (plus (var 0) (var 0))

let _ =
  let prems = [
    {
      ctx = [Term (var 1)];
      mode = Pos;
      boundary = Term(meta_app 1 [var 0])
    };
    {
      ctx = [Term (var 0)];
      mode = Ersd;
      boundary = Term(cst "Type")
    };
    {
      ctx = [];
      mode = Pos;
      boundary = Term(cst "Type")
    }
  ] in
  let mode = Pos in
  let ty = Term(pi (var 2) (meta_app 2 [var 0])) in
  sign := SignTbl.add "abs'" {prems = prems; mode = mode; ty = ty} !sign;
  sign := SignTbl.add "nat" {prems = []; mode = Pos; ty = Term(cst "Type")} !sign

let _ =
  Format.printf "%a@." pp_ty
    @@ read_back_ty 0
    @@ infer [] (abs' (cst "nat") (var 0))


let _ =
  let prems = [
    {
      ctx = [];
      mode = Neg;
      boundary = Term(cst "nat")
    }
  ] in
  let ty = Term(vec (var 0)) in
  sign := SignTbl.add "mk_vec" {prems = prems; mode = Pos; ty = ty} !sign

let _ =
  Format.printf "%a@." pp_ty
    @@ read_back_ty 0
    @@ infer [] (abs' (cst "nat") (mk_vec (plus (var 0) (var 0))))



(*
      let mode, {ctx = delta; ty = ty} = lookup sign ctx tm.head in
  match mode with
  | Pos ->
    let theta = type_spine sign ctx delta tm.spine in
    subst_ty ty theta
  | Neg -> assert false
  | Ersd -> assert false


and check (sign : sign) (ctx : ctx) (tm : term) (ty : ty) : unit =
  let mode, {ctx = delta; ty = ty_sig} = lookup sign ctx tm.head in
  match mode with
  | Pos ->
    let ty' = infer sign ctx tm in equal ty ty'
  | Neg ->
    let theta = match_ty ty ty_sig in
    raise Todo
  | Ersd -> assert false

and type_spine (sign : sign) (gamma : ctx) (delta : ctx) (sp : spine) : spine =
  match delta, sp with
  | [], [] -> []
  | (rule, Pos) :: delta, arg :: sp ->
    let sp' = type_spine sign gamma delta sp in
    let ty' = infer sign (gamma @ (subst_ctx sp' rule.ctx)) arg.body in
    let sp'' = match_ty ty' rule.ty in
    arg :: sp'' @ sp'
  | (rule, Neg) :: delta, arg :: sp ->
    let sp' = type_spine sign gamma delta sp in
    check sign (gamma @ (subst_ctx sp rule.ctx)) arg.body (subst_ty rule.ty sp);
    arg :: sp
  | _ -> assert false
*)
