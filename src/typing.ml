open Term
open Value
open Eval

let remove_last_elems (k : int) l =
  let rec remove_fist_elems k l =
    if k = 0 then l else remove_fist_elems (k - 1) @@ List.tl l in
  l |> List.rev |> remove_fist_elems k |> List.rev

let remove_erased (prems : prem list) : prem list * int =
  let rec removed_erased' (prems : prem list) k =
    match prems with
    | {mode = Ersd; _} :: prems -> removed_erased' prems (k + 1)
    | _ -> prems, k in
  removed_erased' prems 0

let rec dummy_env (size : int) : env =
  if size = 0 then [] else
    Val({head = Symb("DUMMY"); env = []}) :: dummy_env (size - 1)


let lookup_ty (gamma : vctx) (n : int) : vty =
  snd (List.nth gamma n)

exception NotInferable
exception TypingLenghtMismatch
exception SymbolNotDefined of string

let typing_err_mes = false

let get_tm_symb str : tm_symb =
  try
    let symb = SignTbl.find str !sign in
    match symb with
    | Tm_symb(symb) -> symb
    | _ -> failwith "type level constant appears as head of term"
  with Not_found -> raise (SymbolNotDefined(str))

let get_ty_symb str : ty_symb =
  try
    let symb = SignTbl.find str !sign in
    match symb with
    | Ty_symb(symb) -> symb
    | _ -> failwith "term level constant appears as head of type"
  with Not_found -> raise (SymbolNotDefined(str))

let rec infer (gamma : vctx) (tm : term) : vty =
  if typing_err_mes then Format.printf "%a |- %a => ?@." pp_vctx gamma pp_term tm;
  match tm.head with
  | Ix(n) -> lookup_ty gamma n
  | Symb(str) ->
    let symb = get_tm_symb str in
    begin match symb.mode with
      | Pos ->
        let env = type_spine gamma [] symb.prems tm.spine in
        eval_ty env symb.ty
      | Neg -> raise NotInferable
      | Ersd -> assert false (* signatures never contain erased symbs *) end

and check (gamma : vctx) (tm : term) (vty : vty) : unit =
  if typing_err_mes then Format.printf "%a |- %a <= %a@." pp_vctx gamma pp_term tm pp_vty vty;
  match tm.head with
  | Ix(_) ->
    let vty' = infer gamma tm in equal_vty vty vty' (List.length gamma)
  | Symb(str) ->
    let symb = get_tm_symb str in
    begin match symb.mode with
      | Pos ->
        let vty' = infer gamma tm in equal_vty vty vty' (List.length gamma)
      | Ersd -> assert false (* signatures never contain erased symbs *)
      | Neg ->
        let prevals = match_ty symb.ty vty in
        let prems = remove_last_elems (List.length prevals) symb.prems in
        ignore @@ type_spine gamma prevals prems tm.spine end

and check_type (gamma : vctx) (ty : ty) : unit =
  if typing_err_mes then Format.printf "%a |- %a <=> * @." pp_vctx gamma pp_ty ty;
  let symb = get_ty_symb ty.ty_cst in
  ignore @@ type_spine gamma [] symb.prems ty.ty_spine

and type_spine (gamma : vctx) (prevals : env) (prems : prem list) (e : spine) : env =
  if typing_err_mes then Format.printf "%a | %a |- %a ; %a ~~> ?@."
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

  | _ -> raise TypingLenghtMismatch
