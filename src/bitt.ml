module C = Concrete
module T = Term
module V = Value
module Ty = Typing
module P = Parser
module L = Sedlexer
module E = Eval

let colored n s =
  "\027[3" ^ string_of_int n ^ "m" ^ s ^ "\027[m"

let yellow = colored 3
let blue = colored 6
let green = colored 2
let red = colored 1

let syntax_error () = Format.printf "%s: " (red "Syntax error")

let current_entry : C.entry option ref = ref None

let report_error _ =
  match !current_entry with
  | None -> assert false
  | Some entry -> Format.printf "%s@.%a" (yellow "Error while handling the folowing entry:") C.pp_entry entry

let () =
  let input_files : string list ref = ref [] in
  let options = Arg.align [] in
  let usage = "Usage: " ^ Sys.argv.(0) ^ " [FILE]..." in
  Arg.parse options (fun s -> input_files := s :: !input_files) usage;
  try
    List.iter begin fun file ->
      let prog = L.get_concrete_syntax file in
      List.iter begin fun entry ->
        current_entry := Some entry;
        (* C.pp_entry Format.std_formatter entry;*)
        match entry with
        | C.Sort(name, mctx) ->
          let mctx', _ = C.scope_mctx mctx [] in
          T.schem_rules := T.RuleTbl.add name (T.Sort mctx') !T.schem_rules

        | C.Cons(name, mctx_pars, mctx_args, imctx, ty) ->
          let mctx_pars', mscope_pars = C.scope_mctx mctx_pars [] in
          let mctx_args', mscope_pars_args = C.scope_mctx mctx_args mscope_pars in
          let inst_msubst = C.scope_msubst (C.msubst_of_imctx imctx) mscope_pars_args [] in
          let mctx_ixs', mscope_pars_ixs = C.scope_mctx (C.mctx_of_imctx imctx) mscope_pars in
          let ty_p, ty_scope = C.scope_p_tm ty in
          assert (mscope_pars_ixs = ty_scope);
          T.schem_rules :=
            T.RuleTbl.add name (T.Const(List.length inst_msubst, mctx_args', inst_msubst, ty_p)) !T.schem_rules

        | C.Dest(name, mctx_pars, mctx_ixs, name_arg, ty_arg, mctx_args, ty) ->
          let mctx_pars', mscope_pars = C.scope_mctx mctx_pars [] in
          let mctx_ixs', mscope_pars_ixs = C.scope_mctx mctx_ixs mscope_pars in
          let ty_arg_p, arg_mscope = C.scope_p_tm ty_arg in
          assert (mscope_pars_ixs = arg_mscope);
          let mctx_args', mscope_all = C.scope_mctx mctx_args (name_arg :: mscope_pars_ixs) in
          let ty' = C.scope_tm ty mscope_all [] in
          T.schem_rules := T.RuleTbl.add name (T.Dest(ty_arg_p, mctx_args', ty')) !T.schem_rules

        | C.Rew(lhs, rhs) ->
            begin match lhs with
            | Symb(name, msubst) -> begin
              (match T.RuleTbl.find name !T.schem_rules with | Dest(_) -> () | _ -> assert false);
              if msubst = [] then assert false;
              let p_msubst, mscope = C.scope_p_msubst msubst in
              let rhs' = C.scope_tm rhs mscope [] in
              let rews = try T.RewTbl.find name !T.rew_rules with _ -> [] in
              T.rew_rules :=
                T.RewTbl.add name ((p_msubst, rhs') :: rews) !T.rew_rules end
            | _ -> assert false
            end
        | Eval(tm) ->
          let tm = C.scope_tm tm [] [] in
          let vtm = E.eval_tm tm [] [] in
          let tm' = E.read_back_tm 0 vtm in
          Format.printf "[%s] %a -->* %a@." (blue "eval") T.pp_term tm T.pp_term tm'

        | Let(name, ty, tm) ->
          let tm = C.scope_tm tm [] [] in
          let ty = C.scope_tm ty [] [] in
          Ty.check_sort [] [] ty;
          let v_ty = E.eval_tm ty [] [] in
          Ty.check [] [] tm v_ty;
          let v_tm = E.eval_tm tm [] [] in
          V.defs := V.DefTbl.add name {V.rhs = v_tm; ty = v_ty} !V.defs;
          Format.printf "%s %s@." (green "checked definition") name

        | Eq(t, u) ->
          let t' = C.scope_tm t [] [] in
          let u' = C.scope_tm u [] [] in
          E.equal_tm (E.eval_tm t' [] []) (E.eval_tm u' [] []) 0;
          Format.printf "[%s] %a = %a@." (blue "check") T.pp_term t' T.pp_term u'
      end prog
    end !input_files
  with
  | L.SyntaxError(b, e) ->
    let l = b.Lexing.pos_lnum in
    let fc = b.pos_cnum - b.pos_bol + 1 in
    let lc = e.Lexing.pos_cnum - b.pos_bol + 1 in
    syntax_error ();
    Format.printf "line %d, characters %d-%d@." l fc lc
  | e ->
    report_error (); raise e