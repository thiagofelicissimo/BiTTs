module C = Concrete
module T = Term
module Ty = Typing
module P = Parser
(* module L = Lexer *)
module E = Eval


let () =
  let input_files : string list ref = ref [] in
  let options = Arg.align [] in
  let usage = "Usage: " ^ Sys.argv.(0) ^ " [FILE]..." in
  Arg.parse options (fun s -> input_files := s :: !input_files) usage;
  List.iter begin fun file ->
    let prog = Sedlexer.get_concrete_syntax file in
    (*let prog = P.program L.token @@ Lexing.from_channel @@ open_in file in (*"test.thry"*) *)
    List.iter begin fun entry ->
      (*  Format.printf "%a" C.pp_entry entry;*)
      match entry with
      | C.Rule(name, mode, prems, ty) ->
        let rule = C.scope_rule mode prems ty in
        T.sign := T.SignTbl.add name rule !T.sign
      | C.Rew(lhs, rhs) ->
        let head_symb, rew = C.scope_rew lhs rhs in
        let rews = try T.RewTbl.find head_symb !T.rew_map with _ -> [] in
        T.rew_map := T.RewTbl.add head_symb (rew :: rews) !T.rew_map
      | Let(name, None, tm) ->
        let tm = C.scope_tm [] tm in
        let vty =  Ty.infer [] tm in
        let ty = E.read_back_ty 0 vty in
        T.sign := T.SignTbl.add name {T.prems = []; T.mode = T.Pos; T.ty = ty} !T.sign;
        T.rew_map := T.RewTbl.add name [{T.lhs_spine = []; T.rhs = tm}] !T.rew_map
      | Let(name, Some ty, tm) ->
        let tm = C.scope_tm [] tm in
        let ty = C.scope_ty [] ty in
        Ty.check_type [] ty;
        let vty = E.eval_ty [] ty in
        Ty.check [] tm vty;
        T.sign := T.SignTbl.add name {T.prems = []; T.mode = T.Pos; T.ty = ty} !T.sign;
        T.rew_map := T.RewTbl.add name [{T.lhs_spine = []; T.rhs = tm}] !T.rew_map
      | Type(ctm) ->
        let tm = C.scope_tm [] ctm in
        let vty = Ty.infer [] tm in
        let ty = E.read_back_ty 0 vty in
        Format.printf "[type] %a : %a@." T.pp_term tm T.pp_ty ty
      | Eval(ctm) ->
        let tm = C.scope_tm [] ctm in
        let vtm = E.eval_tm [] tm in
        let tm' = E.read_back_tm 0 vtm in
        Format.printf "[eval] %a -->* %a@." T.pp_term tm T.pp_term tm'
    end prog
  end !input_files
