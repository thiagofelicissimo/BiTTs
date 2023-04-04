module C = Concrete
module T = Term
module Ty = Typing
module P = Parser
module L = Sedlexer
module E = Eval

let colored n s =
  "\027[3" ^ string_of_int n ^ "m" ^ s ^ "\027[m"

let yellow = colored 3
let blue = colored 6
let red = colored 1
(* currently not used
let violet = colored 5
let green = colored 2 *)

let typing_error () = Format.printf "%s: " (red "Typing error")
let equality_error () = Format.printf "%s: " (red "Equality checking error")
let matching_error () = Format.printf "%s: " (red "Matching error")
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
      (*let prog = P.program L.token @@ Lexing.from_channel @@ open_in file in (*"test.thry"*) *)
      List.iter begin fun entry ->
        (*  Format.printf "%a" C.pp_entry entry;*)
        current_entry := Some entry;
        match entry with
        | C.Tm_symb(name, mode, prems, ty) ->
          let symb = C.scope_tm_symb mode prems ty in
          T.sign := T.SignTbl.add name (T.Tm_symb symb) !T.sign
        | C.Ty_symb(name, prems) ->
          let symb = C.scope_ty_symb prems in
          T.sign := T.SignTbl.add name (T.Ty_symb symb) !T.sign
        | C.Rew(lhs, rhs) ->
          let head_symb, rew = C.scope_rew lhs rhs in
          let rews = try T.RewTbl.find head_symb !T.rew_map with _ -> [] in
          T.rew_map := T.RewTbl.add head_symb (rew :: rews) !T.rew_map
        | Let(name, None, tm) ->
          let tm = C.scope_tm [] tm in
          let vty =  Ty.infer [] tm in
          let ty = E.read_back_ty 0 vty in
          T.sign := T.SignTbl.add name (T.Tm_symb {T.prems = []; T.mode = T.Pos; T.ty = ty}) !T.sign;
          T.rew_map := T.RewTbl.add name [{T.lhs_spine = []; T.rhs = tm}] !T.rew_map
        | Let(name, Some ty, tm) ->
          let tm = C.scope_tm [] tm in
          let ty = C.scope_ty [] ty in
          Ty.check_type [] ty;
          let vty = E.eval_ty [] ty in
          Ty.check [] tm vty;
          T.sign := T.SignTbl.add name (T.Tm_symb {T.prems = []; T.mode = T.Pos; T.ty = ty}) !T.sign;
          T.rew_map := T.RewTbl.add name [{T.lhs_spine = []; T.rhs = tm}] !T.rew_map
        | Type(ctm) ->
          let tm = C.scope_tm [] ctm in
          let vty = Ty.infer [] tm in
          let ty = E.read_back_ty 0 vty in
          Format.printf "[%s] %a : %a@." (blue "type") (T.ppn_term 0) tm (T.ppn_ty 0) ty
        | Eval(ctm) ->
          let tm = C.scope_tm [] ctm in
          let vtm = E.eval_tm [] tm in
          let tm' = E.read_back_tm 0 vtm in
          Format.printf "[%s] %a -->* %a@." (blue "eval") (T.ppn_term 0) tm (T.ppn_term 0) tm'
      end prog
    end !input_files
  with
  | E.NotEqualValue(v, v', d) ->
    report_error ();
    let tm = E.read_back_tm d v in
    let tm' = E.read_back_tm d v' in
    equality_error ();
    Format.printf "%a != %a@." T.pp_term tm T.pp_term tm'
  | E.NotEqualEnv(e, e', d) ->
    report_error ();
    let e = E.read_back_sp d e in
    let e' = E.read_back_sp d e' in
    equality_error ();
    Format.printf "%a != %a@." T.pp_spine e T.pp_spine e'
  | E.NotEqualVTy(vty, vty', d) ->
    report_error ();
    let ty = E.read_back_ty d vty in
    let ty' = E.read_back_ty d vty' in
    equality_error ();
    Format.printf "%a != %a@." T.pp_ty ty T.pp_ty ty'
  | E.NoMatchTm(t, v) ->
    report_error ();
    let t' = E.read_back_tm 0 v in
    matching_error ();
    Format.printf "%a !< %a@." T.pp_term t T.pp_term t'
  | E.NoMatchSp(e, env) ->
    report_error ();
    let e' = E.read_back_sp 0 env in
    matching_error ();
    Format.printf "%a !< %a@." T.pp_spine e T.pp_spine e'
  | E.NoMatchTy(ty, vty) ->
    report_error ();
    let ty' = E.read_back_ty 0 vty in
    matching_error ();
    Format.printf "%a !< %a@." T.pp_ty ty T.pp_ty ty'
  | Ty.NotInferable ->
    report_error ();
    typing_error ();
    Format.printf "A part of the term that should be inferable cannot synthetize a type@."
  | Ty.TypingLenghtMismatch ->
    report_error ();
    typing_error ();
    Format.printf "Some spine does not match the expected length of the corresponding symbol@."
  | Ty.BindingLengthMismatch ->
    report_error ();
    typing_error ();
    Format.printf "Some argument of a symbol binds a different number of variables then it should@."
  | L.SyntaxError(b, e) ->
    let l = b.Lexing.pos_lnum in
    let fc = b.pos_cnum - b.pos_bol + 1 in
    let lc = e.Lexing.pos_cnum - b.pos_bol + 1 in
    syntax_error ();
    Format.printf "line %d, characters %d-%d@." l fc lc
  | Ty.SymbolNotDefined s ->
    report_error ();
    typing_error ();
    Format.printf "The name %s is not defined@." s
