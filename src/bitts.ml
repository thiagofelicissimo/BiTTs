module C = Concrete
module P = Parser
module L = Sedlexer
module H = Handler
open Common

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
    List.iter (fun file ->
      List.iter (fun entry ->
        current_entry := Some entry;
        H.handle_entry entry)
      (L.get_concrete_syntax file))
    !input_files
  with
  | (L.SyntaxError(b, e) as e') ->
    let l = b.Lexing.pos_lnum in
    let fc = b.pos_cnum - b.pos_bol + 1 in
    let lc = e.Lexing.pos_cnum - b.pos_bol + 1 in
    syntax_error ();
    Format.printf "line %d, characters %d-%d@." l fc lc;
    raise e'
  | e ->
    report_error (); raise e