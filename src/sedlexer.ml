open Parser
open Sedlexing
exception SyntaxError
exception Lexing_error of string

let keyword_or_ident =
  let h = Hashtbl.create 17 in
  List.iter (fun (s, k) -> Hashtbl.add h s k)
    [   "symbol", SYMBOL;
        "rew", REW;
        "let", LET;
        "type", TYPE;
        "eval", EVAL
    ] ;
  fun s ->
    try  Hashtbl.find h s
    with Not_found -> IDENT(s)

let space = [%sedlex.regexp? Chars " \t\n\r"]

let forbidden_letter1 = [%sedlex.regexp? Chars " +-*:,\r\t\n(){}:.`\"@|/"]
let forbidden_letter = [%sedlex.regexp? Chars " *:=>,;\r\t\n(){}[]:.`\"@|/"]
let name = [%sedlex.regexp? (Compl forbidden_letter1) | Star (Compl forbidden_letter1)]

let rec token lb =
  match%sedlex lb with
  | eof -> EOF
  | space -> token lb
  | "(*" -> comment token 0 lb
  | "(" -> LPAR
  | ")" -> RPAR
  | ")+" -> RPAR_POS
  | ")-" -> RPAR_NEG
  | "{"  -> LBRACK
  | "}"  -> RBRACK
  | ":" -> COLON
  | "." -> DOT
  | "," -> COMMA
  | "-->" -> REDUCES
  | ":=" -> DEF
  | "*" -> STAR
  | "+" -> PLUS
  | "-" -> MINUS
  | name -> keyword_or_ident (Utf8.lexeme lb)
  | _ -> raise SyntaxError
and comment next i lb =
  match%sedlex lb with
  | eof -> raise SyntaxError
  | "*)" -> if i=0 then next lb else comment next (i-1) lb
  | "(*" -> comment next (i+1) lb
  | any -> comment next i lb
  | _ -> raise SyntaxError

let get_concrete_syntax filename =
  let lexbuf = Sedlexing.Utf8.from_channel @@ open_in filename in
  let lexer  = Sedlexing.with_tokenizer token lexbuf in
  let parser = MenhirLib.Convert.Simplified.traditional2revised program in
  parser lexer