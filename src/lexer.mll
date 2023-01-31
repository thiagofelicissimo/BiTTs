{
  open Lexing
  open Parser

  exception Lexing_error of string

  let keyword_or_ident =
    let h = Hashtbl.create 17 in
    List.iter (fun (s, k) -> Hashtbl.add h s k)
      [   "rule", RULE;
          "rew", REW;
          "let", LET;
          "type", TYPE;
          "eval", EVAL
      ] ;
    fun s ->
      try  Hashtbl.find h s
      with Not_found -> IDENT(s)
}


let ident = ['a'-'z' '_' 'A'-'Z' '0'-'9' '$'] ['a'-'z' '_' 'A'-'Z' '0'-'9']*


rule token = parse
  | ['\n'] { new_line lexbuf; token lexbuf }
  | [' ' '\t' '\r']+ { token lexbuf }
  | "(*" { comment lexbuf; token lexbuf }
  | ident as id { keyword_or_ident id }
  | "(" { LPAR }
  | ")" { RPAR }
  | ")+" { RPAR_POS }
  | ")-" { RPAR_NEG }
  | "{"  { LBRACK }
  | "}"  { RBRACK }
  | ":" { COLON }
  | "." { DOT }
  | "," { COMMA }
  | "->" { ARROW }
  | ":=" { DEF }
  | "*" { STAR }
  | "+" { PLUS }
  | "-" { MINUS }
  | eof { EOF }

and comment = parse
  | "*)"  { () }
  | "(*"  { comment lexbuf; comment lexbuf }
  | _     { comment lexbuf }
  | eof   { raise (Lexing_error "unterminated comment") }
