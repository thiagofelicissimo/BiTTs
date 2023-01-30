%{

  open Lexing
  open Concrete

%}
%token EOF
%token RULE REW LET
%token LPAR RPAR RPAR_POS RPAR_NEG LBRACK RBRACK
%token COLON SEMICOLON DOT COMMA BACKSLASH ARROW DEF STAR PLUS MINUS
%token <string> IDENT

%start program
%type <entry list> program

%%

term:
  | id=IDENT { {head = id; spine = []} }
  | id=IDENT LPAR e=spine RPAR { {head = id; spine = e} }

spine:
  | e=separated_nonempty_list(COMMA, arg) { List.rev e }

arg:
  | t=term { { scope = []; body = t } }
  | BACKSLASH scope=scope DOT t=term { {scope = scope; body = t} }

scope:
  | l=nonempty_list(IDENT) { List.rev l }

ty:
  | STAR { Star }
  | tm=term { Term(tm) }

ctx_entry:
  | id=IDENT COLON ty=ty { (id, ty) }

ctx:
  | LPAR l=separated_nonempty_list(COMMA, ctx_entry) RPAR { List. rev l }

prem:
  | LPAR id=IDENT COLON ctx=ctx ty=ty RPAR_POS { (Pos, id, ctx, ty) }
  | LPAR id=IDENT COLON ctx=ctx ty=ty RPAR_NEG { (Neg, id, ctx, ty) }
  | LBRACK id=IDENT COLON ctx=ctx ty=ty RBRACK { (Ersd, id, ctx, ty) }
  | LPAR id=IDENT COLON ty=ty RPAR_POS { (Pos, id, [], ty) }
  | LPAR id=IDENT COLON ty=ty RPAR_NEG { (Neg, id, [], ty) }
  | LBRACK id=IDENT COLON ty=ty RBRACK { (Ersd, id, [], ty) }

pol:
  | PLUS { Pos }
  | MINUS { Neg }

entry:
  | RULE id=IDENT pol=pol prems=list(prem) COLON ty=ty SEMICOLON
    { Rule(id, pol, List.rev prems, ty) }
  | REW lhs=term ARROW rhs=term SEMICOLON
    { Rew(lhs, rhs) }
  | LET id=IDENT COLON ty=ty DEF tm=term SEMICOLON
    { Let(id, Some(ty), tm) }
  | LET id=IDENT DEF tm=term SEMICOLON
    { Let(id, None, tm) }

program:
  | l=list(entry) EOF { l }
