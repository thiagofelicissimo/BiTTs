%{

  open Lexing
  open Concrete

%}
%token EOF
%token SYMBOL REW LET TYPE EVAL
%token LPAR RPAR RPAR_POS RPAR_NEG LBRACK RBRACK
%token COLON DOT COMMA REDUCES DEF STAR PLUS MINUS
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
  | scope=scope DOT t=term { {scope = scope; body = t} }

scope:
  | l=nonempty_list(IDENT) { List.rev l }

ty:
  | STAR { Star }
  | tm=term { Term(tm) }
  | id=IDENT t=term { Term({head = id; spine = [{scope = []; body = t}]}) }

ctx_entry:
  | id=IDENT COLON ty=ty { (id, ty) }

ctx:
  | LPAR l=separated_nonempty_list(COMMA, ctx_entry) RPAR { List. rev l }

prem:
  | LPAR id=IDENT COLON ctx=ctx ty=ty RPAR_POS { (Pos, id, ctx, ty) }
  | LPAR id=IDENT COLON ctx=ctx ty=ty RPAR { (Neg, id, ctx, ty) }
  | LPAR id=IDENT COLON ctx=ctx ty=ty RPAR_NEG { (Neg, id, ctx, ty) }
  | LBRACK id=IDENT COLON ctx=ctx ty=ty RBRACK { (Ersd, id, ctx, ty) }
  | LPAR id=IDENT COLON ty=ty RPAR_POS { (Pos, id, [], ty) }
  | LPAR id=IDENT COLON ty=ty RPAR { (Neg, id, [], ty) }
  | LPAR id=IDENT COLON ty=ty RPAR_NEG { (Neg, id, [], ty) }
  | LBRACK id=IDENT COLON ty=ty RBRACK { (Ersd, id, [], ty) }

pol:
  | PLUS { Pos }
  | MINUS { Neg }

entry:
  | SYMBOL pol=pol id=IDENT prems=list(prem) COLON ty=ty
    { Rule(id, pol, List.rev prems, ty) }
  | SYMBOL id=IDENT prems=list(prem) COLON ty=ty
    { Rule(id, Pos, List.rev prems, ty) }
  | REW lhs=term REDUCES rhs=term
    { Rew(lhs, rhs) }
  | LET id=IDENT COLON ty=ty DEF tm=term
    { Let(id, Some(ty), tm) }
  | LET id=IDENT DEF tm=term
    { Let(id, None, tm) }
  | TYPE tm=term
    { Type(tm) }
  | EVAL tm=term
    { Eval(tm) }

program:
  | l=list(entry) EOF { l }
