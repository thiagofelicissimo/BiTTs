%{

  open Concrete

%}
%token EOF
%token SYMBOL CONS DEST SORT REW LET TYPE EVAL
%token LPAR RPAR RPAR_POS RPAR_NEG LBRACK RBRACK
%token COLON DOT COMMA REDUCES DEF STAR PLUS MINUS
%token <string> IDENT

%start program
%type <entry list> program

%%

term:
  | id=IDENT { {head = id; spine = []} }
  | id=IDENT LPAR e=spine RPAR { {head = id; spine = e} }
  | id=IDENT LBRACK e=spine RBRACK { {head = id; spine = e} }

spine:
  | e=separated_nonempty_list(COMMA, arg) { List.rev e }

arg:
  | t=term { { scope = []; body = t } }
  | scope=scope DOT t=term { {scope = scope; body = t} }

scope:
  | l=nonempty_list(IDENT) { List.rev l }

ty:
  | id=IDENT { {ty_cst = id; ty_spine = []} }
 (* special case for allowing to write Tm A and Prf P instead of Tm(A) and Prf(P)*)
  | id=IDENT t=term { {ty_cst = id; ty_spine = [{scope = []; body = t}]} }
  | id=IDENT LPAR e=spine RPAR { {ty_cst = id; ty_spine = e} }
  | id=IDENT LBRACK e=spine RBRACK { {ty_cst = id; ty_spine = e} }

ctx_entry:
  | id=IDENT COLON ty=ty { (id, ty) }

prem:
  | id=IDENT LBRACK l=separated_list(COMMA, ctx_entry) RBRACK COLON ty=ty { (Neg, id, List.rev l, ty) }
  | id=IDENT COLON ty=ty { (Neg, id, [], ty) }

erased_prem:
  | id=IDENT LBRACK l=separated_list(COMMA, ctx_entry) RBRACK COLON ty=ty { (Ersd, id, List.rev l, ty) }
  | id=IDENT COLON ty=ty { (Ersd, id, [], ty) }  

entry:
  | SORT id=IDENT LPAR prems=separated_list(COMMA, prem) RPAR
    {Ty_symb(id, List.rev prems)}
(*  | SORT id=IDENT  
    {Ty_symb(id, [])}  *)
  | CONS id=IDENT LPAR e_prems=separated_list(COMMA, erased_prem) RPAR LPAR prems=separated_list(COMMA, prem) RPAR COLON ty=ty  
    {Tm_symb(id, Neg, (List.rev prems) @ (List.rev e_prems), ty)}
(*  | CONS id=IDENT LPAR prems=separated_nonempty_list(COMMA, prem) RPAR COLON ty=ty
    {Tm_symb(id, Neg, List.rev prems, ty)} *)
  | DEST id=IDENT LPAR e_prems=separated_list(COMMA, erased_prem) RPAR LPAR id_parg=IDENT COLON ty_arg=ty RPAR LPAR prems=separated_list(COMMA, prem) RPAR COLON ty=ty
    {Tm_symb(id, Pos, (List.rev prems) @ [(Pos, id_parg, [], ty_arg)] @ (List.rev e_prems), ty)}
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
