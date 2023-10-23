%{

  open Concrete

%}
%token EOF
%token CONS DEST SORT REW LET EVAL CHECK
%token LPAR RPAR LBRACK RBRACK
%token COLON DOT COMMA REDUCES DEF EQUAL
%token <string> IDENT

%start program
%type <entry list> program

%%


term:
  | id=IDENT { NotApplied(id) }
  | id=IDENT LBRACK subst=subst RBRACK { Meta(id, subst) }  
  | id=IDENT LPAR msubst=msubst RPAR { Symb(id, msubst) }
  
subst:
  | e=separated_list(COMMA, term) { List.rev e }

scope:
  | l=nonempty_list(IDENT) { List.rev l }

arg: 
  | t=term { ([], t) }
  | scope=scope DOT t=term { (scope, t) }

msubst: 
  | e=separated_list(COMMA, arg) { List.rev e }


ctx_entry:
  | id=IDENT COLON ty=term { (id, ty) }

ctx: 
  | LBRACK e=separated_list(COMMA, ctx_entry) RBRACK { List.rev e }


mctx_entry:
  | id=IDENT COLON ty=term { (id, [], ty) }
  | id=IDENT ctx=ctx COLON ty=term { (id, ctx, ty) }

mctx: 
  | LPAR e=separated_list(COMMA, mctx_entry) RPAR { List.rev e }  


entry:
  | SORT id=IDENT mctx=mctx { Sort(id, mctx)}
  | CONS id=IDENT mctx1=mctx mctx2=mctx COLON ty=term 
    { Cons(id, mctx1, mctx2, ty) }    
  | DEST id=IDENT mctx1=mctx LPAR id_arg=IDENT COLON ty_arg=term RPAR mctx2=mctx COLON ty=term 
    { Dest(id, mctx1, id_arg, ty_arg, mctx2, ty) }
  | REW lhs=term REDUCES rhs=term { Rew(lhs, rhs) }
  | LET id=IDENT COLON ty=term DEF tm=term
    { Let(id, ty, tm) }  
  | EVAL tm=term
    { Eval(tm) }    
  | CHECK t=term EQUAL u=term { Eq(t, u) }

program:
  | l=list(entry) EOF { l }