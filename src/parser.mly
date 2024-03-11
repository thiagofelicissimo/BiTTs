%{

  open Concrete

%}
%token EOF
%token CONS DEST SORT REW LET EVAL ASSERT IN
%token LPAR RPAR LBRACK RBRACK LSQB RSQB
%token COLON DOT COMMA REDUCES DEF EQUAL SLASH COCOLON
%token <string> IDENT

%nonassoc IN
%nonassoc COCOLON

%start program
%type <entry list> program

%%


term:
  | t=term COCOLON ty=term { Ascr(t, ty) }
  | LET id=IDENT COLON ty=term DEF t=term IN u=term
  { Let(id, Ascr(t, ty), u) }
  | LET id=IDENT DEF t=term IN u=term
  { Let(id, t, u) }
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

imctx_entry:
  | t=term SLASH id=IDENT COLON ty=term { (id, t, ty) }

imctx:
  | LPAR e=separated_list(COMMA, imctx_entry) RPAR  { List.rev e }

entry:
  | SORT id=IDENT mctx=mctx { Sort(id, mctx)}
  | CONS id=IDENT mctx1=mctx mctx2=mctx COLON ty=term
    { Cons(id, mctx1, mctx2, [], ty) }
  | CONS id=IDENT mctx1=mctx mctx2=mctx imctx=imctx COLON ty=term
    { Cons(id, mctx1, mctx2, imctx, ty) }
  | DEST id=IDENT mctx1=mctx LSQB id_arg=IDENT COLON ty_arg=term RSQB mctx2=mctx COLON ty=term
    { Dest(id, mctx1, id_arg, ty_arg, mctx2, ty) }
  | REW lhs=term REDUCES rhs=term { Rew(None, lhs, rhs) }
  | LET id=IDENT COLON ty=term DEF tm=term
    { Let(id, [], ty, tm) }
  | LET id=IDENT mctx=mctx COLON ty=term DEF tm=term
    { Let(id, mctx, ty, tm) }
  | EVAL tm=term
    { Eval(tm) }
  | ASSERT t=term EQUAL u=term { Eq(t, u) }

program:
  | l=list(entry) EOF { l }