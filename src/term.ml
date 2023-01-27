



type stat =
  | Defined
  | Constant

type head =
  | Symb of string
  | Ix of int

type term =
  {head : head;
   spine : spine}

and spine = arg list

and arg =
  {body : term;
   binds : int}

type ty =
  | Star
  | Ty of term

type mode = Pos | Neg | Ersd

type rule =
  {ctx : ctx;
   ty : ty}
and ctx = (rule * mode) list

type sign = string -> ty
