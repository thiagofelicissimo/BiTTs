open Term


type vhead =
  | Symb of string
  | Var of string

type value =
  {head : vhead;
   spine : env}

and env = enventry list

and enventry =
  | Value of value
  | Clo of closure

and closure =
  {binds : int;
   body : term;
   env : env
  }

(*
type aty =
  | Star
  | Aty of term

type mode = Pos | Neg | Ersd

type ty =
  {ctx : ctx;
   codom : ty}
and ctx = (ty * mode) list

type signature = string -> ty
*)
