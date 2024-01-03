module T = Term       
module V = Value
module Ty = Typing

exception Name_not_in_scope
exception Dest_not_applied
exception Dest_binds_first_arg
exception Not_a_patt

type tm =
    NotApplied of string
  | Meta of string * subst
  | Symb of string * msubst
and subst = tm list
and msubst = (string list * tm) list

type ctx = (string * tm) list
type mctx = (string * ctx * tm) list

type entry =
    Let of string * tm * tm
  | Sort of string * mctx
  | Cons of string * mctx * mctx * tm
  | Dest of string * mctx * string * tm * mctx * tm
  | Rew of tm * tm
  | Eval of tm
  | Eq of tm * tm

val scope_tm : tm -> string list -> string list -> T.tm
val scope_subst : subst -> string list -> string list -> T.subst
val scope_msubst : msubst -> string list -> string list -> T.msubst
val scope_ctx : ctx -> string list -> T.ctx * string list
val scope_mctx : mctx -> string list -> T.mctx * string list

val scope_p_tm : tm -> T.p_tm * string list
val scope_p_msubst : msubst -> T.p_msubst * string list

val pp_entry : Format.formatter -> entry -> unit
