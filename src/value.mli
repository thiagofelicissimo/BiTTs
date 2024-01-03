module T = Term       

type v_tm =
    Var of int
  | Const of string * v_msubst
  | Dest of string * v_tm * v_msubst
and v_subst = v_tm list
and v_arg = Value of v_tm | Closure of int * T.tm * v_msubst * v_subst
and v_msubst = v_arg list

type v_ctx = v_tm list
module DefTbl : Map.S with type key = string

type def = { rhs : v_tm; ty : v_tm; }
type defs = def DefTbl.t
val defs : defs ref

val pp_vterm : Format.formatter -> v_tm -> unit
val pp_vsubst : Format.formatter -> v_subst -> unit
val pp_vmsubst : Format.formatter -> v_msubst -> unit
