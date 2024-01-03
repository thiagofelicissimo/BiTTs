
type tm =                       
    Var of int
  | Meta of int * subst
  | Const of string * msubst
  | Dest of string * tm * msubst
  | Def of string
and subst = tm list
and msubst = (int * tm) list

type ctx = tm list
type mctx = (ctx * tm) list

type p_tm = Meta | Const of string * p_msubst
and p_msubst = (int * p_tm) list

type schem_rule =
    Sort of mctx
  | Const of mctx * mctx * p_tm
  | Dest of mctx * p_tm * mctx * tm

module RuleTbl : Map.S with type key = string
type schem_rules = schem_rule RuleTbl.t
val schem_rules : schem_rules ref

type rew_rule = p_msubst * tm

module RewTbl : Map.S with type key = string
type rew_rules = rew_rule list RewTbl.t
val rew_rules : rew_rules ref

val separator : Format.formatter -> unit -> unit
val pp_term : Format.formatter -> tm -> unit
val pp_subst : Format.formatter -> subst -> unit
val pp_msubst : Format.formatter -> msubst -> unit
val pp_ctx : Format.formatter -> tm list -> unit
val pp_mctx : Format.formatter -> (tm list * tm) list -> unit
val pp_p_term : Format.formatter -> p_tm -> unit
val pp_p_msubst : Format.formatter -> p_msubst -> unit
