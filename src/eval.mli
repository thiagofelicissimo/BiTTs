open Term
open Value

exception Matched of v_msubst * tm
exception Match_failure
exception Equality_check_error

val match_tm : p_tm -> v_tm -> v_msubst
val match_msubst : p_msubst -> v_msubst -> v_msubst

val eval_tm : tm -> v_msubst -> v_subst -> v_tm
val eval_subst : subst -> v_msubst -> v_subst -> v_subst
val eval_msubst : msubst -> v_msubst -> v_subst -> v_msubst
val eval_ctx : ctx -> v_msubst -> int -> v_ctx * v_subst * int

val equal_tm : v_tm -> v_tm -> int -> unit
val equal_msubst : v_msubst -> v_msubst -> int -> unit

val read_back_tm : int -> v_tm -> tm
val read_back_msubst : int -> v_msubst -> msubst
