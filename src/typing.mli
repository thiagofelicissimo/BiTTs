open Term
open Value

exception Not_inferable         
exception Not_a_sort
exception Metas_not_supported
exception Length_mismatch

val infer : v_ctx -> v_subst -> tm -> v_tm
val check : v_ctx -> v_subst -> tm -> v_tm -> unit
val check_msubst : v_ctx -> v_subst -> v_msubst -> msubst -> mctx -> v_msubst
val check_sort : v_ctx -> v_subst -> tm -> unit
