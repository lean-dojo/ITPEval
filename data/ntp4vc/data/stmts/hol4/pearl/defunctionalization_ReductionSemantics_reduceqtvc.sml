(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/defunctionalization_ReductionSemantics_reduceqtvc: a reduction
  semantics verification condition stating that replacing a subtraction
  redex by any expression with the same direct value preserves the value of
  the expression recomposed in its context. This file contains no proof.
*)

open HolKernel Parse boolLib bossLib;
open integerTheory;

Datatype:
  reduction_reduce_expr =
    ReductionReduceCte int
  | ReductionReduceSub reduction_reduce_expr reduction_reduce_expr
End

val reduction_reduce_eval_def = Define `
  (reduction_reduce_eval (ReductionReduceCte n) = n) /\
  (reduction_reduce_eval (ReductionReduceSub e1 e2) =
     reduction_reduce_eval e1 - reduction_reduce_eval e2)`;

Datatype:
  reduction_reduce_context =
    ReductionReduceEmpty
  | ReductionReduceLeft reduction_reduce_context reduction_reduce_expr
  | ReductionReduceRight int reduction_reduce_context
End

val reduction_reduce_recompose_def = Define `
  (reduction_reduce_recompose ReductionReduceEmpty e = e) /\
  (reduction_reduce_recompose (ReductionReduceLeft c1 e2) e =
     reduction_reduce_recompose c1 (ReductionReduceSub e e2)) /\
  (reduction_reduce_recompose (ReductionReduceRight n1 c1) e =
     reduction_reduce_recompose c1
       (ReductionReduceSub (ReductionReduceCte n1) e))`;

val reduction_reduce_is_redex_def = Define `
  reduction_reduce_is_redex e =
    ?n1 n2.
      e =
        ReductionReduceSub
          (ReductionReduceCte n1)
          (ReductionReduceCte n2)`;

val defunctionalization_ReductionSemantics_reduce_vc =
  ``!(c : reduction_reduce_context)
      (r : reduction_reduce_expr)
      (e : reduction_reduce_expr).
      reduction_reduce_recompose c r = e ==>
      reduction_reduce_is_redex r ==>
      reduction_reduce_is_redex r /\
      !result : reduction_reduce_expr.
        (?o1 : reduction_reduce_expr.
           reduction_reduce_eval o1 = reduction_reduce_eval r /\
           result = reduction_reduce_recompose c o1) ==>
        reduction_reduce_eval result = reduction_reduce_eval e``;
