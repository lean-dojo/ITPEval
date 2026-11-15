(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/defunctionalization_ReductionSemantics_eval_1qtvc: a
  reduction-semantics expression-evaluation verification condition combining
  a weighted structural decrease measure with preservation of direct
  evaluation under context recomposition. This file contains no proof.
*)

open HolKernel Parse boolLib bossLib;
open integerTheory;

Datatype:
  reduction_eval_expr =
    ReductionEvalCte int
  | ReductionEvalSub reduction_eval_expr reduction_eval_expr
End

val reduction_eval_eval_def = Define `
  (reduction_eval_eval (ReductionEvalCte n) = n) /\
  (reduction_eval_eval (ReductionEvalSub e1 e2) =
     reduction_eval_eval e1 - reduction_eval_eval e2)`;

val reduction_eval_size_e_def = Define `
  (reduction_eval_size_e (ReductionEvalCte x) = (1 : int)) /\
  (reduction_eval_size_e (ReductionEvalSub e1 e2) =
     (3 : int) +
       reduction_eval_size_e e1 +
       reduction_eval_size_e e2)`;

Datatype:
  reduction_eval_context =
    ReductionEvalEmpty
  | ReductionEvalLeft reduction_eval_context reduction_eval_expr
  | ReductionEvalRight int reduction_eval_context
End

val reduction_eval_recompose_def = Define `
  (reduction_eval_recompose ReductionEvalEmpty e = e) /\
  (reduction_eval_recompose (ReductionEvalLeft c1 e2) e =
     reduction_eval_recompose c1 (ReductionEvalSub e e2)) /\
  (reduction_eval_recompose (ReductionEvalRight n1 c1) e =
     reduction_eval_recompose c1
       (ReductionEvalSub (ReductionEvalCte n1) e))`;

val reduction_eval_size_c_def = Define `
  (reduction_eval_size_c ReductionEvalEmpty = (0 : int)) /\
  (reduction_eval_size_c (ReductionEvalLeft c1 e) =
     (2 : int) +
       reduction_eval_size_c c1 +
       reduction_eval_size_e e) /\
  (reduction_eval_size_c (ReductionEvalRight x c1) =
     (1 : int) + reduction_eval_size_c c1)`;

val defunctionalization_ReductionSemantics_eval_1_vc =
  ``!(e : reduction_eval_expr) (c : reduction_eval_context).
      (case e of
         ReductionEvalCte n =>
           (0 : int) <=
             (2 : int) *
               (reduction_eval_size_c c + reduction_eval_size_e e) /\
           (1 : int) + (2 : int) * reduction_eval_size_c c <
             (2 : int) *
               (reduction_eval_size_c c + reduction_eval_size_e e)
       | ReductionEvalSub e1 e2 =>
           (0 : int) <=
             (2 : int) *
               (reduction_eval_size_c c + reduction_eval_size_e e) /\
           (2 : int) *
               (reduction_eval_size_c (ReductionEvalLeft c e2) +
                reduction_eval_size_e e1) <
             (2 : int) *
               (reduction_eval_size_c c + reduction_eval_size_e e)) /\
      !result : int.
        (case e of
           ReductionEvalCte n =>
             result =
               reduction_eval_eval
                 (reduction_eval_recompose c (ReductionEvalCte n))
         | ReductionEvalSub e1 e2 =>
             result =
               reduction_eval_eval
                 (reduction_eval_recompose
                    (ReductionEvalLeft c e2)
                    e1)) ==>
        result =
          reduction_eval_eval (reduction_eval_recompose c e)``;
