(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/defunctionalization_ReductionSemantics_eval_2qtvc: a
  reduction-semantics continuation-evaluation verification condition
  combining a weighted structural decrease measure with preservation of
  direct evaluation under context recomposition. This file contains no proof.
*)

open HolKernel Parse boolLib bossLib;
open integerTheory;

Datatype:
  reduction_eval2_expr =
    ReductionEval2Cte int
  | ReductionEval2Sub reduction_eval2_expr reduction_eval2_expr
End

val reduction_eval2_eval_def = Define `
  (reduction_eval2_eval (ReductionEval2Cte n) = n) /\
  (reduction_eval2_eval (ReductionEval2Sub e1 e2) =
     reduction_eval2_eval e1 - reduction_eval2_eval e2)`;

val reduction_eval2_size_e_def = Define `
  (reduction_eval2_size_e (ReductionEval2Cte x) = (1 : int)) /\
  (reduction_eval2_size_e (ReductionEval2Sub e1 e2) =
     (3 : int) +
       reduction_eval2_size_e e1 +
       reduction_eval2_size_e e2)`;

Datatype:
  reduction_eval2_context =
    ReductionEval2Empty
  | ReductionEval2Left reduction_eval2_context reduction_eval2_expr
  | ReductionEval2Right int reduction_eval2_context
End

val reduction_eval2_recompose_def = Define `
  (reduction_eval2_recompose ReductionEval2Empty e = e) /\
  (reduction_eval2_recompose (ReductionEval2Left c1 e2) e =
     reduction_eval2_recompose c1 (ReductionEval2Sub e e2)) /\
  (reduction_eval2_recompose (ReductionEval2Right n1 c1) e =
     reduction_eval2_recompose c1
       (ReductionEval2Sub (ReductionEval2Cte n1) e))`;

val reduction_eval2_size_c_def = Define `
  (reduction_eval2_size_c ReductionEval2Empty = (0 : int)) /\
  (reduction_eval2_size_c (ReductionEval2Left c1 e) =
     (2 : int) +
       reduction_eval2_size_c c1 +
       reduction_eval2_size_e e) /\
  (reduction_eval2_size_c (ReductionEval2Right x c1) =
     (1 : int) + reduction_eval2_size_c c1)`;

val defunctionalization_ReductionSemantics_eval_2_vc =
  ``!(c : reduction_eval2_context) (n : int).
      (case c of
         ReductionEval2Empty => T
       | ReductionEval2Left c1 e =>
           (0 : int) <=
             (1 : int) + (2 : int) * reduction_eval2_size_c c /\
           (2 : int) *
               (reduction_eval2_size_c (ReductionEval2Right n c1) +
                reduction_eval2_size_e e) <
             (1 : int) + (2 : int) * reduction_eval2_size_c c
       | ReductionEval2Right n1 c1 =>
           (0 : int) <=
             (1 : int) + (2 : int) * reduction_eval2_size_c c /\
           (2 : int) *
               (reduction_eval2_size_c c1 +
                reduction_eval2_size_e (ReductionEval2Cte (n1 - n))) <
             (1 : int) + (2 : int) * reduction_eval2_size_c c) /\
      !result : int.
        (case c of
           ReductionEval2Empty =>
             result = n
         | ReductionEval2Left c1 e =>
             result =
               reduction_eval2_eval
                 (reduction_eval2_recompose
                    (ReductionEval2Right n c1)
                    e)
         | ReductionEval2Right n1 c1 =>
             result =
               reduction_eval2_eval
                 (reduction_eval2_recompose
                    c1
                    (ReductionEval2Cte (n1 - n)))) ==>
        result =
          reduction_eval2_eval
            (reduction_eval2_recompose c (ReductionEval2Cte n))``;
