(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/defunctionalization_ReductionSemantics_interpretqtvc: direct
  expression evaluation is unchanged by recomposition in the empty reduction
  context. This file contains no proof.
*)

open HolKernel Parse boolLib bossLib;
open integerTheory;

Datatype:
  reduction_interpret_expr =
    ReductionInterpretCte int
  | ReductionInterpretSub reduction_interpret_expr reduction_interpret_expr
End

val reduction_interpret_eval_def = Define `
  (reduction_interpret_eval (ReductionInterpretCte n) = n) /\
  (reduction_interpret_eval (ReductionInterpretSub e1 e2) =
     reduction_interpret_eval e1 - reduction_interpret_eval e2)`;

val reduction_interpret_size_e_def = Define `
  (reduction_interpret_size_e (ReductionInterpretCte x) = (1 : int)) /\
  (reduction_interpret_size_e (ReductionInterpretSub e1 e2) =
     (3 : int) +
       reduction_interpret_size_e e1 +
       reduction_interpret_size_e e2)`;

Datatype:
  reduction_interpret_context =
    ReductionInterpretEmpty
  | ReductionInterpretLeft
      reduction_interpret_context reduction_interpret_expr
  | ReductionInterpretRight int reduction_interpret_context
End

val reduction_interpret_recompose_def = Define `
  (reduction_interpret_recompose ReductionInterpretEmpty e = e) /\
  (reduction_interpret_recompose
     (ReductionInterpretLeft c1 e2) e =
     reduction_interpret_recompose c1 (ReductionInterpretSub e e2)) /\
  (reduction_interpret_recompose
     (ReductionInterpretRight n1 c1) e =
     reduction_interpret_recompose c1
       (ReductionInterpretSub (ReductionInterpretCte n1) e))`;

val reduction_interpret_is_a_redex_def = Define `
  reduction_interpret_is_a_redex e <=>
    ?n1 n2 : int.
      e =
        ReductionInterpretSub
          (ReductionInterpretCte n1)
          (ReductionInterpretCte n2)`;

val reduction_interpret_is_a_value_def = Define `
  reduction_interpret_is_a_value e <=>
    ?n : int. e = ReductionInterpretCte n`;

val reduction_interpret_is_empty_context_def = Define `
  reduction_interpret_is_empty_context c <=>
    c = ReductionInterpretEmpty`;

val reduction_interpret_size_c_def = Define `
  (reduction_interpret_size_c ReductionInterpretEmpty = (0 : int)) /\
  (reduction_interpret_size_c (ReductionInterpretLeft c1 e) =
     (2 : int) +
       reduction_interpret_size_c c1 +
       reduction_interpret_size_e e) /\
  (reduction_interpret_size_c (ReductionInterpretRight x c1) =
     (1 : int) + reduction_interpret_size_c c1)`;

val defunctionalization_ReductionSemantics_interpret_vc =
  ``!p : reduction_interpret_expr.
      reduction_interpret_eval
        (reduction_interpret_recompose ReductionInterpretEmpty p) =
      reduction_interpret_eval p``;
