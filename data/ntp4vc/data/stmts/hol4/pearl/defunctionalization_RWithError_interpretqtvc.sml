(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/defunctionalization_RWithError_interpretqtvc: underflow-aware
  expression evaluation is unchanged by recomposition in the empty context.
  This file contains no proof.
*)

open HolKernel Parse boolLib bossLib;
open integerTheory;

Datatype:
  rwitherror_expr =
    RWithErrorCte int
  | RWithErrorSub rwitherror_expr rwitherror_expr
End

val rwitherror_size_e_def = Define `
  (rwitherror_size_e (RWithErrorCte x) = (1 : int)) /\
  (rwitherror_size_e (RWithErrorSub e1 e2) =
     (3 : int) + rwitherror_size_e e1 + rwitherror_size_e e2)`;

Datatype:
  rwitherror_value =
    RWithErrorVnum int
  | RWithErrorUnderflow
End

val rwitherror_eval_def = Define `
  (rwitherror_eval (RWithErrorCte n) =
     if (0 : int) <= n then RWithErrorVnum n
     else RWithErrorUnderflow) /\
  (rwitherror_eval (RWithErrorSub e1 e2) =
     case rwitherror_eval e1 of
       RWithErrorUnderflow => RWithErrorUnderflow
     | RWithErrorVnum v1 =>
         (case rwitherror_eval e2 of
            RWithErrorUnderflow => RWithErrorUnderflow
          | RWithErrorVnum v2 =>
              if v2 <= v1 then RWithErrorVnum (v1 - v2)
              else RWithErrorUnderflow))`;

Datatype:
  rwitherror_context =
    RWithErrorEmpty
  | RWithErrorLeft rwitherror_context rwitherror_expr
  | RWithErrorRight int rwitherror_context
End

val rwitherror_size_c_def = Define `
  (rwitherror_size_c RWithErrorEmpty = (0 : int)) /\
  (rwitherror_size_c (RWithErrorLeft c1 e) =
     (2 : int) + rwitherror_size_c c1 + rwitherror_size_e e) /\
  (rwitherror_size_c (RWithErrorRight x c1) =
     (1 : int) + rwitherror_size_c c1)`;

val rwitherror_recompose_def = Define `
  (rwitherror_recompose RWithErrorEmpty e = e) /\
  (rwitherror_recompose (RWithErrorLeft c1 e2) e =
     rwitherror_recompose c1 (RWithErrorSub e e2)) /\
  (rwitherror_recompose (RWithErrorRight n1 c1) e =
     rwitherror_recompose c1
       (RWithErrorSub (RWithErrorCte n1) e))`;

val defunctionalization_RWithError_interpret_vc =
  ``!p : rwitherror_expr.
      rwitherror_eval (rwitherror_recompose RWithErrorEmpty p) =
      rwitherror_eval p``;
