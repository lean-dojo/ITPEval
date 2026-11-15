(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/defunctionalization_RWithError_eval_1qtvc: an underflow-aware
  defunctionalized expression-evaluation verification condition combining a
  structural termination measure with correctness of context recomposition.
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

val defunctionalization_RWithError_eval_1_vc =
  ``!(e : rwitherror_expr) (c : rwitherror_context).
      (case e of
         RWithErrorCte n =>
           (0 : int) <= n ==>
           (((0 : int) <=
               (2 : int) *
                 (rwitherror_size_c c + rwitherror_size_e e) /\
             (1 : int) + (2 : int) * rwitherror_size_c c <
               (2 : int) *
                 (rwitherror_size_c c + rwitherror_size_e e)) /\
            (0 : int) <= n)
       | RWithErrorSub e1 e2 =>
           (0 : int) <=
             (2 : int) *
               (rwitherror_size_c c + rwitherror_size_e e) /\
           (2 : int) *
               (rwitherror_size_c (RWithErrorLeft c e2) +
                rwitherror_size_e e1) <
             (2 : int) *
               (rwitherror_size_c c + rwitherror_size_e e)) /\
      !result : rwitherror_value.
        (case e of
           RWithErrorCte n =>
             if (0 : int) <= n then
               result =
                 rwitherror_eval
                   (rwitherror_recompose c (RWithErrorCte n))
             else
               result = RWithErrorUnderflow
         | RWithErrorSub e1 e2 =>
             result =
               rwitherror_eval
                 (rwitherror_recompose
                    (RWithErrorLeft c e2)
                    e1)) ==>
        result = rwitherror_eval (rwitherror_recompose c e)``;
