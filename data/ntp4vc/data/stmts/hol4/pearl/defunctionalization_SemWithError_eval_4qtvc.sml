(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/defunctionalization_SemWithError_eval_4qtvc: an underflow-aware
  defunctionalized expression-evaluation verification condition combining
  structural size decrease with preservation of the continuation evaluation
  relation. This file contains no proof.
*)

open HolKernel Parse boolLib bossLib;
open integerTheory;

Datatype:
  semwitherror_eval4_expr =
    SemWithErrorEval4Cte int
  | SemWithErrorEval4Sub semwitherror_eval4_expr semwitherror_eval4_expr
End

Datatype:
  semwitherror_eval4_value =
    SemWithErrorEval4Vnum int
  | SemWithErrorEval4Underflow
End

val semwitherror_eval4_eval_def = Define `
  (semwitherror_eval4_eval (SemWithErrorEval4Cte n) =
     if (0 : int) <= n then SemWithErrorEval4Vnum n
     else SemWithErrorEval4Underflow) /\
  (semwitherror_eval4_eval (SemWithErrorEval4Sub e1 e2) =
     case semwitherror_eval4_eval e1 of
       SemWithErrorEval4Underflow => SemWithErrorEval4Underflow
     | SemWithErrorEval4Vnum v1 =>
         (case semwitherror_eval4_eval e2 of
            SemWithErrorEval4Underflow => SemWithErrorEval4Underflow
          | SemWithErrorEval4Vnum v2 =>
              if v2 <= v1 then SemWithErrorEval4Vnum (v1 - v2)
              else SemWithErrorEval4Underflow))`;

val semwitherror_eval4_defunctionalization_size_e_def = Define `
  (semwitherror_eval4_defunctionalization_size_e
     (SemWithErrorEval4Cte x) = (1 : int)) /\
  (semwitherror_eval4_defunctionalization_size_e
     (SemWithErrorEval4Sub e1 e2) =
     (3 : int) +
       semwitherror_eval4_defunctionalization_size_e e1 +
       semwitherror_eval4_defunctionalization_size_e e2)`;

val semwitherror_eval4_size_e_def = Define `
  (semwitherror_eval4_size_e (SemWithErrorEval4Cte x) = (1 : int)) /\
  (semwitherror_eval4_size_e (SemWithErrorEval4Sub e1 e2) =
     (3 : int) +
       semwitherror_eval4_size_e e1 +
       semwitherror_eval4_size_e e2)`;

Datatype:
  semwitherror_eval4_cont =
    SemWithErrorEval4I
  | SemWithErrorEval4A semwitherror_eval4_expr semwitherror_eval4_cont
  | SemWithErrorEval4B int semwitherror_eval4_cont
End

val (semwitherror_eval4_eval_cont_rules,
     semwitherror_eval4_eval_cont_ind,
     semwitherror_eval4_eval_cont_cases) =
  Hol_reln `
    (!k.
       semwitherror_eval4_eval_cont
         k
         SemWithErrorEval4Underflow
         SemWithErrorEval4Underflow) /\
    (!v k e2 r.
       semwitherror_eval4_eval_cont
         (SemWithErrorEval4B v k)
         (semwitherror_eval4_eval e2)
         r ==>
       semwitherror_eval4_eval_cont
         (SemWithErrorEval4A e2 k)
         (SemWithErrorEval4Vnum v)
         r) /\
    (!k v v1 r.
       semwitherror_eval4_eval_cont
         k
         (if v <= v1 then SemWithErrorEval4Vnum (v1 - v)
          else SemWithErrorEval4Underflow)
         r ==>
       semwitherror_eval4_eval_cont
         (SemWithErrorEval4B v1 k)
         (SemWithErrorEval4Vnum v)
         r) /\
    (!v.
       semwitherror_eval4_eval_cont
         SemWithErrorEval4I
         (SemWithErrorEval4Vnum v)
         (SemWithErrorEval4Vnum v))
  `;

val semwitherror_eval4_size_c_def = Define `
  (semwitherror_eval4_size_c SemWithErrorEval4I = (0 : int)) /\
  (semwitherror_eval4_size_c (SemWithErrorEval4A e2 k) =
     (2 : int) +
       semwitherror_eval4_defunctionalization_size_e e2 +
       semwitherror_eval4_size_c k) /\
  (semwitherror_eval4_size_c (SemWithErrorEval4B x k) =
     (1 : int) + semwitherror_eval4_size_c k)`;

val defunctionalization_SemWithError_eval_4_vc =
  ``!(e : semwitherror_eval4_expr) (c : semwitherror_eval4_cont).
      (case e of
         SemWithErrorEval4Cte n =>
           (0 : int) <= n ==>
           (((0 : int) <=
               semwitherror_eval4_size_c c +
               semwitherror_eval4_defunctionalization_size_e e /\
             semwitherror_eval4_size_c c <
               semwitherror_eval4_size_c c +
               semwitherror_eval4_defunctionalization_size_e e) /\
            (0 : int) <= n)
       | SemWithErrorEval4Sub e1 e2 =>
           (0 : int) <=
             semwitherror_eval4_size_c c +
             semwitherror_eval4_defunctionalization_size_e e /\
           semwitherror_eval4_size_c (SemWithErrorEval4A e2 c) +
             semwitherror_eval4_defunctionalization_size_e e1 <
           semwitherror_eval4_size_c c +
             semwitherror_eval4_defunctionalization_size_e e) /\
      !result : semwitherror_eval4_value.
        (case e of
           SemWithErrorEval4Cte n =>
             if (0 : int) <= n then
               semwitherror_eval4_eval_cont
                 c
                 (SemWithErrorEval4Vnum n)
                 result
             else
               result = SemWithErrorEval4Underflow
         | SemWithErrorEval4Sub e1 e2 =>
             semwitherror_eval4_eval_cont
               (SemWithErrorEval4A e2 c)
               (semwitherror_eval4_eval e1)
               result) ==>
        semwitherror_eval4_eval_cont
          c
          (semwitherror_eval4_eval e)
          result``;
