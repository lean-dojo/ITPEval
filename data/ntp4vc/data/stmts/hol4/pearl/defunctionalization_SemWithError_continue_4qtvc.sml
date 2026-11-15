(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/defunctionalization_SemWithError_continue_4qtvc: an underflow-aware
  defunctionalized continuation verification condition combining structural
  size decrease with preservation of the continuation evaluation relation.
  This file contains no proof.
*)

open HolKernel Parse boolLib bossLib;
open integerTheory;

Datatype:
  semwitherror_expr =
    SemWithErrorCte int
  | SemWithErrorSub semwitherror_expr semwitherror_expr
End

Datatype:
  semwitherror_value =
    SemWithErrorVnum int
  | SemWithErrorUnderflow
End

val semwitherror_eval_def = Define `
  (semwitherror_eval (SemWithErrorCte n) =
     if (0 : int) <= n then SemWithErrorVnum n
     else SemWithErrorUnderflow) /\
  (semwitherror_eval (SemWithErrorSub e1 e2) =
     case semwitherror_eval e1 of
       SemWithErrorUnderflow => SemWithErrorUnderflow
     | SemWithErrorVnum v1 =>
         (case semwitherror_eval e2 of
            SemWithErrorUnderflow => SemWithErrorUnderflow
          | SemWithErrorVnum v2 =>
              if v2 <= v1 then SemWithErrorVnum (v1 - v2)
              else SemWithErrorUnderflow))`;

val semwitherror_defunctionalization_size_e_def = Define `
  (semwitherror_defunctionalization_size_e (SemWithErrorCte x) =
     (1 : int)) /\
  (semwitherror_defunctionalization_size_e
     (SemWithErrorSub e1 e2) =
     (3 : int) +
       semwitherror_defunctionalization_size_e e1 +
       semwitherror_defunctionalization_size_e e2)`;

val semwitherror_size_e_def = Define `
  (semwitherror_size_e (SemWithErrorCte x) = (1 : int)) /\
  (semwitherror_size_e (SemWithErrorSub e1 e2) =
     (3 : int) + semwitherror_size_e e1 + semwitherror_size_e e2)`;

Datatype:
  semwitherror_cont =
    SemWithErrorI
  | SemWithErrorA semwitherror_expr semwitherror_cont
  | SemWithErrorB int semwitherror_cont
End

val (semwitherror_eval_cont_rules,
     semwitherror_eval_cont_ind,
     semwitherror_eval_cont_cases) =
  Hol_reln `
    (!k.
       semwitherror_eval_cont
         k
         SemWithErrorUnderflow
         SemWithErrorUnderflow) /\
    (!v k e2 r.
       semwitherror_eval_cont
         (SemWithErrorB v k)
         (semwitherror_eval e2)
         r ==>
       semwitherror_eval_cont
         (SemWithErrorA e2 k)
         (SemWithErrorVnum v)
         r) /\
    (!k v v1 r.
       semwitherror_eval_cont
         k
         (if v <= v1 then SemWithErrorVnum (v1 - v)
          else SemWithErrorUnderflow)
         r ==>
       semwitherror_eval_cont
         (SemWithErrorB v1 k)
         (SemWithErrorVnum v)
         r) /\
    (!v.
       semwitherror_eval_cont
         SemWithErrorI
         (SemWithErrorVnum v)
         (SemWithErrorVnum v))
  `;

val semwitherror_size_c_def = Define `
  (semwitherror_size_c SemWithErrorI = (0 : int)) /\
  (semwitherror_size_c (SemWithErrorA e2 k) =
     (2 : int) +
       semwitherror_defunctionalization_size_e e2 +
       semwitherror_size_c k) /\
  (semwitherror_size_c (SemWithErrorB x k) =
     (1 : int) + semwitherror_size_c k)`;

val defunctionalization_SemWithError_continue_4_vc =
  ``!(v : int) (c : semwitherror_cont).
      (0 : int) <= v ==>
      ((case c of
          SemWithErrorA e2 k =>
            (0 : int) <= semwitherror_size_c c /\
            semwitherror_size_c (SemWithErrorB v k) +
              semwitherror_defunctionalization_size_e e2 <
            semwitherror_size_c c
        | SemWithErrorB v1 k =>
            v <= v1 ==>
            (((0 : int) <= semwitherror_size_c c /\
              semwitherror_size_c k < semwitherror_size_c c) /\
             (0 : int) <= v1 - v)
        | SemWithErrorI => T) /\
       !result : semwitherror_value.
         (case c of
            SemWithErrorA e2 k =>
              semwitherror_eval_cont
                (SemWithErrorB v k)
                (semwitherror_eval e2)
                result
          | SemWithErrorB v1 k =>
              if v <= v1 then
                semwitherror_eval_cont
                  k
                  (SemWithErrorVnum (v1 - v))
                  result
              else
                result = SemWithErrorUnderflow
          | SemWithErrorI =>
              result = SemWithErrorVnum v) ==>
         semwitherror_eval_cont c (SemWithErrorVnum v) result)``;
