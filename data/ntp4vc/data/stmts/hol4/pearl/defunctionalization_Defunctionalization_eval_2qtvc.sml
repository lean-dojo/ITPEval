(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/defunctionalization_Defunctionalization_eval_2qtvc: a
  defunctionalized expression-evaluation verification condition combining
  structural size decrease with preservation of continuation evaluation.
  This file contains no proof.
*)

open HolKernel Parse boolLib bossLib;
open integerTheory;

Datatype:
  defunctionalization_expr =
    DefunctionalizationCte int
  | DefunctionalizationSub
      defunctionalization_expr
      defunctionalization_expr
End

val defunctionalization_eval_def = Define `
  (defunctionalization_eval (DefunctionalizationCte n) = n) /\
  (defunctionalization_eval (DefunctionalizationSub e1 e2) =
     defunctionalization_eval e1 - defunctionalization_eval e2)`;

Datatype:
  defunctionalization_cont =
    DefunctionalizationA1
      defunctionalization_expr
      defunctionalization_cont
  | DefunctionalizationA2 int defunctionalization_cont
  | DefunctionalizationI
End

val (defunctionalization_eval_cont_rules,
     defunctionalization_eval_cont_ind,
     defunctionalization_eval_cont_cases) =
  Hol_reln `
    (!v k e2 r.
       defunctionalization_eval_cont
         (DefunctionalizationA2 v k)
         (defunctionalization_eval e2)
         r ==>
       defunctionalization_eval_cont
         (DefunctionalizationA1 e2 k)
         v
         r) /\
    (!k v1 v r.
       defunctionalization_eval_cont k (v1 - v) r ==>
       defunctionalization_eval_cont
         (DefunctionalizationA2 v1 k)
         v
         r) /\
    (!v.
       defunctionalization_eval_cont
         DefunctionalizationI
         v
         v)
  `;

val defunctionalization_size_e_def = Define `
  (defunctionalization_size_e (DefunctionalizationCte x) = (1 : int)) /\
  (defunctionalization_size_e (DefunctionalizationSub e1 e2) =
     (3 : int) +
       defunctionalization_size_e e1 +
       defunctionalization_size_e e2)`;

val defunctionalization_size_c_def = Define `
  (defunctionalization_size_c DefunctionalizationI = (0 : int)) /\
  (defunctionalization_size_c (DefunctionalizationA1 e2 k) =
     (2 : int) +
       defunctionalization_size_e e2 +
       defunctionalization_size_c k) /\
  (defunctionalization_size_c (DefunctionalizationA2 x k) =
     (1 : int) + defunctionalization_size_c k)`;

val defunctionalization_Defunctionalization_eval_2_vc =
  ``!(e : defunctionalization_expr) (c : defunctionalization_cont).
      (case e of
         DefunctionalizationCte n =>
           (0 : int) <=
             defunctionalization_size_c c +
             defunctionalization_size_e e /\
           defunctionalization_size_c c <
             defunctionalization_size_c c +
             defunctionalization_size_e e
       | DefunctionalizationSub e1 e2 =>
           (0 : int) <=
             defunctionalization_size_c c +
             defunctionalization_size_e e /\
           defunctionalization_size_c
             (DefunctionalizationA1 e2 c) +
             defunctionalization_size_e e1 <
           defunctionalization_size_c c +
             defunctionalization_size_e e) /\
      !result : int.
        (case e of
           DefunctionalizationCte n =>
             defunctionalization_eval_cont c n result
         | DefunctionalizationSub e1 e2 =>
             defunctionalization_eval_cont
               (DefunctionalizationA1 e2 c)
               (defunctionalization_eval e1)
               result) ==>
        defunctionalization_eval_cont
          c
          (defunctionalization_eval e)
          result``;
