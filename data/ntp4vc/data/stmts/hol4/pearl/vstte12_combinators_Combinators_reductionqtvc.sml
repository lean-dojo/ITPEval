(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/vstte12_combinators_Combinators_reductionqtvc: the call-by-value
  reduction verification condition for S-K combinator terms, using evaluation
  contexts and reflexive-transitive reduction. This file contains no proof.
*)

open HolKernel Parse boolLib bossLib;
open relationTheory;

Datatype:
  crq_term =
    CrqS
  | CrqK
  | CrqApp crq_term crq_term
End

val crq_is_value_def = Define `
  crq_is_value t =
    case t of
      CrqS => T
    | CrqK => T
    | CrqApp f v =>
        case f of
          CrqS => crq_is_value v
        | CrqK => crq_is_value v
        | CrqApp f1 v1 =>
            if f1 = CrqS then
              crq_is_value v1 /\ crq_is_value v
            else
              F`;

Datatype:
  crq_context =
    CrqHole
  | CrqLeft crq_context crq_term
  | CrqRight crq_term crq_context
End

val crq_is_context_def = Define `
  (crq_is_context CrqHole = T) /\
  (crq_is_context (CrqLeft c t) =
     crq_is_context c) /\
  (crq_is_context (CrqRight v c) =
     (crq_is_value v /\ crq_is_context c))`;

val crq_subst_def = Define `
  (crq_subst CrqHole t = t) /\
  (crq_subst (CrqLeft c1 t2) t =
     CrqApp (crq_subst c1 t) t2) /\
  (crq_subst (CrqRight v1 c2) t =
     CrqApp v1 (crq_subst c2 t))`;

val crq_one_step_def = new_definition (
  "crq_one_step_def",
  ``crq_one_step source target <=>
      (?c v1 v2.
         crq_is_context c /\
         crq_is_value v1 /\
         crq_is_value v2 /\
         source =
           crq_subst c
             (CrqApp (CrqApp CrqK v1) v2) /\
         target = crq_subst c v1) \/
      (?c v1 v2 v3.
         crq_is_context c /\
         crq_is_value v1 /\
         crq_is_value v2 /\
         crq_is_value v3 /\
         source =
           crq_subst c
             (CrqApp (CrqApp (CrqApp CrqS v1) v2) v3) /\
         target =
           crq_subst c
             (CrqApp (CrqApp v1 v3) (CrqApp v2 v3)))``);

val crq_relTR_def = new_definition (
  "crq_relTR_def",
  ``crq_relTR source target <=>
      RTC crq_one_step source target``);

val crq_subst_c_def = Define `
  (crq_subst_c CrqHole ct = ct) /\
  (crq_subst_c (CrqLeft c1 t2) ct =
     CrqLeft (crq_subst_c c1 ct) t2) /\
  (crq_subst_c (CrqRight v1 c2) ct =
     CrqRight v1 (crq_subst_c c2 ct))`;

val crq_reduction_case_def = new_definition (
  "crq_reduction_case_def",
  ``crq_reduction_case c t <=>
      case t of
        CrqS =>
          crq_relTR
            (crq_subst c t)
            (crq_subst c CrqS) /\
          crq_is_value CrqS
      | CrqK =>
          crq_relTR
            (crq_subst c t)
            (crq_subst c CrqK) /\
          crq_is_value CrqK
      | CrqApp t1 t2 =>
          let o1 = CrqLeft CrqHole t2
          in
          let o2 = crq_subst_c c o1
          in
            (crq_is_context c /\ crq_is_context o1 ==>
             crq_is_context o2) ==>
            crq_is_context o2 /\
            (!v1.
               (crq_relTR
                  (crq_subst o2 t1)
                  (crq_subst o2 v1) /\
                crq_is_value v1) ==>
               let o3 = CrqRight v1 CrqHole
               in
               let o4 = crq_subst_c c o3
               in
                 (crq_is_context c /\ crq_is_context o3 ==>
                  crq_is_context o4) ==>
                 crq_is_context o4 /\
                 (!v2.
                    (crq_relTR
                       (crq_subst o4 t2)
                       (crq_subst o4 v2) /\
                     crq_is_value v2) ==>
                    case v1 of
                      CrqK =>
                        crq_relTR
                          (crq_subst c t)
                          (crq_subst c (CrqApp v1 v2)) /\
                        crq_is_value (CrqApp v1 v2)
                    | CrqS =>
                        crq_relTR
                          (crq_subst c t)
                          (crq_subst c (CrqApp v1 v2)) /\
                        crq_is_value (CrqApp v1 v2)
                    | CrqApp f v4 =>
                        case f of
                          CrqS =>
                            crq_relTR
                              (crq_subst c t)
                              (crq_subst c (CrqApp v1 v2)) /\
                            crq_is_value (CrqApp v1 v2)
                        | CrqK =>
                            crq_relTR
                              (crq_subst c t)
                              (crq_subst c v4) /\
                            crq_is_value v4
                        | CrqApp f0 v3 =>
                            if f0 = CrqS then
                              crq_is_context c /\
                              (!result.
                                 (crq_relTR
                                    (crq_subst c
                                      (CrqApp
                                        (CrqApp v3 v2)
                                        (CrqApp v4 v2)))
                                    (crq_subst c result) /\
                                  crq_is_value result) ==>
                                 crq_relTR
                                   (crq_subst c t)
                                   (crq_subst c result) /\
                                 crq_is_value result)
                            else
                              F))``);

val vstte12_combinators_Combinators_reduction_vc =
  ``!(c : crq_context) (t : crq_term).
      crq_is_context c ==>
      crq_reduction_case c t``;
