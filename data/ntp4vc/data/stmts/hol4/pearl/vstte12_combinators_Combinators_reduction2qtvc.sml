(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/vstte12_combinators_Combinators_reduction2qtvc: the recursive
  call-by-value reduction verification condition for S-K combinator terms
  containing only K, using evaluation contexts and reflexive-transitive
  reduction. This file contains no proof.
*)

open HolKernel Parse boolLib bossLib;
open relationTheory;

Datatype:
  c2q_term =
    C2qS
  | C2qK
  | C2qApp c2q_term c2q_term
End

val c2q_is_value_def = Define `
  c2q_is_value t =
    case t of
      C2qS => T
    | C2qK => T
    | C2qApp f v =>
        case f of
          C2qS => c2q_is_value v
        | C2qK => c2q_is_value v
        | C2qApp f1 v1 =>
            if f1 = C2qS then
              c2q_is_value v1 /\ c2q_is_value v
            else
              F`;

Datatype:
  c2q_context =
    C2qHole
  | C2qLeft c2q_context c2q_term
  | C2qRight c2q_term c2q_context
End

val c2q_is_context_def = Define `
  (c2q_is_context C2qHole = T) /\
  (c2q_is_context (C2qLeft c t) =
     c2q_is_context c) /\
  (c2q_is_context (C2qRight v c) =
     (c2q_is_value v /\ c2q_is_context c))`;

val c2q_subst_def = Define `
  (c2q_subst C2qHole t = t) /\
  (c2q_subst (C2qLeft c1 t2) t =
     C2qApp (c2q_subst c1 t) t2) /\
  (c2q_subst (C2qRight v1 c2) t =
     C2qApp v1 (c2q_subst c2 t))`;

val c2q_one_step_def = new_definition (
  "c2q_one_step_def",
  ``c2q_one_step source target <=>
      (?c v1 v2.
         c2q_is_context c /\
         c2q_is_value v1 /\
         c2q_is_value v2 /\
         source =
           c2q_subst c
             (C2qApp (C2qApp C2qK v1) v2) /\
         target = c2q_subst c v1) \/
      (?c v1 v2 v3.
         c2q_is_context c /\
         c2q_is_value v1 /\
         c2q_is_value v2 /\
         c2q_is_value v3 /\
         source =
           c2q_subst c
             (C2qApp (C2qApp (C2qApp C2qS v1) v2) v3) /\
         target =
           c2q_subst c
             (C2qApp (C2qApp v1 v3) (C2qApp v2 v3)))``);

val c2q_relTR_def = new_definition (
  "c2q_relTR_def",
  ``c2q_relTR source target <=>
      RTC c2q_one_step source target``);

val c2q_subst_c_def = Define `
  (c2q_subst_c C2qHole ct = ct) /\
  (c2q_subst_c (C2qLeft c1 t2) ct =
     C2qLeft (c2q_subst_c c1 ct) t2) /\
  (c2q_subst_c (C2qRight v1 c2) ct =
     C2qRight v1 (c2q_subst_c c2 ct))`;

val c2q_only_K_def = Define `
  (c2q_only_K C2qS = F) /\
  (c2q_only_K C2qK = T) /\
  (c2q_only_K (C2qApp t1 t2) =
     (c2q_only_K t1 /\ c2q_only_K t2))`;

val c2q_subterm_match_def = Define `
  c2q_subterm_match t subterm <=>
    case t of
      C2qApp f f1 => (f = subterm \/ f1 = subterm)
    | _ => F`;

val c2q_k_head_shape_def = Define `
  c2q_k_head_shape v <=>
    case v of
      C2qK => T
    | C2qApp C2qK v3 => T
    | _ => F`;

val c2q_reduction_result_def = Define `
  c2q_reduction_result v1 v2 result <=>
    case v1 of
      C2qK => (result = C2qApp v1 v2)
    | C2qApp C2qK v3 => (result = v3)
    | _ => F`;

val c2q_initial_condition_def = new_definition (
  "c2q_initial_condition_def",
  ``c2q_initial_condition t c <=>
      case t of
        C2qK => T
      | C2qApp t1 t2 =>
          let o1 = C2qLeft C2qHole t2
          in
          let o2 = c2q_subst_c c o1
          in
            (c2q_is_context c /\ c2q_is_context o1 ==>
             c2q_is_context o2) ==>
            (c2q_subterm_match t t1 /\
             c2q_only_K t1 /\
             c2q_is_context o2) /\
            (!v1.
               ((c2q_only_K v1 /\ c2q_is_value v1) /\
                c2q_relTR
                  (c2q_subst o2 t1)
                  (c2q_subst o2 v1)) ==>
               let o3 = C2qRight v1 C2qHole
               in
               let o4 = c2q_subst_c c o3
               in
                 (c2q_is_context c /\ c2q_is_context o3 ==>
                  c2q_is_context o4) ==>
                 (c2q_subterm_match t t2 /\
                  c2q_only_K t2 /\
                  c2q_is_context o4) /\
                 (!v2.
                    ((c2q_only_K v2 /\ c2q_is_value v2) /\
                     c2q_relTR
                       (c2q_subst o4 t2)
                       (c2q_subst o4 v2)) ==>
                    c2q_k_head_shape v1))
      | C2qS => F``);

val c2q_result_premise_def = new_definition (
  "c2q_result_premise_def",
  ``c2q_result_premise t c result <=>
      case t of
        C2qK => (result = C2qK)
      | C2qApp t1 t2 =>
          let o1 = C2qLeft C2qHole t2
          in
          let o2 = c2q_subst_c c o1
          in
            (c2q_is_context c /\ c2q_is_context o1 ==>
             c2q_is_context o2) /\
            (?v1.
               ((c2q_only_K v1 /\ c2q_is_value v1) /\
                c2q_relTR
                  (c2q_subst o2 t1)
                  (c2q_subst o2 v1)) /\
               let o3 = C2qRight v1 C2qHole
               in
               let o4 = c2q_subst_c c o3
               in
                 (c2q_is_context c /\ c2q_is_context o3 ==>
                  c2q_is_context o4) /\
                 (?v2.
                    ((c2q_only_K v2 /\ c2q_is_value v2) /\
                     c2q_relTR
                       (c2q_subst o4 t2)
                       (c2q_subst o4 v2)) /\
                    c2q_reduction_result v1 v2 result))
      | C2qS => F``);

val vstte12_combinators_Combinators_reduction2_vc =
  ``!(t : c2q_term) (c : c2q_context).
      c2q_only_K t ==>
      c2q_is_context c ==>
      c2q_initial_condition t c /\
      (!result : c2q_term.
         c2q_result_premise t c result ==>
         (c2q_only_K result /\ c2q_is_value result) /\
         c2q_relTR
           (c2q_subst c t)
           (c2q_subst c result))``;
