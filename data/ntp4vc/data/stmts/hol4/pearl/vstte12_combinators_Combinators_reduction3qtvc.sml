(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/vstte12_combinators_Combinators_reduction3qtvc: the recursive
  call-by-value reduction verification condition for iterated K-combinator
  terms, with evaluation contexts, reflexive-transitive reduction, and
  parity-sensitive results. This file contains no proof.
*)

open HolKernel Parse boolLib bossLib;
open integerTheory relationTheory;

Datatype:
  c3q_term =
    C3qS
  | C3qK
  | C3qApp c3q_term c3q_term
End

val c3q_is_value_def = Define `
  c3q_is_value t =
    case t of
      C3qS => T
    | C3qK => T
    | C3qApp f v =>
        case f of
          C3qS => c3q_is_value v
        | C3qK => c3q_is_value v
        | C3qApp f1 v1 =>
            if f1 = C3qS then
              c3q_is_value v1 /\ c3q_is_value v
            else
              F`;

Datatype:
  c3q_context =
    C3qHole
  | C3qLeft c3q_context c3q_term
  | C3qRight c3q_term c3q_context
End

val c3q_is_context_def = Define `
  (c3q_is_context C3qHole = T) /\
  (c3q_is_context (C3qLeft c t) =
     c3q_is_context c) /\
  (c3q_is_context (C3qRight v c) =
     (c3q_is_value v /\ c3q_is_context c))`;

val c3q_subst_def = Define `
  (c3q_subst C3qHole t = t) /\
  (c3q_subst (C3qLeft c1 t2) t =
     C3qApp (c3q_subst c1 t) t2) /\
  (c3q_subst (C3qRight v1 c2) t =
     C3qApp v1 (c3q_subst c2 t))`;

val c3q_one_step_def = new_definition (
  "c3q_one_step_def",
  ``c3q_one_step source target <=>
      (?c v1 v2.
         c3q_is_context c /\
         c3q_is_value v1 /\
         c3q_is_value v2 /\
         source =
           c3q_subst c
             (C3qApp (C3qApp C3qK v1) v2) /\
         target = c3q_subst c v1) \/
      (?c v1 v2 v3.
         c3q_is_context c /\
         c3q_is_value v1 /\
         c3q_is_value v2 /\
         c3q_is_value v3 /\
         source =
           c3q_subst c
             (C3qApp (C3qApp (C3qApp C3qS v1) v2) v3) /\
         target =
           c3q_subst c
             (C3qApp (C3qApp v1 v3) (C3qApp v2 v3)))``);

val c3q_relTR_def = new_definition (
  "c3q_relTR_def",
  ``c3q_relTR source target <=>
      RTC c3q_one_step source target``);

val c3q_subst_c_def = Define `
  (c3q_subst_c C3qHole ct = ct) /\
  (c3q_subst_c (C3qLeft c1 t2) ct =
     C3qLeft (c3q_subst_c c1 ct) t2) /\
  (c3q_subst_c (C3qRight v1 c2) ct =
     C3qRight v1 (c3q_subst_c c2 ct))`;

val c3q_ks_nat_def = Define `
  (c3q_ks_nat 0 = C3qK) /\
  (c3q_ks_nat (SUC n) =
     C3qApp (c3q_ks_nat n) C3qK)`;

val c3q_ks_def = Define `
  c3q_ks (n : int) = c3q_ks_nat (Num n)`;

val c3q_even_def = new_definition (
  "c3q_even_def",
  ``c3q_even (n : int) <=> ?k : int. n = (2 : int) * k``);

val c3q_odd_def = new_definition (
  "c3q_odd_def",
  ``c3q_odd (n : int) <=>
      ?k : int. n = (2 : int) * k + (1 : int)``);

val c3q_k_head_shape_def = Define `
  c3q_k_head_shape v <=>
    case v of
      C3qK => T
    | C3qApp C3qK v3 => T
    | _ => F`;

val c3q_reduction_result_def = Define `
  c3q_reduction_result v1 v2 result <=>
    case v1 of
      C3qK => (result = C3qApp v1 v2)
    | C3qApp C3qK v3 => (result = v3)
    | _ => F`;

val c3q_initial_condition_def = new_definition (
  "c3q_initial_condition_def",
  ``c3q_initial_condition (n : int) c <=>
      case c3q_ks n of
        C3qK => T
      | C3qApp t1 t2 =>
          let o1 = n - (1 : int)
          in
          let o2 = C3qLeft C3qHole t2
          in
          let o3 = c3q_subst_c c o2
          in
            (c3q_is_context c /\ c3q_is_context o2 ==>
             c3q_is_context o3) ==>
            ((((0 : int) <= n /\ o1 < n) /\
              (0 : int) <= o1 /\
              t1 = c3q_ks o1 /\
              c3q_is_context o3) /\
             (!v1.
                (c3q_relTR
                   (c3q_subst o3 t1)
                   (c3q_subst o3 v1) /\
                 c3q_is_value v1 /\
                 (c3q_even o1 ==> v1 = C3qK) /\
                 (c3q_odd o1 ==>
                  v1 = C3qApp C3qK C3qK)) ==>
                let o4 = C3qRight v1 C3qHole
                in
                let o5 = c3q_subst_c c o4
                in
                  (c3q_is_context c /\ c3q_is_context o4 ==>
                   c3q_is_context o5) ==>
                  ((((0 : int) <= n /\ (0 : int) < n) /\
                    (0 : int) <= (0 : int) /\
                    t2 = c3q_ks (0 : int) /\
                    c3q_is_context o5) /\
                   (!v2.
                      (c3q_relTR
                         (c3q_subst o5 t2)
                         (c3q_subst o5 v2) /\
                       c3q_is_value v2 /\
                       (c3q_even (0 : int) ==> v2 = C3qK) /\
                       (c3q_odd (0 : int) ==>
                        v2 = C3qApp C3qK C3qK)) ==>
                      c3q_k_head_shape v1))))
      | C3qS => F``);

val c3q_result_premise_def = new_definition (
  "c3q_result_premise_def",
  ``c3q_result_premise (n : int) c result <=>
      case c3q_ks n of
        C3qK => (result = C3qK)
      | C3qApp t1 t2 =>
          let o1 = n - (1 : int)
          in
          let o2 = C3qLeft C3qHole t2
          in
          let o3 = c3q_subst_c c o2
          in
            (c3q_is_context c /\ c3q_is_context o2 ==>
             c3q_is_context o3) /\
            (?v1.
               (c3q_relTR
                  (c3q_subst o3 t1)
                  (c3q_subst o3 v1) /\
                c3q_is_value v1 /\
                (c3q_even o1 ==> v1 = C3qK) /\
                (c3q_odd o1 ==>
                 v1 = C3qApp C3qK C3qK)) /\
               let o4 = C3qRight v1 C3qHole
               in
               let o5 = c3q_subst_c c o4
               in
                 (c3q_is_context c /\ c3q_is_context o4 ==>
                  c3q_is_context o5) /\
                 (?v2.
                    (c3q_relTR
                       (c3q_subst o5 t2)
                       (c3q_subst o5 v2) /\
                     c3q_is_value v2 /\
                     (c3q_even (0 : int) ==> v2 = C3qK) /\
                     (c3q_odd (0 : int) ==>
                      v2 = C3qApp C3qK C3qK)) /\
                    c3q_reduction_result v1 v2 result))
      | C3qS => F``);

val vstte12_combinators_Combinators_reduction3_vc =
  ``!(n : int) (c : c3q_context).
      (0 : int) <= n ==>
      c3q_is_context c ==>
      c3q_initial_condition n c /\
      (!result : c3q_term.
         c3q_result_premise n c result ==>
         c3q_relTR
           (c3q_subst c (c3q_ks n))
           (c3q_subst c result) /\
         c3q_is_value result /\
         (c3q_even n ==> result = C3qK) /\
         (c3q_odd n ==>
          result = C3qApp C3qK C3qK))``;
