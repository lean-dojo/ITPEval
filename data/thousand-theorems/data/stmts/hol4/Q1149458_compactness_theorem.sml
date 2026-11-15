(*
  Statement-only formalization of the Thousand Theorems corpus artifact
  Q1149458 (thousand-theorems__hol4__Q1149458), "Compactness theorem": an
  arbitrary first-order theory has a nonempty model if and only if each of its
  finite subtheories has a nonempty model. This file contains no proof.
*)

open HolKernel Parse boolLib bossLib;
open listTheory pred_setTheory;

Datatype:
  q1149458_term =
    Q1149458Var num
  | Q1149458Fun 'f (q1149458_term list)
End

Datatype:
  q1149458_formula =
    Q1149458False
  | Q1149458Equal ('f q1149458_term) ('f q1149458_term)
  | Q1149458Rel 'r (('f q1149458_term) list)
  | Q1149458Imp q1149458_formula q1149458_formula
  | Q1149458Forall q1149458_formula
End

val q1149458_term_wf_def = Define`
  (q1149458_term_wf FS f_arity (Q1149458Var n) <=> T) /\
  (q1149458_term_wf FS f_arity (Q1149458Fun f ts) <=>
     f IN FS /\
     LENGTH ts = f_arity f /\
     EVERY (q1149458_term_wf FS f_arity) ts)`;

val q1149458_formula_wf_def = Define`
  (q1149458_formula_wf FS RS f_arity r_arity Q1149458False <=> T) /\
  (q1149458_formula_wf FS RS f_arity r_arity (Q1149458Equal s t) <=>
     q1149458_term_wf FS f_arity s /\
     q1149458_term_wf FS f_arity t) /\
  (q1149458_formula_wf FS RS f_arity r_arity (Q1149458Rel r ts) <=>
     r IN RS /\
     LENGTH ts = r_arity r /\
     EVERY (q1149458_term_wf FS f_arity) ts) /\
  (q1149458_formula_wf FS RS f_arity r_arity (Q1149458Imp p q) <=>
     q1149458_formula_wf FS RS f_arity r_arity p /\
     q1149458_formula_wf FS RS f_arity r_arity q) /\
  (q1149458_formula_wf FS RS f_arity r_arity (Q1149458Forall p) <=>
     q1149458_formula_wf FS RS f_arity r_arity p)`;

val q1149458_term_closed_at_def = Define`
  (q1149458_term_closed_at k (Q1149458Var n) <=> n < k) /\
  (q1149458_term_closed_at k (Q1149458Fun f ts) <=>
     EVERY (q1149458_term_closed_at k) ts)`;

val q1149458_formula_closed_at_def = Define`
  (q1149458_formula_closed_at k Q1149458False <=> T) /\
  (q1149458_formula_closed_at k (Q1149458Equal s t) <=>
     q1149458_term_closed_at k s /\
     q1149458_term_closed_at k t) /\
  (q1149458_formula_closed_at k (Q1149458Rel r ts) <=>
     EVERY (q1149458_term_closed_at k) ts) /\
  (q1149458_formula_closed_at k (Q1149458Imp p q) <=>
     q1149458_formula_closed_at k p /\
     q1149458_formula_closed_at k q) /\
  (q1149458_formula_closed_at k (Q1149458Forall p) <=>
     q1149458_formula_closed_at (SUC k) p)`;

val q1149458_term_value_def = Define`
  (q1149458_term_value fnI v (Q1149458Var n) = v n) /\
  (q1149458_term_value fnI v (Q1149458Fun f ts) =
     fnI f (MAP (q1149458_term_value fnI v) ts))`;

val q1149458_satisfies_def = Define`
  (q1149458_satisfies carrier fnI relI v Q1149458False <=> F) /\
  (q1149458_satisfies carrier fnI relI v (Q1149458Equal s t) <=>
     q1149458_term_value fnI v s = q1149458_term_value fnI v t) /\
  (q1149458_satisfies carrier fnI relI v (Q1149458Rel r ts) <=>
     relI r (MAP (q1149458_term_value fnI v) ts)) /\
  (q1149458_satisfies carrier fnI relI v (Q1149458Imp p q) <=>
     (q1149458_satisfies carrier fnI relI v p ==>
      q1149458_satisfies carrier fnI relI v q)) /\
  (q1149458_satisfies carrier fnI relI v (Q1149458Forall p) <=>
     !x.
       x IN carrier
       ==>
       q1149458_satisfies carrier fnI relI
         (\n. if n = 0 then x else v (PRE n)) p)`;

val q1149458_structure_def = new_definition (
  "q1149458_structure_def",
  ``q1149458_structure FS f_arity carrier fnI <=>
      !f xs.
        f IN FS /\
        LENGTH xs = f_arity f /\
        EVERY (\x. x IN carrier) xs
        ==>
        fnI f xs IN carrier``);

val q1149458_theory_def = new_definition (
  "q1149458_theory_def",
  ``q1149458_theory FS RS f_arity r_arity thy <=>
      !p.
        p IN thy
        ==>
        q1149458_formula_wf FS RS f_arity r_arity p /\
        q1149458_formula_closed_at 0 p``);

val q1149458_satisfiable_def = new_definition (
  "q1149458_satisfiable_def",
  ``q1149458_satisfiable
      (FS : 'f set) (RS : 'r set)
      (f_arity : 'f -> num) (r_arity : 'r -> num) thy <=>
      ?carrier : (('f + 'r) + num) set.
      ?fnI : 'f -> ((('f + 'r) + num) list) -> (('f + 'r) + num).
      ?relI : 'r -> ((('f + 'r) + num) list) -> bool.
        carrier <> {} /\
        q1149458_structure FS f_arity carrier fnI /\
        !p v.
          p IN thy /\
          (!n. v n IN carrier)
          ==>
          q1149458_satisfies carrier fnI relI v p``);

val q1149458_finitely_satisfiable_def = new_definition (
  "q1149458_finitely_satisfiable_def",
  ``q1149458_finitely_satisfiable FS RS f_arity r_arity thy <=>
      !thy0.
        FINITE thy0 /\
        thy0 SUBSET thy
        ==>
        q1149458_satisfiable FS RS f_arity r_arity thy0``);

val compactness_theorem =
  ``!(FS : 'f set) (RS : 'r set)
      (f_arity : 'f -> num) (r_arity : 'r -> num) thy.
      q1149458_theory FS RS f_arity r_arity thy
      ==>
      (q1149458_satisfiable FS RS f_arity r_arity thy <=>
       q1149458_finitely_satisfiable FS RS f_arity r_arity thy)``;
