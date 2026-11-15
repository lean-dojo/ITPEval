(*
  Statement-only formalization of the Thousand Theorems corpus artifact
  Q1068283 (thousand-theorems__hol4__Q1068283), "Löwenheim–Skolem theorem":
  for an infinite first-order structure and an infinite cardinal at least as
  large as its language, there is a structure of that cardinality elementarily
  embedding into, or admitting an elementary embedding from, the original
  structure. This file contains no proof.
*)

open HolKernel Parse boolLib bossLib;
open cardinalTheory listTheory pred_setTheory;

Datatype:
  q1068283_term =
    Q1068283Var num
  | Q1068283Fun 'f (q1068283_term list)
End

Datatype:
  q1068283_formula =
    Q1068283False
  | Q1068283Equal ('f q1068283_term) ('f q1068283_term)
  | Q1068283Rel 'r (('f q1068283_term) list)
  | Q1068283Imp q1068283_formula q1068283_formula
  | Q1068283Forall q1068283_formula
End

val q1068283_term_wf_def = Define`
  (q1068283_term_wf FS f_arity (Q1068283Var n) <=> T) /\
  (q1068283_term_wf FS f_arity (Q1068283Fun f ts) <=>
     f IN FS /\
     LENGTH ts = f_arity f /\
     EVERY (q1068283_term_wf FS f_arity) ts)`;

val q1068283_formula_wf_def = Define`
  (q1068283_formula_wf FS RS f_arity r_arity Q1068283False <=> T) /\
  (q1068283_formula_wf FS RS f_arity r_arity
       (Q1068283Equal s t) <=>
     q1068283_term_wf FS f_arity s /\
     q1068283_term_wf FS f_arity t) /\
  (q1068283_formula_wf FS RS f_arity r_arity
       (Q1068283Rel r ts) <=>
     r IN RS /\
     LENGTH ts = r_arity r /\
     EVERY (q1068283_term_wf FS f_arity) ts) /\
  (q1068283_formula_wf FS RS f_arity r_arity
       (Q1068283Imp p q) <=>
     q1068283_formula_wf FS RS f_arity r_arity p /\
     q1068283_formula_wf FS RS f_arity r_arity q) /\
  (q1068283_formula_wf FS RS f_arity r_arity
       (Q1068283Forall p) <=>
     q1068283_formula_wf FS RS f_arity r_arity p)`;

val q1068283_term_value_def = Define`
  (q1068283_term_value fnI v (Q1068283Var n) = v n) /\
  (q1068283_term_value fnI v (Q1068283Fun f ts) =
     fnI f (MAP (q1068283_term_value fnI v) ts))`;

val q1068283_satisfies_def = Define`
  (q1068283_satisfies carrier fnI relI v Q1068283False <=> F) /\
  (q1068283_satisfies carrier fnI relI v (Q1068283Equal s t) <=>
     q1068283_term_value fnI v s = q1068283_term_value fnI v t) /\
  (q1068283_satisfies carrier fnI relI v (Q1068283Rel r ts) <=>
     relI r (MAP (q1068283_term_value fnI v) ts)) /\
  (q1068283_satisfies carrier fnI relI v (Q1068283Imp p q) <=>
     (q1068283_satisfies carrier fnI relI v p ==>
      q1068283_satisfies carrier fnI relI v q)) /\
  (q1068283_satisfies carrier fnI relI v (Q1068283Forall p) <=>
     !x.
       x IN carrier
       ==>
       q1068283_satisfies carrier fnI relI
         (\n. if n = 0 then x else v (PRE n)) p)`;

val q1068283_structure_def = new_definition(
  "q1068283_structure_def",
  ``q1068283_structure FS f_arity carrier fnI <=>
      !f xs.
        f IN FS /\
        LENGTH xs = f_arity f /\
        EVERY (\x. x IN carrier) xs
        ==>
        fnI f xs IN carrier``);

val q1068283_elementary_embedding_def = new_definition(
  "q1068283_elementary_embedding_def",
  ``q1068283_elementary_embedding
      FS RS f_arity r_arity carrierA FA RA carrierB FB RB e <=>
      INJ e carrierA carrierB /\
      !p v.
        q1068283_formula_wf FS RS f_arity r_arity p /\
        (!n. v n IN carrierA)
        ==>
        (q1068283_satisfies carrierA FA RA v p <=>
         q1068283_satisfies carrierB FB RB (\n. e (v n)) p)``);

val lowenheim_skolem_theorem =
  ``!(FS : 'f set) (RS : 'r set)
      (f_arity : 'f -> num) (r_arity : 'r -> num)
      (MF : 'f -> 'm list -> 'm) (MR : 'r -> 'm list -> bool)
      (K : 'k set).
      INFINITE (UNIV : 'm set) /\
      (UNIV : num set) <<= K /\
      (IMAGE INL FS UNION IMAGE INR RS) <<= K
      ==>
      ?N : ('m + 'k) set.
      ?NF : 'f -> ('m + 'k) list -> ('m + 'k).
      ?NR : 'r -> ('m + 'k) list -> bool.
        q1068283_structure FS f_arity N NF /\
        N =~ K /\
        ((?e : ('m + 'k) -> 'm.
            q1068283_elementary_embedding
              FS RS f_arity r_arity N NF NR
              (UNIV : 'm set) MF MR e) \/
         (?e : 'm -> ('m + 'k).
            q1068283_elementary_embedding
              FS RS f_arity r_arity (UNIV : 'm set) MF MR
              N NF NR e))``;
