(*
  Statement-only formalization of the Thousand Theorems corpus artifact
  Q1535225 (thousand-theorems__hol4__Q1535225), "Łoś' theorem": a
  first-order sentence holds in an ultraproduct exactly when it holds in an
  ultrafilter-large set of component structures. This file contains no proof.
*)

open HolKernel Parse boolLib bossLib;
open listTheory pred_setTheory;

Datatype:
  q1535225_term =
    Q1535225Var num
  | Q1535225Fun 'f (q1535225_term list)
End

Datatype:
  q1535225_formula =
    Q1535225False
  | Q1535225Equal ('f q1535225_term) ('f q1535225_term)
  | Q1535225Rel 'r (('f q1535225_term) list)
  | Q1535225Imp q1535225_formula q1535225_formula
  | Q1535225Forall q1535225_formula
End

val q1535225_term_wf_def = Define`
  (q1535225_term_wf FS f_arity (Q1535225Var n) <=> T) /\
  (q1535225_term_wf FS f_arity (Q1535225Fun f ts) <=>
     f IN FS /\
     LENGTH ts = f_arity f /\
     EVERY (q1535225_term_wf FS f_arity) ts)`;

val q1535225_formula_wf_def = Define`
  (q1535225_formula_wf FS RS f_arity r_arity Q1535225False <=> T) /\
  (q1535225_formula_wf FS RS f_arity r_arity
       (Q1535225Equal s t) <=>
     q1535225_term_wf FS f_arity s /\
     q1535225_term_wf FS f_arity t) /\
  (q1535225_formula_wf FS RS f_arity r_arity
       (Q1535225Rel r ts) <=>
     r IN RS /\
     LENGTH ts = r_arity r /\
     EVERY (q1535225_term_wf FS f_arity) ts) /\
  (q1535225_formula_wf FS RS f_arity r_arity
       (Q1535225Imp p q) <=>
     q1535225_formula_wf FS RS f_arity r_arity p /\
     q1535225_formula_wf FS RS f_arity r_arity q) /\
  (q1535225_formula_wf FS RS f_arity r_arity
       (Q1535225Forall p) <=>
     q1535225_formula_wf FS RS f_arity r_arity p)`;

val q1535225_term_closed_at_def = Define`
  (q1535225_term_closed_at k (Q1535225Var n) <=> n < k) /\
  (q1535225_term_closed_at k (Q1535225Fun f ts) <=>
     EVERY (q1535225_term_closed_at k) ts)`;

val q1535225_formula_closed_at_def = Define`
  (q1535225_formula_closed_at k Q1535225False <=> T) /\
  (q1535225_formula_closed_at k (Q1535225Equal s t) <=>
     q1535225_term_closed_at k s /\
     q1535225_term_closed_at k t) /\
  (q1535225_formula_closed_at k (Q1535225Rel r ts) <=>
     EVERY (q1535225_term_closed_at k) ts) /\
  (q1535225_formula_closed_at k (Q1535225Imp p q) <=>
     q1535225_formula_closed_at k p /\
     q1535225_formula_closed_at k q) /\
  (q1535225_formula_closed_at k (Q1535225Forall p) <=>
     q1535225_formula_closed_at (SUC k) p)`;

val q1535225_term_value_def = Define`
  (q1535225_term_value fnI v (Q1535225Var n) = v n) /\
  (q1535225_term_value fnI v (Q1535225Fun f ts) =
     fnI f (MAP (q1535225_term_value fnI v) ts))`;

val q1535225_satisfies_def = Define`
  (q1535225_satisfies carrier fnI relI v Q1535225False <=> F) /\
  (q1535225_satisfies carrier fnI relI v (Q1535225Equal s t) <=>
     q1535225_term_value fnI v s = q1535225_term_value fnI v t) /\
  (q1535225_satisfies carrier fnI relI v (Q1535225Rel r ts) <=>
     relI r (MAP (q1535225_term_value fnI v) ts)) /\
  (q1535225_satisfies carrier fnI relI v (Q1535225Imp p q) <=>
     (q1535225_satisfies carrier fnI relI v p ==>
      q1535225_satisfies carrier fnI relI v q)) /\
  (q1535225_satisfies carrier fnI relI v (Q1535225Forall p) <=>
     !x.
       x IN carrier
       ==>
       q1535225_satisfies carrier fnI relI
         (\n. if n = 0 then x else v (PRE n)) p)`;

val q1535225_structure_def = new_definition (
  "q1535225_structure_def",
  ``q1535225_structure FS f_arity carrier fnI <=>
      !f xs.
        f IN FS /\
        LENGTH xs = f_arity f /\
        EVERY (\x. x IN carrier) xs
        ==>
        fnI f xs IN carrier``);

val q1535225_ultrafilter_def = new_definition (
  "q1535225_ultrafilter_def",
  ``q1535225_ultrafilter (U : ('i set) set) <=>
      (UNIV : 'i set) IN U /\
      EMPTY NOTIN U /\
      (!s t. s IN U /\ t IN U ==> s INTER t IN U) /\
      (!s t. s IN U /\ s SUBSET t ==> t IN U) /\
      (!s : 'i set. s IN U \/ COMPL s IN U)``);

val q1535225_choice_function_def = new_definition (
  "q1535225_choice_function_def",
  ``q1535225_choice_function carrier (x : 'i -> 'm) <=>
      !i. x i IN carrier i``);

val q1535225_equivalent_def = new_definition (
  "q1535225_equivalent_def",
  ``q1535225_equivalent (U : ('i set) set)
      (x : 'i -> 'm) (y : 'i -> 'm) <=>
      {i | x i = y i} IN U``);

val q1535225_class_def = new_definition (
  "q1535225_class_def",
  ``q1535225_class U carrier (x : 'i -> 'm) =
      {y |
        q1535225_choice_function carrier y /\
        q1535225_equivalent U x y}``);

val q1535225_representative_def = new_definition (
  "q1535225_representative_def",
  ``q1535225_representative (c : ('i -> 'm) set) =
      @x. x IN c``);

val q1535225_ultraproduct_carrier_def = new_definition (
  "q1535225_ultraproduct_carrier_def",
  ``q1535225_ultraproduct_carrier U carrier =
      IMAGE (q1535225_class U carrier)
        {x | q1535225_choice_function carrier x}``);

val q1535225_ultraproduct_function_def = new_definition (
  "q1535225_ultraproduct_function_def",
  ``q1535225_ultraproduct_function U carrier fnI f cs =
      q1535225_class U carrier
        (\i.
          fnI i f
            (MAP (\c. q1535225_representative c i) cs))``);

val q1535225_ultraproduct_relation_def = new_definition (
  "q1535225_ultraproduct_relation_def",
  ``q1535225_ultraproduct_relation U relI r cs <=>
      {i |
        relI i r
          (MAP (\c. q1535225_representative c i) cs)} IN U``);

val q1535225_models_def = new_definition (
  "q1535225_models_def",
  ``q1535225_models carrier fnI relI p <=>
      !v.
        (!n. v n IN carrier)
        ==>
        q1535225_satisfies carrier fnI relI v p``);

val los_theorem =
  ``!(FS : 'f set) (RS : 'r set)
      (f_arity : 'f -> num) (r_arity : 'r -> num)
      (carrier : 'i -> 'm set)
      (fnI : 'i -> 'f -> 'm list -> 'm)
      (relI : 'i -> 'r -> 'm list -> bool)
      (U : ('i set) set) p.
      q1535225_ultrafilter U /\
      (!i.
        carrier i <> EMPTY /\
        q1535225_structure FS f_arity (carrier i) (fnI i)) /\
      q1535225_formula_wf FS RS f_arity r_arity p /\
      q1535225_formula_closed_at 0 p
      ==>
      (q1535225_models
         (q1535225_ultraproduct_carrier U carrier)
         (q1535225_ultraproduct_function U carrier fnI)
         (q1535225_ultraproduct_relation U relI)
         p
       <=>
       {i |
         q1535225_models (carrier i) (fnI i) (relI i) p} IN U)``;
