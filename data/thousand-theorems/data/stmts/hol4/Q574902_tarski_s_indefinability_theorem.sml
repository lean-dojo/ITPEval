(*
  Statement-only formalization of the Thousand Theorems corpus artifact
  Q574902 (thousand-theorems__hol4__Q574902), "Tarski's indefinability
  theorem": no unary first-order arithmetic formula defines truth in the
  standard natural-number structure for every arithmetic sentence. This file
  contains no proof.
*)

open HolKernel Parse boolLib bossLib;
open arithmeticTheory;

Datatype:
  q574902_term =
    Q574902Var num
  | Q574902Zero
  | Q574902One
  | Q574902Add q574902_term q574902_term
  | Q574902Mul q574902_term q574902_term
End

Datatype:
  q574902_formula =
    Q574902Equal q574902_term q574902_term
  | Q574902Less q574902_term q574902_term
  | Q574902Not q574902_formula
  | Q574902And q574902_formula q574902_formula
  | Q574902Forall q574902_formula
End

val q574902_term_closed_at_def = Define`
  (q574902_term_closed_at k (Q574902Var n) <=> n < k) /\
  (q574902_term_closed_at k Q574902Zero <=> T) /\
  (q574902_term_closed_at k Q574902One <=> T) /\
  (q574902_term_closed_at k (Q574902Add s t) <=>
     q574902_term_closed_at k s /\ q574902_term_closed_at k t) /\
  (q574902_term_closed_at k (Q574902Mul s t) <=>
     q574902_term_closed_at k s /\ q574902_term_closed_at k t)`;

val q574902_formula_closed_at_def = Define`
  (q574902_formula_closed_at k (Q574902Equal s t) <=>
     q574902_term_closed_at k s /\ q574902_term_closed_at k t) /\
  (q574902_formula_closed_at k (Q574902Less s t) <=>
     q574902_term_closed_at k s /\ q574902_term_closed_at k t) /\
  (q574902_formula_closed_at k (Q574902Not p) <=>
     q574902_formula_closed_at k p) /\
  (q574902_formula_closed_at k (Q574902And p q) <=>
     q574902_formula_closed_at k p /\
     q574902_formula_closed_at k q) /\
  (q574902_formula_closed_at k (Q574902Forall p) <=>
     q574902_formula_closed_at (SUC k) p)`;

val q574902_numeral_def = Define`
  (q574902_numeral 0 = Q574902Zero) /\
  (q574902_numeral (SUC n) =
     Q574902Add Q574902One (q574902_numeral n))`;

val q574902_subst_num_term_def = Define`
  (q574902_subst_num_term depth code (Q574902Var n) =
     if n = depth then q574902_numeral code
     else if depth < n then Q574902Var (PRE n)
     else Q574902Var n) /\
  (q574902_subst_num_term depth code Q574902Zero = Q574902Zero) /\
  (q574902_subst_num_term depth code Q574902One = Q574902One) /\
  (q574902_subst_num_term depth code (Q574902Add s t) =
     Q574902Add
       (q574902_subst_num_term depth code s)
       (q574902_subst_num_term depth code t)) /\
  (q574902_subst_num_term depth code (Q574902Mul s t) =
     Q574902Mul
       (q574902_subst_num_term depth code s)
       (q574902_subst_num_term depth code t))`;

val q574902_subst_num_formula_def = Define`
  (q574902_subst_num_formula depth code (Q574902Equal s t) =
     Q574902Equal
       (q574902_subst_num_term depth code s)
       (q574902_subst_num_term depth code t)) /\
  (q574902_subst_num_formula depth code (Q574902Less s t) =
     Q574902Less
       (q574902_subst_num_term depth code s)
       (q574902_subst_num_term depth code t)) /\
  (q574902_subst_num_formula depth code (Q574902Not p) =
     Q574902Not (q574902_subst_num_formula depth code p)) /\
  (q574902_subst_num_formula depth code (Q574902And p q) =
     Q574902And
       (q574902_subst_num_formula depth code p)
       (q574902_subst_num_formula depth code q)) /\
  (q574902_subst_num_formula depth code (Q574902Forall p) =
     Q574902Forall
       (q574902_subst_num_formula (SUC depth) code p))`;

val q574902_instantiate_def = new_definition (
  "q574902_instantiate_def",
  ``q574902_instantiate p code =
      q574902_subst_num_formula 0 code p``
);

val q574902_term_value_def = Define`
  (q574902_term_value v (Q574902Var n) = v n) /\
  (q574902_term_value v Q574902Zero = 0) /\
  (q574902_term_value v Q574902One = 1) /\
  (q574902_term_value v (Q574902Add s t) =
     q574902_term_value v s + q574902_term_value v t) /\
  (q574902_term_value v (Q574902Mul s t) =
     q574902_term_value v s * q574902_term_value v t)`;

val q574902_satisfies_def = Define`
  (q574902_satisfies v (Q574902Equal s t) <=>
     q574902_term_value v s = q574902_term_value v t) /\
  (q574902_satisfies v (Q574902Less s t) <=>
     q574902_term_value v s < q574902_term_value v t) /\
  (q574902_satisfies v (Q574902Not p) <=>
     ~q574902_satisfies v p) /\
  (q574902_satisfies v (Q574902And p q) <=>
     q574902_satisfies v p /\ q574902_satisfies v q) /\
  (q574902_satisfies v (Q574902Forall p) <=>
     !x : num.
       q574902_satisfies
         (\n. if n = 0 then x else v (PRE n)) p)`;

val q574902_truth_def = new_definition (
  "q574902_truth_def",
  ``q574902_truth p <=> q574902_satisfies (\n : num. 0) p``
);

val q574902_pair_def = new_definition (
  "q574902_pair_def",
  ``q574902_pair a b =
      ((a + b) * (a + b + 1)) DIV 2 + b``
);

val q574902_term_code_def = Define`
  (q574902_term_code (Q574902Var n) = 5 * n) /\
  (q574902_term_code Q574902Zero = 1) /\
  (q574902_term_code Q574902One = 2) /\
  (q574902_term_code (Q574902Add s t) =
     5 * q574902_pair
       (q574902_term_code s) (q574902_term_code t) + 3) /\
  (q574902_term_code (Q574902Mul s t) =
     5 * q574902_pair
       (q574902_term_code s) (q574902_term_code t) + 4)`;

val q574902_formula_code_def = Define`
  (q574902_formula_code (Q574902Equal s t) =
     6 * q574902_pair
       (q574902_term_code s) (q574902_term_code t)) /\
  (q574902_formula_code (Q574902Less s t) =
     6 * q574902_pair
       (q574902_term_code s) (q574902_term_code t) + 1) /\
  (q574902_formula_code (Q574902Not p) =
     6 * q574902_formula_code p + 2) /\
  (q574902_formula_code (Q574902And p q) =
     6 * q574902_pair
       (q574902_formula_code p) (q574902_formula_code q) + 3) /\
  (q574902_formula_code (Q574902Forall p) =
     6 * q574902_formula_code p + 4)`;

val q574902_tarski_s_indefinability_theorem =
  ``~(?tau : q574902_formula.
       q574902_formula_closed_at 1 tau /\
       !sigma : q574902_formula.
         q574902_formula_closed_at 0 sigma
         ==>
         (q574902_truth sigma <=>
          q574902_truth
            (q574902_instantiate tau
              (q574902_formula_code sigma))))``;
