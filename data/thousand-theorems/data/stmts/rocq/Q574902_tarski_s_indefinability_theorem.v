(*
  Statement-only formalization of Thousand Theorems corpus artifact Q574902
  (thousand-theorems__rocq__Q574902), "Tarski's indefinability theorem": no
  unary first-order arithmetic formula defines truth for every closed
  arithmetic sentence in the standard natural-number model when applied to
  that sentence's Goedel code. This file contains no proof.
*)

From Stdlib Require Import Arith.PeanoNat.
From Stdlib Require Import Vectors.Fin.

Set Implicit Arguments.

Inductive q574902_term (variables : nat) : Type :=
| q574902_variable :
    Fin.t variables -> q574902_term variables
| q574902_zero :
    q574902_term variables
| q574902_one :
    q574902_term variables
| q574902_add :
    q574902_term variables ->
    q574902_term variables ->
    q574902_term variables
| q574902_multiply :
    q574902_term variables ->
    q574902_term variables ->
    q574902_term variables.

Arguments q574902_variable {variables} _.
Arguments q574902_zero {variables}.
Arguments q574902_one {variables}.
Arguments q574902_add {variables} _ _.
Arguments q574902_multiply {variables} _ _.

Inductive q574902_formula (variables : nat) : Type :=
| q574902_equal :
    q574902_term variables ->
    q574902_term variables ->
    q574902_formula variables
| q574902_not_equal :
    q574902_term variables ->
    q574902_term variables ->
    q574902_formula variables
| q574902_less_than :
    q574902_term variables ->
    q574902_term variables ->
    q574902_formula variables
| q574902_not_less_than :
    q574902_term variables ->
    q574902_term variables ->
    q574902_formula variables
| q574902_truth :
    q574902_formula variables
| q574902_falsum :
    q574902_formula variables
| q574902_conjunction :
    q574902_formula variables ->
    q574902_formula variables ->
    q574902_formula variables
| q574902_disjunction :
    q574902_formula variables ->
    q574902_formula variables ->
    q574902_formula variables
| q574902_forall :
    q574902_formula (S variables) ->
    q574902_formula variables
| q574902_exists :
    q574902_formula (S variables) ->
    q574902_formula variables.

Arguments q574902_equal {variables} _ _.
Arguments q574902_not_equal {variables} _ _.
Arguments q574902_less_than {variables} _ _.
Arguments q574902_not_less_than {variables} _ _.
Arguments q574902_truth {variables}.
Arguments q574902_falsum {variables}.
Arguments q574902_conjunction {variables} _ _.
Arguments q574902_disjunction {variables} _ _.
Arguments q574902_forall {variables} _.
Arguments q574902_exists {variables} _.

Fixpoint q574902_term_map
    {n m : nat}
    (rho : Fin.t n -> Fin.t m)
    (t : q574902_term n) : q574902_term m :=
  match t with
  | q574902_variable i => q574902_variable (rho i)
  | q574902_zero => q574902_zero
  | q574902_one => q574902_one
  | q574902_add x y =>
      q574902_add
        (q574902_term_map rho x)
        (q574902_term_map rho y)
  | q574902_multiply x y =>
      q574902_multiply
        (q574902_term_map rho x)
        (q574902_term_map rho y)
  end.

Definition q574902_lift_substitution
    {n m : nat}
    (substitution : Fin.t n -> q574902_term m)
    (i : Fin.t (S n)) : q574902_term (S m) :=
  Fin.caseS' i
    (fun _ => q574902_term (S m))
    (q574902_variable Fin.F1)
    (fun j => q574902_term_map Fin.FS (substitution j)).

Fixpoint q574902_term_substitute
    {n m : nat}
    (substitution : Fin.t n -> q574902_term m)
    (t : q574902_term n) : q574902_term m :=
  match t with
  | q574902_variable i => substitution i
  | q574902_zero => q574902_zero
  | q574902_one => q574902_one
  | q574902_add x y =>
      q574902_add
        (q574902_term_substitute substitution x)
        (q574902_term_substitute substitution y)
  | q574902_multiply x y =>
      q574902_multiply
        (q574902_term_substitute substitution x)
        (q574902_term_substitute substitution y)
  end.

Fixpoint q574902_formula_substitute
    {n m : nat}
    (substitution : Fin.t n -> q574902_term m)
    (phi : q574902_formula n) : q574902_formula m :=
  match phi with
  | q574902_equal x y =>
      q574902_equal
        (q574902_term_substitute substitution x)
        (q574902_term_substitute substitution y)
  | q574902_not_equal x y =>
      q574902_not_equal
        (q574902_term_substitute substitution x)
        (q574902_term_substitute substitution y)
  | q574902_less_than x y =>
      q574902_less_than
        (q574902_term_substitute substitution x)
        (q574902_term_substitute substitution y)
  | q574902_not_less_than x y =>
      q574902_not_less_than
        (q574902_term_substitute substitution x)
        (q574902_term_substitute substitution y)
  | q574902_truth => q574902_truth
  | q574902_falsum => q574902_falsum
  | q574902_conjunction psi chi =>
      q574902_conjunction
        (q574902_formula_substitute substitution psi)
        (q574902_formula_substitute substitution chi)
  | q574902_disjunction psi chi =>
      q574902_disjunction
        (q574902_formula_substitute substitution psi)
        (q574902_formula_substitute substitution chi)
  | q574902_forall psi =>
      q574902_forall
        (q574902_formula_substitute
           (q574902_lift_substitution substitution) psi)
  | q574902_exists psi =>
      q574902_exists
        (q574902_formula_substitute
           (q574902_lift_substitution substitution) psi)
  end.

Definition q574902_substitute_only_variable
    (t : q574902_term 0)
    (i : Fin.t 1) : q574902_term 0 :=
  Fin.caseS' i
    (fun _ => q574902_term 0)
    t
    (fun j => match j with end).

Definition q574902_instantiate
    (tau : q574902_formula 1)
    (t : q574902_term 0) : q574902_formula 0 :=
  q574902_formula_substitute
    (q574902_substitute_only_variable t) tau.

Fixpoint q574902_numeral
    {variables : nat} (n : nat) : q574902_term variables :=
  match n with
  | 0 => q574902_zero
  | S k => q574902_add q574902_one (q574902_numeral k)
  end.

Definition q574902_extend_valuation
    (x : nat)
    (valuation : nat -> nat)
    (i : nat) : nat :=
  match i with
  | 0 => x
  | S j => valuation j
  end.

Fixpoint q574902_term_denote
    {variables : nat}
    (valuation : nat -> nat)
    (t : q574902_term variables) : nat :=
  match t with
  | q574902_variable i => valuation (proj1_sig (Fin.to_nat i))
  | q574902_zero => 0
  | q574902_one => 1
  | q574902_add x y =>
      q574902_term_denote valuation x +
      q574902_term_denote valuation y
  | q574902_multiply x y =>
      q574902_term_denote valuation x *
      q574902_term_denote valuation y
  end.

Fixpoint q574902_satisfies
    {variables : nat}
    (valuation : nat -> nat)
    (phi : q574902_formula variables) : Prop :=
  match phi with
  | q574902_equal x y =>
      q574902_term_denote valuation x =
      q574902_term_denote valuation y
  | q574902_not_equal x y =>
      q574902_term_denote valuation x <>
      q574902_term_denote valuation y
  | q574902_less_than x y =>
      (q574902_term_denote valuation x <
       q574902_term_denote valuation y)%nat
  | q574902_not_less_than x y =>
      ~ (q574902_term_denote valuation x <
         q574902_term_denote valuation y)%nat
  | q574902_truth => True
  | q574902_falsum => False
  | q574902_conjunction psi chi =>
      q574902_satisfies valuation psi /\
      q574902_satisfies valuation chi
  | q574902_disjunction psi chi =>
      q574902_satisfies valuation psi \/
      q574902_satisfies valuation chi
  | q574902_forall psi =>
      forall x : nat,
        q574902_satisfies
          (q574902_extend_valuation x valuation) psi
  | q574902_exists psi =>
      exists x : nat,
        q574902_satisfies
          (q574902_extend_valuation x valuation) psi
  end.

Definition q574902_empty_valuation
    (_ : nat) : nat := 0.

Definition q574902_sentence_true
    (sigma : q574902_formula 0) : Prop :=
  q574902_satisfies q574902_empty_valuation sigma.

Definition q574902_pair (x y : nat) : nat :=
  (x + y) * (x + y) + x.

Fixpoint q574902_term_code
    {variables : nat}
    (t : q574902_term variables) : nat :=
  match t with
  | q574902_variable i => 5 * proj1_sig (Fin.to_nat i)
  | q574902_zero => 1
  | q574902_one => 2
  | q574902_add x y =>
      5 * q574902_pair
            (q574902_term_code x)
            (q574902_term_code y) + 3
  | q574902_multiply x y =>
      5 * q574902_pair
            (q574902_term_code x)
            (q574902_term_code y) + 4
  end.

Fixpoint q574902_formula_code
    {variables : nat}
    (phi : q574902_formula variables) : nat :=
  match phi with
  | q574902_equal x y =>
      10 * q574902_pair
             (q574902_term_code x)
             (q574902_term_code y)
  | q574902_not_equal x y =>
      10 * q574902_pair
             (q574902_term_code x)
             (q574902_term_code y) + 1
  | q574902_less_than x y =>
      10 * q574902_pair
             (q574902_term_code x)
             (q574902_term_code y) + 2
  | q574902_not_less_than x y =>
      10 * q574902_pair
             (q574902_term_code x)
             (q574902_term_code y) + 3
  | q574902_truth => 4
  | q574902_falsum => 5
  | q574902_conjunction psi chi =>
      10 * q574902_pair
             (q574902_formula_code psi)
             (q574902_formula_code chi) + 6
  | q574902_disjunction psi chi =>
      10 * q574902_pair
             (q574902_formula_code psi)
             (q574902_formula_code chi) + 7
  | q574902_forall psi =>
      10 * q574902_formula_code psi + 8
  | q574902_exists psi =>
      10 * q574902_formula_code psi + 9
  end.

Theorem q574902_undefinability_of_truth :
  ~ exists tau : q574902_formula 1,
      forall sigma : q574902_formula 0,
        q574902_sentence_true sigma <->
        q574902_sentence_true
          (q574902_instantiate tau
             (q574902_numeral (q574902_formula_code sigma))).
Admitted.
