From mathcomp Require Import all_algebra all_ssreflect.
From mathcomp Require Import reals sequences topology normedtype.
From mathcomp Require Import classical_sets.
Import numFieldNormedType.Exports.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Variable R : realType.
Definition putnam_2021_b2_solution : R := 2/3.

Definition putnam_2021_b2_admissible (a : R ^nat) : Prop :=
  series (fun k => a k.+1) @ \oo --> (1 : R) /\
  forall k, 0 <= a k.+1.

Definition putnam_2021_b2_has_value
    (a : R ^nat) (S : R) : Prop :=
  series
    (fun n : nat =>
      let m := n.+1 in
      m%:R / (2 ^+ m) *
        (\prod_(1 <= k < m.+1) a k) ^ (1 / m%:R))
    @ \oo --> S.

Theorem putnam_2021_b2 :
    (exists a : R ^nat,
      putnam_2021_b2_admissible a /\
      putnam_2021_b2_has_value a putnam_2021_b2_solution) /\
    (forall (a : R ^nat) (S : R),
      putnam_2021_b2_admissible a ->
      putnam_2021_b2_has_value a S ->
      S <= putnam_2021_b2_solution).
Proof. Admitted.
