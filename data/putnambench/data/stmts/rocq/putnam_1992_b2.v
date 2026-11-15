(* Statement-only formalization of PutnamBench artifact putnam_1992_b2:
   coefficients of powers of 1 + x + x^2 + x^3 as a binomial sum.
   This file contains no proof. *)

From mathcomp Require Import all_ssreflect.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope nat_scope.

Definition putnam_1992_b2_polynomial : Type := seq nat.

Definition putnam_1992_b2_coefficient
    (p : putnam_1992_b2_polynomial) (k : nat) : nat :=
  nth 0 p k.

Definition putnam_1992_b2_multiply
    (p q : putnam_1992_b2_polynomial) : putnam_1992_b2_polynomial :=
  map
    (fun k =>
      \sum_(0 <= i < k.+1)
        (putnam_1992_b2_coefficient p i *
         putnam_1992_b2_coefficient q (k - i)))
    (iota 0 (size p + size q).-1).

Fixpoint putnam_1992_b2_power
    (p : putnam_1992_b2_polynomial) (n : nat) :
    putnam_1992_b2_polynomial :=
  match n with
  | 0 => [:: 1]
  | n'.+1 => putnam_1992_b2_multiply (putnam_1992_b2_power p n') p
  end.

Definition putnam_1992_b2_base_polynomial :
    putnam_1992_b2_polynomial :=
  [:: 1; 1; 1; 1].

Theorem putnam_1992_b2
    (Q : nat -> nat -> nat)
    (hQ : Q =
      fun n k : nat =>
        putnam_1992_b2_coefficient
          (putnam_1992_b2_power putnam_1992_b2_base_polynomial n) k) :
    forall n k : nat,
      Q n k =
        \sum_(0 <= j < k.+1)
          (binomial n j *
            (if 2 * j <= k then binomial n (k - 2 * j) else 0)).
Admitted.
