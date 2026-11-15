(* Statement-only formalization of PutnamBench artifact putnam_2016_a1:
   the least positive derivative order for which every integer-coefficient
   polynomial has values divisible by 2016 at every integer. This file
   contains no proof. *)

From Stdlib Require Import ZArith Lists.List.

Open Scope Z_scope.

Definition putnam_2016_a1_polynomial : Type := list Z.

Fixpoint putnam_2016_a1_eval
    (P : putnam_2016_a1_polynomial) (x : Z) : Z :=
  match P with
  | nil => 0
  | coefficient :: remaining =>
      coefficient + x * putnam_2016_a1_eval remaining x
  end.

Fixpoint putnam_2016_a1_derivative_coefficients
    (degree : nat)
    (P : putnam_2016_a1_polynomial) :
    putnam_2016_a1_polynomial :=
  match P with
  | nil => nil
  | coefficient :: remaining =>
      (Z.of_nat degree * coefficient) ::
      putnam_2016_a1_derivative_coefficients (S degree) remaining
  end.

Definition putnam_2016_a1_derivative
    (P : putnam_2016_a1_polynomial) :
    putnam_2016_a1_polynomial :=
  match P with
  | nil => nil
  | _ :: remaining =>
      putnam_2016_a1_derivative_coefficients 1 remaining
  end.

Fixpoint putnam_2016_a1_iterated_derivative
    (order : nat)
    (P : putnam_2016_a1_polynomial) :
    putnam_2016_a1_polynomial :=
  match order with
  | O => P
  | S previous =>
      putnam_2016_a1_derivative
        (putnam_2016_a1_iterated_derivative previous P)
  end.

Definition putnam_2016_a1_qualifies (j : nat) : Prop :=
  (0 < j)%nat /\
  forall (P : putnam_2016_a1_polynomial) (k : Z),
    Z.divide 2016
      (putnam_2016_a1_eval
        (putnam_2016_a1_iterated_derivative j P) k).

Definition putnam_2016_a1_solution : nat := 8%nat.

Theorem putnam_2016_a1 :
  putnam_2016_a1_qualifies putnam_2016_a1_solution /\
  forall j : nat,
    putnam_2016_a1_qualifies j ->
    (putnam_2016_a1_solution <= j)%nat.
Admitted.
