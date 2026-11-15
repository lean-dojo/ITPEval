(* Statement-only formalization of PutnamBench artifact putnam_1976_b1:
   the limit of a normalized sum of differences of floor functions is
   ln 4 minus 1; this file contains no proof. *)

From Stdlib Require Import Reals ZArith.

Open Scope R_scope.

Definition putnam_1976_b1_solution : (nat * nat)%type := (4%nat, 1%nat).

Fixpoint putnam_1976_b1_sum (n k : nat) : R :=
  match k with
  | O => 0
  | S m =>
      putnam_1976_b1_sum n m +
      IZR
        ((Int_part (2 * INR n / INR (S m)) -
          2 * Int_part (INR n / INR (S m)))%Z)
  end.

Definition putnam_1976_b1_sequence (n : nat) : R :=
  / INR n * putnam_1976_b1_sum n n.

Definition putnam_1976_b1_tends_to
    (u : nat -> R) (limit : R) : Prop :=
  forall epsilon : R,
    0 < epsilon ->
    exists N : nat,
      forall n : nat,
        (N <= n)%nat ->
        Rabs (u n - limit) < epsilon.

Theorem putnam_1976_b1 :
  putnam_1976_b1_tends_to putnam_1976_b1_sequence
    (ln (INR (fst putnam_1976_b1_solution)) -
     INR (snd putnam_1976_b1_solution)).
Admitted.
