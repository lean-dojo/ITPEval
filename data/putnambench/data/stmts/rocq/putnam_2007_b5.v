(* Statement-only formalization of PutnamBench artifact putnam_2007_b5:
   expressing the kth power of floor(n/k) as a polynomial-weighted sum of
   its lower powers for every integer n. This file contains no proof. *)

From Stdlib Require Import Reals ZArith List Arith.

Import ListNotations.
Open Scope R_scope.

Record putnam_2007_b5_real_polynomial : Type := {
  putnam_2007_b5_coefficient : nat -> R;
  putnam_2007_b5_bound : nat;
  putnam_2007_b5_finite_support :
    forall degree : nat,
      (putnam_2007_b5_bound < degree)%nat ->
      putnam_2007_b5_coefficient degree = 0
}.

Definition putnam_2007_b5_evaluate
    (P : putnam_2007_b5_real_polynomial) (x : R) : R :=
  sum_f_R0
    (fun degree : nat =>
      putnam_2007_b5_coefficient P degree * x ^ degree)
    (putnam_2007_b5_bound P).

Fixpoint putnam_2007_b5_weighted_sum
    (polynomials : list putnam_2007_b5_real_polynomial)
    (n quotient : R) (index : nat) : R :=
  match polynomials with
  | [] => 0
  | P :: remaining =>
      putnam_2007_b5_evaluate P n * quotient ^ index +
      putnam_2007_b5_weighted_sum remaining n quotient (S index)
  end.

Definition putnam_2007_b5_floor (x : R) : R :=
  IZR (Int_part x).

Theorem putnam_2007_b5 :
  forall k : nat,
    (0 < k)%nat ->
    exists polynomials : list putnam_2007_b5_real_polynomial,
      length polynomials = k /\
      forall n : Z,
        let quotient :=
          putnam_2007_b5_floor (IZR n / INR k) in
        quotient ^ k =
        putnam_2007_b5_weighted_sum
          polynomials (IZR n) quotient 0.
Admitted.
