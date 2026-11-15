(* Statement-only formalization of PutnamBench corpus artifact putnam_2019_a3:
   the greatest universal lower bound for the average modulus of the complex
   roots of a degree-2019 polynomial with strictly increasing real
   coefficients between 1 and 2019. This file contains no proof. *)

From Stdlib Require Import Reals Lists.List Arith.PeanoNat.

Import ListNotations.
Open Scope R_scope.

Record putnam_2019_a3_complex : Type := {
  putnam_2019_a3_re : R;
  putnam_2019_a3_im : R
}.

Definition putnam_2019_a3_Czero : putnam_2019_a3_complex :=
  {| putnam_2019_a3_re := 0; putnam_2019_a3_im := 0 |}.

Definition putnam_2019_a3_Cone : putnam_2019_a3_complex :=
  {| putnam_2019_a3_re := 1; putnam_2019_a3_im := 0 |}.

Definition putnam_2019_a3_RtoC
    (x : R) : putnam_2019_a3_complex :=
  {| putnam_2019_a3_re := x; putnam_2019_a3_im := 0 |}.

Definition putnam_2019_a3_Cadd
    (z w : putnam_2019_a3_complex) : putnam_2019_a3_complex :=
  {| putnam_2019_a3_re :=
       putnam_2019_a3_re z + putnam_2019_a3_re w;
     putnam_2019_a3_im :=
       putnam_2019_a3_im z + putnam_2019_a3_im w |}.

Definition putnam_2019_a3_Cneg
    (z : putnam_2019_a3_complex) : putnam_2019_a3_complex :=
  {| putnam_2019_a3_re := - putnam_2019_a3_re z;
     putnam_2019_a3_im := - putnam_2019_a3_im z |}.

Definition putnam_2019_a3_Csub
    (z w : putnam_2019_a3_complex) : putnam_2019_a3_complex :=
  putnam_2019_a3_Cadd z (putnam_2019_a3_Cneg w).

Definition putnam_2019_a3_Cmul
    (z w : putnam_2019_a3_complex) : putnam_2019_a3_complex :=
  {| putnam_2019_a3_re :=
       putnam_2019_a3_re z * putnam_2019_a3_re w -
       putnam_2019_a3_im z * putnam_2019_a3_im w;
     putnam_2019_a3_im :=
       putnam_2019_a3_re z * putnam_2019_a3_im w +
       putnam_2019_a3_im z * putnam_2019_a3_re w |}.

Definition putnam_2019_a3_Cmod
    (z : putnam_2019_a3_complex) : R :=
  sqrt
    (putnam_2019_a3_re z ^ 2 +
     putnam_2019_a3_im z ^ 2).

Fixpoint putnam_2019_a3_eval
    (coefficients : list R)
    (z : putnam_2019_a3_complex) : putnam_2019_a3_complex :=
  match coefficients with
  | [] => putnam_2019_a3_Czero
  | coefficient :: remaining =>
      putnam_2019_a3_Cadd
        (putnam_2019_a3_RtoC coefficient)
        (putnam_2019_a3_Cmul z
          (putnam_2019_a3_eval remaining z))
  end.

Fixpoint putnam_2019_a3_linear_product
    (roots : list putnam_2019_a3_complex)
    (z : putnam_2019_a3_complex) : putnam_2019_a3_complex :=
  match roots with
  | [] => putnam_2019_a3_Cone
  | root :: remaining =>
      putnam_2019_a3_Cmul
        (putnam_2019_a3_Csub z root)
        (putnam_2019_a3_linear_product remaining z)
  end.

Definition putnam_2019_a3_admissible
    (coefficients : list R) : Prop :=
  length coefficients = 2020%nat /\
  1 <= nth 0 coefficients 0 /\
  nth 2019 coefficients 0 <= 2019 /\
  forall i : nat,
    (i < 2019)%nat ->
    nth i coefficients 0 < nth (S i) coefficients 0.

Definition putnam_2019_a3_root_enumeration
    (coefficients : list R)
    (roots : list putnam_2019_a3_complex) : Prop :=
  length roots = 2019%nat /\
  forall z : putnam_2019_a3_complex,
    putnam_2019_a3_eval coefficients z =
    putnam_2019_a3_Cmul
      (putnam_2019_a3_RtoC (nth 2019 coefficients 0))
      (putnam_2019_a3_linear_product roots z).

Fixpoint putnam_2019_a3_sum_moduli
    (roots : list putnam_2019_a3_complex) : R :=
  match roots with
  | [] => 0
  | root :: remaining =>
      putnam_2019_a3_Cmod root +
      putnam_2019_a3_sum_moduli remaining
  end.

Definition putnam_2019_a3_average_modulus
    (roots : list putnam_2019_a3_complex) : R :=
  putnam_2019_a3_sum_moduli roots / INR 2019.

Definition putnam_2019_a3_is_lower_bound (M : R) : Prop :=
  forall (coefficients : list R)
         (roots : list putnam_2019_a3_complex),
    putnam_2019_a3_admissible coefficients ->
    putnam_2019_a3_root_enumeration coefficients roots ->
    putnam_2019_a3_average_modulus roots >= M.

Definition putnam_2019_a3_is_greatest_lower_bound (M : R) : Prop :=
  putnam_2019_a3_is_lower_bound M /\
  forall candidate : R,
    putnam_2019_a3_is_lower_bound candidate ->
    candidate <= M.

Definition putnam_2019_a3_solution : R :=
  Rpower (INR 2019) (-1 / INR 2019).

Theorem putnam_2019_a3 :
  putnam_2019_a3_is_greatest_lower_bound
    putnam_2019_a3_solution.
Admitted.
