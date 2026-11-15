(* Statement-only formalization of PutnamBench artifact putnam_1987_a4:
   the distance forced by a real-coefficient trivariate polynomial satisfying
   a homogeneous translation identity and three prescribed values. This file
   contains no proof. *)

From Stdlib Require Import Reals Arith.PeanoNat.

Open Scope R_scope.

Definition putnam_1987_a4_complex : Type := (R * R)%type.

Definition putnam_1987_a4_of_real
    (x : R) : putnam_1987_a4_complex :=
  (x, 0).

Definition putnam_1987_a4_complex_add
    (z w : putnam_1987_a4_complex) : putnam_1987_a4_complex :=
  (fst z + fst w, snd z + snd w).

Definition putnam_1987_a4_complex_neg
    (z : putnam_1987_a4_complex) : putnam_1987_a4_complex :=
  (- fst z, - snd z).

Definition putnam_1987_a4_complex_sub
    (z w : putnam_1987_a4_complex) : putnam_1987_a4_complex :=
  putnam_1987_a4_complex_add z (putnam_1987_a4_complex_neg w).

Definition putnam_1987_a4_complex_mul
    (z w : putnam_1987_a4_complex) : putnam_1987_a4_complex :=
  (fst z * fst w - snd z * snd w,
   fst z * snd w + snd z * fst w).

Fixpoint putnam_1987_a4_complex_pow
    (z : putnam_1987_a4_complex) (n : nat) :
    putnam_1987_a4_complex :=
  match n with
  | O => putnam_1987_a4_of_real 1
  | S m =>
      putnam_1987_a4_complex_mul z
        (putnam_1987_a4_complex_pow z m)
  end.

Definition putnam_1987_a4_complex_norm
    (z : putnam_1987_a4_complex) : R :=
  sqrt (fst z ^ 2 + snd z ^ 2).

Record putnam_1987_a4_polynomial : Type := {
  putnam_1987_a4_coefficient : nat -> nat -> nat -> R;
  putnam_1987_a4_x_bound : nat;
  putnam_1987_a4_y_bound : nat;
  putnam_1987_a4_z_bound : nat;
  putnam_1987_a4_vanishes_outside :
    forall i j k : nat,
      Nat.lt putnam_1987_a4_x_bound i \/
      Nat.lt putnam_1987_a4_y_bound j \/
      Nat.lt putnam_1987_a4_z_bound k ->
      putnam_1987_a4_coefficient i j k = 0
}.

Fixpoint putnam_1987_a4_complex_sum_to
    (n : nat) (term : nat -> putnam_1987_a4_complex) :
    putnam_1987_a4_complex :=
  match n with
  | O => term O
  | S m =>
      putnam_1987_a4_complex_add
        (putnam_1987_a4_complex_sum_to m term) (term (S m))
  end.

Definition putnam_1987_a4_eval
    (P : putnam_1987_a4_polynomial)
    (x y z : putnam_1987_a4_complex) :
    putnam_1987_a4_complex :=
  putnam_1987_a4_complex_sum_to
    (putnam_1987_a4_x_bound P)
    (fun i : nat =>
      putnam_1987_a4_complex_sum_to
        (putnam_1987_a4_y_bound P)
        (fun j : nat =>
          putnam_1987_a4_complex_sum_to
            (putnam_1987_a4_z_bound P)
            (fun k : nat =>
              putnam_1987_a4_complex_mul
                (putnam_1987_a4_of_real
                  (putnam_1987_a4_coefficient P i j k))
                (putnam_1987_a4_complex_mul
                  (putnam_1987_a4_complex_pow x i)
                  (putnam_1987_a4_complex_mul
                    (putnam_1987_a4_complex_pow y j)
                    (putnam_1987_a4_complex_pow z k)))))).

Definition putnam_1987_a4_solution : R :=
  (5 / 3) * sqrt 30.

Theorem putnam_1987_a4
    (P : putnam_1987_a4_polynomial)
    (F : R -> R -> R)
    (h :
      forall x y z u : R,
        putnam_1987_a4_eval P
          (putnam_1987_a4_of_real (u * x))
          (putnam_1987_a4_of_real (u * y))
          (putnam_1987_a4_of_real (u * z)) =
        putnam_1987_a4_of_real (u ^ 2 * F (y - x) (z - x)))
    (hPval :
      putnam_1987_a4_eval P
        (putnam_1987_a4_of_real 1)
        (putnam_1987_a4_of_real 0)
        (putnam_1987_a4_of_real 0) =
          putnam_1987_a4_of_real 4 /\
      putnam_1987_a4_eval P
        (putnam_1987_a4_of_real 0)
        (putnam_1987_a4_of_real 1)
        (putnam_1987_a4_of_real 0) =
          putnam_1987_a4_of_real 5 /\
      putnam_1987_a4_eval P
        (putnam_1987_a4_of_real 0)
        (putnam_1987_a4_of_real 0)
        (putnam_1987_a4_of_real 1) =
          putnam_1987_a4_of_real 6)
    (A B Cpoint : putnam_1987_a4_complex)
    (hPABC :
      putnam_1987_a4_eval P A B Cpoint =
        putnam_1987_a4_of_real 0)
    (habs :
      putnam_1987_a4_complex_norm
        (putnam_1987_a4_complex_sub B A) = 10) :
  putnam_1987_a4_complex_norm
    (putnam_1987_a4_complex_sub Cpoint A) =
      putnam_1987_a4_solution.
Admitted.
