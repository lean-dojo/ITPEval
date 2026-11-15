(* Statement-only formalization of PutnamBench corpus artifact putnam_2004_b4:
   the composition of equally angled rotations about consecutive points on
   the real axis is a translation by n. This file contains no proof. *)

From Stdlib Require Import Reals.

Open Scope R_scope.

Definition putnam_2004_b4_complex := (R * R)%type.

Definition putnam_2004_b4_of_real
    (x : R) : putnam_2004_b4_complex :=
  (x, 0).

Definition putnam_2004_b4_of_nat
    (n : nat) : putnam_2004_b4_complex :=
  putnam_2004_b4_of_real (INR n).

Definition putnam_2004_b4_i : putnam_2004_b4_complex :=
  (0, 1).

Definition putnam_2004_b4_add
    (z w : putnam_2004_b4_complex) : putnam_2004_b4_complex :=
  (fst z + fst w, snd z + snd w).

Definition putnam_2004_b4_neg
    (z : putnam_2004_b4_complex) : putnam_2004_b4_complex :=
  (- fst z, - snd z).

Definition putnam_2004_b4_sub
    (z w : putnam_2004_b4_complex) : putnam_2004_b4_complex :=
  putnam_2004_b4_add z (putnam_2004_b4_neg w).

Definition putnam_2004_b4_mul
    (z w : putnam_2004_b4_complex) : putnam_2004_b4_complex :=
  (fst z * fst w - snd z * snd w,
   fst z * snd w + snd z * fst w).

Definition putnam_2004_b4_inv
    (z : putnam_2004_b4_complex) : putnam_2004_b4_complex :=
  (fst z / (fst z ^ 2 + snd z ^ 2),
   - snd z / (fst z ^ 2 + snd z ^ 2)).

Definition putnam_2004_b4_div
    (z w : putnam_2004_b4_complex) : putnam_2004_b4_complex :=
  putnam_2004_b4_mul z (putnam_2004_b4_inv w).

Definition putnam_2004_b4_exp
    (z : putnam_2004_b4_complex) : putnam_2004_b4_complex :=
  (exp (fst z) * cos (snd z),
   exp (fst z) * sin (snd z)).

Definition putnam_2004_b4_rotation
    (n k : nat)
    (Q : putnam_2004_b4_complex) : putnam_2004_b4_complex :=
  putnam_2004_b4_add
    (putnam_2004_b4_of_nat k)
    (putnam_2004_b4_mul
      (putnam_2004_b4_exp
        (putnam_2004_b4_div
          (putnam_2004_b4_mul
            (putnam_2004_b4_mul
              putnam_2004_b4_i
              (putnam_2004_b4_of_real 2))
            (putnam_2004_b4_of_real PI))
          (putnam_2004_b4_of_nat n)))
      (putnam_2004_b4_sub Q (putnam_2004_b4_of_nat k))).

Definition putnam_2004_b4_solution
    (n : nat)
    (z : putnam_2004_b4_complex) : putnam_2004_b4_complex :=
  putnam_2004_b4_add z (putnam_2004_b4_of_nat n).

Theorem putnam_2004_b4
    (n : nat)
    (nge2 : (2 <= n)%nat)
    (R Rk : nat -> putnam_2004_b4_complex -> putnam_2004_b4_complex)
    (hR :
      R 0%nat = (fun Q => Q) /\
      forall k : nat,
        R (k + 1)%nat =
          (fun Q => Rk (k + 1)%nat (R k Q)))
    (hRk : Rk = putnam_2004_b4_rotation n) :
  R n = putnam_2004_b4_solution n.
Admitted.
