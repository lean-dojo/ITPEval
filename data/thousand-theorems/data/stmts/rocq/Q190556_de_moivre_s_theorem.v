(*
  Statement-only formalization of Thousand Theorems corpus artifact Q190556
  (thousand-theorems__rocq__Q190556), "De Moivre's theorem": for every
  natural exponent and complex argument, the corresponding power of
  cos(z) + i sin(z) equals cos(nz) + i sin(nz). This file contains no proof.
*)

From Stdlib Require Import Reals.

Local Open Scope R_scope.

Definition q190556_C := (R * R)%type.

Definition q190556_of_R (x : R) : q190556_C := (x, 0).

Definition q190556_of_nat (n : nat) : q190556_C :=
  q190556_of_R (INR n).

Definition q190556_I : q190556_C := (0, 1).

Definition q190556_add (z w : q190556_C) : q190556_C :=
  (fst z + fst w, snd z + snd w).

Definition q190556_neg (z : q190556_C) : q190556_C :=
  (- fst z, - snd z).

Definition q190556_sub (z w : q190556_C) : q190556_C :=
  q190556_add z (q190556_neg w).

Definition q190556_mul (z w : q190556_C) : q190556_C :=
  (fst z * fst w - snd z * snd w,
   fst z * snd w + snd z * fst w).

Definition q190556_inv (z : q190556_C) : q190556_C :=
  (fst z / (fst z ^ 2 + snd z ^ 2),
   - snd z / (fst z ^ 2 + snd z ^ 2)).

Definition q190556_div (z w : q190556_C) : q190556_C :=
  q190556_mul z (q190556_inv w).

Fixpoint q190556_pow (z : q190556_C) (n : nat) : q190556_C :=
  match n with
  | O => q190556_of_R 1
  | S k => q190556_mul z (q190556_pow z k)
  end.

Definition q190556_exp (z : q190556_C) : q190556_C :=
  (exp (fst z) * cos (snd z),
   exp (fst z) * sin (snd z)).

Definition q190556_sin (z : q190556_C) : q190556_C :=
  q190556_div
    (q190556_mul
      (q190556_sub
        (q190556_exp (q190556_mul (q190556_neg z) q190556_I))
        (q190556_exp (q190556_mul z q190556_I)))
      q190556_I)
    (q190556_of_R 2).

Definition q190556_cos (z : q190556_C) : q190556_C :=
  q190556_div
    (q190556_add
      (q190556_exp (q190556_mul z q190556_I))
      (q190556_exp (q190556_mul (q190556_neg z) q190556_I)))
    (q190556_of_R 2).

Theorem cos_add_sin_mul_I_pow :
  forall (n : nat) (z : q190556_C),
    q190556_pow
      (q190556_add
        (q190556_cos z)
        (q190556_mul (q190556_sin z) q190556_I))
      n =
    q190556_add
      (q190556_cos (q190556_mul (q190556_of_nat n) z))
      (q190556_mul
        (q190556_sin (q190556_mul (q190556_of_nat n) z))
        q190556_I).
Admitted.
