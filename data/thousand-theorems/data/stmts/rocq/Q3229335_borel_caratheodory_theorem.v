(*
  Statement-only formalization of Thousand Theorems corpus artifact Q3229335
  (thousand-theorems__rocq__Q3229335), "Borel–Carathéodory theorem": an
  analytic complex-valued function on a disk whose real part is bounded above
  satisfies the Borel–Carathéodory pointwise norm estimate. This file contains
  no proof.
*)

From Stdlib Require Import Reals.

Set Implicit Arguments.
Local Open Scope R_scope.

Definition q3229335_complex : Type := (R * R)%type.

Definition q3229335_zero : q3229335_complex := (0, 0).

Definition q3229335_add
    (z w : q3229335_complex) : q3229335_complex :=
  (fst z + fst w, snd z + snd w).

Definition q3229335_neg
    (z : q3229335_complex) : q3229335_complex :=
  (- fst z, - snd z).

Definition q3229335_sub
    (z w : q3229335_complex) : q3229335_complex :=
  q3229335_add z (q3229335_neg w).

Definition q3229335_mul
    (z w : q3229335_complex) : q3229335_complex :=
  (fst z * fst w - snd z * snd w,
   fst z * snd w + snd z * fst w).

Definition q3229335_norm_sq
    (z : q3229335_complex) : R :=
  fst z * fst z + snd z * snd z.

Definition q3229335_norm
    (z : q3229335_complex) : R :=
  sqrt (q3229335_norm_sq z).

Definition q3229335_open_ball_zero
    (radius : R) (z : q3229335_complex) : Prop :=
  q3229335_norm z < radius.

Definition q3229335_has_complex_derivative_within_ball_at
    (f : q3229335_complex -> q3229335_complex)
    (radius : R)
    (z derivative : q3229335_complex) : Prop :=
  forall epsilon : R,
    0 < epsilon ->
    exists delta : R,
      0 < delta /\
      forall w : q3229335_complex,
        q3229335_open_ball_zero radius w ->
        q3229335_norm (q3229335_sub w z) < delta ->
        q3229335_norm
          (q3229335_sub
            (q3229335_sub (f w) (f z))
            (q3229335_mul derivative (q3229335_sub w z)))
        <= epsilon * q3229335_norm (q3229335_sub w z).

Definition q3229335_differentiable_on_ball
    (f : q3229335_complex -> q3229335_complex)
    (radius : R) : Prop :=
  forall z : q3229335_complex,
    q3229335_open_ball_zero radius z ->
    exists derivative : q3229335_complex,
      q3229335_has_complex_derivative_within_ball_at
        f radius z derivative.

Definition q3229335_maps_real_part_below
    (f : q3229335_complex -> q3229335_complex)
    (radius bound : R) : Prop :=
  forall z : q3229335_complex,
    q3229335_open_ball_zero radius z ->
    fst (f z) <= bound.

Theorem Complex_borelCaratheodory :
  forall (f : q3229335_complex -> q3229335_complex)
         (M R0 : R)
         (z : q3229335_complex),
    0 < M ->
    q3229335_differentiable_on_ball f R0 ->
    q3229335_maps_real_part_below f R0 M ->
    0 < R0 ->
    q3229335_open_ball_zero R0 z ->
    q3229335_norm (f z) <=
      2 * M * q3229335_norm z / (R0 - q3229335_norm z) +
      q3229335_norm (f q3229335_zero) *
        (R0 + q3229335_norm z) / (R0 - q3229335_norm z).
Admitted.
